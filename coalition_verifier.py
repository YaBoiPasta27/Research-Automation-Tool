"""
Coalition Membership Verifier — Sustainable Silicon Valley edition
------------------------------------------------------------------
Verifies that known member companies appear in archived snapshots of a
coalition membership page (via the Wayback Machine) at 3-year intervals
starting from a given date.

Also surfaces NEW institutions found in the snapshots that were not in
the pre-existing member list.

Input CSV format (matches sustainable_silicon_valley_members.csv):
    Columns: all_name_match, group, source1, source2, source3, source4, links
    - all_name_match : canonical member name used for fuzzy matching
    - group          : display / alternate name
    - source1-4      : presence flags (1 = present in that snapshot)
    - links          : footnotes mapping source numbers to URLs

Usage
-----
    1. Edit the CONFIG block near the top of this file.
    2. Run:  python coalition_verifier.py

Dependencies
------------
    pip install requests beautifulsoup4 rapidfuzz pandas openpyxl tqdm
"""

import re
import time
import json
import logging
from datetime import datetime, date
from dataclasses import dataclass, field
from typing import Optional
import os

import requests
from bs4 import BeautifulSoup
from rapidfuzz import fuzz, process
import pandas as pd
from tqdm import tqdm

# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s  %(levelname)-8s  %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger(__name__)

# ===========================================================================
# CONFIG — edit these values, then run:  python coalition_verifier.py
# ===========================================================================

# -- Required ---------------------------------------------------------------

# URL of the coalition's membership page (live or canonical)
COALITION_URL = "https://www.wp.sustainablesv.org/members/"

# Path to your members file (CSV or Excel; SSV format: all_name_match, group, source1-4 …)
MEMBERS_CSV = "sustainable silicon valley members - sustainable silicon valley members.csv"
# Note: also supports .xlsx format

# When to check — pick ONE of the two options below and comment out the other:
#
#   Option A — auto-generate years from a start date at a fixed interval:
#       START_DATE = "2006-01-01"    (INTERVAL_YEARS controls the step)
#
#   Option B — explicit list of specific years to check:
#       START_DATE = [2007, 2012, 2016, 2019, 2022]
#       (INTERVAL_YEARS is ignored when START_DATE is a list)
#
START_DATE = "2016-05-11"

# -- Output -----------------------------------------------------------------

# Prefix for output files (all saved as .xlsx Excel format):
#   <OUTPUT_PREFIX>_verification.xlsx  — one row per member x snapshot
#   <OUTPUT_PREFIX>_new_members.xlsx   — candidate new members not in your list
OUTPUT_PREFIX = "results"

# -- Optional ---------------------------------------------------------------

# Years between each Wayback snapshot check (only used when START_DATE is a string)
INTERVAL_YEARS = 3

# Fuzzy-match thresholds (token_set_ratio score, 0–100)
#   >= SCORE_CONFIRMED  →  "confirmed"
#   >= SCORE_UNCERTAIN  →  "uncertain"  (flag for manual review)
#   <  SCORE_UNCERTAIN  →  "not_found"
# Raise thresholds to reduce false positives; lower to catch more variants.
SCORE_CONFIRMED = 30
SCORE_UNCERTAIN = 10

# ===========================================================================
# Internal constants — no need to edit below this line
# ===========================================================================
WAYBACK_CDX_API    = "http://web.archive.org/cdx/search/cdx"
WAYBACK_BASE_URL   = "https://web.archive.org/web"
MAX_CDX_CANDIDATES = 5      # snapshot candidates to retrieve per year-window
REQUEST_TIMEOUT    = 30     # seconds per HTTP request
RETRY_LIMIT        = 3
RETRY_BACKOFF      = 5      # seconds between retries
POLITENESS_DELAY   = 1.5    # seconds between Wayback requests

# Candidate-block filters
BLOCK_MAX_WORDS      = 12
NEW_MEMBER_MIN_WORDS = 2

# HTML tags scanned for member names
CANDIDATE_TAGS = ["li", "a", "td", "p", "div", "span", "h3", "h4", "h5", "alt", "title"]

# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------

@dataclass
class MemberResult:
    canonical:     str           # all_name_match value
    aliases:       list          # alternate names tried
    timestamp:     str           # YYYYMMDDHHMMSS
    snapshot_url:  str
    status:        str           # confirmed | uncertain | not_found | error
    matched_text:  str = ""      # page fragment that matched
    best_alias:    str = ""      # which alias triggered the match
    score:         int = 0


@dataclass
class SnapshotResult:
    year:           int
    timestamp:      str
    snapshot_url:   str
    member_results: list = field(default_factory=list)
    new_candidates: list = field(default_factory=list)
    error:          Optional[str] = None


# ---------------------------------------------------------------------------
# Wayback Machine helpers
# ---------------------------------------------------------------------------

def _cdx_timestamps(url: str, year: int) -> list:
    """Query CDX API for up to MAX_CDX_CANDIDATES timestamps in `year`."""
    params = {
        "url":      url,
        "output":   "json",
        "from":     f"{year}0101",
        "to":       f"{year}1231",
        "limit":    MAX_CDX_CANDIDATES,
        "fl":       "timestamp,statuscode",
        "filter":   "statuscode:200",
        "collapse": "timestamp:6",
    }
    for attempt in range(1, RETRY_LIMIT + 1):
        try:
            r = requests.get(WAYBACK_CDX_API, params=params, timeout=REQUEST_TIMEOUT)
            r.raise_for_status()
            rows = r.json()
            if len(rows) <= 1:
                return []
            return [row[0] for row in rows[1:]]
        except Exception as exc:
            log.warning("CDX attempt %d/%d failed: %s", attempt, RETRY_LIMIT, exc)
            if attempt < RETRY_LIMIT:
                time.sleep(RETRY_BACKOFF * attempt)
    return []


def _pick_best_timestamp(timestamps: list, year: int) -> str:
    """Prefer the snapshot closest to July 1 of the year."""
    mid = datetime(year, 7, 1)
    def dist(ts):
        try:
            return abs((datetime.strptime(ts[:8], "%Y%m%d") - mid).days)
        except ValueError:
            return 9999
    return min(timestamps, key=dist)


def _fetch_html(url: str, timestamp: str) -> Optional[str]:
    """Fetch archived HTML with retries."""
    snapshot_url = f"{WAYBACK_BASE_URL}/{timestamp}/{url}"
    for attempt in range(1, RETRY_LIMIT + 1):
        try:
            r = requests.get(snapshot_url, timeout=REQUEST_TIMEOUT)
            r.raise_for_status()
            return r.text
        except Exception as exc:
            log.warning("Fetch attempt %d/%d (%s): %s",
                        attempt, RETRY_LIMIT, snapshot_url, exc)
            if attempt < RETRY_LIMIT:
                time.sleep(RETRY_BACKOFF * attempt)
    return None


# ---------------------------------------------------------------------------
# Text extraction
# ---------------------------------------------------------------------------

def _extract_blocks(html: str) -> list:
    """Return deduplicated visible text blocks likely to contain org names."""
    soup = BeautifulSoup(html, "html.parser")
    for tag in soup.find_all(["nav", "header", "footer", "script", "style", "noscript"]):
        tag.decompose()

    seen = set()
    blocks = []
    for tag in CANDIDATE_TAGS:
        for el in soup.find_all(tag):
            text = el.get_text(separator=" ").strip()
            key  = text.lower()
            if 2 <= len(text) <= 150 and key not in seen:
                seen.add(key)
                blocks.append(text)
    return blocks


# ---------------------------------------------------------------------------
# Normalisation
# ---------------------------------------------------------------------------

_LEGAL_RE = re.compile(
    r"\b(inc|llc|ltd|corp|plc|co|gmbh|ag|sa|bv|nv|se|lp|the|group|"
    r"corporation|company|associates|partners|services|solutions)\b\.?",
    re.IGNORECASE,
)

def _normalize(text: str) -> str:
    text = text.lower()
    text = _LEGAL_RE.sub(" ", text)
    text = re.sub(r"[^a-z0-9\s]", " ", text)
    return re.sub(r"\s+", " ", text).strip()


# ---------------------------------------------------------------------------
# Verification
# ---------------------------------------------------------------------------

def _best_match(aliases: list, norm_blocks: list, raw_blocks: list) -> tuple:
    """Try every alias; return (best_score, matched_raw_text, winning_alias)."""
    best_score, best_raw, best_alias = 0, "", ""
    for alias in aliases:
        match = process.extractOne(
            _normalize(alias), norm_blocks, scorer=fuzz.token_set_ratio
        )
        if match and match[1] > best_score:
            best_score = match[1]
            best_raw   = raw_blocks[match[2]]
            best_alias = alias
    return best_score, best_raw, best_alias


def _verify_members(members: list, raw_blocks: list, timestamp: str, snap_url: str) -> list:
    norm_blocks = [_normalize(b) for b in raw_blocks]
    results = []
    for m in members:
        score, matched_text, best_alias = _best_match(
            m["aliases"], norm_blocks, raw_blocks
        )
        if score >= SCORE_CONFIRMED:
            status = "confirmed"
        elif score >= SCORE_UNCERTAIN:
            status = "uncertain"
        else:
            status = "not_found"

        results.append(MemberResult(
            canonical    = m["canonical"],
            aliases      = m["aliases"],
            timestamp    = timestamp,
            snapshot_url = snap_url,
            status       = status,
            matched_text = matched_text[:100],
            best_alias   = best_alias,
            score        = score,
        ))
    return results


def _find_new_candidates(members: list, raw_blocks: list) -> list:
    """Blocks that don't match any known alias — potential new members."""
    all_aliases  = [a for m in members for a in m["aliases"]]
    norm_aliases = [_normalize(a) for a in all_aliases]
    candidates   = []

    for block in raw_blocks:
        words = block.split()
        if len(words) < NEW_MEMBER_MIN_WORDS or len(words) > BLOCK_MAX_WORDS:
            continue
        if block.endswith((".", "?", "!", ":")):
            continue
        if re.fullmatch(r"[\d\s\-/]+", block):
            continue
        match = process.extractOne(
            _normalize(block), norm_aliases, scorer=fuzz.token_set_ratio
        )
        if not match or match[1] < SCORE_UNCERTAIN:
            candidates.append(block)

    return candidates


# ---------------------------------------------------------------------------
# CSV/Excel loader — understands the SSV schema
# ---------------------------------------------------------------------------

def _detect_file_format(path: str) -> str:
    """Detect file format from extension."""
    _, ext = os.path.splitext(path.lower())
    if ext in ['.xlsx', '.xls']:
        return 'excel'
    return 'csv'

def load_members_csv(path: str) -> list:
    """
    Parse the SSV-style CSV or Excel file:
        Columns: all_name_match, group, source1-4, links

    Supports both .csv and .xlsx formats.
    Returns a list of dicts: {canonical, aliases, sources}
    """
    file_format = _detect_file_format(path)
    if file_format == 'excel':
        df = pd.read_excel(path, dtype=str).fillna("")
    else:
        df = pd.read_csv(path, dtype=str).fillna("")

    # Find canonical-name column
    canon_col = None
    for c in ["all_name_match", "canonical", "member", "company", "name"]:
        if c in df.columns:
            canon_col = c
            break
    if canon_col is None:
        canon_col = df.columns[0]
        log.warning("Using first column '%s' as canonical name", canon_col)

    alias_col   = "group" if "group" in df.columns else None
    source_cols = sorted([c for c in df.columns if re.match(r"source\d+", c, re.I)])

    members = []
    for _, row in df.iterrows():
        canonical = row[canon_col].strip()
        if not canonical:
            continue

        aliases = {canonical}
        if alias_col and row.get(alias_col, "").strip():
            aliases.add(row[alias_col].strip())

        # Extract names from parentheses: "Alphabet, Inc. (Google Inc.)" -> "Google Inc."
        for raw in list(aliases):
            parens = re.findall(r"\(([^)]+)\)", raw)
            aliases.update(p.strip() for p in parens)
            stripped = re.sub(r"\s*\([^)]*\)", "", raw).strip()
            if stripped:
                aliases.add(stripped)

        sources = {col: (row.get(col, "").strip() == "1") for col in source_cols}

        members.append({
            "canonical": canonical,
            "aliases":   list(aliases),
            "sources":   sources,
        })

    log.info("Loaded %d members from %s", len(members), path)
    return members


# ---------------------------------------------------------------------------
# Core orchestration
# ---------------------------------------------------------------------------

def _resolve_years(start_date, interval: int) -> list:
    """
    Return the list of years to check.

    - If start_date is a list/tuple of ints  → use it directly (sorted, deduped).
    - If start_date is a "YYYY-MM-DD" string → generate start, start+interval, …
      up to and including the current year.
    """
    if isinstance(start_date, (list, tuple)):
        years = sorted(set(int(y) for y in start_date))
        log.info("Using explicit year list: %s", years)
        return years

    start   = datetime.strptime(start_date, "%Y-%m-%d").year
    current = date.today().year
    years   = list(range(start, current + 1, interval))
    log.info("Auto-generated years (%d-yr intervals from %d): %s",
             interval, start, years)
    return years


def run_verification(
    coalition_url:  str,
    start_date,                  # str "YYYY-MM-DD"  OR  list of ints e.g. [2007, 2013, 2019]
    known_members:  list,
    interval_years: int  = 3,
    verbose:        bool = True,
) -> list:
    """
    Main entry point.

    Parameters
    ----------
    coalition_url   : Live URL of the coalition membership page.
    start_date      : Either a "YYYY-MM-DD" string (auto-generates years at
                      interval_years steps up to today) OR a list of ints
                      e.g. [2007, 2012, 2016, 2019] to check specific years.
    known_members   : Output of load_members_csv().
    interval_years  : Years between checks — ignored when start_date is a list.
    verbose         : Show tqdm progress bar.

    Returns
    -------
    list[SnapshotResult]
    """
    years = _resolve_years(start_date, interval_years)

    all_results = []
    iterator = tqdm(years, desc="Snapshots") if verbose else years

    for year in iterator:
        log.info("── %d ──", year)

        timestamps = _cdx_timestamps(coalition_url, year)
        if not timestamps:
            log.info("  No snapshot for %d", year)
            all_results.append(SnapshotResult(
                year=year, timestamp=str(year), snapshot_url="",
                error=f"No Wayback Machine snapshot found for {year}",
            ))
            continue

        ts       = _pick_best_timestamp(timestamps, year)
        snap_url = f"{WAYBACK_BASE_URL}/{ts}/{coalition_url}"
        log.info("  → %s", snap_url)

        html = _fetch_html(coalition_url, ts)
        if html is None:
            all_results.append(SnapshotResult(
                year=year, timestamp=ts, snapshot_url=snap_url,
                error="Failed to retrieve snapshot HTML",
            ))
            continue

        raw_blocks = _extract_blocks(html)
        log.info("  Extracted %d text blocks", len(raw_blocks))

        member_results = _verify_members(known_members, raw_blocks, ts, snap_url)
        new_candidates = _find_new_candidates(known_members, raw_blocks)

        log.info("  confirmed=%d  uncertain=%d  not_found=%d  new_candidates=%d",
                 sum(1 for r in member_results if r.status == "confirmed"),
                 sum(1 for r in member_results if r.status == "uncertain"),
                 sum(1 for r in member_results if r.status == "not_found"),
                 len(new_candidates))

        all_results.append(SnapshotResult(
            year=year,
            timestamp=ts,
            snapshot_url=snap_url,
            member_results=member_results,
            new_candidates=new_candidates,
        ))

        time.sleep(POLITENESS_DELAY)

    return all_results


# ---------------------------------------------------------------------------
# Output helpers
# ---------------------------------------------------------------------------

def to_ssv_format(
    results:       list,
    known_members: list,
    original_csv:  str,
) -> pd.DataFrame:
    """
    Rebuild a CSV that mirrors the original SSV schema:

        all_name_match | group | source1 | source2 | … | sourceN

    Source columns are built entirely from this run's snapshots, numbered
    fresh from 1 regardless of what existed in the original file.
    Each sourceN column corresponds to one checked snapshot year (chronological).
    A cell contains the source number if the member was confirmed/uncertain,
    blank if not found.

    New candidate members are appended at the bottom.
    The original file is only read for all_name_match and group values.
    """
    # --- Snapshots that succeeded, sorted chronologically --------------------
    valid_snaps = [s for s in results if not s.error and s.member_results]
    valid_snaps.sort(key=lambda s: s.year)

    # --- Load original file for name/group lookup only (supports CSV and Excel) ------
    file_format = _detect_file_format(original_csv)
    if file_format == 'excel':
        orig_df = pd.read_excel(original_csv, dtype=str).fillna("")
    else:
        orig_df = pd.read_csv(original_csv, dtype=str).fillna("")
    
    canon_col = next(
        (c for c in ["all_name_match", "canonical", "member", "company", "name"]
         if c in orig_df.columns),
        orig_df.columns[0],
    )
    group_col = "group" if "group" in orig_df.columns else None

    orig_lookup = {}
    for _, row in orig_df.iterrows():
        key = row[canon_col].strip()
        if key:
            orig_lookup[key] = row

    # --- Source columns: one per snapshot, numbered from 1 -------------------
    new_years    = [s.year for s in valid_snaps]
    src_cols     = [f"source{i + 1}" for i in range(len(new_years))]
    src_numbers  = list(range(1, len(new_years) + 1))   # 1, 2, 3, …

    # --- Build lookup: canonical → {year: status} ----------------------------
    member_year_status = {}
    for snap in valid_snaps:
        for mr in snap.member_results:
            member_year_status.setdefault(mr.canonical, {})[snap.year] = mr.status

    # --- Rows for known members -----------------------------------------------
    rows = []
    for m in known_members:
        canonical = m["canonical"]
        orig_row  = orig_lookup.get(canonical, {})

        row = {"all_name_match": canonical}
        if group_col:
            row["group"] = orig_row.get(group_col, canonical) if hasattr(orig_row, "get") else canonical

        year_status = member_year_status.get(canonical, {})
        for col, year, num in zip(src_cols, new_years, src_numbers):
            status = year_status.get(year, "not_found")
            row[col] = str(num) if status in ("confirmed", "uncertain") else ""

        rows.append(row)

    # --- Rows for new candidate members --------------------------------------
    all_candidates = {}
    for snap in valid_snaps:
        for cand in snap.new_candidates:
            all_candidates.setdefault(cand, {})[snap.year] = True

    for cand, year_seen in sorted(all_candidates.items()):
        row = {"all_name_match": cand}
        if group_col:
            row["group"] = cand
        for col, year, num in zip(src_cols, new_years, src_numbers):
            row[col] = str(num) if year_seen.get(year) else ""
        rows.append(row)

    # --- Assemble DataFrame ---------------------------------------------------
    all_cols = ["all_name_match"] + ([group_col] if group_col else []) + src_cols
    ssv_df = pd.DataFrame(rows)
    for col in all_cols:
        if col not in ssv_df.columns:
            ssv_df[col] = ""
    return ssv_df[all_cols].fillna("")


def to_dataframes(results: list) -> tuple:
    """
    Returns:
      verification_df  — one row per (member x snapshot)
      new_members_df   — deduplicated candidate new members
    """
    ver_rows, new_rows = [], []

    for snap in results:
        year     = snap.year
        ts       = snap.timestamp
        snap_url = snap.snapshot_url
        err      = snap.error or ""

        if snap.member_results:
            for mr in snap.member_results:
                ver_rows.append({
                    "year":          year,
                    "timestamp":     ts,
                    "snapshot_url":  snap_url,
                    "member":        mr.canonical,
                    "aliases_tried": " | ".join(mr.aliases),
                    "status":        mr.status if not err else "error",
                    "matched_text":  mr.matched_text,
                    "best_alias":    mr.best_alias,
                    "fuzzy_score":   mr.score,
                    "error":         err,
                })
        else:
            ver_rows.append({
                "year": year, "timestamp": ts, "snapshot_url": snap_url,
                "member": "(snapshot failed)", "aliases_tried": "",
                "status": "error", "matched_text": "", "best_alias": "",
                "fuzzy_score": 0, "error": err,
            })

        for cand in snap.new_candidates:
            new_rows.append({
                "year": year, "timestamp": ts,
                "snapshot_url": snap_url, "candidate_name": cand,
            })

    ver_df = pd.DataFrame(ver_rows)

    if new_rows:
        new_df = (
            pd.DataFrame(new_rows)
            .sort_values("candidate_name")
            .drop_duplicates(subset=["candidate_name"])
            .reset_index(drop=True)
        )
    else:
        new_df = pd.DataFrame(
            columns=["year", "timestamp", "snapshot_url", "candidate_name"]
        )

    return ver_df, new_df


def save_results(
    results:       list,
    output_prefix: str  = "results",
    known_members: list = None,
    original_csv:  str  = None,
) -> None:
    ver_df, new_df = to_dataframes(results)
    ver_path = f"{output_prefix}_verification.xlsx"
    new_path = f"{output_prefix}_new_members.xlsx"
    ssv_path = f"{output_prefix}_updated_members.xlsx"

    ver_df.to_excel(ver_path, index=False, engine='openpyxl')
    new_df.to_excel(new_path, index=False, engine='openpyxl')
    log.info("Saved → %s", ver_path)
    log.info("Saved → %s", new_path)

    # Third file: updated Excel in original SSV format
    if known_members is not None and original_csv is not None:
        ssv_df = to_ssv_format(results, known_members, original_csv)
        ssv_df.to_excel(ssv_path, index=False, engine='openpyxl')
        log.info("Saved → %s", ssv_path)
    else:
        ssv_path = None

    # Summary table
    print("\n" + "="*62)
    print("VERIFICATION SUMMARY  (confirmed / uncertain / not_found)")
    print("="*62)
    if not ver_df.empty and "status" in ver_df.columns:
        pivot = (
            ver_df[ver_df["member"].str.strip() != ""]
            .groupby(["year", "status"])
            .size()
            .unstack(fill_value=0)
        )
        for col in ["confirmed", "uncertain", "not_found", "error"]:
            if col not in pivot.columns:
                pivot[col] = 0
        print(pivot[["confirmed", "uncertain", "not_found", "error"]].to_string())

    # Items needing manual review
    print("\n" + "="*62)
    print("MEMBERS NEEDING REVIEW  (uncertain or not_found)")
    print("="*62)
    if not ver_df.empty:
        review = ver_df[ver_df["status"].isin(["uncertain", "not_found"])]
        if not review.empty:
            for _, row in review.sort_values(["member", "year"]).iterrows():
                print(f"  [{row['status'].upper():<10}] {str(row['member']):<45} "
                      f"year={row['year']}  score={row['fuzzy_score']}")
        else:
            print("  All members confirmed at every time-point!")

    # New candidates
    print("\n" + "="*62)
    print(f"CANDIDATE NEW MEMBERS  ({len(new_df)} unique)")
    print("="*62)
    if not new_df.empty:
        for _, row in new_df.head(40).iterrows():
            print(f"  • {str(row['candidate_name']):<55} first seen {row['year']}")
        if len(new_df) > 40:
            print(f"  ... and {len(new_df)-40} more — see {new_path}")
    else:
        print("  No new candidates detected.")

    if ssv_path:
        print("\n" + "="*62)
        print(f"UPDATED MEMBERS CSV (original format)  →  {ssv_path}")
        print("="*62)
        print("  Existing source columns preserved. New snapshot columns appended.")

    # Source legend — original links preserved + new ones from this run
    print("\n" + "="*62)
    print("SOURCE KEY")
    print("="*62)

    # Pull existing links from original CSV if available
    if original_csv is not None:
        try:
            orig = pd.read_csv(original_csv, dtype=str).fillna("")
            if "links" in orig.columns:
                raw_links = orig["links"].dropna()
                raw_links = raw_links[raw_links.str.strip() != ""]
                if not raw_links.empty:
                    print("  (from original file)")
                    for line in raw_links.iloc[0].splitlines():
                        line = line.strip()
                        if line:
                            print(f"    {line}")
        except Exception:
            pass

    # New sources from this run
    valid_snaps = sorted(
        [s for s in results if not s.error and s.member_results],
        key=lambda s: s.year,
    )
    if valid_snaps:
        print("  (from this run)")
        for i, snap in enumerate(valid_snaps):
            src_num = i + 1
            try:
                src_date = datetime.strptime(snap.timestamp[:8], "%Y%m%d").strftime("%-m.%-d.%Y")
            except Exception:
                src_date = str(snap.year)
            print(f"    {src_num} - {snap.snapshot_url}  {src_date}")


def to_json(results: list) -> str:
    out = []
    for snap in results:
        out.append({
            "year":           snap.year,
            "timestamp":      snap.timestamp,
            "snapshot_url":   snap.snapshot_url,
            "error":          snap.error,
            "member_results": [
                {
                    "member":       mr.canonical,
                    "status":       mr.status,
                    "matched_text": mr.matched_text,
                    "best_alias":   mr.best_alias,
                    "score":        mr.score,
                }
                for mr in snap.member_results
            ],
            "new_candidates": snap.new_candidates,
        })
    return json.dumps(out, indent=2)


# ---------------------------------------------------------------------------
# Entry point — reads CONFIG values set at the top of this file
# ---------------------------------------------------------------------------

def main():
    known_members = load_members_csv(MEMBERS_CSV)

    results = run_verification(
        coalition_url  = COALITION_URL,
        start_date     = START_DATE,
        known_members  = known_members,
        interval_years = INTERVAL_YEARS,
    )

    save_results(
        results        = results,
        output_prefix  = OUTPUT_PREFIX,
        known_members  = known_members,
        original_csv   = MEMBERS_CSV,
    )


if __name__ == "__main__":
    main()
