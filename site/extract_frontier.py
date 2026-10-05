#!/usr/bin/env python3
"""Extract site/frontier.json from Frontier.lean.  python3 stdlib only; read-only on Lean files.

Frontier.lean is the leaderboard's source of truth; this script NEVER writes to it.  It derives a small JSON projection that the static-site
generator (site/generate.py) consumes.

Extraction strategy, in preference order:

1. A machine-readable JSON block embedded in the module docstring between the sentinel lines
   ``<<<FRONTIER-JSON`` and ``FRONTIER-JSON>>>`` (a proposed convention, not yet
   adopted by Frontier.lean; schema in site/README.md).
   If present, it is parsed and cross-checked against the Lean text.

2. Two pinned, deliberately brittle patterns on the load-bearing lines of the file:

       def frontierConstant : ℚ := <num> / <den>
       exact <Endpoint.theorem_name> K        (the sole such line, inside `theorem frontier`)

   plus the shape of ``theorem frontier : <Shape> frontierConstant``, the ``#assert_axioms``
   lines, and the committed ``#assert_statement_fingerprint`` lines.  If the Frontier owner
   reformats these lines, extraction fails LOUDLY (non-zero exit) instead of letting the
   public site drift silently.  That is a feature.

Usage:
    python3 site/extract_frontier.py            # (re)write site/frontier.json
    python3 site/extract_frontier.py --check    # verify site/frontier.json is fresh; exit 1 on drift
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

SITE = Path(__file__).resolve().parent
REPO = SITE.parent
FRONTIER_LEAN = REPO / "Frontier.lean"
OUT = SITE / "frontier.json"

SENTINEL_OPEN = "<<<FRONTIER-JSON"
SENTINEL_CLOSE = "FRONTIER-JSON>>>"

# Volatile provenance keys: informational, excluded from the --check comparison.
VOLATILE_KEYS = {"provenance"}


def die(msg: str) -> None:
    sys.stderr.write(f"extract_frontier: ERROR: {msg}\n")
    sys.exit(1)


def strip_lean_comments(text: str) -> str:
    """Remove Lean block comments (/- ... -/, nesting-aware) and line comments (-- ...)."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        two = text[i : i + 2]
        if two == "/-":
            depth += 1
            i += 2
        elif two == "-/" and depth > 0:
            depth -= 1
            i += 2
        elif depth > 0:
            i += 1
        elif two == "--":
            j = text.find("\n", i)
            i = n if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def exact_decimal(fr: Fraction) -> str:
    """Exact decimal string for a rational with terminating decimal expansion."""
    den = fr.denominator
    k2 = k5 = 0
    while den % 2 == 0:
        den //= 2
        k2 += 1
    while den % 5 == 0:
        den //= 5
        k5 += 1
    if den != 1:
        die(f"frontierConstant {fr} has no terminating decimal expansion")
    k = max(k2, k5)
    if k == 0:
        return str(fr.numerator)
    scaled = fr.numerator * 10**k // fr.denominator
    sign = "-" if scaled < 0 else ""
    scaled = abs(scaled)
    ip, fp = divmod(scaled, 10**k)
    return f"{sign}{ip}.{str(fp).zfill(k).rstrip('0')}"


def git(args: list[str]) -> str:
    try:
        return subprocess.run(
            ["git", "-C", str(REPO), *args],
            capture_output=True, text=True, check=True,
        ).stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        return ""


def parse_sentinel_block(text: str) -> dict | None:
    if SENTINEL_OPEN not in text:
        return None
    try:
        block = text.split(SENTINEL_OPEN, 1)[1].split(SENTINEL_CLOSE, 1)[0]
        data = json.loads(block)
    except (IndexError, json.JSONDecodeError) as exc:
        die(f"malformed {SENTINEL_OPEN} block in Frontier.lean: {exc}")
    if data.get("schema") != 1 or not data.get("records"):
        die("FRONTIER-JSON block must have schema=1 and a non-empty records list")
    return data


def parse_pinned(text: str) -> dict:
    """The regex fallback: pinned patterns on Frontier.lean's load-bearing lines."""
    stripped = strip_lean_comments(text)

    m = re.search(
        r"^def\s+frontierConstant\s*:\s*ℚ\s*:=\s*(\d+)\s*(?:/\s*(\d+))?\s*$",
        stripped, re.M,
    )
    if not m:
        die("could not find `def frontierConstant : ℚ := <num> / <den>` on a single line")
    num, den = int(m.group(1)), int(m.group(2) or 1)
    constant = Fraction(num, den)

    m = re.search(r"^theorem\s+frontier\s*:\s*([A-Za-z0-9_.]+)\s+frontierConstant\b", stripped, re.M)
    if not m:
        die("could not find `theorem frontier : <Shape> frontierConstant`")
    shape = m.group(1)

    exacts = re.findall(r"^\s*exact\s+([A-Za-z0-9_.']+)\s+K\s*$", stripped, re.M)
    if len(exacts) != 1:
        die(f"expected exactly one `exact <endpoint> K` line, found {len(exacts)}")
    endpoint_ref = exacts[0]

    opens = re.findall(r"^open\s+([A-Za-z0-9_.]+)\s*$", stripped, re.M)
    imports = re.findall(r"^import\s+([A-Za-z0-9_.]+)\s*$", stripped, re.M)

    last = endpoint_ref.rsplit(".", 1)[-1]
    endpoint_file = None
    for mod in imports:
        p = REPO / (mod.replace(".", "/") + ".lean")
        if p.is_file() and re.search(rf"^theorem\s+{re.escape(last)}\b", p.read_text(encoding="utf-8"), re.M):
            endpoint_file = str(p.relative_to(REPO))
            break
    if endpoint_file is None:
        die(f"endpoint theorem `{last}` not found in any module imported by Frontier.lean")

    qualified = endpoint_ref
    for o in opens:
        if endpoint_file.replace("/", ".").startswith(o + "."):
            qualified = f"{o}.{endpoint_ref}"
            break

    shape_stmt = None
    m = re.search(rf"^def\s+{re.escape(shape)}\b[^\n]*:=\s*\n\s*(.+)$", stripped, re.M)
    if m:
        shape_stmt = m.group(1).strip()

    axiom_asserts = re.findall(r"^#assert_axioms\s+([A-Za-z0-9_.]+)", stripped, re.M)
    fingerprints = dict(
        re.findall(r'^#assert_statement_fingerprint\s+([A-Za-z0-9_.]+)\s+"([^"]+)"', stripped, re.M)
    )

    dec = exact_decimal(constant)
    record = {
        "slug": "omega-" + dec.replace(".", "p"),
        "class": "unconditional" if shape == "OmegaBound" else shape,
        "shape": f"Frontier.{shape}",
        "shape_statement": shape_stmt,
        "constant": f"{constant.numerator}/{constant.denominator}",
        "decimal": dec,
        "frontier_theorem": "Frontier.frontier",
        "endpoint_theorem": qualified,
        "endpoint_file": endpoint_file,
    }
    return {
        "schema": 1,
        "source": "Frontier.lean (pinned-pattern extraction)",
        "record": record,
        "records": [record],
        "axiom_asserts": axiom_asserts,
        "statement_fingerprints": fingerprints,
    }


def build() -> dict:
    if not FRONTIER_LEAN.is_file():
        die("Frontier.lean not found at repository root")
    text = FRONTIER_LEAN.read_text(encoding="utf-8")

    sentinel = parse_sentinel_block(text)
    if sentinel is not None:
        records = sentinel["records"]
        # Cross-check: every declared theorem must appear in the Lean text OUTSIDE the JSON
        # block itself (the block must not satisfy its own check).
        lean_only = text.split(SENTINEL_OPEN, 1)[0] + text.split(SENTINEL_CLOSE, 1)[-1]
        for r in records:
            name = r.get("theorem", "").rsplit(".", 1)[-1]
            if not name or name not in lean_only:
                die(f"FRONTIER-JSON row {r.get('slug')} cites `{r.get('theorem')}`, "
                    "not found in the Lean text outside the JSON block")
        data = {
            "schema": 1,
            "source": "Frontier.lean (FRONTIER-JSON sentinel block)",
            "record": records[0],
            "records": records,
            "axiom_asserts": re.findall(r"^#assert_axioms\s+([A-Za-z0-9_.]+)", text, re.M),
            "statement_fingerprints": dict(
                re.findall(r'^#assert_statement_fingerprint\s+([A-Za-z0-9_.]+)\s+"([^"]+)"', text, re.M)
            ),
        }
    else:
        data = parse_pinned(text)

    data["provenance"] = {
        "generated_utc": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
        "repo_commit": git(["rev-parse", "HEAD"]) or "unknown",
        "frontier_lean_tracked": bool(git(["ls-files", "--", "Frontier.lean"])),
    }
    return data


def stable(d: dict) -> dict:
    return {k: v for k, v in d.items() if k not in VOLATILE_KEYS}


def main(argv: list[str]) -> int:
    data = build()
    if "--check" in argv:
        if not OUT.is_file():
            die("site/frontier.json missing; run `python3 site/extract_frontier.py`")
        existing = json.loads(OUT.read_text(encoding="utf-8"))
        if stable(existing) != stable(data):
            die("site/frontier.json is STALE relative to Frontier.lean; "
                "re-run `python3 site/extract_frontier.py` and commit the result")
        print("extract_frontier: OK - site/frontier.json matches Frontier.lean")
        return 0
    OUT.write_text(json.dumps(data, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")
    r = data["record"]
    print(f"extract_frontier: wrote {OUT.relative_to(REPO)}: "
          f"omega < {r['decimal']} (= {r['constant']}) via {r['endpoint_theorem']}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
