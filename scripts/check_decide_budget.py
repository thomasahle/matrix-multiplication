#!/usr/bin/env python3
"""Enforce the DESIGN.md rule that no single reduction command becomes the memory boundary.

DESIGN.md:590 -- "No single `decide`, `decide +kernel`, or `decide_cbv` may become the project's
memory boundary.", in "Reduction and elaboration budgets" (DESIGN.md:580) -- and DESIGN.md:545,
which reserves `decide` for "genuinely tiny closed finite facts".  Both went long unenforced.  On 2026-08-28 one
`decide +kernel` in `SimplifiedVolumeRecurrenceZeroFour1` needed 133 GB, and the whole
`SimplifiedVolumeRecurrenceEdge*` family needed 7.3-19.6 GB per module, on a 16 GB machine.

"Genuinely tiny" is not mechanically decidable, so this gate is an honest two-part proxy:

  MEASURED  `scripts/decide_memory_budget.tsv` records real per-module peak RSS.  A module whose
            recorded peak exceeds the budget (default 6000 MB, see `--budget`) fails.  This is the
            authority: where a number exists, no proxy is consulted.

  STATIC    For an *un-measured* module, the proxy is the literal numeric payload that a
            `decide` / `decide +kernel` / `decide_cbv` declaration drags into its own goal:
            the digits in the declaration itself, plus the digits of same-module definitions it
            names (transitively), plus the digits of every imported module whose namespace the
            declaration explicitly mentions.  That last term is the load-bearing one --
            `SimplifiedVolumeRecurrenceZeroFour1.lean` is a 2 KB file, and its 133 GB comes
            entirely from the sixteen `Zero4Data*`/`TopData*` payload modules its proof inlines
            with `rw [... .data_eq_rawData]` before reducing.  A proxy that looked only at file
            size would have missed today's worst case completely.

  OPAQUE    `opaque name : ... := by decide` hides a reduction obligation from every tool that
            scans for `theorem`; today's investigation found that blind spot the hard way.  The
            census is reported here, and an opaque-decide *outside* `MatrixMultiplication/Generated`
            fails -- the same boundary `scripts/trust_scan.sh` already draws for `opaque` itself.

REPOSITORY, NOT WORKING TREE.  Five lanes hold uncommitted edits in this checkout, and reading
working-tree state as repository state produced three wrong conclusions on 2026-08-28.  Sources are
therefore read from `git archive HEAD` -- one process, the whole committed tree, no per-file
`git show` fan-out and no chance of a lane's in-flight `.lean` file being scored as landed work.
Pass `--worktree` to score your own uncommitted edits before you commit them; CI must not.

NO `grep -r` WITH A FILE GLOB.  `grep` on the author's machine is ugrep 7.8.4, where
`grep -rl PAT dir/*.lean` returns zero matches *silently* instead of erroring, while
`--include=` and `find -exec` behave the same as GNU grep on ubuntu-latest.  This script shells
out only to `git archive` and does all matching in Python, so the hazard cannot apply.

DEBT IS GRANDFATHERED, NOT FORGIVEN.  The repository already violates this rule in ~100 places.
`scripts/decide_budget_grandfathered.txt` lists them, is printed as a count on every clean run, and
may only shrink: an entry that stops violating is a notice, never a failure, so the commit that
pays debt down can never be the commit that goes red.  A grandfathered entry that gets *worse*
(payload grown past `--regression-slack`, or a measured peak grown past its recorded value) fails.

Usage:
  python3 scripts/check_decide_budget.py                 # the CI gate
  python3 scripts/check_decide_budget.py --report        # ranked payloads, no gate
  python3 scripts/check_decide_budget.py --update        # regenerate the grandfather file
"""

from __future__ import annotations

import argparse
import io
import os
import re
import subprocess
import sys
import tarfile
from collections import defaultdict

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BUDGET_FILE = "scripts/decide_memory_budget.tsv"
GRANDFATHER_FILE = "scripts/decide_budget_grandfathered.txt"

# Only the trees that a configured Lake target can build (see lakefile.toml).  `better_bound/` is
# untracked-by-Lake producer scratch: it is deliberately NOT scanned, because a `decide` there is
# never elaborated by any gate and because this repository's lane rules forbid editing it.
ROOT_PREFIXES = (
    "AlgebraicComplexity/",
    "MatrixMultiplication/",
    "AxiomAudit/",
    "AxiomAuditCertificate/",
)
ROOT_FILES = (
    "AlgebraicComplexity.lean",
    "AlgebraicComplexityClients.lean",
    "MatrixMultiplication.lean",
    "MatrixMultiplicationCertificate.lean",
    "AxiomAudit.lean",
    "AxiomAuditCertificate.lean",
    "Frontier.lean",
)
GENERATED_PREFIX = "MatrixMultiplication/Generated/"

# --- defaults -------------------------------------------------------------------------------
#
# BUDGET: ubuntu-latest gives 16 GB.  `.github/workflows/ci.yml` pins LEAN_NUM_THREADS=2, so two
# modules elaborate at once; 2 x 6000 MB = 12 GB leaves ~4 GB for the OS, Lake, and the olean cache.
# The number is also the one that separates today's measurements the way the policy intends: it
# passes the TopScatter family (2467-4172 MB) and the A4 closure (max 3319 MB), and fails the Edge
# family (7.3-19.6 GB) and ZeroFour1 (133 GB).
DEFAULT_BUDGET_MB = 6000

# PAYLOAD THRESHOLD, in digit characters of literal numeric payload reachable from one reduction.
# Calibrated against the committed tree (`--report` reproduces the table): of 28,228 reduction
# declarations the median drags 134 digits, the 90th percentile 2,382 and the 99th 4,290.  The
# families with measured peaks sit far above all of that -- TopScatter ~15,900 digits for
# 2467-4172 MB, Edge ~54,000 for 7.3-19.6 GB, ZeroFour1 93,785 for 133 GB.  12,000 digits is ~2.8x
# the 99th percentile and ~75% of the smallest family ever measured above 2 GB.  It selects 85
# declarations out of 28,228; a 4,000-digit line would have selected 692, and a 2,000-digit line
# thousands, which is how a gate gets switched off instead of fixed.
DEFAULT_PAYLOAD_THRESHOLD = 12000

# A grandfathered payload may drift with regenerated data; it may not balloon.
DEFAULT_REGRESSION_SLACK = 0.25
REGRESSION_FLOOR = 1000

DECIDE_TACTICS = ("decide", "decide_cbv")
DECL_KEYWORDS = (
    "opaque", "theorem", "lemma", "example", "def", "abbrev",
    "instance", "structure", "class", "inductive",
)

RE_IMPORT = re.compile(r"^import\s+(\S+)", re.M)
RE_NAMESPACE_DECL = re.compile(r"^namespace\s+(\S+)", re.M)
RE_DIGIT = re.compile(r"[0-9]")
# `decide`, `decide +kernel`, `decide_cbv` in tactic position; never `Decidable`, `decide_eq_true`,
# `Nat.decide`, nor a `decide` that is part of a longer identifier.
RE_DECIDE = re.compile(
    r"(?<![A-Za-z0-9_.])(?:decide(?:[ \t]*\+[ \t]*kernel)?|decide_cbv)(?![A-Za-z0-9_])"
)
RE_COMMAND = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)?"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)[ \t]+)*"
    r"(" + "|".join(DECL_KEYWORDS) + r"|namespace|end|section)"
    r"(?:[ \t]+([^\s:({\[]+))?",
    re.M,
)
# An uppercase-initial dotted prefix is how this project names a payload module's namespace
# (`Zero4Data7.data_eq_rawData`, `Mass3.expectedNumerators`).
RE_NAMESPACE_REF = re.compile(r"(?<![A-Za-z0-9_.'])([A-Z][A-Za-z0-9_']*)\.")
# A bare identifier: a same-module definition the declaration names.
RE_LOCAL_REF = re.compile(r"(?<![A-Za-z0-9_.'])([a-zA-Z_][A-Za-z0-9_']*)(?![A-Za-z0-9_'.])")
RE_COMMENT_TOKEN = re.compile(r"--|/-|-/")


def die(message: str) -> "None":
    print("FAIL: " + message, file=sys.stderr)
    raise SystemExit(2)


# --- source loading -------------------------------------------------------------------------

def load_sources(worktree: bool) -> "dict[str, str]":
    """Every `.lean` file under a configured Lake root, keyed by repo-relative path."""
    if worktree:
        sources = {}
        for prefix in ROOT_PREFIXES:
            for dirpath, _dirnames, filenames in os.walk(os.path.join(REPO, prefix)):
                for name in filenames:
                    if not name.endswith(".lean"):
                        continue
                    full = os.path.join(dirpath, name)
                    rel = os.path.relpath(full, REPO)
                    with open(full, "rb") as handle:
                        sources[rel] = handle.read().decode("utf-8", "replace")
        for name in ROOT_FILES:
            full = os.path.join(REPO, name)
            if os.path.exists(full):
                with open(full, "rb") as handle:
                    sources[name] = handle.read().decode("utf-8", "replace")
        return sources

    try:
        archive = subprocess.run(
            ["git", "archive", "--format=tar", "HEAD"],
            cwd=REPO, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        ).stdout
    except (OSError, subprocess.CalledProcessError) as error:
        die("cannot read the repository with `git archive HEAD`: %s" % (error,))

    sources = {}
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        for member in tar:
            name = member.name
            if not member.isfile() or not name.endswith(".lean"):
                continue
            if not (name.startswith(ROOT_PREFIXES) or name in ROOT_FILES):
                continue
            handle = tar.extractfile(member)
            if handle is not None:
                sources[name] = handle.read().decode("utf-8", "replace")
    if not sources:
        die("`git archive HEAD` produced no Lean sources under the configured Lake roots; "
            "the root list in this script is stale or HEAD is not the project.")
    return sources


def strip_comments(text: str) -> str:
    """Blank out `--` line comments and *nested* `/- -/` block comments, preserving line numbers.

    Prose must not be able to create or hide a `decide`, a `namespace`, or a numeric payload.
    """
    pieces = []
    index = 0
    depth = 0
    length = len(text)
    while index < length:
        match = RE_COMMENT_TOKEN.search(text, index)
        if match is None:
            if depth == 0:
                pieces.append(text[index:])
            else:
                pieces.append(re.sub(r"[^\n]", " ", text[index:]))
            break
        start, token = match.start(), match.group(0)
        chunk = text[index:start]
        pieces.append(chunk if depth == 0 else re.sub(r"[^\n]", " ", chunk))
        if depth > 0:
            if token == "/-":
                depth += 1
            elif token == "-/":
                depth -= 1
            pieces.append("  ")
            index = start + 2
        elif token == "--":
            end = text.find("\n", start)
            if end < 0:
                pieces.append(" " * (length - start))
                break
            pieces.append(" " * (end - start))
            index = end
        else:  # "/-" opening, or a stray "-/" which Lean would reject anyway
            if token == "/-":
                depth += 1
            pieces.append("  ")
            index = start + 2
    return "".join(pieces)


# --- analysis -------------------------------------------------------------------------------

class Declaration:
    __slots__ = ("path", "line", "keyword", "name", "payload", "namespaces", "has_decide")

    def __init__(self, path, line, keyword, name, payload, namespaces, has_decide):
        self.path = path
        self.line = line
        self.keyword = keyword
        self.name = name
        self.payload = payload
        self.namespaces = namespaces
        self.has_decide = has_decide

    @property
    def key(self) -> str:
        """Stable across edits: the line number moves, the declaration name does not."""
        return "%s::%s" % (self.path, self.name)


OPENERS = "([{\u27e8"
CLOSERS = ")]}\u27e9"


def reduction_scope(body, at):
    """The text one reduction command is actually responsible for, and whether it is the proof.

    `theorem floor_le_lower : rootFloor \u27e81, by decide\u27e9 \u2264 lower := by norm_num [...]` is a
    600 KB generated declaration whose `decide` proves `1 < 116`.  Charging that declaration's whole
    payload to that `decide` is the single most common false positive in this repository -- the
    `\u27e8n, by decide\u27e9` bound proof is everywhere.  So: scan back for the innermost UNMATCHED
    bracket.  If there is none the reduction is the declaration's own proof and owns the whole
    declaration; if there is one the reduction is a side condition inside that bracketed group and
    owns only it.  Unbalanced text falls back to the whole declaration, which over-counts rather
    than under-counts, because a parse this checker cannot follow is not a parse it should excuse.
    """
    depth = 0
    index = at - 1
    while index >= 0:
        character = body[index]
        if character in CLOSERS:
            depth += 1
        elif character in OPENERS:
            if depth == 0:
                forward = index
                nesting = 0
                while forward < len(body):
                    if body[forward] in OPENERS:
                        nesting += 1
                    elif body[forward] in CLOSERS:
                        nesting -= 1
                        if nesting == 0:
                            return body[index: forward + 1], False
                    forward += 1
                return body, True
            depth -= 1
        index -= 1
    return body, True


def module_name(path: str) -> str:
    return path[: -len(".lean")].replace("/", ".")


def analyse(sources: "dict[str, str]"):
    """Return (declarations, payload_of_declaration, opaque_decides).

    `payload_of_declaration[decl.key]` is the digit count of literal numeric payload that one
    reduction command in `decl` has to chew through, under the model described at the top of the
    file.  It is deliberately an *under*-estimate wherever name resolution is ambiguous: a proxy
    that guesses high would fail honest work, and a gate nobody trusts gets deleted.
    """
    clean = {path: strip_comments(text) for path, text in sources.items()}
    imports = {path: RE_IMPORT.findall(text) for path, text in clean.items()}
    module_digits = {path: len(RE_DIGIT.findall(text)) for path, text in clean.items()}
    path_of_module = {module_name(path): path for path in clean}

    # namespace short name -> the modules that open it
    namespace_modules = defaultdict(set)
    for path, text in clean.items():
        for declared in RE_NAMESPACE_DECL.findall(text):
            namespace_modules[declared.split(".")[-1]].add(path)

    import_closure_cache = {}

    def import_closure(path):
        cached = import_closure_cache.get(path)
        if cached is not None:
            return cached
        seen = {path}
        stack = [path]
        while stack:
            current = stack.pop()
            for imported in imports.get(current, ()):
                target = path_of_module.get(imported)
                if target is not None and target not in seen:
                    seen.add(target)
                    stack.append(target)
        import_closure_cache[path] = seen
        return seen

    declarations = []
    payloads = {}
    opaque_decides = []

    for path, text in clean.items():
        if not RE_DECIDE.search(text) and "opaque" not in text:
            continue
        commands = list(RE_COMMAND.finditer(text))
        local = []
        for position, command in enumerate(commands):
            keyword, name = command.group(1), command.group(2)
            if keyword not in DECL_KEYWORDS or not name:
                continue
            # A declaration runs to the next declaration-level command; everything between is its
            # statement and its tactic proof.
            following = position + 1
            while following < len(commands) and commands[following].group(1) not in (
                DECL_KEYWORDS + ("namespace", "end", "section")
            ):
                following += 1
            end = commands[following].start() if following < len(commands) else len(text)
            body = text[command.start(): end]
            local.append({
                "short": name.split(".")[-1],
                "body": body,
                "digits": len(RE_DIGIT.findall(body)),
                "line": text.count("\n", 0, command.start()) + 1,
                "keyword": keyword,
                "name": name,
                "decide": bool(RE_DECIDE.search(body)),
            })

        index_by_short = {}
        for position, entry in enumerate(local):
            index_by_short.setdefault(entry["short"], position)

        local_cache = {}

        def local_payload(position, seen=frozenset()):
            """Digits of a declaration plus, transitively, the same-module definitions it names."""
            cached = local_cache.get(position)
            if cached is not None:
                return cached
            if position in seen:
                return 0
            total = local[position]["digits"]
            for reference in set(RE_LOCAL_REF.findall(local[position]["body"])):
                target = index_by_short.get(reference)
                if target is not None and target != position:
                    total += local_payload(target, seen | {position})
            # The definition graph inside one module is a DAG, so a memo entry is path
            # independent and this stays linear even in a 5,000-declaration generated file.
            local_cache[position] = total
            return total

        closure = None
        for position, entry in enumerate(local):
            if not entry["decide"]:
                continue
            if closure is None:
                closure = import_closure(path)
            body = entry["body"]

            best = None
            censused = False
            for occurrence in RE_DECIDE.finditer(body):
                scope, top_level = reduction_scope(body, occurrence.start())
                # `opaque foo : ... := by decide` is the audit blind spot: a reduction obligation
                # no `theorem`-scanning tool can see.  A nested `⟨1, by decide⟩` inside an opaque
                # declaration is not that, so only a top-level reduction is censused.
                if top_level and entry["keyword"] == "opaque" and not censused:
                    opaque_decides.append((path, entry["line"], entry["name"]))
                    censused = True
                inlined = set()
                for referenced in set(RE_NAMESPACE_REF.findall(scope)):
                    candidates = [
                        module for module in namespace_modules.get(referenced, ())
                        if module in closure and module != path
                    ]
                    # Ambiguous namespaces are skipped rather than guessed: under-count, never over.
                    if len(candidates) == 1:
                        inlined.add(candidates[0])
                if top_level:
                    own = local_payload(position)
                else:
                    own = len(RE_DIGIT.findall(scope)) + sum(
                        local_payload(target)
                        for target in {
                            index_by_short[reference]
                            for reference in set(RE_LOCAL_REF.findall(scope))
                            if reference in index_by_short and index_by_short[reference] != position
                        }
                    )
                total = own + sum(module_digits[module] for module in inlined)
                line = entry["line"] + body.count("\n", 0, occurrence.start())
                if best is None or total > best[0]:
                    best = (total, line, sorted(inlined))

            if best is None:
                continue
            declaration = Declaration(
                path=path, line=best[1], keyword=entry["keyword"], name=entry["name"],
                payload=best[0], namespaces=best[2], has_decide=True,
            )
            declarations.append(declaration)
            payloads[declaration.key] = declaration.payload

    declarations.sort(key=lambda item: (-item.payload, item.path, item.line))
    opaque_decides.sort()
    return declarations, payloads, opaque_decides


# --- the measured-memory budget file --------------------------------------------------------

class Measurement:
    __slots__ = ("kind", "key", "peak_mb", "measured_at", "line")

    def __init__(self, kind, key, peak_mb, measured_at, line):
        self.kind = kind
        self.key = key
        self.peak_mb = peak_mb
        self.measured_at = measured_at
        self.line = line


def read_budget_file(path):
    """Parse `scripts/decide_memory_budget.tsv`.

    Append-only TSV so a janitor's remote run can add a row with `printf '%s\\t...' >> file`
    and never has to rewrite what is already there.  Columns:

        kind    module | family      ('family' keys a trailing-`*` glob)
        key     module name, or module-name glob
        peak_mb integer peak resident set size, megabytes
        date    ISO-8601 (`YYYY-MM-DD`); the newest row for a key wins, so a module that was
                fixed is retired by appending its new lower number, never by editing history
        host    free-form provenance ('mac-16gb', 'gh-ubuntu-latest', ...)
        tool    how it was measured
        note    free-form
    """
    rows = []
    full = os.path.join(REPO, path)
    if not os.path.exists(full):
        die("%s is missing; the measured-memory budget cannot be checked." % (path,))
    with open(full, "r", encoding="utf-8") as handle:
        for number, raw in enumerate(handle, 1):
            line = raw.rstrip("\n")
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            fields = line.split("\t")
            if len(fields) < 4:
                die("%s:%d: expected at least 4 tab-separated fields, got %d."
                    % (path, number, len(fields)))
            kind, key, peak, date = fields[0].strip(), fields[1].strip(), fields[2].strip(), fields[3].strip()
            if kind not in ("module", "family"):
                die("%s:%d: unknown kind %r (expected 'module' or 'family')." % (path, number, kind))
            if not re.fullmatch(r"[0-9]+", peak):
                die("%s:%d: peak_mb %r is not an integer." % (path, number, peak))
            if not re.fullmatch(r"[0-9]{4}-[0-9]{2}-[0-9]{2}", date):
                die("%s:%d: date %r is not ISO-8601 YYYY-MM-DD." % (path, number, date))
            if kind == "family" and not key.endswith("*"):
                die("%s:%d: a 'family' key must end in '*'." % (path, number))
            rows.append(Measurement(kind, key, int(peak), date, number))
    return rows


def measurement_for(module, rows):
    """The governing measurement for a module: its own newest row, else its newest family row.

    A module-level row always beats a family row, however old, because it is the more specific
    statement about that exact module.
    """
    own = [row for row in rows if row.kind == "module" and row.key == module]
    if own:
        return max(own, key=lambda row: (row.measured_at, row.line))
    families = [
        row for row in rows
        if row.kind == "family" and module.startswith(row.key[:-1])
    ]
    if families:
        return max(families, key=lambda row: (row.measured_at, row.line))
    return None


# --- the grandfather file -------------------------------------------------------------------

GRANDFATHER_HEADER = """\
# Known `decide` memory-boundary debt, as of the commit that generated this file.
#
# DESIGN.md:590 ("Reduction and elaboration budgets", DESIGN.md:580) forbids letting a single
# reduction command become the project's memory boundary.
# The rule went unenforced for a long time; `scripts/check_decide_budget.py` enforces it now, and
# every line below is a place where the committed tree already breaks it.  The list exists so the
# debt is VISIBLE rather than forgotten: a clean run prints how many entries are still here.
#
# The list is APPEND-BLOCKED and may only shrink.
#   * A violation that is NOT listed here fails the build.
#   * An entry here that no longer violates is reported as a stale-entry notice, never a failure --
#     the commit that pays debt down must not be the commit that goes red.
#   * An entry here that gets WORSE fails: a recorded payload may drift by the regression slack
#     (default 25%, floor 1000 digits) but may not balloon.
#
# Two record types:
#
#   measured  <module>  <peak_mb>
#       A module in scripts/decide_memory_budget.tsv whose measured peak exceeds the budget.
#       Retire it by making the reduction cheaper and appending the new measurement.
#
#   payload   <path>::<declaration>  <digits>
#       An un-measured `decide` / `decide +kernel` / `decide_cbv` declaration whose inlined
#       literal payload exceeds the static threshold.  Retire it by shrinking the payload (split
#       the reduction, or replace it by a proved checker per DESIGN.md's "untrusted producer,
#       proved checker" architecture) -- or by MEASURING the module and appending the number to
#       scripts/decide_memory_budget.tsv, which retires the proxy in favour of a real figure.
#       The key is `path::name`, not `path:line`, so ordinary edits above a declaration do not
#       churn this file.
#
# Do not add a line here to silence the gate on new work.  Regenerate deliberately with
#
#   python3 scripts/check_decide_budget.py --update
#
"""


def read_grandfather_file(path):
    measured = {}
    payload = {}
    full = os.path.join(REPO, path)
    if not os.path.exists(full):
        die("%s is missing; refusing to run with no grandfather list (every existing violation "
            "would fail at once). Regenerate it with --update." % (path,))
    with open(full, "r", encoding="utf-8") as handle:
        for number, raw in enumerate(handle, 1):
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            fields = line.split()
            if len(fields) != 3 or fields[0] not in ("measured", "payload"):
                die("%s:%d: expected `measured <module> <mb>` or `payload <path>::<name> <digits>`."
                    % (path, number))
            if not re.fullmatch(r"[0-9]+", fields[2]):
                die("%s:%d: %r is not an integer." % (path, number, fields[2]))
            (measured if fields[0] == "measured" else payload)[fields[1]] = int(fields[2])
    return measured, payload


def write_grandfather_file(path, measured, payload):
    lines = [GRANDFATHER_HEADER]
    lines.append("# %d measured modules over budget, %d un-measured declarations over the static "
                 "payload threshold.\n\n" % (len(measured), len(payload)))
    for key in sorted(measured):
        lines.append("measured %s %d\n" % (key, measured[key]))
    if measured and payload:
        lines.append("\n")
    for key in sorted(payload):
        lines.append("payload %s %d\n" % (key, payload[key]))
    with open(os.path.join(REPO, path), "w", encoding="utf-8") as handle:
        handle.write("".join(lines))


# --- self-test ------------------------------------------------------------------------------

SELF_TEST_TREE = {
    # A payload module: the numerals actually live here.
    "MatrixMultiplication/SelfTest/Data0.lean": (
        "namespace Data0\n"
        "def rawData : List Nat := [" + ", ".join("%d" % (100000 + i) for i in range(4000)) + "]\n"
        "def data : List Nat := rawData\n"
        "theorem data_eq_rawData : data = rawData := rfl\n"
        "end Data0\n"
    ),
    # ZeroFour1's real shape: a TINY module whose reduction inlines the payload module above.
    # Any proxy that looked at file size, or at the declaration text alone, would score this 0.
    "MatrixMultiplication/SelfTest/Heavy.lean": (
        "import MatrixMultiplication.SelfTest.Data0\n"
        "opaque heavy_normalizes : Data0.data = Data0.rawData := by\n"
        "  rw [Data0.data_eq_rawData]\n"
        "  decide +kernel\n"
    ),
    # A genuinely tiny closed finite fact: exactly what DESIGN.md:545 permits.
    "MatrixMultiplication/SelfTest/Small.lean": (
        "theorem small : 2 + 2 = 4 := by decide\n"
    ),
    # The most common false positive in this repository: a `\u27e8n, by decide\u27e9` bound proof, a
    # genuinely tiny closed finite fact, sitting inside a huge generated declaration.  Charging the
    # declaration's payload to that reduction would flag hundreds of legitimate decides.
    "MatrixMultiplication/SelfTest/Sidecondition.lean": (
        "import MatrixMultiplication.SelfTest.Data0\n"
        "noncomputable def sideCondition : Fin 200000 := \u27e81, by decide\u27e9\n"
        "def bulk : List Nat := " + str([700000 + i for i in range(4000)]) + "\n"
    ),
    # Prose must not be able to manufacture a reduction, a namespace, or a payload.
    "MatrixMultiplication/SelfTest/Prose.lean": (
        "/-- Discussion of `decide +kernel` and of " + " ".join("%d" % i for i in range(9000)) +
        " numerals. -/\n"
        "theorem prose : True := trivial\n"
    ),
}


def self_test(threshold=DEFAULT_PAYLOAD_THRESHOLD):
    """Prove the scanner fires before trusting it to report the repository clean.

    A gate that silently matches nothing converts an unchecked invariant into a green check mark,
    which is how 2026-08-28's failures hid in the first place.
    """
    declarations, payloads, opaque_decides = analyse(dict(SELF_TEST_TREE))
    found = {declaration.key: declaration for declaration in declarations}

    heavy = "MatrixMultiplication/SelfTest/Heavy.lean::heavy_normalizes"
    small = "MatrixMultiplication/SelfTest/Small.lean::small"
    prose = "MatrixMultiplication/SelfTest/Prose.lean::prose"
    side = "MatrixMultiplication/SelfTest/Sidecondition.lean::sideCondition"

    problems = []
    if heavy not in found:
        problems.append("the ZeroFour1-shaped `opaque ... := by ... decide +kernel` was not seen")
    elif payloads[heavy] < threshold:
        problems.append(
            "the ZeroFour1-shaped reduction scored %d digits, under the %d-digit threshold: the "
            "proxy is no longer following payload through imports"
            % (payloads[heavy], threshold))
    if small not in found:
        problems.append("a plain `by decide` was not seen at all")
    elif payloads[small] >= threshold:
        problems.append("a genuinely tiny `by decide` scored %d digits" % payloads[small])
    if prose in found:
        problems.append("a `decide` inside a docstring was treated as a tactic")
    if side not in found:
        problems.append("a nested `\u27e8n, by decide\u27e9` side condition was not seen at all")
    elif payloads[side] >= threshold:
        problems.append(
            "a `\u27e8n, by decide\u27e9` bound proof scored %d digits: the checker is charging a "
            "whole declaration to a reduction that only proves `n < N`" % payloads[side])
    if not any(path.endswith("Heavy.lean") for path, _line, _name in opaque_decides):
        problems.append("the `opaque ... := by decide` census missed an opaque decide")
    if any(path.endswith("Small.lean") for path, _line, _name in opaque_decides):
        problems.append("the `opaque ... := by decide` census claimed a plain theorem")

    if problems:
        for problem in problems:
            print("FAIL: self-test: %s" % problem, file=sys.stderr)
        raise SystemExit(2)
    return payloads[heavy], payloads[small]


# --- the gate -------------------------------------------------------------------------------

def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Enforce DESIGN.md's `decide` memory-boundary rule (DESIGN.md:545, :590).",
    )
    parser.add_argument("--budget", type=int, default=int(os.environ.get("DECIDE_BUDGET_MB", DEFAULT_BUDGET_MB)),
                        help="measured peak RSS a single module may reach, in MB "
                             "(default %d; also settable with DECIDE_BUDGET_MB)" % DEFAULT_BUDGET_MB)
    parser.add_argument("--payload-threshold", type=int, default=DEFAULT_PAYLOAD_THRESHOLD,
                        help="static proxy: digits of literal payload one reduction may inline "
                             "(default %d)" % DEFAULT_PAYLOAD_THRESHOLD)
    parser.add_argument("--regression-slack", type=float, default=DEFAULT_REGRESSION_SLACK,
                        help="fraction a grandfathered payload may grow before it fails "
                             "(default %.2f)" % DEFAULT_REGRESSION_SLACK)
    parser.add_argument("--worktree", action="store_true",
                        help="score the working tree instead of HEAD (author convenience; CI must "
                             "not use it -- five lanes hold uncommitted edits in this checkout)")
    parser.add_argument("--report", action="store_true",
                        help="print the ranked payload table and the opaque census, then exit 0")
    parser.add_argument("--top", type=int, default=40, help="rows for --report (default 40)")
    parser.add_argument("--update", action="store_true",
                        help="regenerate %s from the current tree" % GRANDFATHER_FILE)
    parser.add_argument("--budget-file", default=BUDGET_FILE,
                        help="override %s (tests only)" % BUDGET_FILE)
    parser.add_argument("--grandfather-file", default=GRANDFATHER_FILE,
                        help="override %s (tests only)" % GRANDFATHER_FILE)
    parser.add_argument("--self-test", action="store_true",
                        help="run the built-in fixture that proves the scanner fires, then exit")
    args = parser.parse_args(argv)

    if args.self_test:
        heavy, small = self_test(args.payload_threshold)
        print("self-test ok: the ZeroFour1-shaped reduction scores %d digits (threshold %d) from a "
              "%d-byte module; a tiny `by decide` scores %d."
              % (heavy, args.payload_threshold,
                 len(SELF_TEST_TREE["MatrixMultiplication/SelfTest/Heavy.lean"]), small))
        return 0

    sources = load_sources(args.worktree)
    declarations, _payloads, opaque_decides = analyse(sources)
    # A scan that matched nothing must never be reported as a clean scan: that is precisely the
    # failure mode (ugrep's silent `grep -r PAT dir/*.lean`) this whole file is written against.
    if not declarations:
        die("scanned %d Lean sources and found no `decide` declaration at all. This project has "
            "thousands; the scanner or the root list is broken." % (len(sources),))
    budget_rows = read_budget_file(args.budget_file)

    if args.report:
        print("Reduction declarations (`decide`, `decide +kernel`, `decide_cbv`): %d in %d modules."
              % (len(declarations), len({d.path for d in declarations})))
        print("Top %d by inlined literal payload:" % args.top)
        for declaration in declarations[: args.top]:
            governing = measurement_for(module_name(declaration.path), budget_rows)
            measured = "  [measured %d MB]" % governing.peak_mb if governing else ""
            print("  %9d digits  %s:%d  %s %s%s"
                  % (declaration.payload, declaration.path, declaration.line,
                     declaration.keyword, declaration.name, measured))
        print()
        print("`opaque ... := by ... decide ...` declarations: %d in %d modules "
              "(invisible to any tool that scans for `theorem`)."
              % (len(opaque_decides), len({path for path, _line, _name in opaque_decides})))
        outside = [item for item in opaque_decides if not item[0].startswith(GENERATED_PREFIX)]
        print("  outside %s: %d" % (GENERATED_PREFIX, len(outside)))
        for path, line, name in outside[:20]:
            print("    %s:%d opaque %s" % (path, line, name))
        return 0

    # --- collect today's violations, independent of the grandfather list --------------------
    measured_violations = {}   # module -> peak MB
    for module in sorted({module_name(d.path) for d in declarations}):
        governing = measurement_for(module, budget_rows)
        if governing is not None and governing.peak_mb > args.budget:
            measured_violations[module] = governing.peak_mb

    payload_violations = {}    # path::name -> digits
    for declaration in declarations:
        module = module_name(declaration.path)
        # A real measurement is the authority; the proxy speaks only where nobody has measured.
        if measurement_for(module, budget_rows) is not None:
            continue
        if declaration.payload >= args.payload_threshold:
            payload_violations[declaration.key] = declaration.payload

    if args.update:
        write_grandfather_file(args.grandfather_file, measured_violations, payload_violations)
        print("Wrote %s: %d measured modules over the %d MB budget, %d un-measured declarations "
              "over the %d-digit static payload threshold."
              % (args.grandfather_file, len(measured_violations), args.budget,
                 len(payload_violations), args.payload_threshold))
        return 0

    known_measured, known_payload = read_grandfather_file(args.grandfather_file)
    failures = []
    notices = []

    # 1. NEW measured modules over budget.
    for module in sorted(measured_violations):
        peak = measured_violations[module]
        if module not in known_measured:
            location = next((d.path for d in declarations if module_name(d.path) == module), module)
            failures.append(
                "%s:1: module %s has a measured peak of %d MB, over the %d MB budget for a single "
                "reduction (DESIGN.md:590). Split the reduction or move it behind a proved checker."
                % (location, module, peak, args.budget))
        elif peak > known_measured[module]:
            failures.append(
                "%s:1: grandfathered module %s got WORSE: measured %d MB, was %d MB."
                % (module.replace(".", "/") + ".lean", module, peak, known_measured[module]))

    # 2. NEW static-proxy violations.
    location_of = {d.key: (d.path, d.line, d.keyword, d.name) for d in declarations}
    for key in sorted(payload_violations):
        digits = payload_violations[key]
        path, line, keyword, name = location_of[key]
        if key not in known_payload:
            failures.append(
                "%s:%d: %s %s inlines %d digits of literal payload into one reduction, over the "
                "%d-digit threshold, and the module has no measured peak. Either shrink the "
                "reduction (DESIGN.md:545 reserves `decide` for genuinely tiny closed finite "
                "facts) or measure the module and append the figure to %s."
                % (path, line, keyword, name, digits, args.payload_threshold, args.budget_file))
        else:
            ceiling = max(known_payload[key] * (1.0 + args.regression_slack),
                          known_payload[key] + REGRESSION_FLOOR)
            if digits > ceiling:
                failures.append(
                    "%s:%d: grandfathered %s %s got WORSE: %d digits, was %d (slack %.0f%%)."
                    % (path, line, keyword, name, digits, known_payload[key],
                       args.regression_slack * 100))

    # 3. `opaque ... := by decide` outside the reviewed generated surface.
    #    `scripts/trust_scan.sh` already restricts `opaque` to MatrixMultiplication/Generated; an
    #    opaque-decide in hand-written code is that policy violation *plus* an audit blind spot.
    for path, line, name in opaque_decides:
        if not path.startswith(GENERATED_PREFIX):
            failures.append(
                "%s:%d: `opaque %s := by ... decide ...` outside %s hides a reduction obligation "
                "from every tool that scans for `theorem`. Make it a theorem, or move it to the "
                "reviewed generated surface." % (path, line, name, GENERATED_PREFIX))

    # 4. Stale entries: notices, never failures.
    for module in sorted(known_measured):
        if module not in measured_violations:
            notices.append("stale grandfather entry (no longer over budget, or gone): measured %s"
                           % module)
    for key in sorted(known_payload):
        if key not in payload_violations:
            notices.append("stale grandfather entry (payload shrank, module measured, or "
                           "declaration gone or renamed): payload %s" % key)

    for notice in notices:
        print("notice: %s" % notice)

    if failures:
        print()
        for failure in failures:
            print("FAIL: %s" % failure, file=sys.stderr)
        print("\n%d new `decide` memory-boundary violation(s)." % len(failures), file=sys.stderr)
        print("Grandfathered debt still outstanding: %d measured module(s) over budget, "
              "%d declaration(s) over the static payload threshold (%s)."
              % (len(known_measured), len(known_payload), args.grandfather_file), file=sys.stderr)
        return 1

    opaque_modules = len({path for path, _line, _name in opaque_decides})
    print("decide budget: %d reduction declarations scanned in %d modules; "
          "budget %d MB, static payload threshold %d digits."
          % (len(declarations), len({d.path for d in declarations}), args.budget,
             args.payload_threshold))
    print("Grandfathered debt: %d measured module(s) over budget, %d un-measured declaration(s) "
          "over the payload threshold (%s)."
          % (len(known_measured), len(known_payload), args.grandfather_file))
    print("Audit blind spot, reported not gated: %d `opaque ... := by ... decide ...` declarations "
          "in %d modules, all inside %s." % (len(opaque_decides), opaque_modules, GENERATED_PREFIX))
    if notices:
        print("%d stale grandfather entry/entries above: prune them with --update." % len(notices))
    print("Decide budget check clean.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
