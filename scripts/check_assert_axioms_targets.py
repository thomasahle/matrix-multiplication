#!/usr/bin/env python3
"""Static resolution check for every `#assert_axioms` target in the committed tree.

WHY THIS EXISTS
---------------
`#assert_axioms id` (see `AxiomAudit/Command.lean`) calls `realizeGlobalConstWithInfos`
*before* it collects any axioms.  An unknown constant therefore raises `unknownIdentifier`
at that point: the assertion is never evaluated, and — because the whole command file fails
to elaborate — every other assertion in the same module goes dark with it.  In a globbed
build target that failure mode is easy to miss for a long time.

Commit 95347e18 repaired exactly that: `AxiomAuditCertificate/TotalQuotientExponentLevelFour
Validity.lean` asserted `...Validity.Region{0..5}.coverageChecked` for six regions, a name
that existed nowhere in the tree (the region checks had been regenerated to prove
`normalizationChecked` and `childRowsValid`).  Nine assertions in a built target had been
providing no assurance at all since fb638dc4.  This check makes that class visible statically,
without a compiler.

WHAT IS ANALYSED: THE REPOSITORY, NOT THE WORKING TREE
------------------------------------------------------
The tree is read with `git archive HEAD` (streamed through `tarfile`), never from the
filesystem.  Five lanes hold uncommitted edits in this repo, so the working tree is not what
CI checks out and not what "the repository asserts" means: a name that only exists in one
lane's unstaged buffer must still count as missing.  `git archive` is preferred over 12k
`git show HEAD:<path>` calls purely for speed — it is one process and one pass.
`--rev <rev>` analyses any other commit, which is how the historical case is reproduced:

    python3 scripts/check_assert_axioms_targets.py --rev 95347e18^

NO `grep` IS USED ANYWHERE
-------------------------
`grep` on the maintainer's machine is ugrep 7.8.4, where `grep -r PAT dir/*.lean` silently
returns zero matches instead of erroring — a check that silently matches nothing is worse
than no check.  All scanning happens in this file, so behaviour is identical on macOS and on
the ubuntu-latest runner.

CLASSIFICATION (deliberately three-valued)
------------------------------------------
Each `#assert_axioms <name>` is classified as:

  OK          the name resolves to a declaration parsed out of the committed tree, either
              directly, through an enclosing `namespace`, or through a file-level `open`.
  DARK        the name does not resolve, its root component is one of this package's own
              library roots, its parent namespace *does* exist in the tree, and either
                * "absent": its final component does not occur as an identifier token ANYWHERE
                  in any committed `.lean` file (comments and string literals included) outside
                  the argument of an `#assert_axioms` -- the `coverageChecked` signature; or
                * "moved": its final component IS declared, but only under a different fully
                  qualified name -- the `AlgebraicComplexity.asymptoticRank_power_le_pow_of_lt`
                  signature, an assertion left behind when its target was promoted into
                  `AlgebraicComplexity.Tensor`.
              These are the only two conditions this check fails on.
  UNRESOLVED  everything else: Mathlib/Cslib/core names, unqualified names, names under a
              namespace this parser did not see, and names whose final component appears
              somewhere in the tree but never as a declaration the parser could read (so a
              macro could plausibly be producing it).  Reported with a count, never failed on.

A false FAIL here is worse than a miss, so anything the parser cannot settle confidently lands
in UNRESOLVED.

GRANDFATHERING
--------------
`scripts/assert_axioms_dark_grandfathered.txt` lists `path:name` pairs that are DARK today and
are exempt.  The list may only shrink: an entry that stopped being DARK, or whose file is gone,
is a stale-entry notice rather than a failure, so paying the debt can never fail on the commit
that pays it.  Regenerate deliberately with `--update`.

Exit status: 0 clean (or only grandfathered/unresolved), 1 on a NEW dark assertion, 2 on usage
or environment errors.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tarfile

GRANDFATHER_FILE = "scripts/assert_axioms_dark_grandfathered.txt"

# Declaration keywords that introduce a name we can index by reading one line.
DECL_KEYWORDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "instance",
    "opaque",
    "axiom",
    "structure",
    "inductive",
    "class",
    "alias",
    "register_simp_attr",
)

# Modifiers and attribute clusters that may sit between the line start and the keyword.
_MODIFIER = r"(?:@\[[^\]]*\]|private|protected|noncomputable|unsafe|partial|nonrec|scoped|local|mutual)"

DECL_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?:" + _MODIFIER + r"[ \t]+)*"
    r"(?P<kw>" + "|".join(DECL_KEYWORDS) + r")"
    r"(?P<tail>[ \t]*(?P<name>[^\s:(){}\[\]⦃⦄⟨⟩,]+)?.*)$"
)

# `structure`/`class` fields and `inductive` constructors are declarations too (projections and
# constructors), and asserting one is legitimate.  They are indexed on a best-effort basis: a
# spurious index entry can only turn a FAIL into a pass, never the other way round.
FIELD_RE = re.compile(
    r"^(?P<indent>[ \t]+)(?:@\[[^\]]*\][ \t]*)*"
    r"(?P<names>[^\W\d][\w'!?]*(?:[ \t]+[^\W\d][\w'!?]*)*)[ \t]*:(?!=)"
)
CTOR_RE = re.compile(r"^[ \t]*\|[ \t]*(?P<name>[^\W\d][\w'!?]*)")

NAMESPACE_RE = re.compile(r"^[ \t]*namespace[ \t]+(?P<name>[^\s]+)")
# `noncomputable section` opens an ordinary anonymous section.  It needs its own stack frame:
# otherwise the matching bare `end` incorrectly pops the surrounding namespace, and every
# declaration after it is indexed at the root.  Named sections then make the resulting false
# namespace move especially visible (as in `DuanWuZhouLevelTwoOrbitTag.lean`).
SECTION_RE = re.compile(
    r"^[ \t]*(?:noncomputable[ \t]+)?(?:section|mutual)"
    r"(?:[ \t]+(?P<name>[^\s]+))?[ \t]*$"
)
END_RE = re.compile(r"^[ \t]*end(?:[ \t]+(?P<name>[^\s]+))?[ \t]*$")
OPEN_RE = re.compile(r"^[ \t]*open[ \t]+(?P<rest>.*)$")
# `export A.B (x y z)`, whose parenthesised list routinely spans several lines, introduces
# `<current namespace>.x` and friends.  MatrixMultiplication/EntropyDual.lean is the whole of
# `MatrixMultiplication.EntropyDual` and consists of exactly one such re-export.
EXPORT_RE = re.compile(r"^[ \t]*export[ \t]+(?P<ns>[^\s(]+)[ \t\r\n]*\((?P<names>[^)]*)\)", re.MULTILINE)

# `#assert_axioms` may carry its argument on the next line (209 such sites at the time of
# writing), so the argument is matched across newlines.
ASSERT_RE = re.compile(r"^[ \t]*#assert_axioms\b(?P<arg>(?:[ \t\r\n]+)[^\s]+)?", re.MULTILINE)

# An identifier component: a non-digit word character followed by word characters, primes and
# the `!`/`?` Lean allows.  French quotes are handled by the caller.
_COMP = r"[^\W\d][\w'!?]*"
IDENT_RE = re.compile(r"^«?" + _COMP + r"»?(?:\.«?" + _COMP + r"»?)*$", re.UNICODE)
TOKEN_RE = re.compile(_COMP, re.UNICODE)

# Names Lean's elaborator generates for a declaration without them appearing in the source.
# If a final component is one of these, the assertion is UNRESOLVED rather than DARK.
AUTO_GENERATED_COMPONENTS = frozenset(
    """
    rec recOn casesOn below brecOn ibelow binductionOn induct fun_cases
    noConfusion noConfusionType toCtorIdx ctorIdx mk inj injEq sizeOf_spec
    eq_def eq_1 eq_2 eq_3 match_1 proof_1 sizeOf ofNat toString
    """.split()
)


def die(message: str) -> None:
    sys.stderr.write("check_assert_axioms_targets: %s\n" % message)
    raise SystemExit(2)


def iter_lean_sources(rev: str):
    """Yield (path, text) for every committed `.lean` file at `rev`, plus `lakefile.toml`."""
    proc = subprocess.Popen(
        ["git", "archive", "--format=tar", rev],
        stdout=subprocess.PIPE,
    )
    assert proc.stdout is not None
    try:
        with tarfile.open(fileobj=proc.stdout, mode="r|") as archive:
            for member in archive:
                if not member.isfile():
                    continue
                if not (member.name.endswith(".lean") or member.name == "lakefile.toml"):
                    continue
                handle = archive.extractfile(member)
                if handle is None:
                    continue
                yield member.name, handle.read().decode("utf-8", "replace")
    finally:
        if proc.stdout is not None:
            proc.stdout.close()
        if proc.wait() != 0:
            die("`git archive %s` failed" % rev)


def blank_comments(text: str) -> str:
    """Replace Lean comments with spaces, preserving every offset and newline.

    String literals are left intact (they are scanned over, not blanked, so that a `--` or
    `/-` inside a string cannot open a comment).  Nested `/- ... -/` is handled.
    """
    out = list(text)
    i = 0
    n = len(text)
    depth = 0
    while i < n:
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if text[i] != "\n":
                out[i] = " "
            i += 1
            continue
        c = text[i]
        if c == "/" and text.startswith("/-", i):
            depth = 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if c == "-" and text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0:
                j = n
            for k in range(i, j):
                out[k] = " "
            i = j
            continue
        if c == '"':
            i += 1
            while i < n:
                if text[i] == "\\":
                    i += 2
                    continue
                if text[i] == '"':
                    i += 1
                    break
                i += 1
            continue
        i += 1
    return "".join(out)


class FileFacts:
    __slots__ = ("path", "asserts", "opens", "assert_spans")

    def __init__(self, path):
        self.path = path
        self.asserts = []       # (line, name, enclosing_namespace)
        self.opens = set()      # namespace prefixes opened anywhere in the file
        self.assert_spans = []  # (start, end) offsets of assert arguments in the raw text


def scan_file(path: str, raw: str, decls: set, namespaces: set) -> FileFacts:
    facts = FileFacts(path)
    code = blank_comments(raw)

    # Offsets -> line numbers, computed once.
    line_starts = [0]
    for m in re.finditer("\n", code):
        line_starts.append(m.end())

    def line_of(offset: int) -> int:
        lo, hi = 0, len(line_starts) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if line_starts[mid] <= offset:
                lo = mid
            else:
                hi = mid - 1
        return lo + 1

    # --- namespace / declaration pass -------------------------------------------------
    frames = []  # each entry is (components, section_name_or_None)

    def current_namespace() -> str:
        return ".".join(part for comps, _ in frames for part in comps)

    def register_namespace(full: str) -> None:
        parts = full.split(".")
        for k in range(1, len(parts) + 1):
            namespaces.add(".".join(parts[:k]))

    ns_at_offset = []  # (offset, namespace) checkpoints, ascending
    pending_name_for = None   # keyword whose name sits on the following line
    container = None          # (indent, full name) of an open `structure`/`class`/`inductive`

    def record(full: str) -> None:
        decls.add(full)
        if "." in full:
            register_namespace(full.rsplit(".", 1)[0])

    for match in re.finditer(r"^.*$", code, re.MULTILINE):
        line = match.group(0)
        stripped = line.strip()
        if not stripped:
            continue

        if pending_name_for is not None:
            token = stripped.split()[0]
            if IDENT_RE.match(token):
                ns = current_namespace()
                if token.startswith("_root_."):
                    record(token[len("_root_.") :])
                else:
                    record(token if not ns else ns + "." + token)
            pending_name_for = None
            continue

        if container is not None:
            indent = len(line) - len(line.lstrip())
            m = CTOR_RE.match(line)
            if m is not None:
                record(container[1] + "." + m.group("name"))
                continue
            if indent > container[0]:
                m = FIELD_RE.match(line)
                if m is not None:
                    for field in m.group("names").split():
                        record(container[1] + "." + field)
                continue
            container = None

        m = END_RE.match(line)
        if m is not None:
            name = m.group("name")
            if name is None:
                if frames:
                    frames.pop()
            else:
                needed = len(name.split("."))
                while needed > 0 and frames:
                    comps, section_name = frames.pop()
                    if not comps:
                        if section_name == name:
                            needed = 0
                        # an anonymous section frame consumes nothing
                    else:
                        needed -= len(comps)
            ns_at_offset.append((match.start(), current_namespace()))
            continue

        m = NAMESPACE_RE.match(line)
        if m is not None:
            comps = m.group("name").split(".")
            frames.append((comps, None))
            register_namespace(current_namespace())
            ns_at_offset.append((match.start(), current_namespace()))
            continue

        m = SECTION_RE.match(line)
        if m is not None:
            frames.append(([], m.group("name")))
            continue

        m = OPEN_RE.match(line)
        if m is not None:
            rest = m.group("rest").split(" in")[0]
            names = []
            for token in rest.replace("(", " ").replace(")", " ").split():
                if token in ("scoped", "in", "renaming", "hiding"):
                    continue
                if IDENT_RE.match(token):
                    names.append(token)
            # `open A B` opens `A` and then `B`, and `B` is itself resolved against the already
            # opened `A`, so `A.B` is in scope too.  Record every cumulative prefix.
            for index, token in enumerate(names):
                facts.opens.add(token)
                facts.opens.add(".".join(names[: index + 1]))
            continue

        m = DECL_RE.match(line)
        if m is not None:
            name = m.group("name")
            if not m.group("tail").strip():
                # `noncomputable def` with the name alone on the next line, a shape the generated
                # and the hand-written sources both use for very long names.
                pending_name_for = m.group("kw")
                continue
            if name and IDENT_RE.match(name):
                if name.startswith("_root_."):
                    # `theorem _root_.A.B.c` declares `A.B.c`, ignoring the enclosing namespace.
                    full = name[len("_root_.") :]
                else:
                    ns = current_namespace()
                    full = name if not ns else ns + "." + name
                record(full)
                if m.group("kw") in ("structure", "class", "inductive"):
                    container = (len(m.group("indent")), full)
            continue

    # --- assertion pass ---------------------------------------------------------------
    ns_at_offset.sort()

    def namespace_at(offset: int) -> str:
        ns = ""
        for start, value in ns_at_offset:
            if start <= offset:
                ns = value
            else:
                break
        return ns

    # --- `export` re-export pass ------------------------------------------------------
    for match in EXPORT_RE.finditer(code):
        ns = namespace_at(match.start())
        for token in match.group("names").split():
            if IDENT_RE.match(token):
                decls.add(ns + "." + token if ns else token)

    for match in ASSERT_RE.finditer(code):
        arg = match.group("arg")
        line = line_of(match.start())
        if arg is None:
            facts.asserts.append((line, None, namespace_at(match.start())))
            continue
        name = arg.strip()
        facts.assert_spans.append((match.start("arg"), match.end("arg")))
        facts.asserts.append((line, name, namespace_at(match.start())))

    return facts


def tokens_outside_asserts(raw: str, spans) -> set:
    """Every identifier token in the RAW text (comments and strings included), minus the
    tokens sitting inside an `#assert_axioms` argument.  Deliberately generous: the more
    places a name could be coming from, the less confident a DARK verdict is."""
    if not spans:
        return set(TOKEN_RE.findall(raw))
    result = set()
    cursor = 0
    for start, end in sorted(spans):
        if start > cursor:
            result.update(TOKEN_RE.findall(raw[cursor:start]))
        cursor = max(cursor, end)
    result.update(TOKEN_RE.findall(raw[cursor:]))
    return result


def prefixes(namespace: str):
    if not namespace:
        return []
    parts = namespace.split(".")
    return [".".join(parts[:k]) for k in range(len(parts), 0, -1)]


def load_grandfather(repo_root: str):
    path = os.path.join(repo_root, GRANDFATHER_FILE)
    entries = set()
    if not os.path.exists(path):
        return entries
    with open(path, "r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            entries.add(line)
    return entries


HEADER = """\
# `#assert_axioms` targets that name a declaration this checker cannot find (DARK).
#
# A DARK assertion names a declaration rooted in one of this package's own libraries, under a
# namespace that does exist, which nevertheless resolves to nothing.  Two shapes are failed on:
#
#   absent  the final component appears in NO committed `.lean` file at all.  This is
#           AxiomAuditCertificate/TotalQuotientExponentLevelFourValidity.lean before commit
#           95347e18: six `Region{i}.coverageChecked` assertions whose target had been
#           regenerated out of existence in favour of `normalizationChecked`/`childRowsValid`.
#   moved   the final component IS declared, but only under a different fully qualified name.
#           This is AxiomAudit.lean:1398, left behind when
#           `asymptoticRank_power_le_pow_of_lt` was promoted out of `AlgebraicComplexity` into
#           `AlgebraicComplexity.Tensor` (the correct assertion was added at line 1458 and the
#           stale one never removed).
#
# `realizeGlobalConstWithInfos` throws on the unknown constant before any axiom is collected,
# so such an assertion is not merely wrong: it takes every other assertion in its module down
# with it, silently, inside a globbed build target.
#
# Every line here is `path/to/file.lean:Fully.Qualified.Name` and is pre-existing debt.
#
# The list is APPEND-BLOCKED and may only shrink.  A new dark assertion that is not listed
# here fails the gate; an entry here that has stopped being dark, or whose file is gone, is
# reported as a stale-entry notice rather than a failure, so repairing an assertion can never
# fail on the commit that repairs it.
#
# To retire an entry: point the assertion at a declaration that exists (or delete it), then
# delete its line.  Regenerate the whole file with:
#     python3 scripts/check_assert_axioms_targets.py --update
"""


def analyse(sources):
    """Classify every `#assert_axioms` in `sources`, an iterable of (path, text) pairs.

    Returns (total, ok, unresolved, dark, malformed).  `dark` entries are
    (path, line, name, kind, nearby_declarations) with kind in {"absent", "moved"}.
    """
    decls = set()
    namespaces = set()
    file_facts = []
    token_corpus = set()
    package_roots = set()

    for path, raw in sources:
        if path == "lakefile.toml":
            for m in re.finditer(r'^name[ \t]*=[ \t]*"([^"]+)"', raw, re.MULTILINE):
                package_roots.add(m.group(1))
            continue
        facts = scan_file(path, raw, decls, namespaces)
        file_facts.append(facts)
        token_corpus |= tokens_outside_asserts(raw, facts.assert_spans)

    # The lakefile's package name is not a namespace root; the `lean_lib` names are.
    package_roots.discard("matrix-multiplication")
    if not package_roots:
        die("could not read any lean_lib name out of lakefile.toml")

    namespace_like = set(namespaces)
    declared_base = {}
    for name in decls:
        parts = name.split(".")
        for k in range(1, len(parts)):
            namespace_like.add(".".join(parts[:k]))
        declared_base.setdefault(parts[-1], []).append(name)

    total = 0
    ok = 0
    unresolved = []
    dark = []
    malformed = []

    for facts in file_facts:
        for line, name, enclosing in facts.asserts:
            total += 1
            if name is None or not IDENT_RE.match(name):
                malformed.append((facts.path, line, name))
                continue
            candidates = [name]
            for prefix in prefixes(enclosing):
                candidates.append(prefix + "." + name)
            for opened in sorted(facts.opens):
                candidates.append(opened + "." + name)

            if any(candidate in decls for candidate in candidates):
                ok += 1
                continue

            last = name.rsplit(".", 1)[-1].strip("«»")
            parent = name.rsplit(".", 1)[0] if "." in name else ""

            # Only a dotted name rooted in one of this package's own libraries is judged.  An
            # unqualified assertion, or one rooted in Mathlib/Cslib/core, is left UNRESOLVED:
            # this checker has no view of those environments.
            in_package = bool(parent) and name.split(".", 1)[0] in package_roots
            parent_known = bool(parent) and parent in namespace_like

            if not (in_package and parent_known) or last in AUTO_GENERATED_COMPONENTS:
                unresolved.append((facts.path, line, name))
            elif last in declared_base:
                # The parser demonstrably sees declarations with this base name, and none of them
                # is the one asserted: the target moved namespace, or was renamed around it.
                dark.append((facts.path, line, name, "moved", sorted(declared_base[last])[:3]))
            elif last not in token_corpus:
                # The base name occurs in no committed .lean file at all: the `coverageChecked`
                # signature -- regenerated out of existence, assertion left behind.
                dark.append((facts.path, line, name, "absent", []))
            else:
                # The base name is written somewhere but never as a declaration this parser can
                # see; a macro could be producing it.  Not confident enough to fail.
                unresolved.append((facts.path, line, name))

    return total, ok, unresolved, dark, malformed


# A fixture the classifier is run against before every real scan.  Today's failures hid because
# a scan silently matched nothing; this makes that impossible to do quietly here.
SELF_TEST_SOURCES = [
    ("lakefile.toml", 'name = "matrix-multiplication"\n[[lean_lib]]\nname = "Demo"\n'),
    (
        "Demo/Decls.lean",
        "namespace Demo.Region0\n"
        "/-- doc mentioning ghostChecked, which is only a comment -/\n"
        "theorem normalizationChecked : True := trivial\n"
        "noncomputable def\n"
        "    veryLongDefinitionNameOnItsOwnLine : Nat := 0\n"
        "structure Config where\n"
        "  slack : Nat\n"
        "end Demo.Region0\n"
        "namespace Demo\n"
        "noncomputable section\n"
        "theorem insideNoncomputableSection : True := trivial\n"
        "end\n"
        "section Count\n"
        "theorem insideNamedSectionAfterIt : True := trivial\n"
        "end Count\n"
        "theorem _root_.Demo.Other.rootedTheorem : True := trivial\n"
        "end Demo\n",
    ),
    (
        "Demo/Audit.lean",
        "open Demo Region0\n"
        "#assert_axioms Demo.Region0.normalizationChecked\n"
        "#assert_axioms\n"
        "  Demo.Region0.veryLongDefinitionNameOnItsOwnLine\n"
        "#assert_axioms Demo.Region0.Config.slack\n"
        "#assert_axioms Demo.Other.rootedTheorem\n"
        "#assert_axioms Demo.insideNoncomputableSection\n"
        "#assert_axioms Demo.insideNamedSectionAfterIt\n"
        "#assert_axioms Mathlib.Nowhere.someExternalName\n"
        "#assert_axioms Demo.Region0.coverageChecked\n"
        "#assert_axioms Demo.normalizationChecked\n"
        "-- #assert_axioms Demo.Region0.commentedOutChecked\n",
    ),
]

SELF_TEST_EXPECTED_DARK = {
    ("Demo/Audit.lean", "Demo.Region0.coverageChecked", "absent"),
    ("Demo/Audit.lean", "Demo.normalizationChecked", "moved"),
}


def self_test() -> int:
    total, ok, unresolved, dark, malformed = analyse(SELF_TEST_SOURCES)
    problems = []
    if total != 9:
        problems.append("expected 9 assertions in the fixture, found %d" % total)
    if ok != 6:
        problems.append(
            "expected 6 resolved assertions, found %d (%s)"
            % (ok, "resolution regressed")
        )
    got_dark = set((path, name, kind) for path, _line, name, kind, _near in dark)
    if got_dark != SELF_TEST_EXPECTED_DARK:
        problems.append("dark set mismatch: expected %s, got %s" % (sorted(SELF_TEST_EXPECTED_DARK), sorted(got_dark)))
    external = [item for item in unresolved if item[2] == "Mathlib.Nowhere.someExternalName"]
    if len(unresolved) != 1 or not external:
        problems.append("expected exactly the external name to be UNRESOLVED, got %s" % (unresolved,))
    if malformed:
        problems.append("unexpected malformed assertions: %s" % (malformed,))
    if problems:
        for problem in problems:
            sys.stderr.write("check_assert_axioms_targets: SELF-TEST FAILED: %s\n" % problem)
        return 1
    print("self-test: 9 fixture assertions, 6 resolved, 1 unresolved, "
          "2 dark (absent + moved). OK.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(add_help=True, description=__doc__.splitlines()[0])
    parser.add_argument("--rev", default="HEAD", help="git revision to analyse (default HEAD)")
    parser.add_argument(
        "--update",
        action="store_true",
        help="regenerate " + GRANDFATHER_FILE + " from the analysed revision",
    )
    parser.add_argument(
        "--list-unresolved",
        action="store_true",
        help="print every UNRESOLVED assertion instead of just counting them",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run the classifier against its built-in fixture and exit",
    )
    args = parser.parse_args()

    if args.self_test:
        return self_test()

    try:
        repo_root = subprocess.check_output(
            ["git", "rev-parse", "--show-toplevel"], text=True
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        die("not inside a git work tree")
        return 2

    total, ok, unresolved, dark, malformed = analyse(iter_lean_sources(args.rev))

    if total == 0:
        die(
            "found no `#assert_axioms` at all at %s -- refusing to report a clean scan, since a "
            "check that silently matches nothing is worse than no check" % args.rev
        )

    grandfathered = load_grandfather(repo_root)

    if args.update:
        target = os.path.join(repo_root, GRANDFATHER_FILE)
        with open(target, "w", encoding="utf-8") as handle:
            handle.write(HEADER)
            if dark:
                handle.write("\n")
                for path, _line, name, kind, near in sorted(dark):
                    if kind == "moved" and near:
                        handle.write("# `%s` is declared as %s.\n" % (name.rsplit(".", 1)[-1], ", ".join(near)))
                    handle.write("%s:%s\n" % (path, name))
        print("Wrote %s with %d dark assertion(s) from %s." % (GRANDFATHER_FILE, len(dark), args.rev))
        return 0

    dark_keys = set("%s:%s" % (item[0], item[2]) for item in dark)
    new_dark = [item for item in dark if "%s:%s" % (item[0], item[2]) not in grandfathered]
    old_dark = len(dark) - len(new_dark)
    stale = sorted(entry for entry in grandfathered if entry not in dark_keys)

    print(
        "#assert_axioms targets at %s: %d asserted, %d resolved, %d unresolved, %d dark "
        "(%d grandfathered, %d new)."
        % (args.rev, total, ok, len(unresolved), len(dark), old_dark, len(new_dark))
    )

    if malformed:
        for path, line, name in malformed:
            print("NOTICE: %s:%d: #assert_axioms without a parsable argument (%r)." % (path, line, name))

    if args.list_unresolved:
        for path, line, name in sorted(unresolved):
            print("UNRESOLVED: %s:%d: %s" % (path, line, name))
    elif unresolved:
        print(
            "NOTICE: %d assertion(s) name declarations outside this package or beyond this "
            "parser (Mathlib/Cslib/core names, macro-generated names, structure fields). "
            "Re-run with --list-unresolved to see them; they are never failed on." % len(unresolved)
        )

    if stale:
        print(
            "NOTICE: %d stale entry/entries in %s (no longer dark, or the file is gone); "
            "delete them:" % (len(stale), GRANDFATHER_FILE)
        )
        for entry in stale:
            print("  %s" % entry)

    if old_dark:
        print(
            "NOTICE: %d grandfathered dark assertion(s) still provide no assurance; see %s."
            % (old_dark, GRANDFATHER_FILE)
        )

    if new_dark:
        print("")
        for path, line, name, kind, near in sorted(new_dark):
            print(
                "FAIL: %s:%d: `#assert_axioms %s` names a declaration that does not exist."
                % (path, line, name)
            )
            if kind == "absent":
                print(
                    "      `%s` is declared nowhere and even the bare name `%s` appears in no "
                    "committed .lean file." % (name, name.rsplit(".", 1)[-1])
                )
            else:
                print(
                    "      `%s` is declared as %s -- the target moved or was renamed and this "
                    "assertion was left behind." % (name.rsplit(".", 1)[-1], ", ".join(near))
                )
            print(
                "      realizeGlobalConstWithInfos throws before any axiom is collected, so this "
                "assertion never runs, and it takes every other assertion in %s down with it."
                % os.path.basename(path)
            )
        print("")
        print(
            "If this really is a name the parser cannot see (a macro-generated declaration), "
            "say so in %s and add the line there." % GRANDFATHER_FILE
        )
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
