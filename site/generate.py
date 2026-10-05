#!/usr/bin/env python3
"""Static-site generator for the omega leaderboard.  python3 stdlib only, no framework, no JS.

Inputs (all in this directory unless noted):
    frontier.json    projection of Frontier.lean, built by extract_frontier.py (the committed
                     leaderboard record; verified fresh against Frontier.lean at every run)
    history.json     published record history + this repo's formalized ladder + conditional tracks
    style.css        the shared stylesheet (copied verbatim into the output)
    ../notes/        record notes; a row links its note iff notes/<slug>/ exists

Outputs (default site/_site/, gitignored):
    index.html scoreboard.html contribute.html about.html style.css records.json

Every emitted page is round-tripped through html.parser and the build fails on any
unbalanced tag or dangling local link.

Usage:
    python3 site/generate.py [--out DIR]
"""

from __future__ import annotations

import json
import shutil
import sys
from fractions import Fraction
from html import escape
from html.parser import HTMLParser
from pathlib import Path

SITE = Path(__file__).resolve().parent
REPO = SITE.parent
REPO_URL = "https://github.com/thomasahle/matrix-multiplication"
BLOB = REPO_URL + "/blob/main/"

# ----------------------------------------------------------------------------- data loading


def load_inputs():
    frontier = json.loads((SITE / "frontier.json").read_text(encoding="utf-8"))
    # Keep decimals exact: floats in history.json become strings.
    hist = json.loads((SITE / "history.json").read_text(encoding="utf-8"), parse_float=str)

    # Freshness gate: frontier.json must match Frontier.lean right now.
    sys.path.insert(0, str(SITE))
    import extract_frontier  # noqa: E402

    fresh = extract_frontier.build()
    if extract_frontier.stable(fresh) != extract_frontier.stable(frontier):
        sys.stderr.write(
            "generate: ERROR: site/frontier.json is stale relative to Frontier.lean.\n"
            "          Run `python3 site/extract_frontier.py` and commit the result.\n"
        )
        sys.exit(1)
    return frontier, hist


def accuracy_checks(frontier, hist):
    """Every formalized claim must trace to a real file containing the named declaration."""
    problems = []
    rows = list(hist["formalized_ladder"])
    rows += [r for r in hist["records"] if r["status"] in ("formalized", "conditional_pending")]
    for r in rows:
        mod, decl = r.get("lean_module"), r.get("lean_declaration")
        pending = (
            r.get("status") == "conditional_pending"
            or r.get("date_landed") == "pending commit"
        )
        if not mod:
            if not pending:
                problems.append(f"row {r.get('display') or r.get('bound')}: no lean_module")
            continue
        p = REPO / mod
        if not p.is_file():
            if pending:
                # Pending rows are advertised as not-yet-citable; their files may be
                # untracked or absent in a clean checkout. Best-effort only.
                sys.stderr.write(f"generate: note: pending row {mod} not present (ok)\n")
            else:
                problems.append(f"{mod}: file does not exist")
        elif decl and decl not in p.read_text(encoding="utf-8"):
            problems.append(f"{mod}: declaration `{decl}` not found in file")
    fr = frontier["record"]
    ep = REPO / fr["endpoint_file"]
    if not ep.is_file() or fr["endpoint_theorem"].rsplit(".", 1)[-1] not in ep.read_text(encoding="utf-8"):
        problems.append(f"frontier endpoint `{fr['endpoint_theorem']}` not found in {fr['endpoint_file']}")
    if problems:
        sys.stderr.write("generate: ERROR: content-accuracy check failed:\n")
        for p in problems:
            sys.stderr.write(f"  - {p}\n")
        sys.exit(1)


# ----------------------------------------------------------------------------- small helpers


def note_href(slug):
    if slug and (REPO / "notes" / slug / "note.tex").is_file():
        return f"{BLOB}notes/{slug}/note.tex"
    return None


def dec(s) -> Fraction:
    return Fraction(str(s))


def fmt_delta(a: Fraction, b: Fraction, approx: bool) -> str:
    d = a - b
    s = f"{float(d):.7f}".rstrip("0").rstrip(".")
    return ("≈ −" if approx else "−") + s


def mono(s: str) -> str:
    return f"<code>{escape(s)}</code>"


def gh(path: str, label: str | None = None) -> str:
    return f'<a href="{BLOB}{escape(path)}">{escape(label or path)}</a>'


# ----------------------------------------------------------------------------- timeline SVG


def timeline_svg(frontier, hist) -> str:
    """The record-history chart: inline SVG, no JS, theme-aware via CSS variables.

    Two tracks: the published world-record progression (neutral, step line + open circles)
    and this repository's formalized ladder (accent, filled circles), plotted at the year the
    mathematics was published.  Conditional tracks are open dashed diamonds: visibly not records.
    """
    pub = [r for r in hist["records"] if r["status"] in ("literature", "formalized")]
    cond = [r for r in hist["records"] if r["status"] == "conditional_pending"]
    ladder = hist["formalized_ladder"]
    fr = frontier["record"]

    W, H = 760, 430
    ml, mr, mt, mb = 56, 14, 46, 46
    iw, ih = W - ml - mr, H - mt - mb
    x0, x1 = 1966, 2030
    ylo, yhi = Fraction("2.34"), Fraction("2.86")

    def X(year) -> float:
        return ml + (float(year) - x0) / (x1 - x0) * iw

    def Y(bound) -> float:
        return mt + float((yhi - dec(bound)) / (yhi - ylo)) * ih

    e = []  # svg elements
    # gridlines + y ticks
    for t in ("2.4", "2.5", "2.6", "2.7", "2.8"):
        y = Y(t)
        e.append(f'<line class="grid" x1="{ml}" y1="{y:.1f}" x2="{ml + iw}" y2="{y:.1f}"/>')
        e.append(f'<text x="{ml - 8}" y="{y + 4:.1f}" text-anchor="end">{t}</text>')
    # x ticks
    for yr in range(1970, 2030, 10):
        x = X(yr)
        e.append(f'<line class="axis" x1="{x:.1f}" y1="{mt + ih}" x2="{x:.1f}" y2="{mt + ih + 5}"/>')
        e.append(f'<text x="{x:.1f}" y="{mt + ih + 20}" text-anchor="middle">{yr}</text>')
    # axes
    e.append(f'<line class="axis" x1="{ml}" y1="{mt}" x2="{ml}" y2="{mt + ih}"/>')
    e.append(f'<line class="axis" x1="{ml}" y1="{mt + ih}" x2="{ml + iw}" y2="{mt + ih}"/>')
    e.append(f'<text class="axis-title" x="{ml}" y="{mt - 18}" text-anchor="start">upper bound on ω</text>')
    e.append(f'<text class="axis-title" x="{ml + iw / 2:.0f}" y="{H - 6}" text-anchor="middle">year</text>')

    # published-record step line (step-after)
    pts = sorted(pub, key=lambda r: (int(r["year"]), -float(dec(r["bound"]))))
    d = [f"M {X(pts[0]['year']):.1f} {Y(pts[0]['bound']):.1f}"]
    for prev, cur in zip(pts, pts[1:]):
        d.append(f"H {X(cur['year']):.1f}")
        d.append(f"V {Y(cur['bound']):.1f}")
    e.append(f'<path class="step" d="{" ".join(d)}"/>')

    ladder_keys = {(int(l["published_year"]), str(dec(l["decimal"]))) for l in ladder}

    # published points (skip those the ladder also plots — the accent marker wins)
    for r in pts:
        if (int(r["year"]), str(dec(r["bound"]))) in ladder_keys:
            continue
        tip = f"{r['year']} · {r['bound']} · {r['authors']} — published record, not formalized here"
        e.append(
            f'<circle class="pt-lit" cx="{X(r["year"]):.1f}" cy="{Y(r["bound"]):.1f}" r="3.5">'
            f"<title>{escape(tip)}</title></circle>"
        )

    # formalized ladder points + frontier ring
    labels = []
    fr_short = fr["endpoint_theorem"].rsplit(".", 1)[-1]
    for l in ladder:
        x, y = X(l["published_year"]), Y(l["decimal"])
        is_frontier = l["lean_declaration"] == fr_short
        tip = f"{l['display']} · {l['source']} — formalized in this repo ({l['lean_declaration']})"
        if is_frontier:
            tip += " — CURRENT FRONTIER RECORD"
            e.append(f'<circle class="ring" cx="{x:.1f}" cy="{y:.1f}" r="8"/>')
        if l["date_landed"] == "pending commit":
            tip += " — pending commit, not yet citable by Frontier.lean"
        e.append(
            f'<circle class="pt-formal" cx="{x:.1f}" cy="{y:.1f}" r="4.5">'
            f"<title>{escape(tip)}</title></circle>"
        )
        text = l["decimal"] + (" ← frontier" if is_frontier else "")
        labels.append([x + 12, y + 4, text, "start", is_frontier])

    # conditional diamonds
    for r in cond:
        x, y = X(r["year"]), Y(r["bound"])
        s = 5.2
        tip = (f"{r['bound']} — CONDITIONAL track (named unproved obligations); "
               "not a record and not claimed as one")
        e.append(
            f'<path class="pt-cond" d="M {x:.1f} {y - s:.1f} L {x + s:.1f} {y:.1f} '
            f'L {x:.1f} {y + s:.1f} L {x - s:.1f} {y:.1f} Z"><title>{escape(tip)}</title></path>'
        )
    if cond:
        cx = X(cond[0]["year"])
        cy = min(Y(r["bound"]) for r in cond)
        labels.append([cx - 12, cy - 16, "conditional targets (not records)", "end", False])

    # published-record label (last literature point)
    lit = [r for r in pts if r["status"] == "literature"]
    if lit:
        last = min(lit, key=lambda r: dec(r["bound"]))
        labels.append([X(last["year"]) - 12, Y(last["bound"]) + 20,
                       f"{last['bound']} published record", "end", False])

    # de-collide labels that share an x-region: enforce 14px vertical spacing
    labels.sort(key=lambda L: (round(L[0] / 40), L[1]))
    for prev, cur in zip(labels, labels[1:]):
        if round(prev[0] / 40) == round(cur[0] / 40) and cur[1] - prev[1] < 14:
            cur[1] = prev[1] + 14
    for x, y, text, anchor, strong in labels:
        cls = ' class="lbl-strong"' if strong else ' class="lbl"'
        e.append(f'<text{cls} x="{x:.1f}" y="{y:.1f}" text-anchor="{anchor}">{escape(text)}</text>')

    # legend (top right, an empty data region)
    lx, ly = ml + iw - 248, mt + 8
    e.append(f'<circle class="pt-formal" cx="{lx}" cy="{ly}" r="4.5"/>'
             f'<text x="{lx + 12}" y="{ly + 4}">formalized in this repo</text>')
    e.append(f'<circle class="pt-lit" cx="{lx}" cy="{ly + 19}" r="3.5"/>'
             f'<text x="{lx + 12}" y="{ly + 23}">published record (literature only)</text>')
    s = 5.2
    e.append(f'<path class="pt-cond" d="M {lx} {ly + 38 - s:.1f} L {lx + s:.1f} {ly + 38} '
             f'L {lx} {ly + 38 + s:.1f} L {lx - s:.1f} {ly + 38} Z"/>'
             f'<text x="{lx + 12}" y="{ly + 42}">conditional (not a record)</text>')

    return (
        f'<svg class="chart" viewBox="0 0 {W} {H}" role="img" '
        'aria-label="Upper bounds on the matrix multiplication exponent omega over time: the '
        'published record progression from 2.8074 in 1969 to 2.371339 in 2024, the bounds '
        'formalized in this repository down to 2.375477, and two conditional targets near 2.366.">'
        "<desc>Step chart of the published record progression with this repository's formalized "
        "ladder overlaid; conditional certificate targets shown as open diamonds.</desc>"
        + "".join(e)
        + "</svg>"
    )


# ----------------------------------------------------------------------------- page shell


NAV = [("index.html", "Home"), ("scoreboard.html", "Scoreboard"),
       ("contribute.html", "Contribute"), ("about.html", "About")]


def shell(title: str, active: str, body: str, frontier) -> str:
    prov = frontier.get("provenance", {})
    commit = prov.get("repo_commit", "unknown")[:12]
    when = prov.get("generated_utc", "")
    tracked = prov.get("frontier_lean_tracked", False)
    tracked_note = "" if tracked else (
        "<br>Note: at generation time <code>Frontier.lean</code> existed in the working tree "
        "but was not yet committed; the frontier data reflects the working tree."
    )
    nav = "".join(
        f'<a href="{h}"{" class=\"active\"" if h == active else ""}>{t}</a>' for h, t in NAV
    )
    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="color-scheme" content="light dark">
<title>{escape(title)}</title>
<meta name="description" content="A machine-checked leaderboard for upper bounds on the matrix multiplication exponent omega: every entry is a Lean 4 theorem verified by the Lean kernel.">
<link rel="stylesheet" href="style.css">
<link rel="icon" href="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 16 16'%3E%3Ctext y='13' font-size='13'%3E%CF%89%3C/text%3E%3C/svg%3E">
</head>
<body>
<header>
<div class="wrap bar">
<a class="brand" href="index.html">ω&#8201;&lt;&#8201;?</a>
<nav>{nav}<a href="{REPO_URL}" rel="external">GitHub&#8599;</a></nav>
</div>
</header>
<main class="wrap">
{body}
</main>
<footer>
<div class="wrap">
<p>Generated {escape(when)} from commit <code>{escape(commit)}</code> ·
data: <code>Frontier.lean</code> → <code>site/frontier.json</code> + <code>site/history.json</code> ·
<a href="records.json">records.json</a>{tracked_note}</p>
<p>Referee: the Lean kernel. Axioms: <code>propext</code> · <code>Classical.choice</code> · <code>Quot.sound</code> — nothing else.</p>
</div>
</footer>
</body>
</html>
"""


# ----------------------------------------------------------------------------- index


def index_page(frontier, hist) -> str:
    fr = frontier["record"]
    ladder = hist["formalized_ladder"]
    sharpest = min(ladder, key=lambda l: dec(l["decimal"]))
    fr_dec = dec(fr["decimal"])
    pending = [l for l in ladder if dec(l["decimal"]) < fr_dec]
    lit_rec = str(hist["meta"]["current_literature_record"])

    pending_chip = ""
    if pending:
        best = min(pending, key=lambda l: dec(l["decimal"]))
        pending_chip = (
            f'<p class="chip-line"><span class="badge b-pend">frontier upgrade pending</span> '
            f'A sharper bound, <strong>ω&nbsp;&lt;&nbsp;{escape(best["decimal"])}</strong> '
            f'({mono(best["lean_declaration"])}), is fully formalized in the working tree and '
            f'becomes the record via a documented three-line PR the moment its files are '
            f'committed — see the <a href="scoreboard.html">scoreboard</a>.</p>'
        )

    fingerprints = frontier.get("statement_fingerprints", {})
    fp_rows = "".join(
        f"<tr><td>{mono(k)}</td><td>{mono(v)}</td></tr>" for k, v in fingerprints.items()
    )

    return f"""
<section class="hero">
<p class="eyebrow">A machine-checked leaderboard for the matrix-multiplication exponent</p>
<h1 class="big">ω&#8202;&lt;&#8202;{escape(fr["decimal"])}</h1>
<p class="sub">Kernel-checked in Lean&nbsp;4, over <em>every</em> field.
The frontier is a file, and it moves when you push.</p>
<p class="hero-meta">
exact constant {mono(fr["constant"])} ·
theorem {mono(fr["frontier_theorem"])} = {mono(fr["endpoint_theorem"])} ·
axioms {mono("propext")} {mono("Classical.choice")} {mono("Quot.sound")} only
</p>
{pending_chip}
<p class="triad">
<a class="btn" href="{BLOB}Frontier.lean">The record file: Frontier.lean&#8599;</a>
<a class="btn" href="scoreboard.html">Full scoreboard</a>
<a class="btn" href="about.html#trust">How it's checked</a>
</p>
</section>

<section>
<h2>The challenge</h2>
<p>How fast can two matrices be multiplied? This is an open, Polymath-style attack on the
matrix-multiplication exponent ω — anyone may contribute, every claimed bound must be a Lean&nbsp;4
theorem checked by the Lean kernel, and the record lives on a machine-checked leaderboard whose
referee is a compiler, not a committee.</p>
<div class="stats">
<div class="stat"><div class="n">1,900+</div><div class="d">enforcing <code>#assert_axioms</code> checks — the build fails if any audited theorem touches an extra axiom</div></div>
<div class="stat"><div class="n">3</div><div class="d">axioms in the trusted base: Lean's standard <code>propext</code>, <code>Classical.choice</code>, <code>Quot.sound</code></div></div>
<div class="stat"><div class="n">0</div><div class="d"><code>sorry</code>, project axioms, or floating point anywhere in the trusted path — every inequality is exact rational arithmetic with directed rounding</div></div>
</div>
</section>

<section>
<h2>Sixty years of ω</h2>
{timeline_svg(frontier, hist)}
<p class="caption">The published world record (open circles, step line) against what this
repository has machine-checked (filled). Open dashed diamonds are <em>conditional</em>
certificate tracks — proved implications with named unproved hypotheses; they are not records
and are not claimed as bounds. Hover any point for details; the
<a href="scoreboard.html">scoreboard</a> is the full table.</p>
</section>

<section>
<h2>Where things stand</h2>
<div class="tiles">
<div class="tile t-accent"><div class="k">current frontier (committed, kernel-checked)</div><div class="v">ω&nbsp;&lt;&nbsp;{escape(fr["decimal"])}</div></div>
<div class="tile"><div class="k">sharpest formalized in the tree{" (pending commit)" if sharpest["date_landed"] == "pending commit" else ""}</div><div class="v">ω&nbsp;&lt;&nbsp;{escape(sharpest["decimal"])}</div></div>
<div class="tile t-lit"><div class="k">published record — literature only, <em>not</em> formalized</div><div class="v">ω&nbsp;&lt;&nbsp;{escape(lit_rec)}</div></div>
</div>
<p><a href="scoreboard.html">Full scoreboard →</a></p>
</section>

<section id="trust">
<h2>The trust contract</h2>
<p>An entry on the leaderboard is a Lean theorem — not a paper, not a preprint, not a numerical
experiment. The frontier itself is a single Lean file ({gh("Frontier.lean", "Frontier.lean")}):
one exact rational constant, one fixed statement shape for what "a bound on ω" means, and a
theorem in that shape proved by direct application of a result committed to this repository. The
Lean kernel type-checks every proof in the entry's dependency cone; an enforcing audit fails the
build if any leaderboard theorem depends on any axiom beyond Lean's three standard ones; static
gates reject <code>sorry</code>, hidden axioms, and unreviewed escape hatches; and statement
fingerprints make it impossible to silently weaken a theorem while keeping its name. Human
maintainers review whether a statement <em>means</em> what it claims — the one thing a kernel
cannot check — but no human can declare a green, correctly shaped entry invalid, and no human can
argue an unproved one in. How you found your proof is irrelevant: an LLM, a SAT solver, an
optimizer, or a pencil are all equally acceptable, because none of them is trusted — the kernel
checks the result either way.</p>
<div class="tablewrap"><table class="mini">
<caption>Committed statement fingerprints (pin what the statements <em>mean</em>)</caption>
<thead><tr><th scope="col">declaration</th><th scope="col">fingerprint</th></tr></thead>
<tbody>{fp_rows}</tbody>
</table></div>
</section>

<section class="cta">
<h2>You can help</h2>
<p>Every open circle on the chart is an unformalized published record — a concrete target. So is
every named proof obligation on the conditional tracks. Proofs by humans, LLMs, SAT solvers, and
optimizers are all welcome; the kernel referees.</p>
<p><a class="btn b-primary" href="contribute.html">How to contribute</a></p>
</section>
"""


# ----------------------------------------------------------------------------- scoreboard


def scoreboard_page(frontier, hist) -> str:
    fr = frontier["record"]
    ladder = sorted(hist["formalized_ladder"], key=lambda l: -dec(l["decimal"]))
    fr_short = fr["endpoint_theorem"].rsplit(".", 1)[-1]

    rows = []
    prev = None
    for l in ladder:
        is_frontier = l["lean_declaration"] == fr_short
        pending = l["date_landed"] == "pending commit"
        badge = ""
        if is_frontier:
            badge = ' <span class="badge b-frontier">current frontier</span>'
        elif pending:
            badge = ' <span class="badge b-pend">pending commit</span>'
        exact = f'<br><span class="muted">= {escape(l["exact"])}</span>' if l["exact"] else ""
        if prev is None:
            margin = "—"
        else:
            approx = not (prev.get("exact") and l.get("exact"))
            margin = fmt_delta(dec(prev["decimal"]), dec(l["decimal"]), approx)
        note = note_href(l["note_slug"])
        note_cell = f'<a href="{note}">note</a>' if note else '<span class="muted">—</span>'
        cert_cell = ('<span class="muted">— (kernel-checked; no external certificate)</span>'
                     if not l["certificate"] else mono(l["certificate"]))
        cls = ' class="frontier-row"' if is_frontier else (' class="pending-row"' if pending else "")
        rows.append(f"""<tr{cls}>
<td><strong>{escape(l["display"])}</strong>{badge}{exact}</td>
<td><span class="badge b-form">unconditional</span><br><span class="muted">{escape(l["generality"])}</span></td>
<td>{escape(l["date_landed"])}</td>
<td>{escape(l["formalized_by"])}<br><span class="muted">after {escape(l["source"])}</span></td>
<td>{mono(l["lean_declaration"])}<br><a href="{BLOB}{escape(l["lean_module"])}">{escape(l["lean_module"])}</a></td>
<td>{note_cell}</td>
<td>{cert_cell}</td>
<td>{margin}</td>
</tr>""")
        prev = l

    cond = [r for r in hist["records"] if r["status"] == "conditional_pending"]
    cond_rows = []
    for r in cond:
        decl = (mono(r["lean_declaration"]) if r.get("lean_declaration")
                else '<span class="muted">adapter boundary (no single endpoint yet)</span>')
        cond_rows.append(f"""<tr>
<td><strong>ω&nbsp;&lt;&nbsp;{escape(str(r["bound"]))}</strong></td>
<td><span class="badge b-cond">conditional — not a record</span></td>
<td>{decl}<br><a href="{BLOB}{escape(r["lean_module"])}">{escape(r["lean_module"])}</a></td>
<td class="digest">{mono(r["certificate"])}</td>
<td>{escape(r["notes"])}</td>
</tr>""")

    lit_rows = []
    for r in sorted(hist["records"], key=lambda r: (int(r["year"]), -float(dec(r["bound"])))):
        if r["status"] == "conditional_pending":
            continue
        if r["status"] == "formalized":
            status = ('<span class="badge b-form">formalized here</span><br>'
                      + mono(r["lean_declaration"]) + "<br>"
                      + f'<a href="{BLOB}{escape(r["lean_module"])}">{escape(r["lean_module"])}</a>')
        else:
            status = '<span class="badge b-lit">literature — not formalized here</span>'
        bound = r.get("bound_display", str(r["bound"]))
        lit_rows.append(f"""<tr>
<td>{r["year"]}</td>
<td><strong>{escape(str(bound))}</strong></td>
<td>{escape(r["authors"])}</td>
<td>{escape(r["citation"])}<br><span class="muted">{escape(r["notes"])}</span></td>
<td>{status}</td>
</tr>""")

    return f"""
<h1>Scoreboard</h1>
<section class="hero-panel">
<h2>The frontier</h2>
<p class="frontier-line"><strong class="frontier-num">ω&#8202;&lt;&#8202;{escape(fr["decimal"])}</strong>
<span class="muted">exactly {mono(fr["constant"])}, over every field, in every universe</span></p>
<p>Shape {mono(fr["shape"])}: {mono(fr["shape_statement"] or "")}<br>
Record theorem {mono(fr["frontier_theorem"])} in {gh("Frontier.lean")}, proved by
<code>exact</code>-application of {mono(fr["endpoint_theorem"])}
({gh(fr["endpoint_file"])}).<br>
Enforcement: {mono("#assert_axioms")} on the record and committed
{mono("#assert_statement_fingerprint")} lines on the statement spine — no PR can redefine what
"ω&nbsp;&lt;&nbsp;c over every field" means without a visible hash change.</p>
</section>

<section>
<h2>Formalized ladder — this repository</h2>
<p>Machine-checked Lean theorems, axiom-audited to Lean's three standard axioms. Every row links
the exact declaration; "margin" is the improvement over the row above (≈ where a bound is an
irrational log form). Rows follow the repository's history of the classical constructions; the
notes convention (<a href="{BLOB}notes/README.md">notes/</a>, "no note, no merge") applies to all
records from launch onward — these inaugural rows predate it.</p>
<div class="tablewrap">
<table>
<thead><tr>
<th scope="col">bound</th><th scope="col">class</th><th scope="col">date landed</th>
<th scope="col">contributors</th><th scope="col">Lean declaration</th><th scope="col">note</th>
<th scope="col">certificate</th><th scope="col">margin</th>
</tr></thead>
<tbody>
{"".join(rows)}
</tbody>
</table>
</div>
</section>

<section>
<h2>Conditional tracks — <em>not</em> records</h2>
<p>Proved Lean implications whose hypotheses are named unproved <code>Prop</code> obligations
(never axioms, never silent). They are listed because they are real, auditable work in the tree —
and honestly labeled because none of them is a bound on ω until every obligation is discharged.</p>
<div class="tablewrap">
<table>
<thead><tr>
<th scope="col">target</th><th scope="col">status</th><th scope="col">Lean implication</th>
<th scope="col">certificate digest (SHA-256)</th><th scope="col">obligations / notes</th>
</tr></thead>
<tbody>
{"".join(cond_rows)}
</tbody>
</table>
</div>
</section>

<section>
<h2>Published record history</h2>
<p>The progression of the world record in the literature. Gray rows are <strong>not formalized in
this repository</strong> — each one is an open target (see
<a href="contribute.html">Contribute</a>).</p>
<div class="tablewrap">
<table>
<thead><tr>
<th scope="col">year</th><th scope="col">bound</th><th scope="col">authors</th>
<th scope="col">citation / notes</th><th scope="col">status</th>
</tr></thead>
<tbody>
{"".join(lit_rows)}
</tbody>
</table>
</div>
<p class="muted">Superseding and retraction follow
<a href="{BLOB}GOVERNANCE.md">GOVERNANCE.md</a> §3.</p>
</section>
"""


# ----------------------------------------------------------------------------- contribute


def contribute_page(frontier, hist) -> str:
    lit_targets = [r for r in hist["records"] if r["status"] == "literature"]
    targets = "".join(
        f"<li><strong>{escape(str(r.get('bound_display', r['bound'])))}</strong> "
        f"({escape(r['authors'])}, {r['year']}) — {escape(r['citation'])}</li>"
        for r in lit_targets
    )
    return f"""
<h1>Contribute</h1>
<p>The referee here is a compiler. A contribution counts when the Lean kernel accepts it and the
axiom audit stays clean — whether it was found by a person, an LLM, a SAT solver, or an optimizer.
The full rules live in {gh("CONTRIBUTING.md")} (the trust contract, the record-PR recipe, the AI
policy) and {gh("GOVERNANCE.md")} (roles, merge requirements, superseding). This page is the
short version.</p>

<section>
<h2>Ways in, by impact</h2>
<ol class="ladder">
<li><strong>Move the frontier.</strong> Prove a new unconditional
<code>ω&nbsp;&lt;&nbsp;c</code> endpoint over every field, then make the three-line
{gh("Frontier.lean", "Frontier.lean")} change: add the import, lower
<code>frontierConstant</code>, cite your endpoint in <code>frontier</code>. CI decides
<code>new&nbsp;&lt;&nbsp;old</code> in ℚ. <em>First action:</em> read the record-PR recipe,
{gh("CONTRIBUTING.md", "CONTRIBUTING.md")} §3.</li>
<li><strong>Discharge a named obligation.</strong> The conditional tracks on the
<a href="scoreboard.html">scoreboard</a> carry explicit unproved <code>Prop</code> hypotheses
(constituent type counting, compatibility zeroing and hole repair, exact level-four
reconstruction, …). Each one discharged moves a target toward record status.
<em>First action:</em> the obligation table in the repository {gh("README.md", "README")}.</li>
<li><strong>Formalize a literature record.</strong> Every gray scoreboard row is open:
{f"<ul>{targets}</ul>" if targets else ""}
<em>First action:</em> open a GitHub issue claiming the target before you start.</li>
<li><strong>Machinery, corrections, performance.</strong> Reusable lemmas, errata for published
arguments (this project has already corrected several — see
<a href="about.html#errata">About</a>), build-time wins. See the six contribution categories in
{gh("CONTRIBUTING.md", "CONTRIBUTING.md")} §4.</li>
<li><strong>Reproduce and verify.</strong> Run the build and the audits on your machine and
report anything surprising. This is a real contribution: independent reproduction is the point
of the whole design.</li>
<li><strong>Docs and this site.</strong> The site is generated by
{gh("site/generate.py", "site/generate.py")} from
{gh("Frontier.lean", "Frontier.lean")} and two JSON files — stdlib Python, no framework.</li>
</ol>
</section>

<section>
<h2>Build quickstart</h2>
<pre><code>git clone {REPO_URL}.git
cd matrix-multiplication
# toolchain is pinned by ./lean-toolchain ({escape((REPO / "lean-toolchain").read_text(encoding="utf-8").strip())})
lake build                  # the library
lake build AxiomAudit       # the enforcing audit: 1,900+ #assert_axioms checks</code></pre>
<p>The certificate-side checkers are plain Python; the exact commands are in the repository
{gh("README.md", "README")} ("Current proof draft").</p>
</section>

<section>
<h2>Record PRs, in six steps</h2>
<ol>
<li>Prove the unconditional endpoint theorem (any field, exact rational target).</li>
<li>Make the three-line <code>Frontier.lean</code> change — never touch the shapes or the
committed fingerprints.</li>
<li>Commit certificate artifacts with SHA-256 digests and reproduction commands.</li>
<li>Keep <code>#assert_axioms</code> green: <code>propext</code>, <code>Classical.choice</code>,
<code>Quot.sound</code>, nothing else.</li>
<li>Write the 2–6 page note in {gh("notes/README.md", "notes/")} —
<strong>no note, no merge</strong>.</li>
<li>Open the PR with the AI-disclosure block filled in ({gh("CONTRIBUTING.md", "CONTRIBUTING.md")} §5).</li>
</ol>
</section>

<section>
<h2>Working in the open</h2>
<p>Claim what you are working on (a GitHub issue) before you start, state partial progress
openly, and write up failed routes — they are credited contributions here
({gh("CODE_OF_CONDUCT.md", "CODE_OF_CONDUCT.md")}). Statement-meaning review is human and
collegial; validity review is a machine and non-negotiable.</p>
</section>
"""


# ----------------------------------------------------------------------------- about


def about_page(frontier, hist) -> str:
    fr = frontier["record"]
    toolchain = (REPO / "lean-toolchain").read_text(encoding="utf-8").strip()
    return f"""
<h1>About</h1>

<section>
<h2>What is ω?</h2>
<p>Multiplying two n-by-n matrices the way you learned in school takes about n³ multiplications.
In 1969 Volker Strassen stunned mathematicians by showing you can do better — about n^2.81 — and
set off a fifty-year race to find the true exponent: the smallest ω such that matrices can be
multiplied in roughly n^ω steps. Matrix multiplication sits inside almost everything
computational — solving linear systems, graph algorithms, scientific computing, machine
learning — so the value of ω is a fundamental constant of computation itself: it measures how
much structure the most basic operation of linear algebra really has. The record has crept from
2.81 to 2.371339 through increasingly intricate arguments, and many experts believe ω&nbsp;=&nbsp;2,
meaning matrix multiplication is barely harder than reading the input. The proofs behind the
modern records are so involved that very few people have ever verified one end to end. This
project changes the terms: here, a bound counts only when a computer has checked every step of
its proof — and the same formal microscope has already caught several errors in the published
literature.</p>
</section>

<section id="trust">
<h2>What "machine-checked" means here</h2>
<ul>
<li><strong>Proof assistant:</strong> Lean&nbsp;4, toolchain pinned at <code>{escape(toolchain)}</code>
(with Mathlib pinned by <code>lake-manifest.json</code>). The kernel type-checks every proof in a
record's dependency cone.</li>
<li><strong>Trusted base:</strong> the Lean kernel plus exactly three standard axioms —
<code>propext</code>, <code>Classical.choice</code>, <code>Quot.sound</code>. An enforcing audit of
1,900+ <code>#assert_axioms</code> checks fails the build if any audited theorem touches anything
more (so <code>sorry</code>, <code>native_decide</code>, and project axioms cannot hide).</li>
<li><strong>Statement integrity:</strong> committed <code>#assert_statement_fingerprint</code>
hashes pin what <code>omega</code> and the record shape <em>mean</em>, transitively — a statement
cannot be silently weakened while keeping its name.</li>
<li><strong>Exact arithmetic:</strong> no floating point anywhere in the trusted path; every
numerical inequality is certified by exact rational arithmetic with directed rounding.</li>
<li><strong>Generality:</strong> the record shape quantifies over an arbitrary field —
{mono(fr["shape_statement"] or "")} — not one convenient choice.</li>
</ul>
</section>

<section>
<h2>Reproducibility and verifiability statement</h2>
<pre><code>git clone {REPO_URL}.git
cd matrix-multiplication          # toolchain auto-selected from ./lean-toolchain
lake build                        # the library: no sorry, no admit, no project axioms
lake build AxiomAudit             # enforcing audit; fails on any extra axiom</code></pre>
<p>The frontier record is the theorem {mono(fr["frontier_theorem"])} in
{gh("Frontier.lean")}: shape {mono(fr["shape"])}, constant {mono(fr["constant"])}
(=&nbsp;{escape(fr["decimal"])}), proved by <code>exact</code>-application of
{mono(fr["endpoint_theorem"])}. Certificate-driven work ships SHA-256 digests and Python
checkers (see the repository {gh("README.md", "README")}); certificates are <em>inputs</em> the
Lean proofs re-verify, never trusted outputs. This site is itself generated from the repository
by a stdlib-Python script whose extraction step fails loudly if <code>Frontier.lean</code> and
the published data ever disagree.</p>
</section>

<section>
<h2>Honest project status</h2>
<ul>
<li><strong>The committed frontier record is ω&nbsp;&lt;&nbsp;{escape(fr["decimal"])}</strong>
(Coppersmith–Winograd first power), the sharpest bound that is simultaneously unconditional,
all-fields, committed, and axiom-audited.</li>
<li><strong>ω&nbsp;&lt;&nbsp;2.375477</strong> — the full classical CW tensor-square analysis —
is formalized end to end in the working tree and is the strongest matrix-multiplication exponent
bound ever machine-checked. At generation time its files were awaiting commit; the frontier
upgrade is a documented three-line PR. It is <em>not</em> a new mathematical record: the
literature stands at 2.371339 (Alman–Duan–Vassilevska&nbsp;Williams–Xu–Xu–Zhou), unformalized.</li>
<li><strong>Nothing sharper is claimed.</strong> The 2.36999 and 2.36588731 tracks on the
<a href="scoreboard.html">scoreboard</a> are conditional: proved implications with named unproved
obligations. In the repository's own words: "None of these is currently an unconditional new
matrix-multiplication bound." A sorted-pair diagnostic value near 2.3631 exists but is not
currently admissible and is deliberately not displayed as a target.</li>
<li><strong>The goal</strong> is a machine-checked bound beating the published record — and,
long-run, a formal account of both the upper- and lower-bound sides of the field (the barrier
frameworks of Alman–Vassilevska&nbsp;Williams are already formalized here, including corrections).</li>
</ul>
</section>

<section id="errata">
<h2>Errors found in the literature</h2>
<p>Formalization is a microscope. Working through the published arguments, this project has so
far recorded eight errata — among them: a sign typo in Alman–Vassilevska&nbsp;Williams
Theorem&nbsp;7.3 (the intended relation is ≤, an upper bound); their Corollary&nbsp;5.1's second
corner term is unnecessary; <code>f(1)</code> is undefined, so "every positive integer q" must
read q&nbsp;≥&nbsp;2; and <code>R̲(CW_q^σ)&nbsp;=&nbsp;q+2</code> is <em>false</em> unless
σ²&nbsp;=&nbsp;id. Each erratum is machine-checked in the tree and indexed in the repository
{gh("README.md", "README")}. Where a formalized statement is <em>stronger</em> than the printed
one, that is recorded too.</p>
</section>

<section>
<h2>Kindred projects</h2>
<p>This project sits in a small genre of machine-checked mathematical challenges:
<a href="https://bbchallenge.org" rel="external">bbchallenge</a> (BB(5), Coq),
the <a href="https://teorth.github.io/equational_theories/" rel="external">Equational Theories
Project</a> (22M implications, Lean), and the
<a href="https://imperialcollegelondon.github.io/FLT/" rel="external">FLT formalization</a>
(Lean). Like them, it treats the proof assistant as the referee and the community as the
prover.</p>
</section>

<section>
<h2>People and credit</h2>
<p>Started and maintained by Thomas Dybdahl Ahle, with contributions welcome from anyone —
authorship follows the Polymath/ETP convention described in
{gh("CONTRIBUTING.md", "CONTRIBUTING.md")} §6: contributors are credited by name in the
repository, and records carry their contributors on the
<a href="scoreboard.html">scoreboard</a> forever, including after being superseded.</p>
<pre><code>@misc{{matrix-multiplication-frontier,
  author       = {{Ahle, Thomas Dybdahl and contributors}},
  title        = {{The matrix multiplication exponent frontier:
                  a machine-checked leaderboard}},
  year         = {{2026}},
  howpublished = {{\\url{{{REPO_URL}}}}}
}}</code></pre>
</section>
"""


# ----------------------------------------------------------------------------- validation


VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link",
        "meta", "param", "source", "track", "wbr"}


class Validator(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.stack: list[str] = []
        self.errors: list[str] = []
        self.links: list[str] = []

    def handle_starttag(self, tag, attrs):
        for k, v in attrs:
            if k in ("href", "src") and v:
                self.links.append(v)
        if tag not in VOID:
            self.stack.append(tag)

    def handle_startendtag(self, tag, attrs):
        for k, v in attrs:
            if k in ("href", "src") and v:
                self.links.append(v)

    def handle_endtag(self, tag):
        if tag in VOID:
            return
        if not self.stack:
            self.errors.append(f"closing </{tag}> with empty stack")
        elif self.stack[-1] != tag:
            self.errors.append(f"expected </{self.stack[-1]}>, got </{tag}>")
        else:
            self.stack.pop()


def validate(outdir: Path, pages: list[str]) -> None:
    failed = False
    for name in pages:
        text = (outdir / name).read_text(encoding="utf-8")
        v = Validator()
        v.feed(text)
        v.close()
        if v.stack:
            v.errors.append(f"unclosed tags at EOF: {v.stack}")
        for link in v.links:
            if link.startswith(("http:", "https:", "mailto:", "data:", "#")):
                continue
            target = link.split("#", 1)[0]
            if target and not (outdir / target).is_file():
                v.errors.append(f"dangling local link: {link}")
        if v.errors:
            failed = True
            for err in v.errors:
                sys.stderr.write(f"generate: VALIDATION {name}: {err}\n")
        else:
            print(f"generate: validated {name} ({len(text):,} bytes)")
    if failed:
        sys.exit(1)


# ----------------------------------------------------------------------------- main


def main(argv: list[str]) -> int:
    outdir = SITE / "_site"
    if "--out" in argv:
        outdir = Path(argv[argv.index("--out") + 1]).resolve()
    frontier, hist = load_inputs()
    accuracy_checks(frontier, hist)

    outdir.mkdir(parents=True, exist_ok=True)
    pages = {
        "index.html": ("ω < " + frontier["record"]["decimal"] + " — the matrix multiplication exponent, machine-checked",
                       index_page(frontier, hist)),
        "scoreboard.html": ("Scoreboard — machine-checked bounds on ω", scoreboard_page(frontier, hist)),
        "contribute.html": ("Contribute — the kernel is the referee", contribute_page(frontier, hist)),
        "about.html": ("About — what ω is and what is formalized", about_page(frontier, hist)),
    }
    for name, (title, body) in pages.items():
        (outdir / name).write_text(shell(title, name, body, frontier), encoding="utf-8")
    shutil.copyfile(SITE / "style.css", outdir / "style.css")
    (outdir / "records.json").write_text(
        json.dumps({"frontier": frontier, "history": hist}, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    (outdir / ".nojekyll").write_text("", encoding="utf-8")
    validate(outdir, list(pages))
    print(f"generate: site written to {outdir}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
