# Contributing

This is a formalized, open, incremental attack on the matrix-multiplication exponent ω, in Lean 4
on top of Mathlib.

It is a **Polymath project with a machine-checked scoreboard, and with more AI**. The Polymath half
is the tradition it comes from: open massively-collaborative mathematics, many small contributions
rather than a few heroic ones, partial progress posted openly and valued, failed attempts treated as
results. The scoreboard half is what formalization adds: the frontier of what is proved is a Lean
file, the referee is the Lean kernel, and a contribution is accepted when CI is green — not when a
human is persuaded. The *more AI* half is not a caveat we bury: this repository is substantially
AI-built, AI agents are first-class participants in it, one of the three trust layers below is an AI
reviewer, and §5 and §6 say exactly what that means for disclosure and for credit.

Read this file before your first pull request. It is the newcomer-facing distillation of two longer
documents that stay normative:

- **[`DESIGN.md`](DESIGN.md)** — the architecture, layering, API principles, trust policy, and
  numerics rules. When this file and `DESIGN.md` disagree, `DESIGN.md` wins and this file is buggy;
  say so in an issue.
- **[`README.md`](README.md)** — the consolidated index of everything currently proved here, the
  build targets, and the named proof obligations that are explicitly *not* proved.

Everything else you need is in this file.

**Documents this file mentions that are planned but not in the tree.** They are named here because
the practice they describe is already decided, not because you can click them: a `GOVERNANCE.md`
(the record-PR approval rule, retraction, and the change tiers), a `CODE_OF_CONDUCT.md`, a
pull-request template (`.github/PULL_REQUEST_TEMPLATE.md`), and a `notes/` tree with a `README.md`
and a `TEMPLATE/note.tex`. Until each exists, follow the rule as stated here and say in your PR that
you did; a reviewer will not hold a missing template against you. Everything else this file
references — `Frontier.lean`, `.github/CODEOWNERS`, `.github/workflows/ci.yml`, the `scripts/`
gates, `AxiomAudit/Command.lean`, `LICENSE` — is in the tree today.

---

## 1. The trust contract

Read this section even if you skip the rest.

**An entry on the scoreboard is a Lean theorem.** Not a note, not a numerical experiment, not a
paper. To move the frontier you exhibit a theorem in this repository whose statement matches the
shape the scoreboard fixes — an unconditional bound on ω, or a bound explicitly parameterized by
the named proof obligations it still assumes — and you wire it into `Frontier.lean`.

`Frontier.lean` is in the tree. It declares `Frontier.OmegaBound`, the exact-rational
`Frontier.frontierConstant` (currently `2374631/1000000`), the minimum improvement
`Frontier.recordDelta = 1/100000`, and the anchor theorem `Frontier.frontier`, and it is its own
Lake target so that a record change cannot be hidden inside a library rebuild.

**Trust rests on three layers, and they answer different questions.**

| Layer | Who | What it decides |
| --- | --- | --- |
| 1. The Lean kernel, and CI around it | machine | **Validity.** Is the theorem proved? |
| 2. Automated AI review, on every PR | machine | Mergeability. Is anything being *gamed*? |
| 3. Human review | maintainers and reviewers | Mergeability. Is this the right theorem, well built? |

**Only layer 1 decides mathematical validity.** Layers 2 and 3 decide whether a PR merges — which is
a different and weaker question. A green entry is valid whether or not anyone likes the code; a valid
entry can still be sent back for its documentation, its module placement, or its note.

### Layer 1 — the kernel and CI (validity)

1. **Kernel check.** `lake build AlgebraicComplexity AlgebraicComplexityClients
   MatrixMultiplication AxiomAudit Frontier` must succeed. The Lean kernel type-checks every
   proof term in your entry's dependency cone. There is no reviewer discretion here and no
   partial credit.
2. **Axiom census.** Every literature-facing theorem carries an `#assert_axioms` assertion (see
   `AxiomAudit/Command.lean`), and the audit target *fails elaboration* if an audited declaration
   depends on any axiom outside `propext`, `Classical.choice`, and `Quot.sound`. The audit is
   enforcing, not advisory: about 12,000 assertions run today. Your entry needs its own assert,
   in the right audit target (see §3, step 4). `native_decide` is banned — it records a
   compiler-trusting axiom, and the census would catch it anyway.
3. **Fingerprints.** Three kinds:
   - *Statement fingerprints.* The printed statement of an entry theorem, captured under
     `pp.numericTypes` and `pp.coercions.types`, plus its `#print axioms` output. A refactor that
     silently weakens a conclusion or strengthens a hypothesis shows up as a fingerprint diff. This
     is how in-tree retargeting is already validated, and it is stronger than eyeballing a diff.
   - *Certificate digests.* Generated payloads under `MatrixMultiplication/Generated/` and
     optimizer artifacts carry a schema version, dimensions, denominators, generator revision, and
     a content hash, and the hash is checked inside Lean by the module that consumes the payload.
   - *Static gates.* Twelve of them at the time of writing, all static — no Lean, no network.
     `scripts/trust_scan.sh` (no `sorry`, `admit`, or declared `axiom` in committed sources, and
     no `opaque` outside the reviewed generated-certificate pattern),
     `check_tensor_boundary.sh` (the reusable tensor layer may not import matrix-multiplication
     theory), `check_source_coverage.sh` (no Lean file that no target compiles),
     `check_module_docs.sh` (every hand-written file has a module overview),
     `check_copyright_headers.sh`, `check_assert_axioms_targets.sh` (an `#assert_axioms` naming a
     declaration that does not exist silently aborts every other assertion in its module),
     `check_decide_budget.sh`, `check_heartbeat_governor.sh`, `check_certificate_table_wiring.sh`
     (a module's quoted certificate must be the one its proofs use),
     `check_artifact_provenance.sh`, and `check_declaration_collisions.sh` (WARN only — it prints
     and always exits 0) run on every push and every pull request;
     `check_frontier_improvement.sh` runs on record pull requests. Several carry a grandfather list
     under `scripts/` recording standing debt, and **those lists may only shrink** — do not append
     to one to buy a green run. `DESIGN.md` §"Module hygiene" tabulates all twelve with their
     lists.

### Layer 2 — automated AI review (hack-hunting)

**This layer is not wired up in the tree.** The only artifact here is
`.github/workflows/ai-review.yml.disabled`, a stub whose extension keeps GitHub from running it and
whose own header says the reviewer bot has not been chosen. The preferred route, Copilot code
review, is a repository/organization setting rather than a workflow, so whether it is on is not
visible from a checkout — do not assume a review ran because you did not see one. Read the rest of
this subsection as the specification for that layer. Layers 1 and 3 are live.

The intent: every pull request gets an automated AI review. **The reviewer is GitHub Copilot code
review**, configured to review every pull request automatically, with an **Anthropic-based GitHub
Action** as the documented alternative — and the alternative matters, because Copilot code review
is not free for this purpose:

- Copilot code review is **not included in the Copilot Free plan**. Configuring automatic review
  requires a paid plan (Copilot Pro, Pro+, or Max), and that personal setting covers only pull
  requests *you* create — which is the wrong half of the problem for an open project, where the PRs
  that most need hack-hunting come from contributors.
- Reviewing **every** pull request in a repository is done with a branch ruleset in repository
  settings, a capability GitHub documents for organizations on Copilot Business or Enterprise.
- Since **1 June 2026**, all Copilot usage including code reviews is billed as AI Credits, and
  Actions minutes are consumed for reviews on *private* repositories. Public repositories are
  exempt from the minutes charge — "there are no changes to public repositories, where Actions
  minutes remain free" — so on this repository the Actions bill is zero, but the paid-seat and
  ruleset requirements above still stand.

So: Copilot code review runs here where a maintainer seat covers it, and the fallback that actually
guarantees coverage of *every* PR is an Anthropic-based reviewer running as a GitHub Action from
this repository's own workflow (`anthropics/claude-code-action`). It has one decisive advantage over
any off-the-shelf reviewer: it can be **prompted with the specific hack list below**, which is what
this layer is for. Whichever is running, the requirement is fixed: it runs on every PR, and its
findings are visible to human reviewers.

Pricing and availability above checked 2026-08-28 against
[GitHub Docs — Copilot code review](https://docs.github.com/en/copilot/concepts/code-review/code-review),
[GitHub Docs — configuring automatic code review](https://docs.github.com/en/copilot/how-tos/agents/copilot-code-review/configure-automatic-review),
and the
[GitHub Changelog entry of 2026-04-27](https://github.blog/changelog/2026-04-27-github-copilot-code-review-will-start-consuming-github-actions-minutes-on-june-1-2026/).
<!-- pending: the CI workstream owns the configuration — the Copilot ruleset, or the workflow file
     and the API-key secret for the Action. -->

Its job is **not** to judge the mathematics — layer 1 already did that, better. Its job is to hunt
for the ways a formalization can be *gamed*, which are exactly the things a busy human reviewer skims
past:

- **Bypass patterns.** `native_decide` or another compiler-trusting escape; a `sorry` reintroduced
  under a name the scan does not match; an `axiom` in a file outside the scanned trees; an `opaque`
  without a body; a `#assert_axioms` deleted, weakened, or quietly moved to a target CI does not
  build; a CI gate disabled in the same PR that would have failed it.
- **Statement drift.** A conclusion weakened or a hypothesis strengthened while the theorem keeps its
  name; a `Prop` obligation added to a statement without being named in `README.md`; a scoreboard row
  whose constant does not match the theorem it points at; `ω` replaced by a locally defined lookalike.
- **Suspicious metaprogramming.** A macro, elaborator, or `simp` attribute that changes what a later
  declaration *means* rather than how it is proved; a tactic that manufactures the goal it discharges;
  a definition that asserts rather than defines; a certificate whose content hash is computed from the
  same data it is meant to authenticate.

An automated review is a **filter, not an authority.** It has no approval power, its findings are
advisory, and a human decides what to do with them. A false positive costs a sentence in the PR; a
true positive it catches is one a human reviewer would probably have missed, which is the whole
reason for the layer. Note the deliberate asymmetry with §5's rule that *contributors* may not submit
LLM-written review comments: this is a project-operated gate whose output is labelled as machine
output and counts as nobody's review, not a human passing off generated prose as their own judgement.

### Layer 3 — human review (mergeability)

Human review is **required**, not advisory, in two places:

- **The trusted kernel** — the definitions, statement shapes, certificate boundaries, audit
  commands, and CI gates that every entry's validity rests on. These are covered by `CODEOWNERS`, so
  a maintainer review is mechanically required to merge a change to them.
  `.github/CODEOWNERS` is in the tree and covers `.github/`, `scripts/`, `lakefile.toml`,
  `lean-toolchain`, `lake-manifest.json`, the `AxiomAudit*` trees (including
  `AxiomAudit/Command.lean`) and `Frontier.lean` — the files that decide *what* CI checks. It
  assigns reviewers only: it has no effect until "Require review from Code Owners" is enabled on
  the protected branch (`.github/BRANCH_PROTECTION.md`). Not yet covered by it:
  `MatrixMultiplication/CurrentProofObligations.lean` (the obligation boundary), `DESIGN.md` and
  this file.
- **Every record PR**, which needs two maintainer approvals, one of them a *definitional-kernel
  review*: does the theorem say what the scoreboard claims, are the obligations honest, do the new
  definitions mean what they say. Its full definition is planned for `GOVERNANCE.md`, which is not
  in the tree (see the note above); the rule is the two approvals and the definitional-kernel
  review.

Everything else needs one maintainer approval. **Anyone may review anything** — the reviewer tier is
open, no appointment needed, and a careful independent review is the fastest way to make a record PR
merge.

**Tool provenance never affects validity.** How you found the proof is *not* part of the trust
argument. An LLM, an optimizer written in Python, a SAT solver, a flip-graph search, a numerical
scan, a hand computation, a dream — all are equally acceptable *producers*, because none of them is
trusted. The architecture is deliberately **untrusted producer, proved checker**: external code may
supply a certificate or assemble a proof term from small soundness lemmas, and then the ordinary
Lean kernel checks the result. This is why the AI policy in §5 is a *disclosure and accountability*
policy and not a validity policy: disclosure exists so humans can review a PR well, not because
tool-assisted proofs are worth less.

**Two things follow, and they are the reason this project can be open.**

- *A correct entry cannot be blocked by taste.* If the kernel check, the census, and the
  fingerprints pass, and the statement shape matches, the entry is valid — layer 1 said so, and
  layers 2 and 3 have no vote on that. Maintainers can ask you to improve documentation, module
  placement, or your note before merge, but nobody gets to declare a green record invalid because
  they would have done it differently.
- *A wrong entry cannot be argued into the scoreboard.* Including by the maintainers.

**What is *not* covered.** The kernel checks proofs, not modelling. Two failure modes survive a
green CI, and both are what layers 2 and 3 exist for: an entry whose Lean statement is not the theorem the
mathematics community would recognize (wrong quantifier, wrong field assumption, relation direction
reversed, a `Prop` obligation smuggled in as an unremarked hypothesis), and a certificate whose
generator is checked against itself. Say plainly in your note which obligations your entry carries.
The repository's practice is that an unproved deep input is a `Prop` definition exposed as an
explicit hypothesis of every theorem that consumes it — never an `axiom`, never a typeclass
instance, never quietly reported as proved. Breaking that convention is the one thing that would
make the whole scoreboard worthless.

---

## 2. Getting oriented

```bash
git clone <this repo> && cd matrix-multiplication
lake exe cache get      # Mathlib olean cache
lake build              # the reusable core; the fast edit-compile loop
```

The eight Lake targets, and what each is for, are in `README.md` §Build. The one command that
matches CI is:

```bash
lake build AlgebraicComplexity AlgebraicComplexityClients MatrixMultiplication AxiomAudit Frontier
```

On a memory-constrained machine (16 GB is enough, but only just), run public builds through
`scripts/lake_build_serial.sh`, which takes a worktree lock, sets `LEAN_NUM_THREADS=1`, and lowers
process priority. Two concurrent raw Lake builds in one worktree have produced real
missing-`.olean` races here; rerun under the lock before diagnosing anything as a proof failure.

Where the current frontier is, in one paragraph. The strongest **unconditional** exponent bound in
the tree is `ω < 2.374631` — Duan–Wu–Zhou's second-power (level-two) bound on `CW_6^{⊗2}`,
`omega_lt_2374631` in `Examples/DuanWuZhouLevelTwoOmegaBound.lean`, over any field. The classical
Coppersmith–Winograd tensor-square bound `ω < 2.375477`
(`coppersmithWinograd_square_omega_lt_2375477`, ten-digit directed rational atanh arithmetic) is
just behind it. `Frontier.frontierConstant` carries `2374631/1000000`, so that is what a record PR
is measured against today.

The Total-Weight framework in the tree is conditional: `README.md` §"The Total-Weight framework
(conditional)" records what the tree proves and what it still assumes, and its manuscript is in
preparation and not public. **No new bound on ω is claimed by this repository.** (The `9/4` bound and the
rectangular bounds under `ThirdParty/` are OpenAI's, vendored and re-checked here; see `README.md`
§"Vendored".) Closing the named
obligations in `README.md` §Results is worth more than any new numerical constant.

---

## 3. The record-PR recipe

A record PR is deliberately mechanical. If it is not mechanical, the machinery it needs does not
exist yet, and that machinery is itself a contribution (§4).

### The minimum record delta: δ = 1/100000

**A record PR must improve the frontier constant by at least `δ = 1/100000` (that is, `1e-5`).**
Formally, with `old` the current frontier constant and `new` yours, CI requires

```
new + 1/100000 ≤ old
```

and it requires it of *exact rationals*, decided in Lean by `norm_num` — not of printed decimals.
A tie is not an improvement; neither is a strict improvement smaller than δ.

*Why a threshold at all.* Without one, the cheapest way onto the scoreboard is to run somebody
else's numerical search a little longer and shave the last digit. That is digit-fishing: it moves
the printed constant without contributing any new mathematics, it costs reviewers a full record
review, and it pushes the previous holder's row into history for nothing. δ makes the scoreboard a
record of mathematical progress rather than of compute spent on the same certificate.

*The complementary rule, and the reason δ is not a licence to withhold digits.* **A record entry
should state the tightest constant its certificate actually proves at the submitted parameters**,
and reviewers may ask you to demonstrate it. Do not round your own bound up to leave yourself room
for a cheap follow-up record: an improvement should reflect a genuinely better certificate, not
digits held back from the last one. These two rules only work together — δ without canonical
tightness would simply move the digit-fishing one PR earlier.

*Smaller genuine improvements are welcome*, just not as their own record. Two routes: batch the
improvement with other contributions until it clears δ, or land it as a **non-record PR that
tightens an existing entry's stated constant** — the row keeps its original contributor, gains
yours, and the frontier constant follows. That is a credited contribution (§4) and it is the
honest home for a real-but-small gain.

### Step 1 — the endpoint theorem

Prove your bound where its mathematics lives (a client module under
`AlgebraicComplexity/Examples/`, or an endpoint module under `MatrixMultiplication/`), following
the API and documentation rules in §8. State it in the scoreboard's shape. If your bound carries
proof obligations, they are explicit hypotheses of the statement.

### Step 2 — the three-line `Frontier.lean` change

Add your row to `Frontier.lean`: the exact rational constant, the fully qualified theorem name, and
the attribution. That is the whole change; the scoreboard machinery derives the rest, including the
δ-improvement check against the previous record.

The comparison is already built: `scripts/check_frontier_improvement.sh` reads
`Frontier.frontierConstant` from the merge-base and from your tree, and — when they differ —
synthesizes `new + delta ≤ old` over ℚ with `delta` read from `Frontier.recordDelta`, then has Lean
discharge it with `norm_num`. Do not hand-roll a comparison; consume that one, so every record is
compared the same way.

If your change to `Frontier.lean` is longer than a few lines, something is wrong: either your
statement shape does not match, or you are trying to change the scoreboard's *rules* in a record
PR. Those are separate PRs, and the second one is a governance change (one of the change tiers
planned for `GOVERNANCE.md`; see the note at the top).

### Step 3 — the certificate artifacts

If your bound rests on generated data (an optimizer solution, a table of exact rationals, a
recurrence payload):

- store the payload under `MatrixMultiplication/Generated/` (or a paper-client directory), never in
  the reusable library and never under the gitignored `papers/`;
- record schema version, dimensions, denominators, generator revision, and **content hash**, and
  check the hash inside Lean;
- keep the generator in the repository, with the exact command line that reproduces the payload
  byte-for-byte, in your note (step 5);
- expose the smallest possible semantic theorem to downstream modules (the model is
  `BranchFloorCertified`): tensor, value, and exponent modules must depend on that theorem, not on
  your encoding and not on your generator;
- prefer a theorem-level *sufficient statistic* to a big payload. The going example: a level-two
  recurrence with 1,620 serialized rows has only ~70 distinct keys, and a proved grouping lemma
  plus 70 summed masses is the better certificate. Payload size is a design smell, not a badge.

A certificate checker has four jobs — structural checking, semantic reconstruction, directed
analytic checking, and semantic handoff — and keeping them apart is what keeps the proved checker
small. `DESIGN.md` §"Trust and verification policy" has the numerical rules they serve: exact
arithmetic or a proved enclosure, with every rounding direction verified in Lean.

### Step 4 — the axiom asserts

Add an `#assert_axioms` for your endpoint theorem and for any new literature-facing theorem on the
way to it. Placement matters and is enforced:

- a focused audit whose dependency cone **does not** reach `MatrixMultiplication/Generated/` goes
  under the `AxiomAudit.*` glob;
- one that **does** goes under the opt-in `AxiomAuditCertificate.*` glob, so that ordinary CI does
  not reconstruct multi-thousand-entry tables.

During iteration build the nearest focused audit (`lake build AxiomAuditCertificate.<Name>`), not
the monolithic root.

### Step 5 — the note (mandatory)

**Every record PR includes a 2–6 page LaTeX note at `notes/<record>/note.tex`.** No note, no merge.
The `notes/` tree and its template are not in the repository, so write the note in the shape this
section describes and create the directory in your PR; the requirement is the note, not the
template.

**Commit the compiled `note.pdf` next to `note.tex`.** This project commits note PDFs deliberately,
so that a reader on GitHub gets the mathematics by clicking one link, with no LaTeX install and no
CI artifact to hunt for, and so the scoreboard row can point straight at it. Compile before you
push and commit both files together, so the PDF in the tree is the PDF of the `.tex` beside it.

This is the one requirement that is not machine-checkable, and it is not negotiable. The scoreboard
is the publication of record for this project, which means the scoreboard has to carry what a paper
would have carried: *why* the bound moved, in human mathematical language, readable by someone who
does not read Lean. A frontier that only a kernel understands is not a contribution to
mathematics. The note is also how your work gets cited, and how a future survey paper (§6) gets
written without re-deriving everything from proof terms.

### Step 6 — the PR

The pull-request template is planned but not in the tree (see the note at the top); until it is,
state in the PR description: the category, the record checklist (frontier constant moved by at
least `1/100000`, `note.tex` and `note.pdf` committed, digests listed, asserts added), and the
AI-disclosure line.

---

## 4. Contribution categories

All six are named, first-class contributions. All six appear in the scoreboard's credit record.
**Records are the most visible category and not the most valuable one** — machinery and corrections
are what make future records possible, and the project's own history says so: several of the
sharpest results here came from formalizing existing literature and finding it wrong.

| Category | What it is | What review it needs |
| --- | --- | --- |
| **Record** | Moves the frontier constant. | Kernel check + axiom census + fingerprints, all automated; plus human review of the *statement shape* (is this the theorem it claims to be?), the obligations it carries, and the note. Two maintainer approvals — one of them a definitional-kernel reviewer — per §1, layer 3. |
| **Machinery** | New reusable theory: a generic theorem, a certificate schema and its soundness theorem, a probability/entropy bridge, a tensor-layer API. No frontier movement. | Full API review against `DESIGN.md` §"API principles": weakest hypotheses, semantic-theorem/certificate separation, stable naming, module docs, minimal imports, and a **tiny client** (§8). One maintainer approval, plus a reviewer familiar with the layer. |
| **Simplification** | Shortens, generalizes, or de-duplicates an existing proof without changing any statement. | *Statement fingerprints must be identical* — capture `#check @name` under `pp.numericTypes`/`pp.coercions.types` and `#print axioms name` before and after, and paste the empty diff into the PR. That evidence is stronger than a code diff and is what reviewers will ask for. Otherwise light review. |
| **Performance** | Reduces build time or peak memory: import splits, dependency cuts, sufficient statistics replacing payloads, sharding. Statement-preserving. | Same fingerprint requirement as simplification, plus a **measurement**: what you measured, how (`lean --profile` on the individual file, or peak RSS), and the before/after numbers. Wall-clock times printed by Lake are not proof profiles — several competing Lake jobs make a small module look slow. |
| **Correction** | Fixes an error: in this repository, or **in the literature**, found by formalizing it. | The highest-value category per unit of code and the one to treat most carefully. A literature correction needs a precise printed-page citation, a minimal Lean witness of the failure (typically: the published statement instantiated at a case where it is false), and an entry in `README.md` §"Corrections to the literature found by the formalization". If a correction invalidates a scoreboard row, say so explicitly in the PR title; the retraction procedure is planned for `GOVERNANCE.md` (see the note at the top). Retracting your own row is a contribution, and it is recorded as one. |
| **Barrier** | Lower bounds and impossibility results: what the current methods *cannot* do. Rank/border-rank lower bounds, the Alman–Vassilevska Williams program, universal-method barriers. | Ordinary machinery review, plus care that a barrier's scope is stated exactly — a barrier for one method class is not a barrier for another, and an over-broad barrier statement is worse than none. `LOWER_BOUNDS_ROADMAP.md` and `BARRIER_FRAMEWORK.md` are the inventories. |

Two notes on the boundary between categories. A PR that is *both* a record and machinery should be
split: land the machinery first, then the three-line record change on top. It reviews faster, and
the machinery survives even if the record is superseded next week. And a **failed attempt is a
contribution**: post what you tried and where it broke, as an issue or a note (§3, step 5), and it
is credited as such. Negative information is expensive to generate and this project would rather buy
it once.

---

## 5. AI policy

**This repository adopts Mathlib's AI policy verbatim by reference.** The policy is the **"Use of
AI"** section of the Mathlib contribution guide —
[leanprover-community.github.io/contribute/index.html](https://leanprover-community.github.io/contribute/index.html)
— which is where `mathlib4`'s own `.github/CONTRIBUTING.md` points. "Verbatim by reference" names a
fixed text, so it is pinned to a revision:

| The pin | |
| --- | --- |
| Source file | [`templates/contribute/index.md`](https://github.com/leanprover-community/leanprover-community.github.io/blob/lean4/templates/contribute/index.md), branch `lean4` |
| Pinned revision | [`dd3758e0764e924137d6ad5edbc0bf6a139e1984`](https://github.com/leanprover-community/leanprover-community.github.io/blob/dd3758e0764e924137d6ad5edbc0bf6a139e1984/templates/contribute/index.md) (2026-08-19) |
| Last change to the AI section itself | `3831eac8ed915f056596ccca5f71df74c32945cf`, "chore: reword AI policy for clarity" (#850, 2026-05-27) |

When Mathlib revises the policy, updating this pin is a documentation PR, and a substantive change
is a governance question (one of the change tiers planned for `GOVERNANCE.md`) rather than a
silent adoption.

The operative requirements, restated so nobody has to click through:

1. **Disclose the tools you used, in the PR description.** Which tool, and for what — proof search,
   drafting, refactoring, documentation, translation of a paper's argument, the optimizer that
   produced a certificate. A one-line disclosure is enough; see the template.
2. **Label substantially LLM-generated PRs** with the `LLM-generated` label.
   <!-- pending: label to be created on the repository at launch. -->
3. **You must understand and be able to defend every line you submit.** This is the load-bearing
   requirement. If a reviewer asks why a hypothesis is needed, "the model wrote it" is not an
   answer, and a PR that cannot be defended is closed regardless of whether it compiles. The kernel
   check establishes that the proof is correct; it does not establish that anyone understands it,
   and an unmaintainable green proof is a liability for the project.
4. **A quality bar, and it has teeth in the pinned text.** Mathlib's policy states that code
   written by an AI without the supervision of a subject expert falls well short of its standards,
   and that reviewers may summarily close a low-quality LLM-produced PR — especially one opened
   without any prior discussion of its merits. That is review economics, not squeamishness, and it
   applies here for the same reason: a PR that costs more to review than it contributes is a net
   loss however green its build. Discuss first (§7), and do the understanding work in item 3. Note
   what this is and is not: a **mergeability** rule, in layer 3's territory, never a validity rule —
   it cannot make a green entry invalid, and §1's promise that a correct entry cannot be blocked by
   taste is untouched.
5. **No LLM-written review comments.** Review is where humans are irreplaceable here. Use tools to
   *find* things to review; write the review yourself, in your own voice, and own it.

   **This is not in tension with the automated AI reviewer** in §1, layer 2, and the distinction is
   worth stating precisely because it looks like one. **We follow Mathlib's policy; the
   project-operated automated review gets a documented pass.** Mathlib's rule governs *contributor
   conduct*, and the harm it prevents is a false signal — a person passing generated prose off as
   their own human judgement. The layer-2 reviewer creates no such signal: it is a project-operated
   gate, it runs on every PR including maintainers', its output is labelled as machine output, it
   has no approval power, and it claims to be nobody's review. Machine findings are inputs to human
   review; they are not human review.

   The affirmative reason for the pass, and not just the absence of harm: **it reduces the human
   review burden.** Humans should not have to hand-write the comments a machine can make. Every
   bypass pattern the gate catches — a moved `#assert_axioms`, a reintroduced `sorry`, a disabled CI
   check — is a comment a human would otherwise have to write, on a PR where their attention is far
   better spent on statement shape and the note. Spending scarce human review on machine-findable
   defects is the failure mode this layer exists to prevent.

   **The contributor-conduct rule stands unchanged.** Nothing here licenses an LLM-written review
   comment from a contributor, or from a maintainer. Write your review yourself.

Nothing in this section is a validity rule. A proof found by a model and a proof found by hand are
the same proof to the kernel, and §1 is the reason we can say that without flinching.

**And a disclosure of our own, because it would be dishonest to demand one and not give one:** this
repository is *substantially AI-built*. A large fraction of its Lean source, its generated
certificate checkers, its scripts, and its documentation — including this file — was written by AI
agents working under human direction, with the human author reviewing, directing, and taking
responsibility. That is exactly why the trust architecture in §1 is built the way it is: the kernel
check, the enforcing axiom census, the static gates, and the "untrusted producer, proved checker"
boundary are the mechanisms that make an AI-built formalization *checkable* rather than
*believed*. We hold contributors to a policy we are ourselves subject to, and we think the
disclosure makes the project easier to trust, not harder.

---

## 6. Authorship and credit

The credit model is the **Polymath** model — a large, flat, open author set rather than a small one —
in the specific form the **Equational Theories Project** gave it, adapted to a running scoreboard.

**Per-record credit lives in the scoreboard row.** Every entry names its contributor(s). That row
is the citable unit of this project, permanently, including after the record is superseded — a
superseded record is still a result somebody proved, and the scoreboard keeps its history rather
than overwriting it. Machinery, simplification, performance, correction, and barrier contributions
are recorded the same way, against the artifact they produced.

**Any eventual survey or announcement paper** is authored by **all record-holders and all major
machinery contributors, listed alphabetically**, with a **CRediT-style contribution appendix**
saying who did what. Not by whoever writes the LaTeX. There is no invitation committee: if you hold
a scoreboard row or made a major machinery contribution, you are an author, and the appendix
records the specifics.

**"Major machinery contribution" is defined mechanically**, so that authorship is not a judgement
call. You made one if either holds:

- you **authored a module that a scoreboard entry's dependency cone reaches**, or
- you authored a **named reusable theorem cited by a record note**.

The scoreboard computes the first version of this list; a mechanical criterion is the whole point,
and disputes about it are disputes about a computation, not about merit. Neither test is affected by
whether the contribution is currently the frontier: a module a *superseded* row's cone reached still
counts, because the scoreboard keeps its history.

**Leaderboard validity is never contingent on authorship agreement.** This is a rule, not an
aspiration. A green, correctly shaped entry is valid the moment CI passes, and it stays valid
whatever anyone thinks about author lists, ordering, or who deserves what. Credit disputes are
resolved in the credit record and never by touching the scoreboard, reverting an entry, or holding a
merge hostage. If you find yourself in a credit dispute, raise it with the maintainers; the frontier
keeps moving meanwhile.

### AI contributions in the credit record

**Much of this repository was written by AI agents working under human direction**, and pretending
otherwise in an author list would be exactly the kind of quiet overstatement §1 exists to prevent.
So the credit record says so — in four specific, decided places.

**1. For formal authorship, AI systems are tools with operators, not authors.** An AI system is
never a named author of a paper from this project. It appears as a tool attributed to the human who
operated it: *"X, using Claude Code (model M)"*. Two reasons, and the first is decisive:

- **Venue and arXiv policies require human accountability.** An author is someone who can be held
  responsible for the content, respond to a referee, and stand behind the claim. A model cannot, and
  a submission that names one as an author is not submittable at the venues this work targets.
- **It matches the Equational Theories Project's practice**, which is the credit model this section
  is adapted from. The ETP paper
  ([arXiv:2512.07087](https://arxiv.org/abs/2512.07087)) lists only human authors, puts
  per-author attribution in an Appendix B "Author contributions" using the
  [CRediT](https://credit.niso.org/) categories, and gives the machine work its own §11 rather than
  a slot in the byline.

This is a rule about *formal authorship only*. It is not a claim that the AI contribution was small,
and the next three items exist precisely so that the tools-with-operators convention does not become
a way to under-report what happened.

**2. Any survey paper carries a dedicated "AI contributions" appendix section**, describing
**concretely** what the AI systems did — which systems, on which parts of the development, at what
scale, and, just as importantly, where they did *not* help. Not a boilerplate acknowledgement. The
model is again ETP's §11 "AI and Machine Learning contributions", which names the tools and the
specific jobs (LLM-written code for the project's user interfaces; GitHub Copilot autocompletion
while formalizing informal proofs in Lean; one ChatGPT session that guessed a complete rewriting
system for a particular law, which was then formally verified; a convolutional network that
predicted implication-graph edges) and then states plainly that on the hardest implications "LLMs
did not provide useful suggestions beyond what the human participants could already propose". That
last sentence is the part worth copying: an AI-contributions section that only reports successes is
not a record, it is marketing. Given how much of this repository is AI-built, this section will be
substantially longer than ETP's.

**3. Every scoreboard row carries an AI tag**, so the credit record is per-record rather than
per-project:

| Tag | When it applies |
| --- | --- |
| **AI-assisted** | AI tools contributed materially — proof search, drafting, refactoring, the optimizer that produced the certificate — while the mathematical substance was human-directed. |
| **AI-authored** | The entry is *substantially* AI-written. Same threshold as the `LLM-generated` PR label in §5, item 2. |
| *(no tag)* | Neither: no AI tool contributed materially. |

The tag is derived from the PR's tool-disclosure line (§5, item 1), which is why that line is
required on every PR. A tag is a description, never a discount: an **AI-authored** row is exactly as
valid as any other, because layer 1 decided that and §1 means it.

**4. The `Co-Authored-By:` commit trailer is the granular record.** The convention used throughout
this project's development — every commit an agent produced carries a trailer naming it, e.g.
`Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>` — is the finest-grained layer of the
credit record, and it is deliberately kept. Keep using it. `git log` then answers "which model
touched this proof" at commit resolution for every commit after the initial public snapshot, without
anybody having to reconstruct it later from a paper's appendix, and it is the raw material the
survey paper's AI-contributions section is written from.

**What none of this does is obscure the human accountability.** A human contributor stands behind
every entry, understands it, and can defend it (§5, item 3). That is the fixed point the whole
scheme is arranged around: full disclosure of the machine's role, undiluted human responsibility for
the claim.

If you do not want to be named — pseudonym, institution-only, nothing at all — say so in your PR and
that is respected in both the row and any paper.

---

## 7. Claiming work, and where to talk

**Discuss before claiming.** Especially for machinery: a five-minute conversation routinely saves a
week of work that duplicates or contradicts someone else's in-flight design.

**The discussion venue is [GitHub Discussions](../../discussions) on this repository** — not a Zulip
stream. The reason is that everything else about this project already lives on GitHub: the
scoreboard is a Lean file, the board of open work is the issue tracker, the referee is CI, and the
credit record is a merge commit. A separate chat instance would split the record in two and leave
half of it unsearchable from the half that decides anything. Suggested categories:

| Category | For |
| --- | --- |
| **Announcements** | New records, retractions, campaign starts and endings, governance changes. |
| **Ideas** | Routes, designs, and "has anyone tried" — the pre-claim conversation this section is about. |
| **Q&A** | Getting oriented, build problems, "why is this hypothesis here". Answers are searchable, which is the point. |
| **Record attempts** | In-flight attempts at the frontier, including the ones that fail. Post the obstruction; a failed attempt is a credited contribution (§4). |

A durable outcome does not stay in a thread: it goes into `DESIGN.md`, an issue, or a note.

**Then claim it on the issue tracker.** The board of open work lives in GitHub issues. To take an
item, comment `claim` on it; to release it, comment that you are releasing it, with whatever you
learned. Conventions:

- **Claim before you start**, not after you finish. An unclaimed issue is assumed to be unowned and
  someone else may pick it up.
- **Claims expire after 14 days of silence.** If an issue has been claimed and silent that long,
  anyone may ask on it, and then take it.
- **Release loudly.** "I tried X, it fails because Y" is worth more to the next person than silence,
  and it is a credited contribution (§4).
- **Prefer a new leaf module to refactoring a shared foundation** while other work is in flight.
  This is the single most effective habit for parallel work here; `DESIGN.md`
  §"Contribution workflow" has the rest.
- **When two claims need the same declaration**, agree on the smallest shared API first, in the
  issue. One person owns that declaration; the other consumes it after it builds.

<!-- pending: the ETP-style claim automation — a bot that reads `claim` comments, maintains the
     assignment state, and renders the live task board and scoreboard — is the intended mechanism
     and is to be wired after launch. Until it is, claims are manual comments and a maintainer keeps
     the issue list tidy. Nothing about the trust contract depends on the automation. -->

**The issue tracker is kept stocked with small, self-contained tasks on purpose.** A campaign that
offers only its hardest open problem gets no contributors. If you lead a campaign, keeping a supply
of claimable small tasks is part of the job; if you are a newcomer and cannot find one, that is a
bug — say so in an issue and it will be fixed.

**Good first contributions**, if you want a concrete starting point: a tiny client for an existing
semantic operation (§8), a module-documentation improvement on a file whose overview is thin, a
simplification with identical fingerprints, or paying down one entry of a grandfather list under
`scripts/` (a file missing its copyright header, say).

---

## 8. Style, in the small

`DESIGN.md` is normative and this is the short version. Five rules that reviewers will actually
raise:

1. **Module docs are CI-enforced.** Every hand-written Lean file begins with a `/-! ... -/` module
   overview — what it defines, the principal results, where it sits in the layering, the certificate
   or proof strategy when it is not obvious, and the non-goals it leaves to a later module.
   `scripts/check_module_docs.sh` fails the build without one. Every public theorem gets a doc
   comment with a human-readable statement; a substantial theorem gets a `Proof sketch:` paragraph
   explaining the mathematics, *not* narrating tactic calls. Comments must state relation
   direction — which tensor is the source, which is the target — and must distinguish a proved
   theorem from a conditional interface. **No comment may claim more than the declaration proves.**

2. **The tiny-client rule.** Every major semantic operation gets a deliberately tiny client:
   zeroing one term of a two-term tensor, multiplying rank-one tensors, summing one-dimensional
   tensors, a degree-one polynomial degeneration, `⟨1,1,1⟩`, small `CW_1`/`CW_2` instances. These
   catch relation-direction, degree-order, associator, and leg-permutation errors *before* they are
   buried inside a large proof. This is not busywork: it is the cheapest bug-finding mechanism in
   the repository. If you add machinery, add its tiny client in the same PR.

3. **Exact-rational numerics with directed rounding.** No floating point may reach a Lean statement.
   Floating-point or Python output may *generate* a certificate; Lean must then verify the
   certificate **and every rounding direction** before the result is called formalized. Use the
   project's directed logarithm enclosures (`Analysis/Log.lean`, `Analysis/LogConstants.lean`,
   `FastDyadicLog.lean`) rather than unfolding a new twenty-term `log 2` enclosure — factor a
   positive rational as `2^m · (1+x)/(1-x)` with small `x`, use only enough atanh terms to leave a
   documented rational margin, and keep the paper's rational endpoints in the client. Separate the
   symbolic entropy formula from its parameter specialization: prove `∑ᵢ Aᵢ log(N/Aᵢ)` once, then
   reduce natural-number weights in the client.

4. **Imports are narrow.** Import the narrowest module that provides what you need; every file must
   compile on its own; implementation files do not import umbrellas for convenience. Cycles between
   tensor algebra, matrix-multiplication theory, and examples are design errors, and the tensor
   boundary is gated by `scripts/check_tensor_boundary.sh` — its handful of pre-existing mixed-layer
   edges are explicitly grandfathered, so any *new* leak fails CI.

5. **Weakest hypotheses; semantic theorem separate from certificate.** Basic tensor algebra over a
   commutative semiring; rings/fields only where the proof needs them; `Fintype` and bases only in
   modules that need coordinates. Keep the semantic statement, the reusable certificate structure,
   and the concrete certificate instance as three separate things, so that optimizer data never
   becomes part of the foundational API.

Also, because it is coming: the reusable core is intended for upstreaming into
[CSLib](https://github.com/leanprover/cslib), so new files should already look like CSLib files —
Apache-2.0 copyright header with authors, a `/-! # Title -/` module docstring citing published
sources by `[BibKey]`, `Defs.lean`/`Basic.lean` splits for large topics,
Mathlib style, readable rather than golfed proofs, reuse before invention. `DESIGN.md`
§"CSLib integration target" has the details and the known non-conformances.

The license those headers point at is in the repository: [`LICENSE`](LICENSE), Apache-2.0.

---

## 9. Before you open the PR

```bash
for gate in scripts/check_*.sh scripts/trust_scan.sh; do bash "$gate" || echo "RED: $gate"; done
lake build AlgebraicComplexity AlgebraicComplexityClients MatrixMultiplication AxiomAudit Frontier
```

(`scripts/check_frontier_improvement.sh` takes a base ref and is the one gate in that glob you can
skip locally unless you are submitting a record; `scripts/check_declaration_collisions.sh` never
fails.)

And, if you touched generated data:

```bash
lake build AxiomAuditCertificate     # opt-in; covers the generated certificate
```

Then check the list in §3, step 6. If you are submitting a record: frontier constant moved by at
least `1/100000`, `note.tex` and `note.pdf` committed, digests listed, asserts added, AI disclosure
present.

Welcome. The frontier is a file, and it moves when you push.
