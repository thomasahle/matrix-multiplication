# Statement integrity

*This is the "Statement integrity" subsection of the trust-and-verification policy in
`DESIGN.md`, kept in its own file.*

A public leaderboard makes a new kind of mistake possible.  The tree already defends hard against
proving a theorem badly: `scripts/trust_scan.sh` rejects `sorry`/`admit`/`axiom` in committed
sources, and over 1900 `#assert_axioms` lines recompute the axiom cone of every literature-facing
theorem so that a `native_decide` or a project axiom fails the build.  None of that notices a
theorem whose **statement** has drifted.  A record can be weakened rather than mis-proved: a `<`
becomes a `≤`, `Field` becomes `Field` plus a characteristic assumption, a universe quantifier
disappears, or — the quiet one — the *definition the statement is phrased in terms of* is edited
underneath it, and `omega` no longer means what the leaderboard says it means.

Statement integrity is the machinery against that.  It has one anchor file and two enforcement
idioms.

## The anchor: `Frontier.lean`

`Frontier.lean` is the only file the public leaderboard cites.  It contains no mathematics.

* A `Prop`-valued **shape** per generality class, fixing once what a record in that class asserts.
  The primary class is

  ```lean
  def OmegaBound (c : ℚ) : Prop :=
    ∀ (K : Type u) [Field K], omega K < (c : ℝ)
  ```

  Universe-polymorphic and all-fields, because the tree's endpoints are.  The constant is an exact
  rational and never a `Real` literal: comparing records is the leaderboard's whole job, and `ℚ` is
  where `norm_num` decides `new < old` outright.
* `def frontierConstant : ℚ` — the current best constant.
* `theorem frontier : OmegaBound frontierConstant` — proved by an `exact`-application of a
  committed endpoint theorem plus the `ℚ → ℝ` cast, and nothing else.

Secondary classes (fixed characteristic, `CommRing` coefficients, rectangular `ω(1,1,κ)`) are
present only as commented templates.  A shape with no record is a claim about future work; it does
not belong in the anchor.

### Frontier eligibility

A declaration is frontier-eligible only if it is **unconditional**: no `Prop` hypothesis standing
in for an unproved input, no paper-specific assumption, no `variable` carrying a proof obligation.

This is not a formality.  The tree's sharpest exponent statements are *conditional* — for instance
`omega K < 2.36999` given a subexponential laser-volume sequence.  Those are real, valuable, and
recorded in the README's own tables with their hypotheses named; they are not leaderboard records,
and `OmegaBound` has no room to express them.  A conditional endpoint reaches the frontier exactly
when its last hypothesis is discharged, at which point it becomes an ordinary three-line record PR.

## Idiom 1: `rfl` route pins

When a theorem is *re-proved* through a new route while its statement must not move, pin the two
declarations against each other:

```lean
example : @omega_lt_of_cwPower_volumeSequence =
    @omega_lt_of_cwPower_volumeSequence_value := rfl
```

The content is in the type-checking, not the `rfl`: the equation is only well-formed if the two
declarations have the *same* statement, so the elaborator rejects any drift between the old route
and the new one.  This is the right tool when both sides exist as separate declarations — a bridge,
a delegation, a regression kept alongside a sharpening.

Its limit is exactly that: it needs two declarations.  An **in-place** retarget, where a theorem is
re-proved under its own name, leaves nothing to equate, and a same-file `example` restating the
theorem is self-referential noise.  For that case the tree's practice is an olean-level
`#check @name` / `#print axioms name` diff taken before and after, recorded in the commit message —
strictly stronger evidence, but evidence rather than an enforced gate.

## Idiom 2: frontier fingerprints

`#assert_statement_fingerprint`, in `AxiomAudit/StatementFingerprint.lean`, is the enforced gate for
the case a route pin cannot reach: nothing to compare against, and the thing that might move is not
the theorem but the vocabulary underneath it.

```
#assert_statement_fingerprint AlgebraicComplexity.omega "66a867ed9bd02dd6"
#assert_statement_fingerprint Frontier.OmegaBound      "0198dd02aaef14ad"
```

The command recomputes a structural digest of

* the declaration itself — its type always, and its **value** when it is a definition rather than a
  theorem; and
* the **transitive definitional closure** of every project-local constant reached that way, each
  hashed by the same rule,

and fails elaboration unless the digest equals the committed string.  `#statement_fingerprint <name>`
prints the current value, in the exact form the assert line expects, so a reviewed change can be
re-committed.

Two properties make it useful rather than merely noisy.

**It sees the vocabulary.**  The closure of `Frontier.OmegaBound` is 24 project constants: `omega`,
`matrixMultiplicationExponent`, `Growth.polynomialExponent`, `squareMatrixRankSequence`,
`Tensor.rank`, `Tensor.RankLE`, `Tensor.exists_rankLE`, `Tensor.pure`, `Tensor.Tensor3`,
`Tensor.CoordinateSpace`, `Tensor.Leg` and its constructors, `matrixMultiplication`, `mmTerm`,
`mmTermOfTriple`, `MMTriple`, `MMSpace`, `MMIndex`, `Growth.PolynomialBound`.  That is the entire
definitional spine of "the matrix-multiplication exponent is below `c`".  Editing any of it changes
the committed hash, whether or not `Frontier.lean` itself is touched.

**It does not see records, and it does not see proofs.**  A proof term never enters the digest, so
re-proving anything leaves every hash alone; and both pinned declarations are record-independent, so
adding a sharper record never touches a committed hash.  That is why the fingerprints are on the
*shapes* and not on `frontier` itself: the record's integrity is `#assert_axioms` plus the
strict-improvement CI gate, and the shapes' integrity is the hash.

### The boundary

Constants are classified by the root component of the module that declared them.  Project roots
(`AlgebraicComplexity`, `MatrixMultiplication`, `AxiomAudit`, `Frontier`, …) are **unfolded**.
The toolchain, Mathlib, and the other Lake dependencies are an **opaque boundary**: such a constant
enters the digest by name only.  A Mathlib refactor that preserves the names a statement mentions
therefore does not disturb a hash, while a rename does.

A constant from any *other* root is a hard error, naming the module and telling the reader which
list to extend.  The classification is deliberately total: silently treating an unrecognized root
as opaque is the one failure mode this command exists to prevent, so a new top-level library must
be classified before it can appear in an audited statement.

### What the digest ignores, on purpose

Binder names; universe *parameter* names (they are replaced by their index in the declaration's own
`levelParams`, so `u` and `u_1` agree); `Expr.mdata`; the `theorem`/`lemma` keyword; docstrings;
attributes; and every proof term.

### Documented limits

1. **Binder info is significant.**  Changing `[Field K]` to `(inst : Field K)` changes the hash even
   though the resulting `Prop` is the same up to unfolding.  False alarm by design: that edit
   changes how every client applies the statement.
2. **Definitional, not semantic.**  Replacing `omega K` by `matrixMultiplicationExponent K` — the
   same function, since `omega` is an `abbrev` for it — changes the hash.  The command detects
   drift; it does not decide equivalence.  In exchange it is cheap, total, and never wrong in the
   dangerous direction.
3. **Inductive fields.**  For an inductive type the digest covers its own type, its parameter and
   index counts, and its constructors' names and types (constructors are pushed onto the closure
   worklist).  It does not cover attributes such as `@[ext]`, nor projection reducibility.
4. **Macro-scoped auxiliary names.**  A project constant in the closure whose *name* carries hygiene
   information (`…_@._hyg.123`) is hashed as written, so it could in principle shift when unrelated
   declarations in the same file are reordered.  Top-level auxiliaries (`f.match_1`, `f._proof_2`)
   are not macro-scoped and none was observed in the frontier closure; a spurious mismatch of this
   kind is diagnosable by re-running `#statement_fingerprint`.
5. **Toolchain scope.**  The digest is FNV-1a over an encoding written out in
   `AxiomAudit/StatementFingerprint.lean`, not over Lean's internal `Expr.hash`, so it does not move
   with the compiler's hashing internals.  It can still move across a toolchain upgrade that changes
   how a statement *elaborates* — a changed instance path, a new coercion.  That is a review-worthy
   event, not noise, and `schemeTag` in the same module exists to force a deliberate mass
   recomputation if the encoding itself ever has to change.

### Verification of the mechanism

The command was checked to fail on perturbation and pass on the real tree, against the real tree's
oleans:

| Shape definition | Digest | Verdict |
| --- | --- | --- |
| `∀ (K : Type u) [Field K], omega K < (c : ℝ)` (the committed one) | `0198dd02aaef14ad` | passes |
| `… omega K ≤ (c : ℝ)` | `26022cac6d3b7d00` | fails |
| `… matrixMultiplicationExponent K < (c : ℝ)` (definitionally identical) | `10b32638b2d12622` | fails |
| `∀ (K : Type u) [CommRing K], …` | `7ced3c427cac54c7` | fails |
| `∀ (K : Type) [Field K], …` (universe-monomorphic) | `74e675554be33cc0` | fails |

In each perturbed case the *separate* `AlgebraicComplexity.omega` line still passed, so the digest
is local rather than a whole-environment checksum.

Three unit properties were checked on a minimal `base`/`shape`/`t` chain, where the perturbation is
invisible in the theorem's own type expression:

* changing the **value** of a definition two levels below the theorem changes the theorem's digest
  (`21b1e29123c64ebc` → `947cb88c278abd7c`) while the theorem's statement text is untouched;
* changing the shape changes the shape's and the theorem's digests but leaves the unrelated
  sibling's digest bit-identical;
* renaming a universe parameter and a binder changes nothing, and two genuinely different proofs of
  the same statement give the same digest.

Removing `Init` from `externalRoots` in a scratch copy made `Nat` unclassified and produced the
intended hard error rather than a silently weaker check.

## The record-PR protocol

A record PR is **three lines** in `Frontier.lean`:

1. add the `import` of the module holding the new endpoint,
2. change `frontierConstant`,
3. change the endpoint cited by `frontier`.

Nothing else may change.  In particular a record PR must not touch a shape, a fingerprint line, or
the proof structure of `frontier` beyond the cited name — and if it needs to, it is not a record PR
and should be reviewed as a change to the kernel.

What CI enforces on it:

* `lake build Frontier` — the record type-checks against the shape, `#assert_axioms` recomputes its
  axiom cone, and both `#assert_statement_fingerprint` lines still hold.
* `scripts/check_frontier_improvement.sh <base-sha>` — extracts `frontierConstant` from the base
  commit and from the PR, and, when they differ, synthesizes and compiles
  `example : (new : ℚ) < (old : ℚ) := by norm_num`.  A record cannot regress the leaderboard, and
  cannot pass by asserting an ordering in prose.

### `frontier-improvement` job spec

For the CI owner.  One job, no new dependencies; `<setup>` is the repo's existing Lean/Lake setup
and cache-restore steps.

```yaml
frontier-improvement:
  # A record claim is a claim about an ordering; make the compiler check it.
  if: github.event_name == 'pull_request'
  runs-on: ubuntu-latest
  steps:
    - uses: actions/checkout@v4
      with:
        fetch-depth: 0          # the base blob must be readable
    - <setup>
    - name: Frontier statement kernel
      run: lake build Frontier
    - name: Frontier record is a strict improvement
      run: scripts/check_frontier_improvement.sh "${{ github.event.pull_request.base.sha }}"
```

Notes for the CI owner:

* `lake build Frontier` should also run in the ordinary build job.  `Frontier` is its own
  `lean_lib` and is deliberately *not* in `defaultTargets` — it must stay a leaf that no library
  depends on — so a plain `lake build` will not notice if it bit-rots.
* The improvement gate is a no-op when `frontierConstant` is unchanged, so it is safe on every PR
  and does not need a path filter.
* `scripts/check_frontier_improvement.sh` exits 0 with a note when the base ref has no
  `Frontier.lean`, so it does not break on the branch that introduces the kernel.
* `CODEOWNERS` should list `Frontier.lean`, `AxiomAudit/StatementFingerprint.lean`, and this file:
  the record line is meant to be routine, but the shapes and the digest are not.

## README leaderboard rules

The README's leaderboard **cites `Frontier` declarations only** — `Frontier.frontier`,
`Frontier.frontierConstant`, `Frontier.frontierConstant_eq_decimal`.  It does not cite an endpoint
theorem directly.  Endpoint theorems are named in the README's `## Results` tables, which is a
different claim: those tables catalogue what is proved, with hypotheses, including conditional and
non-record results.  The leaderboard claims something narrower and stronger — *this is the current
record, unconditional, and here is the declaration that says so.*

Suggested README subsection:

```markdown
### Leaderboard rules

The leaderboard row cites `Frontier.frontier` in `Frontier.lean` and nothing else. A result reaches
it only if it is:

* **unconditional** — no `Prop` hypothesis standing in for an unproved input, no paper-specific
  assumption. Sharper *conditional* endpoints are catalogued in `## Results` above with their
  hypotheses named; they are not records;
* **committed** — a leaderboard may not cite what is not in the repository;
* an instance of a **declared generality class** in `Frontier.lean`, currently
  `∀ (K : Type u) [Field K], omega K < (c : ℚ)`;
* proved by `exact`-application of an endpoint theorem, with no new proof content in
  `Frontier.lean`.

An improvement is a three-line PR — import, `frontierConstant`, cited endpoint — and CI compiles
`example : (new : ℚ) < (old : ℚ) := by norm_num` against the base commit before it can merge. The
statement shapes and the definition of `omega` are pinned by
`#assert_statement_fingerprint`; see `docs/STATEMENT_INTEGRITY.md`.
```
