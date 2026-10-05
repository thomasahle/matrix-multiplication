/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOmegaBound
import AxiomAudit.Command
import AxiomAudit.StatementFingerprint

set_option autoImplicit false

/-!
# The frontier statement kernel

This module is the machine-checked core of the public leaderboard.  It carries **no mathematics**:
it is a *statement anchor*.

* One `Prop`-valued **shape** per generality class fixes, once, what a record in that class
  asserts.  A record is then a single application of an already-proved endpoint to that shape;
  there is nowhere for a record to quietly weaken its own statement.
* `frontierConstant` is the current best constant, as an exact rational.
* `frontier` is the one theorem the leaderboard cites.  Its proof is an `exact`-application of a
  committed endpoint theorem, and nothing else.  If a claimed improvement cannot be phrased that
  way, it is not yet a record.
* The two enforcement idioms sit at the bottom of the file: `#assert_axioms` on the record, and
  `#assert_statement_fingerprint` on the *shapes*.  Fingerprinting the shapes rather than the
  records is deliberate — see `docs/STATEMENT_INTEGRITY.md`.  It means a routine record PR never
  touches a committed hash, while no PR can redefine `omega`, or what "`ω < c` over every field"
  means, without a reviewer seeing a hash change.

## Eligibility

A declaration is frontier-eligible only if it is **unconditional**: no `Prop` hypothesis standing
in for an unproved input, no paper-specific assumption, no `variable` carrying a proof obligation.
The tree contains many sharper *conditional* endpoints (`omega K < 2.36999` given a subexponential
laser-volume sequence, for instance).  Those are real results and the README records them; they are
not frontier records, and `OmegaBound` has no room to express them, which is the point.

## Provenance of the record

`frontier` cites `AlgebraicComplexity.Examples.omega_lt_2374631`
(`ω < 2.374631 = 2374631/1000000`, [duan2023faster], Section 6.3): the sharpest bound in the tree
that is simultaneously unconditional, all-fields, **committed**, and covered by an enforcing axiom audit
(`AxiomAudit/DuanWuZhouLevelTwoOmegaBound.lean`).  The published second-power example is at
`papers/sources/2210.10173/global_value.tex:332-378`, with its bound stated at line 352.
This is not that paper's higher-power headline bound.

The inaugural record was the first-power bound `ω < 2.3872 = 1492/625`
(`coppersmithWinograd_firstPower_omega_lt`, [CW90, §7]), which the kernel cited only because the
tensor-square modules were worktree-only when it landed.  The next record was the classical
tensor-square bound `ω < 2.375477 = 2375477/1000000`
(`coppersmithWinograd_square_omega_lt_2375477`, [CW90, §§7--8]).  Both earlier bounds remain
in the library as unconditional regression theorems.
-/

namespace Frontier

open AlgebraicComplexity

universe u

/-! ## Statement shapes -/

/-- **Primary generality class.**  `OmegaBound c` says that the matrix-multiplication exponent is
strictly below `c` over *every* field, in every universe.

The constant is an exact rational, never a `Real` literal: a leaderboard has to compare records,
and `ℚ` is where `norm_num` can decide `new < old` outright. -/
def OmegaBound (c : ℚ) : Prop :=
  ∀ (K : Type u) [Field K], omega K < (c : ℝ)

/-! ### Secondary generality classes

Templates only.  A class is added here when, and only when, an unconditional committed endpoint
actually inhabits it — a shape with no record is a claim about future work, and this file is not
the place for one.

```text
/-- Records that hold only in a fixed characteristic. -/
def OmegaBoundCharP (p : ℕ) (c : ℚ) : Prop :=
  ∀ (K : Type u) [Field K] [CharP K p], omega K < (c : ℝ)

/-- Records that need no inverses: strictly more general than `OmegaBound`. -/
def OmegaBoundCommRing (c : ℚ) : Prop :=
  ∀ (K : Type u) [CommRing K], omega K < (c : ℝ)

/-- Rectangular records: `ω(1, 1, κ) < c`. Two constants, so improvement is a partial order and
the leaderboard needs one row per pinned `κ`. -/
def RectangularOmegaBound (κ c : ℚ) : Prop :=
  ∀ (K : Type u) [Field K], rectangularOmega K (κ : ℝ) < (c : ℝ)
```
-/

/-! ## The record -/

/-- The current frontier constant: `2.374631`, exactly. -/
def frontierConstant : ℚ := 2374631 / 1000000

/-- Minimum improvement a record claim must show: `new + recordDelta ≤ old`, exactly, over `ℚ`.

Without a floor, the cheapest route onto the leaderboard is to run an existing numerical search a
little longer and shave a final digit — which moves the printed constant with no new mathematics
and costs a full record review.  `CONTRIBUTING.md` §3 states the rule and its companion, canonical
tightness: an entry should state the tightest constant its certificate proves at the submitted
parameters, since δ alone would otherwise reward withholding digits.  Genuine sub-δ improvements
remain welcome — batched, or as a non-record pull request that tightens an existing entry.

`scripts/check_frontier_improvement.sh` reads this definition rather than carrying its own copy of
the number; two literals for one rule is how they drift. -/
def recordDelta : ℚ := 1 / 100000

/-- **The frontier record.**  Over every field, `omega < 2.374631`.

Statement anchor only: the entire content is
`AlgebraicComplexity.Examples.omega_lt_2374631`, plus the
rational-to-real cast that lets the leaderboard compare constants in `ℚ`. -/
theorem frontier : OmegaBound frontierConstant := by
  intro K _
  have hcast : ((frontierConstant : ℚ) : ℝ) = (2374631 / 1000000 : ℝ) := by
    norm_num [frontierConstant]
  rw [hcast]
  exact Examples.omega_lt_2374631 K

/-- The frontier constant in decimal, for the README leaderboard row. -/
theorem frontierConstant_eq_decimal : frontierConstant = 2.374631 := by
  norm_num [frontierConstant]

end Frontier

/-! ## Enforcement

Two idioms, deliberately different in what they are sensitive to.

`#assert_axioms` recomputes the axiom cone: a record proved with `sorry`, `native_decide`, or a
project axiom fails the build here rather than in review.

`#assert_statement_fingerprint` recomputes a structural digest of a declaration's statement
*together with the transitive definitional closure it is phrased in terms of*.  The two lines
below pin, in order: what `omega` is, all the way down; and what the primary generality class
asserts.  Neither depends on the current record's value, so a record PR leaves both alone.

Recompute a line after a reviewed change with `#statement_fingerprint <name>`, and record in the
commit message why the statement moved.
-/

#assert_axioms Frontier.frontier
#assert_axioms Frontier.frontierConstant_eq_decimal

-- The definition of `omega` itself: 23 project constants, from `matrixMultiplicationExponent`
-- and `Growth.polynomialExponent` down through `Tensor.rank`, `matrixMultiplication`, and the
-- `MMIndex`/`Leg` index types.  Nothing in that spine can move unnoticed.
#assert_statement_fingerprint AlgebraicComplexity.omega "66a867ed9bd02dd6"
-- The primary generality class: the same 23 constants plus `omega`, with the quantifier
-- structure, the `Field` instance binder, and the `ℚ → ℝ` cast.
#assert_statement_fingerprint Frontier.OmegaBound "0198dd02aaef14ad"
