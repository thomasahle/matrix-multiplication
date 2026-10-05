/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainSharpDegree
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainCopyCount

set_option autoImplicit false

/-!
# The count side of the plain integration, joined at the seed

Layer 4 (`AlgebraicComplexity/Examples/`).  The plain route's count side is now two chains that
meet at exactly one point.  Upstream of the seed, this lane certifies the leg-fibre degree:
`exists_seed_dwz63PlainJointRetained_at_sharpDegree` produces a seed whose retained support is
large, with the degree taken to be the sharp `N_α' / N_X`.  Downstream of the seed, the count lane
turns a retention bound into a copy count: `dwz63_plainCopyCount_pow_six_fintype`.

`dwz63_exists_seed_plainCopyCount_at_sharpDegree` is the join: it produces a seed together with
the copy count `dwz63TrueCopyRate ^ (6 (n+1)) ≤ lossHash ^ 6 · (#retained) ^ 6` at that seed --- the
exact `hcount` shape `omega_lt_2374631_of_dwz63IsolatedSum` consumes, once `Iso` is instantiated at
the sixfold product the `sym₆` distribution produces.

Producing the seed *inside* is what makes the join possible: `hsharp` and the retention bound must
speak about the same seed, and the seed is existentially quantified in both.

## The one count-side input still open

`hbranch` is the marked-count estimate

`dwz63HashingBranch ^ (n+1) · 4 M² ≤ lossHash · 3 · #marked · #B`,

`[DuanWuZhou2022]`'s step (4) arithmetic.  It is *not* an in-flight lane result --- it is this
lane's remaining work, and it is provable from what is already green here: with
`marked = dwz63PlainMarginalWords K n t` one has `#marked = N_α'`, the modulus is `M ≍ 8 d` with
`d = N_α' / N_X` by `card_dwz63PlainMarginalWords_eq`, and Behrend gives `#B ≍ M / Behrend M`, so
the requirement reduces to `lossHash ≳ Stirling · Behrend`, both subexponential --- the second by
`subexponential_dwz63PlainLossHash`, the first by the committed
`structuralZeroMultinomialLoss_subexponential` through
`dwz63_exp_entropyX_pow_le_loss_mul_dwz63PlainLegCount`.  The `K` of `dwz63HashLossMultiplier` is
spent on the joint-versus-marginal gap and is not needed here, which is what leaves the Stirling
loss to `lossHash`.  It is stated as a hypothesis rather than proved so that the join is available
now and cannot be mistaken for finished.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

/-- **The seed, with its copy count, at the sharp degree.**

The `hXfiber` and `hYfiber` obligations are discharged internally at
`dwz63PlainSharpDegree K n t`; the caller owes only the modulus bound and the marked-count
estimate. -/
theorem dwz63_exists_seed_plainCopyCount_at_sharpDegree {R : Type v} [Field R] [Fintype R]
    [NeZero (2 : R)] (K : Type u) [CommRing K]
    (hinj : Function.Injective (cwSquareFieldValue (R := R))) {n t : ℕ}
    (hn : n + 1 = 100000000 * t)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hmodulus : 8 * dwz63PlainSharpDegree K n t ≤ Fintype.card R)
    {lossHash : ℝ} (hlossHash : 0 ≤ lossHash)
    (hbranch : dwz63HashingBranch ^ (n + 1) *
        (4 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ))) ≤
      lossHash * (3 * (markedWords.card : ℝ) * (B.card : ℝ))) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
        lossHash ^ 6 *
          ((Fintype.card
            (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) : ℝ) ^ 6) := by
  obtain ⟨seed, hseed⟩ :=
    exists_seed_dwz63PlainJointRetained_at_sharpDegree K hinj hn markedWords hmarked B hB hmodulus
  exact ⟨seed, dwz63_plainCopyCount_pow_six_fintype K hinj n t markedWords B seed hlossHash
    hseed hbranch⟩

end AlgebraicComplexity.Examples
