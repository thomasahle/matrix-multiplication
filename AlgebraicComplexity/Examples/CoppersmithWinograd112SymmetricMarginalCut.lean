/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricTypedCut
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLeafTauWeight
import AlgebraicComplexity.MatrixMultiplication.CyclicTypedLeafMarginal
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafMarginalReindex

set_option autoImplicit false

/-!
# The three-marginal cut of the `112` value certificate refines the leaf's `Z`-typed cut

Layer 4 (`AlgebraicComplexity/Examples/`).

## The paper step

`[DuanWuZhou2022]` arXiv:2210.10173, `second_power_appendix.tex:47` (proof of
`lem:non-rot-values` (d)): "*`\T` is a subtensor of `T_{1,1,2}^{⊗m}[α̃_Z^{(1,1,2)}]`; it can be
obtained by zeroing out X and Y-blocks from `T_{1,1,2}^{⊗m}[α̃_Z^{(1,1,2)}]`*".  The same
condition appears as compatibility in `def:complv2` (`second_power.tex:174-181`): a level-1
`Z`-block is compatible with a level-2 triple when its split over `S_{1,1,2}` is `α̃_A`
(`eq:tilde_A`, `second_power.tex:157-160`).  In the committed formalization the paper's `\T` is the
certificate's three-marginal cut `cw112SymmetricKeepMarginal`, and `T_{1,1,2}^{⊗m}[α̃_Z]` is the
leaf's `Z`-typed cut; this module proves the inclusion the paper asserts.

The `Z`-marginal `α̃_Z^{(1,1,2)}` is the `b`-split of `global_value.tex:341-348`:
`α̃_{1,1,2}(0) = α̃_{1,1,2}(2) = b`, `α̃_{1,1,2}(1) = 1-2b`, at that section's table value
`b = 0.00021015`.  The repository stores it twice, and the whole content of the numeric lemma
below is that the two agree: as `dwz63AlphaTilde 6` at mass `2·10^8`
(`42030, 199915940, 42030`), and as the `112` value certificate's own `(L,L,G,G)` profile at
`dwz112L = 4203`, `dwz112G = 9995797`, whose docstring records `b = 21015/10^8 = L/(2(L+G))`.

## What is paper and what is bridge

The inclusion is the paper step.  The `mass^2` factors and the source relabelling are Lean
bookkeeping (`CyclicTypedLeafMarginal`, `RationalTypedLeafMarginalReindex`): the paper normalizes
its distributions, so neither appears there.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `second_power_appendix.tex:44-50`, `second_power.tex:157-181`
(`eq:tilde_A`, `def:complv2`), `global_value.tex:341-348`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## The `Z` marginal of the primitive `112` typed leaf -/

/-- **The `Z` marginal of the `(L,L,G,G)` leaf is `(L, L, 2G)`.**  The two diagonal `112`
addresses carry the two corners and the two cross addresses both carry the grid, so the grid
collects `G + G`.  This is the integral form of `global_value.tex:341`'s
`(b, 1-2b, b)` at `b = L / (2(L+G))`. -/
theorem cw112BaseLeaf_marginalProfile_Z
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) (b : CW112ZBlock) :
    (cw112RationalTypedLeaf q L G hq hL hG).marginalProfile Leg.Z b =
      match b with
      | CW112ZBlock.firstCorner => L
      | CW112ZBlock.secondCorner => L
      | CW112ZBlock.grid => 2 * G := by
  classical
  unfold RationalTypedLeaf.marginalProfile
  rw [WordType.mappedType_eq_sum_ite, sum_cw112BlockSupportSubtype]
  cases b <;>
    simp [cw112RationalTypedLeaf, cw112IntegralProfile, cw112NaturalType,
      cw112DiagonalFirstS, cw112DiagonalSecondS, cw112CrossFirstS, cw112CrossSecondS,
      cw112DiagonalFirstAddress, cw112DiagonalSecondAddress,
      cw112CrossFirstAddress, cw112CrossSecondAddress, cw112BlockAddress, two_mul]

/-! ## The pushed `alphatilde` row -/

/-- **The `(1,1,2)` `alphatilde` row, pushed along the block dictionary, is
`(42030, 42030, 199915940)`** on `firstCorner`, `secondCorner`, `grid`.

This is `global_value.tex:341-348`'s `2·10^8 · (b, b, 1-2b)` at the table's `b = 0.00021015`.
The fibre sum collapses by image 127's `cw112RawDict_mappedType_apply`, since the row vanishes off
the `(1,1,2)` cell. -/
theorem dwz63_pushedAlphaTildeSix_eq (b : CW112ZBlock) :
    WordType.mappedType (cw112RawDict Leg.Z) (dwz63AlphaTilde 6) b =
      match b with
      | CW112ZBlock.firstCorner => 42030
      | CW112ZBlock.secondCorner => 42030
      | CW112ZBlock.grid => 199915940 := by
  rw [cw112RawDict_mappedType_apply _ dwz63_alphaTildeSix_eq_zero_of_not_cell]
  cases b <;> rfl

/-! ## The two stored copies of the `b`-split agree -/

/-- **The certificate's `Z` marginal and the leaf's `alphatilde` row are the same split**, once the
periods are reconciled at `j = 4·10^13 · k`.

Both sides are profiles on the three `112` `Z` blocks; the left is the value certificate's own
`(L, L, 2G)` scaled by the two masses summed out of the three-orientation product, the right is
`dwz63AlphaTilde 6` pushed along the dictionary and scaled by `j`.  At the committed
`dwz112L = 4203`, `dwz112G = 9995797` --- i.e. `2(L+G) = 2·10^7` --- the identity is
`(4203, 4203, 19991594) · 4·10^14 = (42030, 42030, 199915940) · 4·10^13`. -/
theorem dwz112_marginal_projZ_eq_pushedAlphaTilde (q : ℕ) (hq : 0 < q) (k : ℕ)
    (b : CW112ZBlock) :
    (cw112RationalTypedLeaf q dwz112L dwz112G hq dwz112L_pos dwz112G_pos).marginalProfile
          Leg.Z b * (2 * (dwz112L + dwz112G)) ^ 2 * k =
      WordType.mappedType (cw112RawDict Leg.Z) (dwz63AlphaTilde 6) b * (40000000000000 * k) := by
  rw [cw112BaseLeaf_marginalProfile_Z, dwz63_pushedAlphaTildeSix_eq]
  cases b <;> simp only [dwz112L, dwz112G] <;> ring

/-! ## Reading the transposed symmetric word letterwise -/

/-- **Image 140's label transpose, read at every position.**  A word of triples is, position by
position, the triple of the three component words' letters.  Two applications of the committed
`positiveWordEquiv_positiveWordProdEquiv`.

INTEGRATION WINDOW: this belongs beside `PartitionedTensor.symThreeWordEquiv` in layer 3; it is
here only because that module is already an accepted image and this lane does not edit accepted
images. -/
theorem dwz63_positiveWordEquiv_symThreeWordEquiv
    {A : Leg → Type} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (n : ℕ) (c : Leg)
    (p : ProductBlockIndex (ProductBlockIndex (fun c ↦ PositiveWord (A c) n)
      (PermutedBlockIndex cycle (fun c ↦ PositiveWord (A c) n)))
      (PermutedBlockIndex cycle.symm (fun c ↦ PositiveWord (A c) n)) c) :
    positiveWordEquiv _ n (PartitionedTensor.symThreeWordEquiv (A := A) n c p) =
      fun i ↦ ((positiveWordEquiv (A c) n p.1.1 i,
          positiveWordEquiv (A (cycle.symm c)) n p.1.2 i),
        positiveWordEquiv (A (cycle.symm.symm c)) n p.2 i) := by
  show positiveWordEquiv _ n
      (positiveWordProdEquiv (A c × A (cycle.symm c)) (A (cycle.symm.symm c)) n
        (positiveWordProdEquiv (A c) (A (cycle.symm c)) n (p.1.1, p.1.2), p.2)) = _
  rw [positiveWordEquiv_positiveWordProdEquiv]
  funext i
  rw [positiveWordEquiv_positiveWordProdEquiv]

/-- The same reading from the other side: a symmetric word is, position by position, the triple
of the letters of the three components its transpose names. -/
theorem dwz63_positiveWordEquiv_symThreeWordEquiv_symm
    {A : Leg → Type} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (n : ℕ) (c : Leg)
    (v : PositiveWord (ProductBlockIndex (ProductBlockIndex A (PermutedBlockIndex cycle A))
      (PermutedBlockIndex cycle.symm A) c) n) :
    positiveWordEquiv _ n v =
      fun i ↦
        ((positiveWordEquiv (A c) n
            ((PartitionedTensor.symThreeWordEquiv (A := A) n c).symm v).1.1 i,
          positiveWordEquiv (A (cycle.symm c)) n
            ((PartitionedTensor.symThreeWordEquiv (A := A) n c).symm v).1.2 i),
        positiveWordEquiv (A (cycle.symm.symm c)) n
          ((PartitionedTensor.symThreeWordEquiv (A := A) n c).symm v).2 i) := by
  conv_lhs => rw [← Equiv.apply_symm_apply (PartitionedTensor.symThreeWordEquiv (A := A) n c) v]
  rw [dwz63_positiveWordEquiv_symThreeWordEquiv]

/-! ## The `Z` component of the certificate's marginal -/

/-- **Each component of the certificate's leg marginal, projected to the `Z` block, is the
primitive leaf's `Z` marginal scaled by the two summed-out masses.**  Image 142's bridge composed
with the source relabelling. -/
theorem cw112SymmetricLeaf_marginalProfile_projZ
    (K : Type u) [CommRing K] (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (WordType.mappedType (fun t : CyclicTypedLeafCoordinate CW112Block Leg.Z ↦ t.1.1)
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).marginalProfile Leg.Z) =
      fun a ↦ (cw112RationalTypedLeaf q L G hq hL hG).marginalProfile Leg.Z a *
        (2 * (L + G)) ^ 2) ∧
    (WordType.mappedType (fun t : CyclicTypedLeafCoordinate CW112Block Leg.X ↦ t.1.2)
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).marginalProfile Leg.X) =
      fun a ↦ (cw112RationalTypedLeaf q L G hq hL hG).marginalProfile Leg.Z a *
        (2 * (L + G)) ^ 2) ∧
    (WordType.mappedType (fun t : CyclicTypedLeafCoordinate CW112Block Leg.Y ↦ t.2)
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).marginalProfile Leg.Y) =
      fun a ↦ (cw112RationalTypedLeaf q L G hq hL hG).marginalProfile Leg.Z a *
        (2 * (L + G)) ^ 2) := by
  have hmass : (cw112RationalTypedLeaf q L G hq hL hG).profile.mass = 2 * (L + G) :=
    cw112IntegralProfile_mass L G hL hG
  have hre : ∀ c : Leg,
      (cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).marginalProfile c =
        ((cw112RationalTypedLeaf q L G hq hL hG).cyclicProduct).marginalProfile c := by
    intro c
    exact RationalTypedLeaf.marginalProfile_reindex _ _ c
  refine ⟨?_, ?_, ?_⟩
  · rw [hre Leg.Z, RationalTypedLeaf.marginalProfile_cyclicProduct_fst_fst, hmass]
  · rw [hre Leg.X, RationalTypedLeaf.marginalProfile_cyclicProduct_fst_snd, hmass]
    rfl
  · rw [hre Leg.Y, RationalTypedLeaf.marginalProfile_cyclicProduct_snd, hmass]
    rfl

/-! ## Remaining: the inclusion itself

`cw112SymmetricKeepMarginal_symThreeKeep` --- the paper's
`second_power_appendix.tex:47` inclusion, i.e. image 140's `himp` binder --- is assembled from
exactly the six results above and is the only step of this increment still open.  Its shape is
fixed: `cases c`, two vacuous `symThreeKeep` conjuncts by
`dwz63_keeps_constSeg_of_ne`, and for the surviving one
`dwz63_keeps_constSeg_iff` fed by `dwz63_positiveWordEquiv_symThreeWordEquiv_symm`,
`WordType.multiplicity_comp_eq_mappedType`, the certificate's `KeepsMarginal`,
`WordType.mappedType_proportionalCounts`, `cw112SymmetricLeaf_marginalProfile_projZ` and
`dwz112_marginal_projZ_eq_pushedAlphaTilde`.  The obstruction is purely syntactic: rewriting the
letterwise reading inside the composition `(fun t ↦ t.1.2) ∘ positiveWordEquiv _ r w` does not
match, because `CW112SymmetricBlock c` is a reducible abbreviation of the product block index the
helper is stated at, and `rw` keys on the head symbol.  The fix is to restate the helper directly
at `CW112SymmetricBlock` (or to phrase the component reading as an equation between the two
`positiveWordEquiv` applications rather than through `Function.comp`). -/

end AlgebraicComplexity.Examples
