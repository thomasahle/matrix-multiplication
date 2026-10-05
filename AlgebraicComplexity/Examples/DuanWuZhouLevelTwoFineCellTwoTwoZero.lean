/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellGeneral
import AlgebraicComplexity.Tensor.CoarsenedSupportPreimage
import AlgebraicComplexity.MatrixMultiplication.RestrictedSplittingValue

set_option autoImplicit false

/-!
# The `(2,2,0)` fine cell, exactly, through its coarse constituent

Layer 4 (`AlgebraicComplexity/Examples/`).  `(2,2,0)` is the one cell of `[duan2023faster]`
section 6.3 whose zero coordinate sits on the split leg `Z`, so
`Examples/DuanWuZhouLevelTwoFineCellGeneral.lean` excludes it structurally
(`hzero : zero ≠ Leg.Z`) and it is the one cell whose one-slice exponent is **not** constant on
the fibre: the three admissible `X` letters `(0,2)`, `(1,1)`, `(2,0)` carry `0`, `2`, `0` middle
digits.

That non-uniformity is why the counting route needs a pigeonhole here.  This module takes the
other route, which is exact.

## The split constraint on `(2,2,0)` is vacuous

Row `11` of `dwz63AlphaTilde` --- the `(2,2,0)` row; the cell order is
`(0,0,4) (0,1,3) (0,2,2) (0,3,1) (0,4,0) (1,0,3) (1,1,2) (1,2,1) (1,3,0) (2,0,2) (2,1,1) (2,2,0)
(3,0,1) (3,1,0) (4,0,0)`, so row `6` is `(1,1,2)` --- is the point mass `2 * 10 ^ 8` on the zero
pair.  Its coarse `Z` degree is `0`, and a fine letter of square degree zero *is* the zero pair
(`cwSquareBlockDegree_eq_zero_iff`).  So the type condition on `Z` says exactly what the coarse
target already says, and the localized power's support is precisely the **coarsening preimage** of
the singleton `{(2,2,0)^{n+1}}`.

Once that is known the whole fine cell is a coarse object, and the committed chain closes it with
no estimate anywhere:

* `Isomorphic.withSupport_of_reindex_refl` at `positivePower_coarsen_reindex` crosses the
  power/coarsening seam (`Tensor/CoarsenedSupportPreimage.lean`);
* `Isomorphic.coarsen_withSupport_preimage` identifies the coarse cut with the fine preimage cut
  --- **it is an isomorphism, so it runs in the direction needed here**, which the committed
  `Restricts` corollary `coarsen_withSupport_to_preimage` does not;
* `Restricts.partitionedConstituent` extracts the single supported coarse block;
* `positivePower_constituent_positiveSupportWordBlockAddress` and
  `PartitionedTensor.Isomorphic.positiveSupportWordTensor_const_power` turn the constant coarse
  word into `Tensor.power` of the coarse constituent;
* `dwz63_hasTauWeight_220` (`Examples/DuanWuZhouLevelTwoConstituentValues.lean`) and
  `HasTauWeight.power_succ` supply the value.

The non-uniform shared-leg merge that turns `(q ^ 2) ^ tau` into `(q ^ 2 + 2) ^ tau` is therefore
not redone at the fine level: it is already inside `cwSquareConstituent_220_restricts`, at one
position, where the three fine letters share their (trivial) `Z` block and fuse into
`<1, q ^ 2 + 2, 1>`.

## What this costs, against the counting route

Nothing.  The value is `exp ((n+1) * dwz63LogVal220)` for **every** `n`, with no cutoff and no
deficit --- in particular no `(Finset.range (n+2)).card` pigeonhole factor, which is what a
uniform sub-fibre of `ZeroCoordinateMerge.exists_uniform_fibre_mergedDimension_le` would have
cost.  The `eps`-shaved form `dwz63_exists_fineCellWeight_eleven` is supplied only so that the
fifteen regions can be quoted in one shape, matching
`dwz63_exists_fineCellWeight_logVal`; it is strictly weaker than the exact statement above.

The pigeonhole route's arithmetic input --- that `dwz63CellOnes Leg.Z` is even on this cell, so
the merge may be run at base `q ^ 2` with the halved exponent and loses only `n + 2` rather than
`2n + 3` --- is `Examples/DuanWuZhouLevelTwoFineCellTwoTwoZeroParity.lean`.  Nothing here uses it:
that module states the degree-two row of the middle-count table at a general zero leg (it applies
to the `(0,2,2)` and `(2,0,2)` frames as well) and stands on its own.

Primary source: `[duan2023faster]`, arXiv:2210.10173, section 6.3 (the level-two global-value
example), `papers/sources/2210.10173/global_value.tex:332-348`; the value
`V_tau(T_{2,2,0}) = (q^2 + 2)^tau` is `lem:non-rot-values` (c),
`papers/sources/2210.10173/second_power.tex:144-152` (line 150).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

variable (K : Type u) [CommRing K] (q : ℕ)

/-! ## The coarse `(2,2,0)` block is supported -/

/-- **`(2,2,0)` is a supported coarse square address.**  Witnessed by the fine letter with `X`
pair `(2,0)`, `Y` pair `(0,2)` and `Z` pair `(0,0)`, which is
`dwz63ZeroFineLetterAddress Leg.Z (0,2)`. -/
theorem dwz63_cwSquare220_mem_support :
    cwSquare220 ∈ (cwSquarePartitionedTensor K q).support := by
  classical
  rw [cwSquarePartitionedTensor, PartitionedTensor.coarsen_support]
  refine Finset.mem_image.mpr
    ⟨dwz63ZeroFineLetterAddress Leg.Z ((CWBlock.zero, CWBlock.last) : PositiveWord CWBlock 1),
      dwz63ZeroFineLetterAddress_mem K q Leg.Z _, ?_⟩
  funext c
  cases c <;> decide

/-- The coarse `(2,2,0)` block, as an element of the coarse square's support. -/
def dwz63SquareTwoTwoZero : (cwSquarePartitionedTensor K q).support :=
  ⟨cwSquare220, dwz63_cwSquare220_mem_support K q⟩

@[simp] theorem dwz63SquareTwoTwoZero_val :
    (dwz63SquareTwoTwoZero K q).1 = cwSquare220 := rfl

/-! ## A constant coarse word is the constant coarse target -/

/-- **Transposing a constant supported word gives constant leg words.**  The coarse-square
instance of a fact about `positiveSupportWordBlockAddress`; there is no generic form of it in the
tree, and `new files only` forbids adding one to the tracked `Tensor/IteratedProduct.lean`
(cleanup note for an integration window). -/
theorem dwz63_supportWordBlockAddress_const_square (n : ℕ)
    (s : (cwSquarePartitionedTensor K q).support) (c : Leg) :
    positiveSupportWordBlockAddress (cwSquarePartitionedTensor K q).support n
        (positiveWordConst s n) c = positiveWordConst (s.1 c) n := by
  refine (positiveWordEquiv (Fin 5) n).injective ?_
  funext i
  have h := congrFun
    (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
      (cwSquarePartitionedTensor K q).support n (positiveWordConst s n) c) i
  simp only [h, positiveWordEquiv_const]

/-- **The constant `(2,2,0)` coarse word is the cell's target.** -/
theorem dwz63_supportWordBlockAddress_squareTwoTwoZero_eq_target (n : ℕ) :
    positiveSupportWordBlockAddress (cwSquarePartitionedTensor K q).support n
        (positiveWordConst (dwz63SquareTwoTwoZero K q) n) = dwz63ZeroCellTarget Leg.Z 2 n := by
  funext c
  rw [dwz63_supportWordBlockAddress_const_square, dwz63SquareTwoTwoZero_val]
  cases c <;> exact congrArg (fun d ↦ positiveWordConst d n) (by decide)

/-- **The cell's target is a supported coarse word address.** -/
theorem dwz63_zeroCellTarget_mem_coarsen_support (n : ℕ) :
    dwz63ZeroCellTarget Leg.Z 2 n ∈
      ((((cwPartitionedTensor K q).positivePower 1).positivePower n).coarsen
        (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n)).support := by
  classical
  rw [← Tensor.Restricts.positivePower_coarsen_support_eq,
    ← dwz63_supportWordBlockAddress_squareTwoTwoZero_eq_target K q n]
  show positiveSupportWordBlockAddress (cwSquarePartitionedTensor K q).support n
      (positiveWordConst (dwz63SquareTwoTwoZero K q) n) ∈
    ((cwSquarePartitionedTensor K q).positivePower n).support
  rw [(cwSquarePartitionedTensor K q).positivePower_support_eq_image_positiveSupportWordBlockAddress
    n]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

/-! ## The split constraint on `Z` is vacuous -/

/-- **The `(2,2,0)` fine cell is exactly a coarsening preimage.**

The forward direction drops the type condition; the backward direction *recovers* it, because the
coarse target's `Z` word is constantly the degree-zero letter and only the zero pair has square
degree zero (`dwz63_zeroLegWord_eq_const`).  This is the precise sense in which the split
distribution of `(2,2,0)` prescribes nothing.

Proof sketch: extensionality on supports.  `dwz63_mem_cellPower_support_iff` reads cell membership
as a triple (ambient membership, coarsening equal to the target legwise, `Z`-type equal to `α`) and
`mem_coarseningPreimageSupport` reads preimage membership as the first two alone; forward is
projection.  Backward, the target's `Z` word is constantly the degree-zero letter, so
`dwz63_zeroLegWord_eq_const` forces the address's `Z` word to be the constant zero-pair word ---
degree zero pins the fine letter --- and `positiveWordEquiv_const` with `hα` gives its
multiplicity.  No representative is chosen and no inequality enters. -/
theorem dwz63_twoTwoZeroCell_support_eq_coarseningPreimage (n : ℕ)
    (α : PositiveWord CWBlock 1 → ℕ)
    (hα : α = WordType.multiplicity
      (fun _ : Fin (n + 1) ↦ (positiveWordConst CWBlock.zero 1 : PositiveWord CWBlock 1))) :
    (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α))
        (dwz63ZeroCellTarget Leg.Z 2 n)).support =
      coarseningPreimageSupport (((cwPartitionedTensor K q).positivePower 1).positivePower n)
        (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) {dwz63ZeroCellTarget Leg.Z 2 n} := by
  classical
  ext s
  rw [dwz63_mem_cellPower_support_iff, mem_coarseningPreimageSupport, Finset.mem_singleton]
  constructor
  · rintro ⟨hmem, hcoarse, -⟩
    exact ⟨hmem, funext hcoarse⟩
  · rintro ⟨hmem, hcoarse⟩
    have hcoarse' : ∀ c, positiveWordMap (cwSquareDegreeMap c) n (s c) =
        dwz63ZeroCellTarget Leg.Z 2 n c := fun c ↦ congrFun hcoarse c
    refine ⟨hmem, hcoarse', ?_⟩
    have hz : s Leg.Z = positiveWordConst (positiveWordConst CWBlock.zero 1) n :=
      dwz63_zeroLegWord_eq_const Leg.Z n (s Leg.Z) (hcoarse' Leg.Z)
    rw [hz, positiveWordEquiv_const, hα]

/-! ## The exact restriction onto the coarse constituent's power -/

/-- **The `(2,2,0)` fine cell restricts onto the `(n+1)`-th power of the coarse `(2,2,0)`
constituent.**  Exact, with no representative selection and no estimate.

Proof sketch: rewrite the cell as the ambient power cut to the coarsening preimage of the singleton
target (`dwz63_twoTwoZeroCell_support_eq_coarseningPreimage` through `PartitionedTensor.ext`, only
the supports differing).  Cross the power/coarsening seam with
`Isomorphic.withSupport_of_reindex_refl` at `positivePower_coarsen_reindex`, then identify the
coarse cut with the fine preimage cut by `Isomorphic.coarsen_withSupport_preimage` --- an
*isomorphism*, so it runs in the direction needed here, its side condition being
`dwz63_zeroCellTarget_mem_coarsen_support`.  Composing the two and taking `symm.restricts` lands on
the coarse power cut to `{target}`, where `Restricts.partitionedConstituent` extracts the single
supported block; `dwz63_supportWordBlockAddress_squareTwoTwoZero_eq_target`,
`positivePower_constituent_positiveSupportWordBlockAddress` and
`PartitionedTensor.Isomorphic.positiveSupportWordTensor_const_power` then turn it into
`Tensor.power` of the coarse `(2,2,0)` constituent. -/
theorem dwz63_twoTwoZeroCell_restricts_power (n : ℕ) (α : PositiveWord CWBlock 1 → ℕ)
    (hα : α = WordType.multiplicity
      (fun _ : Fin (n + 1) ↦ (positiveWordConst CWBlock.zero 1 : PositiveWord CWBlock 1))) :
    Restricts
      ((((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α))
        (dwz63ZeroCellTarget Leg.Z 2 n)).realize)
      (Tensor.power ((cwSquarePartitionedTensor K q).constituent cwSquare220) (n + 1)) := by
  classical
  set target := dwz63ZeroCellTarget Leg.Z 2 n with htargetDef
  have hS : ({target} : Finset (BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))) ⊆
      ((((cwPartitionedTensor K q).positivePower 1).positivePower n).coarsen
        (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n)).support :=
    Finset.singleton_subset_iff.mpr (dwz63_zeroCellTarget_mem_coarsen_support K q n)
  have hcelleq :
      (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α)) target) =
      (((cwPartitionedTensor K q).positivePower 1).positivePower n).withSupport
        (coarseningPreimageSupport (((cwPartitionedTensor K q).positivePower 1).positivePower n)
          (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) {target}) :=
    PartitionedTensor.ext
      (dwz63_twoTwoZeroCell_support_eq_coarseningPreimage K q n α hα) rfl
  rw [hcelleq]
  have hiso1 := Isomorphic.withSupport_of_reindex_refl
    (((cwPartitionedTensor K q).positivePower 1).coarsenedPositivePower cwSquareDegreeMap n)
    (PartitionedTensor.positivePower_coarsen_reindex
      ((cwPartitionedTensor K q).positivePower 1) cwSquareDegreeMap n)
    ({target} : Finset (BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n)))
  have hiso2 := Isomorphic.coarsen_withSupport_preimage
    (((cwPartitionedTensor K q).positivePower 1).positivePower n)
    (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n)
    ({target} : Finset (BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))) hS
  refine ((hiso1.trans hiso2).symm.restricts).trans ?_
  refine (Tensor.Restricts.partitionedConstituent _ target (by simp)).trans ?_
  have hconst : ((cwSquarePartitionedTensor K q).positivePower n).constituent
      (positiveSupportWordBlockAddress (cwSquarePartitionedTensor K q).support n
        (positiveWordConst (dwz63SquareTwoTwoZero K q) n)) =
      PartitionedTensor.positiveSupportWordTensor (cwSquarePartitionedTensor K q) n
        (positiveWordConst (dwz63SquareTwoTwoZero K q) n) :=
    PartitionedTensor.positivePower_constituent_positiveSupportWordBlockAddress
      (cwSquarePartitionedTensor K q) n (positiveWordConst (dwz63SquareTwoTwoZero K q) n)
  rw [htargetDef, ← dwz63_supportWordBlockAddress_squareTwoTwoZero_eq_target K q n]
  exact ((Tensor.Isomorphic.of_eq hconst).trans
    (PartitionedTensor.Isomorphic.positiveSupportWordTensor_const_power
      (cwSquarePartitionedTensor K q) (dwz63SquareTwoTwoZero K q) n)).restricts

/-! ## Row eleven is the point mass on the zero pair -/

/-- Row `11` of `dwz63AlphaTilde` on the zero pair. -/
theorem dwz63_alphaTilde_eleven_apply_zeroPair :
    dwz63AlphaTilde 11 (positiveWordConst CWBlock.zero 1) = 200000000 := rfl

/-- Row `11` of `dwz63AlphaTilde` vanishes off the zero pair. -/
theorem dwz63_alphaTilde_eleven_eq_zero_of_ne (p : PositiveWord CWBlock 1)
    (hp : p ≠ positiveWordConst CWBlock.zero 1) : dwz63AlphaTilde 11 p = 0 := by
  obtain ⟨a, b⟩ := p
  rw [show (positiveWordConst CWBlock.zero 1 : PositiveWord CWBlock 1) =
    ((CWBlock.zero, CWBlock.zero) : PositiveWord CWBlock 1) from rfl] at hp
  cases a <;> cases b <;> first | rfl | exact absurd rfl hp

/-- **The `(2,2,0)` split profile at scale `j` is the type of the constant zero-pair word.**
This is the hypothesis `dwz63_twoTwoZeroCell_support_eq_coarseningPreimage` asks for, at the
profile the reference leaf actually carries. -/
theorem dwz63_proportionalCounts_alphaTilde_eleven (n j : ℕ) (hn : n + 1 = 200000000 * j) :
    WordType.proportionalCounts (dwz63AlphaTilde 11) j =
      WordType.multiplicity
        (fun _ : Fin (n + 1) ↦ (positiveWordConst CWBlock.zero 1 : PositiveWord CWBlock 1)) := by
  classical
  funext p
  rw [WordType.multiplicity_const, WordType.proportionalCounts]
  by_cases hp : p = positiveWordConst CWBlock.zero 1
  · rw [if_pos hp, hp, dwz63_alphaTilde_eleven_apply_zeroPair, hn]
  · rw [if_neg hp, dwz63_alphaTilde_eleven_eq_zero_of_ne p hp, Nat.zero_mul]

/-! ## The weight -/

/-- **The `(2,2,0)` fine cell attains `dwz63Val220` per letter, exactly, for every `n`.**

No cutoff, no deficit, no pigeonhole: the value is `exp ((n+1) * dwz63LogVal220)`, which is
`dwz63Val220 ^ (n+1) = 38 ^ (tau (n+1))` at `q = dwz63Q`.

Proof sketch: `HasTauWeight.of_restricts` at `dwz63_twoTwoZeroCell_restricts_power` moves the goal
to `Tensor.power` of the coarse `(2,2,0)` constituent, where the committed
`dwz63_hasTauWeight_220` (`Examples/DuanWuZhouLevelTwoConstituentValues.lean`) supplies the
one-letter weight `dwz63Val220` and `HasTauWeight.power_succ` raises it to the `(n+1)`-st power.
The only remaining step is the arithmetic identity
`dwz63Val220 ^ (n+1) = exp ((n+1) * dwz63LogVal220)`, by `Real.exp_nat_mul`.  The `(q^2 + 2)`
shared-leg merge is not redone here: it is already inside `cwSquareConstituent_220_restricts`. -/
theorem dwz63_hasTauWeight_fineCellTwoTwoZero (n : ℕ) (α : PositiveWord CWBlock 1 → ℕ)
    (hα : α = WordType.multiplicity
      (fun _ : Fin (n + 1) ↦ (positiveWordConst CWBlock.zero 1 : PositiveWord CWBlock 1))) :
    HasTauWeight K
      ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α))
        (dwz63ZeroCellTarget Leg.Z 2 n)).realize) dwz63Tau
      (Real.exp (((n : ℝ) + 1) * dwz63LogVal220)) := by
  refine HasTauWeight.of_restricts
    (dwz63_twoTwoZeroCell_restricts_power K dwz63Q n α hα) ?_
  have hpow := (dwz63_hasTauWeight_220 (K := K)).power_succ
    (le_of_lt (Real.exp_pos dwz63LogVal220)) n
  have hval : dwz63Val220 ^ (n + 1) = Real.exp (((n : ℝ) + 1) * dwz63LogVal220) := by
    rw [dwz63Val220, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  rwa [hval] at hpow

/-- **The region form.**  The same weight quoted in the shape
`dwz63_exists_fineCellWeight_logVal` (`Examples/DuanWuZhouLevelTwoFineCellRegional.lean`) produces
for the nine off-split cells, so that the fifteen regions of the leaf can be listed uniformly.
The cutoff is `0` and the `eps` is pure slack: the exact statement is
`dwz63_hasTauWeight_fineCellTwoTwoZero`. -/
theorem dwz63_exists_fineCellWeight_eleven (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ n : ℕ, n + 1 = 200000000 * j →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 11) j))
          (dwz63ZeroCellTarget Leg.Z 2 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * (j : ℝ) * (dwz63LogVal220 - ε))) := by
  refine ⟨0, fun j _ n hn ↦ ?_⟩
  refine (dwz63_hasTauWeight_fineCellTwoTwoZero K n _
    (dwz63_proportionalCounts_alphaTilde_eleven n j hn)).mono ?_
  refine Real.exp_le_exp.mpr ?_
  have hcast : ((n : ℝ) + 1) = (200000000 : ℝ) * (j : ℝ) := by
    have := congrArg (fun m : ℕ ↦ (m : ℝ)) hn
    push_cast at this
    linarith
  rw [hcast]
  nlinarith [Nat.cast_nonneg (α := ℝ) j, hε.le]

end AlgebraicComplexity.Examples
