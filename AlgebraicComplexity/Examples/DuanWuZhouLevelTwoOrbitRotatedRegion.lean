/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradPartitionRotationPower
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellOrbit
import AlgebraicComplexity.MatrixMultiplication.SymThreeCycleInvariance

set_option autoImplicit false

/-!
# The `(1,2,1)` and `(2,1,1)` orbit regions are rotations of a `(1,1,2)` region

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoFineCellOrbit.lean` carries
the three orbit regions of `[duan2023faster]`'s section 6.3 fine leaf in one family,
`dwz63OrbitRegion K q o t₀ n j`, all three cut on the `Z` leg by the row `alphatilde` of their own
component.  Row `6` is the `(1,1,2)` component, whose `Z` leg carries the coarse degree `2`; rows
`7` and `10` are `(1,2,1)` and `(2,1,1)`, whose degree-`2` leg is `Y` resp. `X` and whose `Z` leg
carries degree `1`.

Because of that, rows `7` and `10` cannot be block mapped legwise onto `cw112PartitionedTensor`:
the `112` partition has its three-block leg on `Z`.  This module removes the obstruction, once, by
rotating: **the `(1,2,1)` region rotated by `cycle` and the `(2,1,1)` region rotated by
`cycle.symm` are both `(1,1,2)` regions**, cut on the `X` resp. `Y` leg by the same degree-one row
`dwz63AlphaTilde 7 = dwz63AlphaTilde 10`.  Since `sym_3` is invariant under rotation
(`MatrixMultiplication/SymThreeCycleInvariance.lean`), the rotation is free at the `sym_3` level,
which is the only level at which `T_{1,1,2}` has a value at all.

The rotation of the ambient object is
`Examples/CoppersmithWinogradPartitionRotation.lean`'s
`cwSquareRawPower_reindexEquiv_permute_cycle`; what is added here is the identification of the
rotated *cut*.

## The paper step

`[duan2023faster]` arXiv:2210.10173, `second_power.tex:142-158` (`lem:non-rot-values`) together
with `:235` (`note:T112`): the level-two component `T_{1,1,2}` has no non-rotational value, so its
value is read on `sym_3`, and the paper imposes `α(1,1,2) = α(1,2,1) = α(2,1,1)` precisely
because the three components are the cyclic rotations of one tensor and share one `V^{(3)}`.  The
split used for rows `7` and `10` is the symmetric degree-one one, `global_value.tex:347`: *"For all
other components, we use the symmetric Z-marginal split distributions ... So the values of all
other components (including `(2,2,0)`, `(1,2,1)`, `(2,1,1)`) do not change"*; the committed table
row is `dwz63AlphaTilde 7 = dwz63AlphaTilde 10`, the mass-`2·10^8` profile
`(zero,middle) ↦ 10^8`, `(middle,zero) ↦ 10^8`.

The statements below are the Lean bridge for the paper's "by symmetry"; the paper states no
lemma of this shape.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, `[duan2023faster]`, `second_power.tex:142-158`, `:235`, `global_value.tex:341-348`
(especially `:347`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u w

/-! ## Two small pieces of general machinery

INTEGRATION WINDOW: `PartitionedTensor.select_congr` belongs beside `PartitionedTensor.select` in
`Tensor/PartitionedCore.lean`; it is here only because that module is a committed file this lane
does not edit. -/

/-- **Pointwise equivalent cut predicates cut the same certificate.** -/
theorem PartitionedTensor.select_congr {K : Type u} [CommSemiring K]
    {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    {V : ∀ c, A c → Type (max u w)}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (keep keep' : ∀ c, A c → Prop)
    [∀ c a, Decidable (keep c a)] [∀ c a, Decidable (keep' c a)]
    (h : ∀ c a, keep c a ↔ keep' c a) :
    P.select keep = P.select keep' := by
  classical
  apply Tensor.PartitionedTensor.ext
  · ext s
    rw [Tensor.PartitionedTensor.mem_select_support,
      Tensor.PartitionedTensor.mem_select_support]
    exact and_congr_right fun _ ↦ forall_congr' fun c ↦ h c (s c)
  · rfl

/-- On the constrained leg of a one-leg segmented restriction over a constant block family, the
keep predicate is the segmentwise type condition. -/
theorem dwz63_keeps_ofLeg_self {I : Type w} [DecidableEq I] {M n : ℕ}
    (c₀ : Leg) (β : Fin M → I → ℕ) (seg : Fin (n + 1) → Fin M)
    (word : PositiveWord I n) :
    (SegmentedSplitRestriction.ofLeg (A := fun _ : Leg ↦ I) c₀ β).Keeps n seg c₀ word ↔
      ∀ t : Fin M, segmentMultiplicity seg (positiveWordEquiv I n word) t = β t :=
  SegmentedSplitRestriction.keeps_iff_of_some
    (fun t ↦ SegmentedSplitRestriction.ofLeg_self (A := fun _ : Leg ↦ I) c₀ β t) word

/-- Off the constrained leg the same restriction keeps every word. -/
theorem dwz63_keeps_ofLeg_ne {I : Type w} [DecidableEq I] {M n : ℕ}
    {c₀ c : Leg} (hc : c₀ ≠ c) (β : Fin M → I → ℕ) (seg : Fin (n + 1) → Fin M)
    (word : PositiveWord I n) :
    (SegmentedSplitRestriction.ofLeg (A := fun _ : Leg ↦ I) c₀ β).Keeps n seg c word :=
  SegmentedSplitRestriction.keeps_of_all_none
    (fun t ↦ SegmentedSplitRestriction.ofLeg_of_ne (A := fun _ : Leg ↦ I) β hc t) word

/-! ## The rotated `(1,1,2)` region, cut on an arbitrary leg -/

variable (K : Type u) [CommRing K] (q : ℕ)

/-- **A `(1,1,2)`-target region of the raw CW square, cut on the leg `cut` by the symmetric
degree-one row `dwz63AlphaTilde 7`.**

At `cut = Leg.X` this is the `cycle` rotation of the `(1,2,1)` orbit region, and at `cut = Leg.Y`
the `cycle.symm` rotation of the `(2,1,1)` one. -/
noncomputable def dwz63SideOrbitRegion (cut : Leg) {M : ℕ} (t₀ : Fin M) (n j : ℕ) :=
  ((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
    cwSquareDegreeMap n M (fun _ ↦ t₀)
    (SegmentedSplitRestriction.ofLeg
      (A := fun _ : Leg ↦ PositiveWord CWBlock 1) cut
      (fun t ↦ if t = t₀ then
        WordType.proportionalCounts (dwz63AlphaTilde 7) j else 0))
    (dwz63OrbitTarget 0 n)

/-- The two rotations of the orbit rows share one `alphatilde` row: the `(1,2,1)` and `(2,1,1)`
rows of `global_value.tex:347`'s symmetric degree-one split are the same profile. -/
theorem dwz63AlphaTilde_ten_eq_seven : dwz63AlphaTilde 10 = dwz63AlphaTilde 7 := rfl

/-- The `(1,2,1)` coarse target, read one leg backwards, is the `(1,1,2)` target. -/
theorem dwz63OrbitTarget_one_cycle_symm (n : ℕ) (c : Leg) :
    dwz63OrbitTarget 1 n (cycle.symm c) = dwz63OrbitTarget 0 n c := by
  cases c <;> rfl

/-- The `(2,1,1)` coarse target, read one leg forwards, is the `(1,1,2)` target. -/
theorem dwz63OrbitTarget_two_cycle (n : ℕ) (c : Leg) :
    dwz63OrbitTarget 2 n (cycle c) = dwz63OrbitTarget 0 n c := by
  cases c <;> rfl

/-! ## The two rotations -/

/-- **The `(1,2,1)` orbit region, rotated by `cycle`, is the `(1,1,2)` region cut on `X`.** -/
theorem dwz63_isomorphic_permute_cycle_orbitRegion_one {M : ℕ} (t₀ : Fin M) (n j : ℕ) :
    Isomorphic (Tensor.permute cycle (dwz63OrbitRegion K q 1 t₀ n j).realize)
      (dwz63SideOrbitRegion K q Leg.X t₀ n j).realize := by
  classical
  refine (isomorphic_permute_cycle_rawSquarePower_select K q n
    (segmentedLocalizedKeep cwSquareDegreeMap (fun _ : Fin (n + 1) ↦ t₀)
      (SegmentedSplitRestriction.ofLeg
        (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
        (fun t ↦ if t = t₀ then
          WordType.proportionalCounts (dwz63AlphaTilde (dwz63OrbitRow 1)) j else 0))
      (dwz63OrbitTarget 1 n))).trans ?_
  refine Isomorphic.of_eq (congrArg Tensor.PartitionedTensor.realize ?_)
  refine PartitionedTensor.select_congr _ _ _ ?_
  intro c a
  show (positiveWordMap (cwSquareDegreeMap (cycle.symm c)) n a
        = dwz63OrbitTarget 1 n (cycle.symm c)
      ∧ (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
          (fun t ↦ if t = t₀ then
            WordType.proportionalCounts (dwz63AlphaTilde (dwz63OrbitRow 1)) j else 0)).Keeps
          n (fun _ ↦ t₀) (cycle.symm c) a)
    ↔ (positiveWordMap (cwSquareDegreeMap c) n a = dwz63OrbitTarget 0 n c
      ∧ (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.X
          (fun t ↦ if t = t₀ then
            WordType.proportionalCounts (dwz63AlphaTilde 7) j else 0)).Keeps
          n (fun _ ↦ t₀) c a)
  rw [dwz63OrbitTarget_one_cycle_symm]
  refine and_congr Iff.rfl ?_
  cases c
  · exact (dwz63_keeps_ofLeg_self Leg.Z _ _ a).trans
      (dwz63_keeps_ofLeg_self Leg.X _ _ a).symm
  · exact iff_of_true (dwz63_keeps_ofLeg_ne (by decide) _ _ a)
      (dwz63_keeps_ofLeg_ne (by decide) _ _ a)
  · exact iff_of_true (dwz63_keeps_ofLeg_ne (by decide) _ _ a)
      (dwz63_keeps_ofLeg_ne (by decide) _ _ a)

/-- **The `(2,1,1)` orbit region, rotated by `cycle.symm`, is the `(1,1,2)` region cut on `Y`.** -/
theorem dwz63_isomorphic_permute_cycleSymm_orbitRegion_two {M : ℕ} (t₀ : Fin M) (n j : ℕ) :
    Isomorphic (Tensor.permute cycle.symm (dwz63OrbitRegion K q 2 t₀ n j).realize)
      (dwz63SideOrbitRegion K q Leg.Y t₀ n j).realize := by
  classical
  refine (isomorphic_permute_cycleSymm_rawSquarePower_select K q n
    (segmentedLocalizedKeep cwSquareDegreeMap (fun _ : Fin (n + 1) ↦ t₀)
      (SegmentedSplitRestriction.ofLeg
        (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
        (fun t ↦ if t = t₀ then
          WordType.proportionalCounts (dwz63AlphaTilde (dwz63OrbitRow 2)) j else 0))
      (dwz63OrbitTarget 2 n))).trans ?_
  refine Isomorphic.of_eq (congrArg Tensor.PartitionedTensor.realize ?_)
  refine PartitionedTensor.select_congr _ _ _ ?_
  intro c a
  show (positiveWordMap (cwSquareDegreeMap (cycle c)) n a
        = dwz63OrbitTarget 2 n (cycle c)
      ∧ (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
          (fun t ↦ if t = t₀ then
            WordType.proportionalCounts (dwz63AlphaTilde (dwz63OrbitRow 2)) j else 0)).Keeps
          n (fun _ ↦ t₀) (cycle c) a)
    ↔ (positiveWordMap (cwSquareDegreeMap c) n a = dwz63OrbitTarget 0 n c
      ∧ (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Y
          (fun t ↦ if t = t₀ then
            WordType.proportionalCounts (dwz63AlphaTilde 7) j else 0)).Keeps
          n (fun _ ↦ t₀) c a)
  rw [dwz63OrbitTarget_two_cycle]
  refine and_congr Iff.rfl ?_
  cases c
  · exact iff_of_true (dwz63_keeps_ofLeg_ne (by decide) _ _ a)
      (dwz63_keeps_ofLeg_ne (by decide) _ _ a)
  · exact (dwz63_keeps_ofLeg_self Leg.Z _ _ a).trans
      (dwz63_keeps_ofLeg_self Leg.Y _ _ a).symm
  · exact iff_of_true (dwz63_keeps_ofLeg_ne (by decide) _ _ a)
      (dwz63_keeps_ofLeg_ne (by decide) _ _ a)

/-! ## `sym₃` of the two rotated rows -/

/-- **`sym₃` of the `(1,2,1)` orbit region is `sym₃` of the `X`-cut `(1,1,2)` region.** -/
theorem dwz63_isomorphic_symThree_orbitRegion_one {M : ℕ} (t₀ : Fin M) (n j : ℕ) :
    Isomorphic (symThree K (dwz63OrbitRegion K q 1 t₀ n j).realize)
      (symThree K (dwz63SideOrbitRegion K q Leg.X t₀ n j).realize) :=
  (Isomorphic.symThree_permute_cycle (K := K) (dwz63OrbitRegion K q 1 t₀ n j).realize).symm.trans
    (Isomorphic.symThree_congr (dwz63_isomorphic_permute_cycle_orbitRegion_one K q t₀ n j))

/-- **`sym₃` of the `(2,1,1)` orbit region is `sym₃` of the `Y`-cut `(1,1,2)` region.** -/
theorem dwz63_isomorphic_symThree_orbitRegion_two {M : ℕ} (t₀ : Fin M) (n j : ℕ) :
    Isomorphic (symThree K (dwz63OrbitRegion K q 2 t₀ n j).realize)
      (symThree K (dwz63SideOrbitRegion K q Leg.Y t₀ n j).realize) :=
  (Isomorphic.symThree_permute_cycleSymm (K := K)
      (dwz63OrbitRegion K q 2 t₀ n j).realize).symm.trans
    (Isomorphic.symThree_congr (dwz63_isomorphic_permute_cycleSymm_orbitRegion_two K q t₀ n j))

end AlgebraicComplexity.Examples
