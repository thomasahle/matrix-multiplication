/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112LegTypedCut
import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricMarginalCut
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLeafTauWeightBeta

set_option autoImplicit false

/-!
# The free-`beta` certificate's marginal, read on a degree-one leg

Layer 4 (`AlgebraicComplexity/Examples/`).
`Examples/CoppersmithWinograd112SymmetricMarginalCut.lean` identifies the `b`-split value
certificate's `Z` marginal with the `(1,1,2)` row `alphatilde` pushed along the block dictionary.
The two rotated orbit rows constrain a degree-one leg instead --- `X` for `(1,2,1)` and `Y` for
`(2,1,1)`, after the rotation of `Examples/DuanWuZhouLevelTwoOrbitRotatedRegion.lean` --- and use
the free-`beta` constants `(dwz121L, dwz121G)`.  This module supplies the corresponding numeric
identity and the three leg-general component readings of the symmetric leaf's marginal.

## The two stored copies of the symmetric degree-one split

`global_value.tex:347`: *"For all other components, we use the symmetric Z-marginal split
distributions ... So the values of all other components (including `(2,2,0)`, `(1,2,1)`,
`(2,1,1)`) do not change"*.  The repository stores that split twice: as `dwz63AlphaTilde 7`
(equal to `dwz63AlphaTilde 10`), the mass-`2·10^8` profile with `10^8` on each of the two
degree-one letters, and as the free-`beta` certificate's own side marginal `L + G` at
`dwz121L = 69022217`, `dwz121G = 2430977783`, i.e. `L + G = 2.5·10^9`.  The whole content of
`dwz121_marginal_side_eq_pushedAlphaTilde` is that the two agree once the periods are reconciled
at `j = 6.25·10^20 · k`:

`2.5·10^9 · (5·10^9)^2 · k = 6.25·10^28 · k = 10^8 · 6.25·10^20 · k`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, `[duan2023faster]` arXiv:2210.10173, `second_power_appendix.tex:44-50`,
`second_power.tex:157-181` (`eq:tilde_A`, `def:complv2`), `global_value.tex:341-348` (`:347`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## The primitive leaf's marginal, on every leg -/

/-- **The `(L,L,G,G)` leaf's marginal is the committed leg marginal**, on every leg: `(L+G, L+G)`
on the two degree-one legs and `(L, L, 2G)` on `Z`.  This is
`global_value.tex:341`'s `(b, 1-2b, b)` at `b = L / (2(L+G))` on `Z`, and the uniform side split
on `X` and `Y`. -/
theorem cw112BaseLeaf_marginalProfile (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (c : Leg) :
    (cw112RationalTypedLeaf q L G hq hL hG).marginalProfile c = cw112MarginalType L G c :=
  cw112_mappedType_eq_marginal L G c

/-! ## The symmetric degree-one row, pushed along the dictionary -/

/-- **The symmetric degree-one row, pushed along the block dictionary of a degree-one leg, is
`10^8` on both sides.** -/
theorem dwz63_pushedAlphaTildeSeven_eq (c₀ : Leg) (hc₀ : cwSquare112 c₀ = 1)
    (b : CW112Block c₀) :
    WordType.mappedType (cw112RawDict c₀) (dwz63AlphaTilde 7) b = 100000000 := by
  rw [cw112RawDict_mappedTypeAt_apply c₀ _
    (dwz63_alphaTildeSeven_eq_zero_of_not_cell c₀ hc₀)]
  revert hc₀ b
  cases c₀ <;> intro hc₀ b
  · cases b <;> rfl
  · cases b <;> rfl
  · exact absurd hc₀ (by decide)

/-! ## The two stored copies of the symmetric degree-one split agree -/

/-- **The free-`beta` certificate's side marginal and the `(1,2,1)` row are the same split**, once
the periods are reconciled at `j = 6.25·10^20 · k`. -/
theorem dwz121_marginal_side_eq_pushedAlphaTilde (q : ℕ) (hq : 0 < q) (c₀ : Leg)
    (hc₀ : cwSquare112 c₀ = 1) (k : ℕ) (b : CW112Block c₀) :
    (cw112RationalTypedLeaf q dwz121L dwz121G hq dwz121L_pos dwz121G_pos).marginalProfile
          c₀ b * (2 * (dwz121L + dwz121G)) ^ 2 * k =
      WordType.mappedType (cw112RawDict c₀) (dwz63AlphaTilde 7) b
        * (625000000000000000000 * k) := by
  rw [cw112BaseLeaf_marginalProfile, dwz63_pushedAlphaTildeSeven_eq c₀ hc₀]
  revert hc₀ b
  cases c₀ <;> intro hc₀ b
  · cases b <;> · show (dwz121L + dwz121G) * _ * k = _
                  norm_num [dwz121L, dwz121G]
                  ring
  · cases b <;> · show (dwz121L + dwz121G) * _ * k = _
                  norm_num [dwz121L, dwz121G]
                  ring
  · exact absurd hc₀ (by decide)

/-! ## The three component readings of the symmetric leaf's marginal, on every leg -/

/-- **The first component of the symmetric leaf's marginal is the primitive marginal at the same
leg**, scaled by the two summed-out masses. -/
theorem cw112SymmetricLeaf_marginalProfile_fstFst
    (K : Type u) [CommRing K] (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) (c : Leg) :
    WordType.mappedType (fun t : CyclicTypedLeafCoordinate CW112Block c ↦ t.1.1)
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).marginalProfile c) =
      fun a ↦ (cw112RationalTypedLeaf q L G hq hL hG).marginalProfile c a
        * (2 * (L + G)) ^ 2 := by
  have hmass : (cw112RationalTypedLeaf q L G hq hL hG).profile.mass = 2 * (L + G) :=
    cw112IntegralProfile_mass L G hL hG
  have hre : (cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).marginalProfile c =
      ((cw112RationalTypedLeaf q L G hq hL hG).cyclicProduct).marginalProfile c :=
    RationalTypedLeaf.marginalProfile_reindex _ _ c
  rw [hre, RationalTypedLeaf.marginalProfile_cyclicProduct_fst_fst, hmass]

/-- **The second component sits over the inverse-cyclic leg.** -/
theorem cw112SymmetricLeaf_marginalProfile_fstSnd
    (K : Type u) [CommRing K] (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) (c : Leg) :
    WordType.mappedType (fun t : CyclicTypedLeafCoordinate CW112Block c ↦ t.1.2)
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).marginalProfile c) =
      fun a ↦ (cw112RationalTypedLeaf q L G hq hL hG).marginalProfile (cycle.symm c) a
        * (2 * (L + G)) ^ 2 := by
  have hmass : (cw112RationalTypedLeaf q L G hq hL hG).profile.mass = 2 * (L + G) :=
    cw112IntegralProfile_mass L G hL hG
  have hre : (cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).marginalProfile c =
      ((cw112RationalTypedLeaf q L G hq hL hG).cyclicProduct).marginalProfile c :=
    RationalTypedLeaf.marginalProfile_reindex _ _ c
  rw [hre, RationalTypedLeaf.marginalProfile_cyclicProduct_fst_snd, hmass]

/-- **The third component sits over the cyclic leg.** -/
theorem cw112SymmetricLeaf_marginalProfile_snd
    (K : Type u) [CommRing K] (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) (c : Leg) :
    WordType.mappedType (fun t : CyclicTypedLeafCoordinate CW112Block c ↦ t.2)
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).marginalProfile c) =
      fun a ↦ (cw112RationalTypedLeaf q L G hq hL hG).marginalProfile (cycle c) a
        * (2 * (L + G)) ^ 2 := by
  have hmass : (cw112RationalTypedLeaf q L G hq hL hG).profile.mass = 2 * (L + G) :=
    cw112IntegralProfile_mass L G hL hG
  have hre : (cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).marginalProfile c =
      ((cw112RationalTypedLeaf q L G hq hL hG).cyclicProduct).marginalProfile c :=
    RationalTypedLeaf.marginalProfile_reindex _ _ c
  rw [hre, RationalTypedLeaf.marginalProfile_cyclicProduct_snd, hmass]

/-! ## One surviving component of the three-marginal condition -/

/-- **One component of the certificate's marginal condition is the rotated row's type
condition.**  The shared body of the six branches of `cw112SymmetricKeepMarginal_symThreeKeepSide`:
read the symmetric word letterwise at the relevant component, push the multiplicity type forward
along that component projection, substitute the certificate's marginal condition, and close with
the identity of the two stored copies of the symmetric degree-one split. -/
theorem dwz121_component_type_of_keepMarginal
    (K : Type u) [CommRing K] (q k j : ℕ) (hq : 0 < q)
    (hj : j = 625000000000000000000 * k) (c₀ : Leg) (hc₀ : cwSquare112 c₀ = 1) (d : Leg)
    (w : PositiveWord (CW112SymmetricBlock d)
      ((cw112SymmetricPartitionRationalTypedLeaf K q dwz121L dwz121G hq dwz121L_pos
        dwz121G_pos).proportionalDepth k))
    (hw : cw112SymmetricKeepMarginal K q dwz121L dwz121G k hq dwz121L_pos dwz121G_pos d w)
    (proj : CyclicTypedLeafCoordinate CW112Block d → CW112Block c₀)
    (hproj : WordType.mappedType proj
        ((cw112SymmetricPartitionRationalTypedLeaf K q dwz121L dwz121G hq dwz121L_pos
          dwz121G_pos).marginalProfile d) =
      fun a ↦ (cw112RationalTypedLeaf q dwz121L dwz121G hq dwz121L_pos
        dwz121G_pos).marginalProfile c₀ a * (2 * (dwz121L + dwz121G)) ^ 2)
    (word : PositiveWord (CW112Block c₀)
      ((cw112SymmetricPartitionRationalTypedLeaf K q dwz121L dwz121G hq dwz121L_pos
        dwz121G_pos).proportionalDepth k))
    (hread : positiveWordEquiv (CW112Block c₀) _ word =
      proj ∘ positiveWordEquiv (CyclicTypedLeafCoordinate CW112Block d) _ w) :
    WordType.multiplicity (positiveWordEquiv (CW112Block c₀) _ word) =
      WordType.mappedType (cw112RawDict c₀)
        (WordType.proportionalCounts (dwz63AlphaTilde 7) j) := by
  unfold cw112SymmetricKeepMarginal RationalTypedLeaf.KeepsMarginal at hw
  rw [hread]
  refine Eq.trans (WordType.multiplicity_comp_eq_mappedType proj _) ?_
  refine Eq.trans (congrArg (WordType.mappedType proj) hw) ?_
  refine Eq.trans (WordType.mappedType_proportionalCounts proj _ k) ?_
  refine Eq.trans (congrArg (fun f ↦ WordType.proportionalCounts f k) hproj) ?_
  refine Eq.trans ?_ (WordType.mappedType_proportionalCounts
    (cw112RawDict c₀) (dwz63AlphaTilde 7) j).symm
  funext b
  show ((cw112RationalTypedLeaf q dwz121L dwz121G hq dwz121L_pos
      dwz121G_pos).marginalProfile c₀ b * (2 * (dwz121L + dwz121G)) ^ 2) * k =
    WordType.mappedType (cw112RawDict c₀) (dwz63AlphaTilde 7) b * j
  rw [hj]
  exact dwz121_marginal_side_eq_pushedAlphaTilde q hq c₀ hc₀ k b

/-! ## The inclusion itself, for a degree-one constrained leg -/

/-- **The free-`beta` certificate's three-marginal cut sits inside `sym₃` of the rotated row's
typed cut.**

This is image 140's `himp` for the two rotated orbit rows: `c₀ = Leg.X` serves `(1,2,1)` and
`c₀ = Leg.Y` serves `(2,1,1)`.  It is `second_power_appendix.tex:47` read in the direction the
value argument uses it, at the symmetric degree-one split of `global_value.tex:347`.

Proof sketch: `cycle` is a three-cycle, so for each leg exactly one of the three `symThreeKeep`
conjuncts sits over `c₀`; the other two are vacuous.  The surviving one is
`dwz121_component_type_of_keepMarginal` at the matching component projection, whose letterwise
reading is a `congrArg` of a `congrFun` --- never a rewrite, because the component projection of a
symmetric word carries the leg in its type. -/
theorem cw112SymmetricKeepMarginal_symThreeKeepSide
    (K : Type u) [CommRing K] (q k j : ℕ) (hq : 0 < q)
    (hj : j = 625000000000000000000 * k) (c₀ : Leg) (hc₀ : cwSquare112 c₀ = 1)
    {M : ℕ} (t₀ : Fin M) (c : Leg)
    (w : PositiveWord (CW112SymmetricBlock c)
      ((cw112SymmetricPartitionRationalTypedLeaf K q dwz121L dwz121G hq dwz121L_pos
        dwz121G_pos).proportionalDepth k))
    (hw : cw112SymmetricKeepMarginal K q dwz121L dwz121G k hq dwz121L_pos dwz121G_pos c w) :
    PartitionedTensor.symThreeKeep
      ((SegmentedSplitRestriction.ofLeg (A := CW112Block) c₀
        (cw112LegPushedProfile c₀ t₀ j)).Keeps
          ((cw112SymmetricPartitionRationalTypedLeaf K q dwz121L dwz121G hq dwz121L_pos
            dwz121G_pos).proportionalDepth k) (fun _ ↦ t₀)) c
      ((PartitionedTensor.symThreeWordEquiv
        ((cw112SymmetricPartitionRationalTypedLeaf K q dwz121L dwz121G hq dwz121L_pos
          dwz121G_pos).proportionalDepth k) c).symm w) := by
  classical
  unfold cw112LegPushedProfile
  revert hc₀
  cases c₀ <;> intro hc₀
  · cases c
    · refine ⟨⟨?_, dwz63_keepsAt_constSeg_of_ne (by decide) _ _ _⟩,
        dwz63_keepsAt_constSeg_of_ne (by decide) _ _ _⟩
      refine (dwz63_keepsAt_constSeg_iff (A := CW112Block) Leg.X t₀ _ _ _).mpr ?_
      refine dwz121_component_type_of_keepMarginal K q k j hq hj Leg.X (by decide) Leg.X w hw
        (fun t ↦ t.1.1)
        (cw112SymmetricLeaf_marginalProfile_fstFst K q dwz121L dwz121G hq dwz121L_pos
          dwz121G_pos Leg.X) _ ?_
      exact funext fun i ↦
        (congrArg (fun t : CyclicTypedLeafCoordinate CW112Block Leg.X ↦ t.1.1)
          (congrFun (dwz63_positiveWordEquiv_symThreeWordEquiv_symm
            (A := CW112Block) _ Leg.X w) i)).symm
    · refine ⟨⟨dwz63_keepsAt_constSeg_of_ne (by decide) _ _ _, ?_⟩,
        dwz63_keepsAt_constSeg_of_ne (by decide) _ _ _⟩
      refine (dwz63_keepsAt_constSeg_iff (A := CW112Block) Leg.X t₀ _ _ _).mpr ?_
      refine dwz121_component_type_of_keepMarginal K q k j hq hj Leg.X (by decide) Leg.Y w hw
        (fun t ↦ t.1.2)
        (cw112SymmetricLeaf_marginalProfile_fstSnd K q dwz121L dwz121G hq dwz121L_pos
          dwz121G_pos Leg.Y) _ ?_
      exact funext fun i ↦
        (congrArg (fun t : CyclicTypedLeafCoordinate CW112Block Leg.Y ↦ t.1.2)
          (congrFun (dwz63_positiveWordEquiv_symThreeWordEquiv_symm
            (A := CW112Block) _ Leg.Y w) i)).symm
    · refine ⟨⟨dwz63_keepsAt_constSeg_of_ne (by decide) _ _ _,
        dwz63_keepsAt_constSeg_of_ne (by decide) _ _ _⟩, ?_⟩
      refine (dwz63_keepsAt_constSeg_iff (A := CW112Block) Leg.X t₀ _ _ _).mpr ?_
      refine dwz121_component_type_of_keepMarginal K q k j hq hj Leg.X (by decide) Leg.Z w hw
        (fun t ↦ t.2)
        (cw112SymmetricLeaf_marginalProfile_snd K q dwz121L dwz121G hq dwz121L_pos
          dwz121G_pos Leg.Z) _ ?_
      exact funext fun i ↦
        (congrArg (fun t : CyclicTypedLeafCoordinate CW112Block Leg.Z ↦ t.2)
          (congrFun (dwz63_positiveWordEquiv_symThreeWordEquiv_symm
            (A := CW112Block) _ Leg.Z w) i)).symm
  · cases c
    · refine ⟨⟨dwz63_keepsAt_constSeg_of_ne (by decide) _ _ _,
        dwz63_keepsAt_constSeg_of_ne (by decide) _ _ _⟩, ?_⟩
      refine (dwz63_keepsAt_constSeg_iff (A := CW112Block) Leg.Y t₀ _ _ _).mpr ?_
      refine dwz121_component_type_of_keepMarginal K q k j hq hj Leg.Y (by decide) Leg.X w hw
        (fun t ↦ t.2)
        (cw112SymmetricLeaf_marginalProfile_snd K q dwz121L dwz121G hq dwz121L_pos
          dwz121G_pos Leg.X) _ ?_
      exact funext fun i ↦
        (congrArg (fun t : CyclicTypedLeafCoordinate CW112Block Leg.X ↦ t.2)
          (congrFun (dwz63_positiveWordEquiv_symThreeWordEquiv_symm
            (A := CW112Block) _ Leg.X w) i)).symm
    · refine ⟨⟨?_, dwz63_keepsAt_constSeg_of_ne (by decide) _ _ _⟩,
        dwz63_keepsAt_constSeg_of_ne (by decide) _ _ _⟩
      refine (dwz63_keepsAt_constSeg_iff (A := CW112Block) Leg.Y t₀ _ _ _).mpr ?_
      refine dwz121_component_type_of_keepMarginal K q k j hq hj Leg.Y (by decide) Leg.Y w hw
        (fun t ↦ t.1.1)
        (cw112SymmetricLeaf_marginalProfile_fstFst K q dwz121L dwz121G hq dwz121L_pos
          dwz121G_pos Leg.Y) _ ?_
      exact funext fun i ↦
        (congrArg (fun t : CyclicTypedLeafCoordinate CW112Block Leg.Y ↦ t.1.1)
          (congrFun (dwz63_positiveWordEquiv_symThreeWordEquiv_symm
            (A := CW112Block) _ Leg.Y w) i)).symm
    · refine ⟨⟨dwz63_keepsAt_constSeg_of_ne (by decide) _ _ _, ?_⟩,
        dwz63_keepsAt_constSeg_of_ne (by decide) _ _ _⟩
      refine (dwz63_keepsAt_constSeg_iff (A := CW112Block) Leg.Y t₀ _ _ _).mpr ?_
      refine dwz121_component_type_of_keepMarginal K q k j hq hj Leg.Y (by decide) Leg.Z w hw
        (fun t ↦ t.1.2)
        (cw112SymmetricLeaf_marginalProfile_fstSnd K q dwz121L dwz121G hq dwz121L_pos
          dwz121G_pos Leg.Z) _ ?_
      exact funext fun i ↦
        (congrArg (fun t : CyclicTypedLeafCoordinate CW112Block Leg.Z ↦ t.1.2)
          (congrFun (dwz63_positiveWordEquiv_symThreeWordEquiv_symm
            (A := CW112Block) _ Leg.Z w) i)).symm
  · exact absurd hc₀ (by decide)

end AlgebraicComplexity.Examples
