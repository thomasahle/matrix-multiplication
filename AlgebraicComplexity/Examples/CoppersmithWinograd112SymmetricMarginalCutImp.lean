/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricMarginalCut

set_option autoImplicit false

/-!
# The certificate's three-marginal cut refines the leaf's `Z`-typed cut

Layer 4 (`AlgebraicComplexity/Examples/`).  This is the inclusion asserted by `[DuanWuZhou2022]`,
`second_power_appendix.tex:47`, in the proof of `lem:non-rot-values` (d):

> *`\T` is a subtensor of `T_{1,1,2}^{⊗m}[α̃_Z^{(1,1,2)}]`; it can be obtained by zeroing out X
and > Y-blocks from `T_{1,1,2}^{⊗m}[α̃_Z^{(1,1,2)}]`.*

The paper's `\T` is the value certificate's three-marginal cut `cw112SymmetricKeepMarginal`; the
paper's `T_{1,1,2}^{⊗m}[α̃_Z]` is the leaf's `Z`-typed cut.  The same condition is `def:complv2`
(`second_power.tex:174-181`), with `α̃_A` at `eq:tilde_A` (`second_power.tex:157-160`); the split
being matched is `global_value.tex:341-348`'s `(b, 1-2b, b)`.  Discharging this predicate is the
`himp` binder of `cw112_symThree_typedCut_restricts_symmetricAmbient`, after which the whole
`T_{1,1,2}` value path carries no hypothesis.

## Why a successor module

Every ingredient is already proved; only the assembly is here.  The assembly needs the letterwise
reading of the label transpose *pointwise* — as `(positiveWordEquiv _ r w i).1.2`, not through
`Function.comp` — because `CW112SymmetricBlock c` is a reducible abbreviation of the product block
index at which the generic reading is stated, and a `rw` keys on the head symbol and misses it.
Building the component equation as a `congrArg`/`congrFun` term instead of a rewrite avoids the
question entirely: this is the same address-free/pointwise discipline that carried the earlier
steps of this lane.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `second_power_appendix.tex:44-50` (`lem:non-rot-values` (d)),
`second_power.tex:157-181` (`eq:tilde_A`, `def:complv2`), `global_value.tex:341-348`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- **The certificate's three-marginal cut sits inside `sym₃` of the leaf's `Z`-typed cut.**

This discharges image 140's `himp`.  It is `second_power_appendix.tex:47`, read in the direction
the value argument uses it, and `def:complv2` (`second_power.tex:174-181`) restated on the
committed objects.

Proof sketch: `cycle` is a three-cycle, so for each leg exactly one of `c`, `cycle⁻¹ c`, `cycle
c` is `Leg.Z`; the other two `symThreeKeep` conjuncts are vacuous off the constrained leg.  For the
surviving one, read the symmetric word letterwise at the relevant component (a `congrArg` of a
`congrFun`, never a rewrite), push the multiplicity type forward along that component projection,
substitute the certificate's marginal condition, and close with the identity of the two stored
copies of the `b`-split at `j = 4·10¹³·k`. -/
theorem cw112SymmetricKeepMarginal_symThreeKeep
    (K : Type u) [CommRing K] (q k j : ℕ) (hq : 0 < q)
    (hj : j = 40000000000000 * k) {M : ℕ} (t₀ : Fin M) (c : Leg)
    (w : PositiveWord (CW112SymmetricBlock c)
      ((cw112SymmetricPartitionRationalTypedLeaf K q dwz112L dwz112G hq dwz112L_pos
        dwz112G_pos).proportionalDepth k))
    (hw : cw112SymmetricKeepMarginal K q dwz112L dwz112G k hq dwz112L_pos dwz112G_pos c w) :
    PartitionedTensor.symThreeKeep
      ((SegmentedSplitRestriction.ofLeg (A := CW112Block) Leg.Z
        (cw112PushedOrbitProfile t₀ j)).Keeps
          ((cw112SymmetricPartitionRationalTypedLeaf K q dwz112L dwz112G hq dwz112L_pos
            dwz112G_pos).proportionalDepth k) (fun _ ↦ t₀)) c
      ((PartitionedTensor.symThreeWordEquiv
        ((cw112SymmetricPartitionRationalTypedLeaf K q dwz112L dwz112G hq dwz112L_pos
          dwz112G_pos).proportionalDepth k) c).symm w) := by
  classical
  unfold cw112SymmetricKeepMarginal RationalTypedLeaf.KeepsMarginal at hw
  have hmarg := cw112SymmetricLeaf_marginalProfile_projZ K q dwz112L dwz112G hq
    dwz112L_pos dwz112G_pos
  cases c
  · -- `Leg.X`: the constrained component is the second, sitting over `cycle⁻¹ X = Z`.
    refine ⟨⟨dwz63_keeps_constSeg_of_ne (by decide) _ _ _, ?_⟩,
      dwz63_keeps_constSeg_of_ne (by decide) _ _ _⟩
    refine (dwz63_keeps_constSeg_iff (A := CW112Block) t₀ _ _ _).mpr ?_
    have hread :
        positiveWordEquiv (CW112Block Leg.Z) _
            ((PartitionedTensor.symThreeWordEquiv (A := CW112Block) _ Leg.X).symm w).1.2 =
          (fun t : CyclicTypedLeafCoordinate CW112Block Leg.X ↦ t.1.2) ∘
            positiveWordEquiv (CyclicTypedLeafCoordinate CW112Block Leg.X) _ w :=
      funext fun i ↦ (congrArg (fun t : CyclicTypedLeafCoordinate CW112Block Leg.X ↦ t.1.2)
        (congrFun (dwz63_positiveWordEquiv_symThreeWordEquiv_symm
          (A := CW112Block) _ Leg.X w) i)).symm
    rw [hread]
    refine Eq.trans (WordType.multiplicity_comp_eq_mappedType
      (fun t : CyclicTypedLeafCoordinate CW112Block Leg.X ↦ t.1.2)
      (positiveWordEquiv (CyclicTypedLeafCoordinate CW112Block Leg.X) _ w)) ?_
    refine Eq.trans (congrArg (WordType.mappedType
      (fun t : CyclicTypedLeafCoordinate CW112Block Leg.X ↦ t.1.2)) hw) ?_
    refine Eq.trans (WordType.mappedType_proportionalCounts
      (fun t : CyclicTypedLeafCoordinate CW112Block Leg.X ↦ t.1.2) _ k) ?_
    refine Eq.trans (congrArg (fun f ↦ WordType.proportionalCounts f k) hmarg.2.1) ?_
    refine Eq.trans ?_ (WordType.mappedType_proportionalCounts
      (cw112RawDict Leg.Z) (dwz63AlphaTilde 6) j).symm
    funext b
    show ((cw112RationalTypedLeaf q dwz112L dwz112G hq dwz112L_pos
      dwz112G_pos).marginalProfile Leg.Z b * (2 * (dwz112L + dwz112G)) ^ 2) * k =
        WordType.mappedType (cw112RawDict Leg.Z) (dwz63AlphaTilde 6) b * j
    rw [hj]
    exact dwz112_marginal_projZ_eq_pushedAlphaTilde q hq k b
  · -- `Leg.Y`: the constrained component is the third, sitting over `cycle Y = Z`.
    refine ⟨⟨dwz63_keeps_constSeg_of_ne (by decide) _ _ _,
      dwz63_keeps_constSeg_of_ne (by decide) _ _ _⟩, ?_⟩
    refine (dwz63_keeps_constSeg_iff (A := CW112Block) t₀ _ _ _).mpr ?_
    have hread :
        positiveWordEquiv (CW112Block Leg.Z) _
            ((PartitionedTensor.symThreeWordEquiv (A := CW112Block) _ Leg.Y).symm w).2 =
          (fun t : CyclicTypedLeafCoordinate CW112Block Leg.Y ↦ t.2) ∘
            positiveWordEquiv (CyclicTypedLeafCoordinate CW112Block Leg.Y) _ w :=
      funext fun i ↦ (congrArg (fun t : CyclicTypedLeafCoordinate CW112Block Leg.Y ↦ t.2)
        (congrFun (dwz63_positiveWordEquiv_symThreeWordEquiv_symm
          (A := CW112Block) _ Leg.Y w) i)).symm
    rw [hread]
    refine Eq.trans (WordType.multiplicity_comp_eq_mappedType
      (fun t : CyclicTypedLeafCoordinate CW112Block Leg.Y ↦ t.2)
      (positiveWordEquiv (CyclicTypedLeafCoordinate CW112Block Leg.Y) _ w)) ?_
    refine Eq.trans (congrArg (WordType.mappedType
      (fun t : CyclicTypedLeafCoordinate CW112Block Leg.Y ↦ t.2)) hw) ?_
    refine Eq.trans (WordType.mappedType_proportionalCounts
      (fun t : CyclicTypedLeafCoordinate CW112Block Leg.Y ↦ t.2) _ k) ?_
    refine Eq.trans (congrArg (fun f ↦ WordType.proportionalCounts f k) hmarg.2.2) ?_
    refine Eq.trans ?_ (WordType.mappedType_proportionalCounts
      (cw112RawDict Leg.Z) (dwz63AlphaTilde 6) j).symm
    funext b
    show ((cw112RationalTypedLeaf q dwz112L dwz112G hq dwz112L_pos
      dwz112G_pos).marginalProfile Leg.Z b * (2 * (dwz112L + dwz112G)) ^ 2) * k =
        WordType.mappedType (cw112RawDict Leg.Z) (dwz63AlphaTilde 6) b * j
    rw [hj]
    exact dwz112_marginal_projZ_eq_pushedAlphaTilde q hq k b
  · -- `Leg.Z`: the constrained component is the first, sitting over `Z` itself.
    refine ⟨⟨?_, dwz63_keeps_constSeg_of_ne (by decide) _ _ _⟩,
      dwz63_keeps_constSeg_of_ne (by decide) _ _ _⟩
    refine (dwz63_keeps_constSeg_iff (A := CW112Block) t₀ _ _ _).mpr ?_
    have hread :
        positiveWordEquiv (CW112Block Leg.Z) _
            ((PartitionedTensor.symThreeWordEquiv (A := CW112Block) _ Leg.Z).symm w).1.1 =
          (fun t : CyclicTypedLeafCoordinate CW112Block Leg.Z ↦ t.1.1) ∘
            positiveWordEquiv (CyclicTypedLeafCoordinate CW112Block Leg.Z) _ w :=
      funext fun i ↦ (congrArg (fun t : CyclicTypedLeafCoordinate CW112Block Leg.Z ↦ t.1.1)
        (congrFun (dwz63_positiveWordEquiv_symThreeWordEquiv_symm
          (A := CW112Block) _ Leg.Z w) i)).symm
    rw [hread]
    refine Eq.trans (WordType.multiplicity_comp_eq_mappedType
      (fun t : CyclicTypedLeafCoordinate CW112Block Leg.Z ↦ t.1.1)
      (positiveWordEquiv (CyclicTypedLeafCoordinate CW112Block Leg.Z) _ w)) ?_
    refine Eq.trans (congrArg (WordType.mappedType
      (fun t : CyclicTypedLeafCoordinate CW112Block Leg.Z ↦ t.1.1)) hw) ?_
    refine Eq.trans (WordType.mappedType_proportionalCounts
      (fun t : CyclicTypedLeafCoordinate CW112Block Leg.Z ↦ t.1.1) _ k) ?_
    refine Eq.trans (congrArg (fun f ↦ WordType.proportionalCounts f k) hmarg.1) ?_
    refine Eq.trans ?_ (WordType.mappedType_proportionalCounts
      (cw112RawDict Leg.Z) (dwz63AlphaTilde 6) j).symm
    funext b
    show ((cw112RationalTypedLeaf q dwz112L dwz112G hq dwz112L_pos
      dwz112G_pos).marginalProfile Leg.Z b * (2 * (dwz112L + dwz112G)) ^ 2) * k =
        WordType.mappedType (cw112RawDict Leg.Z) (dwz63AlphaTilde 6) b * j
    rw [hj]
    exact dwz112_marginal_projZ_eq_pushedAlphaTilde q hq k b

end AlgebraicComplexity.Examples
