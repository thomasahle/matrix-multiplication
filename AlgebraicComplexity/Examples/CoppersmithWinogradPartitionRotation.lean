/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientationOneSliceBase
import AlgebraicComplexity.Tensor.PartitionedPermutePower

set_option autoImplicit false

/-!
# The Coppersmith--Winograd partition is cyclically symmetric, as a partitioned tensor

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/CoppersmithWinogradSquareSymmetryDefs.lean`
proves the cyclic symmetry of the CW tensor one **constituent** at a time
(`cwConstituentOfBlocks_cycle`, and `cwConstituentOfBlocks_cycleSymm` in
`Examples/CoppersmithWinogradZeroOrientationOneSliceBase.lean`).  This module packages those six
identities into the single statement a partitioned client needs:

`(cwPartitionedTensor K q).permute cycle` **is** `cwPartitionedTensor K q`, as a reindex
equivalence along the identity relabelling.

That form is what makes the leg rotation travel through `positivePower`
(`ReindexEquiv.positivePower`, `reindexEquiv_permute_positivePower`) and through a block cut
(`ReindexEquiv.isomorphic_select`), which is what the rotated orbit rows of `[duan2023faster]`'s
level-two fine leaf need: `T_{1,2,1}` and `T_{2,1,1}` are the two cyclic rotations of `T_{1,1,2}`,
so their regions are rotations of a `(1,1,2)` region, and only the *rotated* region can be block
mapped legwise onto `cw112PartitionedTensor`.

The identity relabelling is the right label equivalence because the CW block alphabet is the same
`CWBlock` on all three legs and `cwBlockSupport` is closed under rotating an address: rotating a
leg permutes the *addresses*, and `PartitionedTensor.permute` already performs that permutation, so
no relabelling is left to do.

## The paper step this serves

`[duan2023faster]` arXiv:2210.10173, `second_power.tex:235` (`note:T112`) and
`second_power.tex:142-158` (`lem:non-rot-values`, especially the requirement
`α(1,1,2) = α(1,2,1) = α(2,1,1)`): the level-two component `T_{1,1,2}` has no non-rotational
value, so only `V^{(3)}` is available and the paper reads the *same* value on the three rotations of
the component.  Formally that reading is this rotation together with the cyclic invariance of
`sym_3` (`MatrixMultiplication/SymThreeCycleInvariance.lean`).  The statements below are reusable
partitioned-tensor infrastructure, not published claims: the paper's "by symmetry" is one phrase.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, `[duan2023faster]`, `second_power.tex:142-158`, `:235`; Don Coppersmith and Shmuel
Winograd, *Matrix Multiplication via Arithmetic Progressions*, `[coppersmith1990matrix]`,
pp. 270--272 (the tensor being rotated).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u w

variable (K : Type u) [CommRing K] (q : ℕ)

/-! ## Reading the inverse address transport on the CW alphabet -/

/-- The inverse `cycle` transport of a CW block address, read leg by leg. -/
theorem cwBlockAddress_permute_cycle_symm
    (s : BlockAddress (fun _ : Leg ↦ CWBlock)) :
    (permuteBlockAddress (A := fun _ : Leg ↦ CWBlock) cycle).symm s =
      ofLegs (V := fun _ : Leg ↦ CWBlock) (s Leg.Y) (s Leg.Z) (s Leg.X) := by
  funext c
  cases c
  · exact permuteBlockAddress_symm_apply_apply
      (A := fun _ : Leg ↦ CWBlock) cycle s Leg.Y
  · exact permuteBlockAddress_symm_apply_apply
      (A := fun _ : Leg ↦ CWBlock) cycle s Leg.Z
  · exact permuteBlockAddress_symm_apply_apply
      (A := fun _ : Leg ↦ CWBlock) cycle s Leg.X

/-- The inverse `cycle.symm` transport of a CW block address, read leg by leg. -/
theorem cwBlockAddress_permute_cycleSymm_symm
    (s : BlockAddress (fun _ : Leg ↦ CWBlock)) :
    (permuteBlockAddress (A := fun _ : Leg ↦ CWBlock) cycle.symm).symm s =
      ofLegs (V := fun _ : Leg ↦ CWBlock) (s Leg.Z) (s Leg.X) (s Leg.Y) := by
  funext c
  cases c
  · exact permuteBlockAddress_symm_apply_apply
      (A := fun _ : Leg ↦ CWBlock) cycle.symm s Leg.Z
  · exact permuteBlockAddress_symm_apply_apply
      (A := fun _ : Leg ↦ CWBlock) cycle.symm s Leg.X
  · exact permuteBlockAddress_symm_apply_apply
      (A := fun _ : Leg ↦ CWBlock) cycle.symm s Leg.Y

/-! ## The support is closed under rotating an address -/

/-- **Rotating a CW block address preserves membership in the support.** -/
theorem mem_cwBlockSupport_ofLegs_cycle (x y z : CWBlock) :
    (ofLegs (V := fun _ : Leg ↦ CWBlock) y z x ∈ cwBlockSupport) ↔
      (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z ∈ cwBlockSupport) := by
  cases x <;> cases y <;> cases z <;> decide

/-- The same statement for the inverse rotation. -/
theorem mem_cwBlockSupport_ofLegs_cycleSymm (x y z : CWBlock) :
    (ofLegs (V := fun _ : Leg ↦ CWBlock) z x y ∈ cwBlockSupport) ↔
      (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z ∈ cwBlockSupport) := by
  cases x <;> cases y <;> cases z <;> decide

/-! ## The six constituent identities, extended by zero to every address -/

/-- **`cwConstituentOfBlocks_cycle` with the support hypothesis removed.**  Off the support both
sides are `0`, and the support is rotation-closed, so the identity holds at every address. -/
theorem cwConstituentOfBlocks_cycle_of_all (x y z : CWBlock) :
    map (fun c ↦ (cwBaseConstituentCycleEquiv K q x y z c).toLinearMap)
        (Tensor.permute cycle (cwConstituentOfBlocks K q x y z)) =
      cwConstituentOfBlocks K q z x y := by
  by_cases hs : ofLegs (V := fun _ : Leg ↦ CWBlock) x y z ∈ cwBlockSupport
  · exact cwConstituentOfBlocks_cycle K q x y z hs
  · revert hs
    cases x <;> cases y <;> cases z <;> intro hs <;>
      first
        | exact absurd (by decide) hs
        | simp [cwConstituentOfBlocks]

/-- The same, for the inverse rotation. -/
theorem cwConstituentOfBlocks_cycleSymm_of_all (x y z : CWBlock) :
    map (fun c ↦ (cwBaseConstituentCycleSymmEquiv K q x y z c).toLinearMap)
        (Tensor.permute cycle.symm (cwConstituentOfBlocks K q x y z)) =
      cwConstituentOfBlocks K q y z x := by
  by_cases hs : ofLegs (V := fun _ : Leg ↦ CWBlock) x y z ∈ cwBlockSupport
  · exact cwConstituentOfBlocks_cycleSymm K q x y z hs
  · revert hs
    cases x <;> cases y <;> cases z <;> intro hs <;>
      first
        | exact absurd (by decide) hs
        | simp [cwConstituentOfBlocks]

/-! ## The partitioned rotation -/

/-- **Rotating the legs of the CW partition returns the CW partition.**

The label alphabet is `CWBlock` on all three legs, and `PartitionedTensor.permute` already carries
out the address rotation, so no relabelling is left and the two certificates are literally equal. -/
theorem cwPartitionedTensor_permute_cycle :
    (cwPartitionedTensor K q).permute cycle = cwPartitionedTensor K q := by
  classical
  apply PartitionedTensor.ext
  · ext s
    rw [PartitionedTensor.mem_permute_support, cwBlockAddress_permute_cycle_symm]
    show (ofLegs (V := fun _ : Leg ↦ CWBlock) (s Leg.Y) (s Leg.Z) (s Leg.X) ∈ cwBlockSupport)
      ↔ (s ∈ cwBlockSupport)
    rw [mem_cwBlockSupport_ofLegs_cycle (s Leg.X) (s Leg.Y) (s Leg.Z), ofLegs_eta]
  · funext s
    obtain ⟨t, rfl⟩ : ∃ t, permuteBlockAddress (A := fun _ : Leg ↦ CWBlock) cycle t = s :=
      ⟨_, Equiv.apply_symm_apply _ _⟩
    obtain ⟨x, y, z, rfl⟩ :
        ∃ x y z, ofLegs (V := fun _ : Leg ↦ CWBlock) x y z = t :=
      ⟨t Leg.X, t Leg.Y, t Leg.Z, ofLegs_eta t⟩
    refine map_blockInclude_injective (K := K)
      (V := PermutedBlockSpace cycle (CWPartitionBlockSpace K q)) _ ?_
    have haddr : permuteBlockAddress (A := fun _ : Leg ↦ CWBlock) cycle
        (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z) =
        ofLegs (V := fun _ : Leg ↦ CWBlock) z x y := by
      funext c
      cases c <;> rfl
    have hR := congrArg
      (fun a ↦ map (blockInclude (K := K) (V := CWPartitionBlockSpace K q) a)
        ((cwPartitionedTensor K q).constituent a)) haddr
    have hinc : ∀ c : Leg,
        blockInclude (K := K) (V := CWPartitionBlockSpace K q)
            (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z) (cycle.symm c) =
          (blockInclude (K := K) (V := CWPartitionBlockSpace K q)
            (ofLegs (V := fun _ : Leg ↦ CWBlock) z x y) c).comp
            (cwBaseConstituentCycleEquiv K q x y z c).toLinearMap := by
      intro c
      cases c <;> rfl
    have hL := PartitionedTensor.map_blockInclude_permute_constituent
      (cwPartitionedTensor K q) cycle (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z)
    have hkey :
        Tensor.permute cycle
            (map (blockInclude (K := K) (V := CWPartitionBlockSpace K q)
                (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z))
              (cwPartitionConstituent K q (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z))) =
          map (blockInclude (K := K) (V := CWPartitionBlockSpace K q)
              (ofLegs (V := fun _ : Leg ↦ CWBlock) z x y))
            (cwPartitionConstituent K q (ofLegs (V := fun _ : Leg ↦ CWBlock) z x y)) := by
      rw [cwPartitionConstituent_ofLegs, cwPartitionConstituent_ofLegs,
        ← PiTensorProduct.map_reindex
          (blockInclude (K := K) (V := CWPartitionBlockSpace K q)
            (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z)) cycle,
        ← cwConstituentOfBlocks_cycle_of_all K q x y z, funext hinc]
      exact LinearMap.congr_fun
        (map_comp (fun c ↦ (cwBaseConstituentCycleEquiv K q x y z c).toLinearMap)
          (blockInclude (K := K) (V := CWPartitionBlockSpace K q)
            (ofLegs (V := fun _ : Leg ↦ CWBlock) z x y))) _
    exact hL.trans (hkey.trans hR.symm)

/-- **Rotating the legs of the CW partition backwards returns the CW partition.**  The mirror image
of `cwPartitionedTensor_permute_cycle`, at `cycle.symm`. -/
theorem cwPartitionedTensor_permute_cycleSymm :
    (cwPartitionedTensor K q).permute cycle.symm = cwPartitionedTensor K q := by
  classical
  apply PartitionedTensor.ext
  · ext s
    rw [PartitionedTensor.mem_permute_support, cwBlockAddress_permute_cycleSymm_symm]
    show (ofLegs (V := fun _ : Leg ↦ CWBlock) (s Leg.Z) (s Leg.X) (s Leg.Y) ∈ cwBlockSupport)
      ↔ (s ∈ cwBlockSupport)
    rw [mem_cwBlockSupport_ofLegs_cycleSymm (s Leg.X) (s Leg.Y) (s Leg.Z), ofLegs_eta]
  · funext s
    obtain ⟨t, rfl⟩ :
        ∃ t, permuteBlockAddress (A := fun _ : Leg ↦ CWBlock) cycle.symm t = s :=
      ⟨_, Equiv.apply_symm_apply _ _⟩
    obtain ⟨x, y, z, rfl⟩ :
        ∃ x y z, ofLegs (V := fun _ : Leg ↦ CWBlock) x y z = t :=
      ⟨t Leg.X, t Leg.Y, t Leg.Z, ofLegs_eta t⟩
    refine map_blockInclude_injective (K := K)
      (V := PermutedBlockSpace cycle.symm (CWPartitionBlockSpace K q)) _ ?_
    have haddr : permuteBlockAddress (A := fun _ : Leg ↦ CWBlock) cycle.symm
        (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z) =
        ofLegs (V := fun _ : Leg ↦ CWBlock) y z x := by
      funext c
      cases c <;> rfl
    have hR := congrArg
      (fun a ↦ map (blockInclude (K := K) (V := CWPartitionBlockSpace K q) a)
        ((cwPartitionedTensor K q).constituent a)) haddr
    have hinc : ∀ c : Leg,
        blockInclude (K := K) (V := CWPartitionBlockSpace K q)
            (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z) (cycle.symm.symm c) =
          (blockInclude (K := K) (V := CWPartitionBlockSpace K q)
            (ofLegs (V := fun _ : Leg ↦ CWBlock) y z x) c).comp
            (cwBaseConstituentCycleSymmEquiv K q x y z c).toLinearMap := by
      intro c
      cases c <;> rfl
    have hL := PartitionedTensor.map_blockInclude_permute_constituent
      (cwPartitionedTensor K q) cycle.symm (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z)
    have hkey :
        Tensor.permute cycle.symm
            (map (blockInclude (K := K) (V := CWPartitionBlockSpace K q)
                (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z))
              (cwPartitionConstituent K q (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z))) =
          map (blockInclude (K := K) (V := CWPartitionBlockSpace K q)
              (ofLegs (V := fun _ : Leg ↦ CWBlock) y z x))
            (cwPartitionConstituent K q (ofLegs (V := fun _ : Leg ↦ CWBlock) y z x)) := by
      rw [cwPartitionConstituent_ofLegs, cwPartitionConstituent_ofLegs,
        ← PiTensorProduct.map_reindex
          (blockInclude (K := K) (V := CWPartitionBlockSpace K q)
            (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z)) cycle.symm,
        ← cwConstituentOfBlocks_cycleSymm_of_all K q x y z, funext hinc]
      exact LinearMap.congr_fun
        (map_comp (fun c ↦ (cwBaseConstituentCycleSymmEquiv K q x y z c).toLinearMap)
          (blockInclude (K := K) (V := CWPartitionBlockSpace K q)
            (ofLegs (V := fun _ : Leg ↦ CWBlock) y z x))) _
    exact hL.trans (hkey.trans hR.symm)

end AlgebraicComplexity.Examples
