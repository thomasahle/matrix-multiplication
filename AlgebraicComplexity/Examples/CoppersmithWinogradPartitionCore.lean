/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradPartitionDataCore
import AlgebraicComplexity.Tensor.Partitioned
import Mathlib.LinearAlgebra.Pi

/-!
# Lightweight typed partition of the Coppersmith--Winograd tensor

This module adds the direct-sum coordinate equivalence for the exact finite partition defined in
`CoppersmithWinogradPartitionDataCore`.  Matrix-multiplication restrictions and value certificates
remain in the public re-exporting module `CoppersmithWinogradPartition`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped DirectSum

universe u

/-- Currying two block-coordinate singles gives the corresponding single on the sigma index. -/
theorem sigma_uncurry_single_cwBlockBasis (K : Type u) [AddMonoidWithOne K]
    (q : ℕ) (a : CWBlock) (i : CWBlockIndex q a) :
    Sigma.uncurry
        (Pi.single a (cwBlockBasis K q a i) :
          ∀ a : CWBlock, CWBlockIndex q a → K) =
      (Pi.single ⟨a, i⟩ (1 : K) : (Σ a : CWBlock, CWBlockIndex q a) → K) := by
  funext x
  rcases x with ⟨b, j⟩
  by_cases h : b = a
  · subst b
    simp [Sigma.uncurry, Pi.single_apply, cwBlockBasis_apply]
  · have hs : (⟨b, j⟩ : Σ a : CWBlock, CWBlockIndex q a) ≠ ⟨a, i⟩ := by
      intro hs
      exact h (congrArg Sigma.fst hs)
    simp [Sigma.uncurry, h, hs]

section

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- Canonical equivalence from the direct sum of the three CW blocks to the original coordinate
space. -/
noncomputable def cwPartitionSpaceEquiv (c : Leg) :
    PartitionedSpace K (CWPartitionBlockSpace K q) c ≃ₗ[K] CWSpace K q c :=
  DirectSum.linearEquivFunOnFintype K CWBlock
      (fun a ↦ CWBlockIndex q a → K) ≪≫ₗ
    (LinearEquiv.piCurry K (fun _ : CWBlock ↦ fun _ : CWBlockIndex q _ ↦ K)).symm ≪≫ₗ
    LinearEquiv.piCongrLeft K (fun _ : CWIndex q ↦ K) (cwBlockIndexEquiv q)

/-- Legwise form of `cwPartitionSpaceEquiv`. -/
noncomputable def cwPartitionMap :
    ∀ c, PartitionedSpace K (CWPartitionBlockSpace K q) c →ₗ[K] CWSpace K q c :=
  fun c ↦ (cwPartitionSpaceEquiv K q c).toLinearMap

/-- A block coordinate vector is sent to the corresponding original CW coordinate vector. -/
@[simp] theorem cwPartitionSpaceEquiv_lof_basis
    (c : Leg) (a : CWBlock) (i : CWBlockIndex q a) :
    cwPartitionSpaceEquiv K q c
        (DirectSum.lof K CWBlock (fun a ↦ CWBlockIndex q a → K) a
          (cwBlockBasis K q a i)) =
      cwBasis K q (cwBlockIndexEquiv q ⟨a, i⟩) := by
  simp only [cwPartitionSpaceEquiv, LinearEquiv.trans_apply,
    DirectSum.linearEquivFunOnFintype_lof, LinearEquiv.piCurry_symm_apply,
    cwBasis]
  rw [sigma_uncurry_single_cwBlockBasis]
  ext j
  change
    (Equiv.piCongrLeft (fun _ : CWIndex q ↦ K) (cwBlockIndexEquiv q))
        (Pi.single ⟨a, i⟩ (1 : K) :
          (Σ a : CWBlock, CWBlockIndex q a) → K) j =
      (Pi.single (cwBlockIndexEquiv q ⟨a, i⟩) (1 : K) : CWIndex q → K) j
  rw [Equiv.piCongrLeft_apply]
  simp only [eq_rec_constant]
  by_cases h : j = cwBlockIndexEquiv q ⟨a, i⟩
  · subst j
    simp
  · have h' : (cwBlockIndexEquiv q).symm j ≠ ⟨a, i⟩ := by
      intro h'
      apply h
      rw [← h', Equiv.apply_symm_apply]
    simp [h, h']

end

end AlgebraicComplexity.Examples
