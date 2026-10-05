/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradInterfaceCore
import AlgebraicComplexity.Examples.CoppersmithWinogradPartition
import AlgebraicComplexity.Tensor.PowerCoherence

/-!
# Coppersmith--Winograd interface-term realization

This client connects the standard three-block CW partition to the reusable complete-split API.
At zero-based depth `0`, a split word has one ternary digit, so the three CW block labels encode as
`0`, `1`, and `2`.  We construct the exact singleton interface term for every supported CW
constituent and prove that its tensor realization is obtained from the canonical tensor power by
an actual variable restriction.

Besides being the base case for recursive CW interface tensors, this is a small regression test
for the direction of profile selection and the depth convention.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

section

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- Re-express the source as a nested canonical power of the original partitioned CW tensor. -/
theorem cwNestedPower_selectedExactInterfaceTerm_restricts {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :
    Restricts
      (Tensor.power
        (Tensor.power (cwPartitionedTensor K q).realize (2 ^ depth)) (n + 1))
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize :=
  ((cwChunkPartitionedTensor_isomorphic_power K q depth).restricts.power (n + 1)).trans
    (cwSelectedExactInterfaceTerm_restricts K q term hmultiplicity)

/-- Paper-facing flat-power form: the single `2^depth * (n+1)`th power of `CW_q` restricts to
every exact level-`depth+1` interface term. -/
theorem cwFlatPower_selectedExactInterfaceTerm_restricts {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :
    Restricts
      (Tensor.power (cwPartitionedTensor K q).realize (2 ^ depth * (n + 1)))
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize :=
  ((Tensor.Isomorphic.power_power_mul_comm
      (cwPartitionedTensor K q).realize (2 ^ depth) (n + 1)).symm.restricts).trans
    (cwNestedPower_selectedExactInterfaceTerm_restricts K q term hmultiplicity)

/-- Assemble a nonempty exact CW interface-tensor parameter list into one heterogeneous target
tensor, retaining its certified source power. -/
noncomputable def cwExactInterfacePowerProduct {depth termCount : ℕ}
    (terms : PositiveWord (PositiveExactInterfaceTermParameters depth) termCount) :=
  (cwChunkPartitionedTensor K q depth).encodedExactInterfacePowerProduct
    (fun _c ↦ cwChunkSplitWord depth) termCount terms

/-- Exact finite form of the paper's interface-tensor definition: the single flat power
`CW_q^(2^depth * Σ_t n_t)` restricts to the external product of all selected exact terms. -/
theorem cwFlatPower_exactInterfacePowerProduct_restricts {depth termCount : ℕ}
    (terms : PositiveWord (PositiveExactInterfaceTermParameters depth) termCount) :
    Restricts
      (Tensor.power (cwPartitionedTensor K q).realize
        (2 ^ depth *
          positiveWordSum (fun term ↦ term.term.multiplicity) termCount terms))
      (cwExactInterfacePowerProduct K q terms).target := by
  let totalMultiplicity :=
    positiveWordSum (fun term ↦ term.term.multiplicity) termCount terms
  have hflatten : Restricts
      (Tensor.power (cwPartitionedTensor K q).realize (2 ^ depth * totalMultiplicity))
      (Tensor.power
        (Tensor.power (cwPartitionedTensor K q).realize (2 ^ depth))
        totalMultiplicity) :=
    (Tensor.Isomorphic.power_power_mul_comm
      (cwPartitionedTensor K q).realize (2 ^ depth) totalMultiplicity).symm.restricts
  have hchunk : Restricts
      (Tensor.power
        (Tensor.power (cwPartitionedTensor K q).realize (2 ^ depth))
        totalMultiplicity)
      (Tensor.power (cwChunkPartitionedTensor K q depth).realize totalMultiplicity) :=
    (cwChunkPartitionedTensor_isomorphic_power K q depth).restricts.power totalMultiplicity
  have hselect : Restricts
      (Tensor.power (cwChunkPartitionedTensor K q depth).realize totalMultiplicity)
      (cwExactInterfacePowerProduct K q terms).target := by
    exact Tensor.Restricts.power_encodedExactInterfacePowerProduct
      (cwChunkPartitionedTensor K q depth) (fun _c ↦ cwChunkSplitWord depth)
      termCount terms
  exact hflatten.trans (hchunk.trans hselect)

/-- Tiny two-term regression: the second canonical power of `CW_q` restricts to the external
product selected by any pair of supported level-one constituents. -/
theorem cwLevelOnePairInterfaceProduct_restricts (left right : cwBlockSupport) :
    Restricts
      (Tensor.power (cwPartitionedTensor K q).realize 2)
      (cwExactInterfacePowerProduct K q (cwLevelOnePairParameters left right)).target := by
  have hexponent : 2 =
      2 ^ 0 * positiveWordSum (fun term ↦ term.term.multiplicity) 1
        (cwLevelOnePairParameters left right) := by
    simp [cwLevelOnePairParameters, cwLevelOnePositiveExactInterfaceTerm,
      positiveWordSum]
  exact
    ((Tensor.Isomorphic.power_congr (cwPartitionedTensor K q).realize hexponent).restricts).trans
      (cwFlatPower_exactInterfacePowerProduct_restricts K q
        (cwLevelOnePairParameters left right))

/-- Tensor realization of the exact singleton interface term at a supported CW address. -/
noncomputable def cwLevelOneSelectedInterfaceTerm (address : cwBlockSupport) :=
  (cwPartitionedTensor K q).selectEncodedExactInterfaceTerm
    (fun _c ↦ cwBlockSplitWord) (cwLevelOneExactInterfaceTerm address) (n := 0) rfl

/-- The singleton profile keeps exactly the requested supported CW block address. -/
theorem cwLevelOneSelectedInterfaceTerm_support (address : cwBlockSupport) :
    (cwLevelOneSelectedInterfaceTerm K q address).support = {address.1} := by
  classical
  ext candidate
  unfold cwLevelOneSelectedInterfaceTerm
  unfold Tensor.PartitionedTensor.selectEncodedExactInterfaceTerm
  rw [Tensor.PartitionedTensor.mem_selectEncodedCompleteSplitProfiles_support]
  constructor
  · rintro ⟨_hcandidate, hprofile⟩
    apply Finset.mem_singleton.mpr
    funext c
    apply cwBlockSplitWord_injective
    have hc := hprofile c
    change
      (CompleteSplitProfile.singleton (cwBlockSplitWord (address.1 c))
        (by simp [cwLevelOneExactInterfaceTerm, cwLevelOneIndex])).IsConsistent
        (fun _ : Fin 1 ↦ cwBlockSplitWord (candidate c)) at hc
    exact (CompleteSplitProfile.singleton_isConsistent_const_iff _ _ _).mp hc
  · intro hcandidate
    have heq : candidate = address.1 := Finset.mem_singleton.mp hcandidate
    subst candidate
    refine ⟨?_, ?_⟩
    · change address.1 ∈ (cwPartitionedTensor K q).support
      exact address.2
    · intro c
      change
        (CompleteSplitProfile.singleton (cwBlockSplitWord (address.1 c))
          (by simp [cwLevelOneExactInterfaceTerm, cwLevelOneIndex])).IsConsistent
          (fun _ : Fin 1 ↦ cwBlockSplitWord (address.1 c))
      exact (CompleteSplitProfile.singleton_isConsistent_const_iff _ _ _).2 rfl

/-- The canonical first power of the partitioned CW tensor restricts to every exact singleton
interface term. -/
theorem cwLevelOneSelectedInterfaceTerm_restricts (address : cwBlockSupport) :
    Restricts (Tensor.power (cwPartitionedTensor K q).realize 1)
      (cwLevelOneSelectedInterfaceTerm K q address).realize :=
  Tensor.Restricts.power_selectEncodedExactInterfaceTerm
    (cwPartitionedTensor K q) (fun _c ↦ cwBlockSplitWord)
    (cwLevelOneExactInterfaceTerm address) (n := 0) rfl

end

end AlgebraicComplexity.Examples
