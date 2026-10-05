/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradExactSelectionCore
import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorRealization

/-!
# Lightweight exact CW interface-term realization

This module combines the dependency-light native split-word encoding from
`CoppersmithWinogradSplitWordCore` with exact profile data, the chunk partition, and the direct
selected-term restriction.  Nested flat-power coherence and heterogeneous interface products
remain in the public re-exporting module `CoppersmithWinogradInterface`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- Level-one constituent address associated to a supported base CW block triple. -/
def cwLevelOneIndex (address : cwBlockSupport) : LevelConstituentIndex 0 where
  count c := cwBlockDigit (address.1 c)
  total := by
    simpa using cwBlockSupport_digit_sum address.1 address.2

@[simp] theorem cwLevelOneIndex_count (address : cwBlockSupport) (c : Leg) :
    (cwLevelOneIndex address).count c = cwBlockDigit (address.1 c) :=
  rfl

/-- The exact one-sample complete-split profile on one leg of a base CW constituent. -/
noncomputable def cwLevelOneSplitProfile (address : cwBlockSupport) (c : Leg) :
    CompleteSplitProfile 0 ((cwLevelOneIndex address).count c) 1 :=
  CompleteSplitProfile.singleton (cwBlockSplitWord (address.1 c)) (by simp)

/-- Exact interface metadata for one base CW constituent. -/
noncomputable def cwLevelOneExactInterfaceTerm (address : cwBlockSupport) :
    ExactInterfaceTermParameters 0 where
  multiplicity := 1
  index := cwLevelOneIndex address
  split := cwLevelOneSplitProfile address

@[simp] theorem cwLevelOneExactInterfaceTerm_multiplicity (address : cwBlockSupport) :
    (cwLevelOneExactInterfaceTerm address).multiplicity = 1 :=
  rfl

/-- Positive packaging of a supported base CW constituent for interface-product assembly. -/
noncomputable def cwLevelOnePositiveExactInterfaceTerm (address : cwBlockSupport) :
    PositiveExactInterfaceTermParameters 0 where
  term := cwLevelOneExactInterfaceTerm address
  multiplicity_pos := Nat.zero_lt_one

/-- A two-term exact parameter list used as a minimal regression test for heterogeneous interface
products. -/
noncomputable def cwLevelOnePairParameters (left right : cwBlockSupport) :
    PositiveWord (PositiveExactInterfaceTermParameters 0) 1 :=
  (cwLevelOnePositiveExactInterfaceTerm left, cwLevelOnePositiveExactInterfaceTerm right)

section

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- Chunking does not change the represented tensor: the chunk partition is canonically
isomorphic to the `2^depth`-th tensor power of `CW_q`. -/
theorem cwChunkPartitionedTensor_isomorphic_power (depth : ℕ) :
    Isomorphic (Tensor.power (cwPartitionedTensor K q).realize (2 ^ depth))
      (cwChunkPartitionedTensor K q depth).realize := by
  have h := Tensor.Isomorphic.power_partitionedPositivePower
    (cwPartitionedTensor K q) (2 ^ depth - 1)
  rw [two_pow_sub_one_add_one] at h
  exact h

/-- Every permutation of the `n+1` selected samples is a genuine structure-preserving
relabeling of the concrete CW interface term. -/
noncomputable def cwSelectedExactInterfaceTermPositionRelabeling {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Equiv.Perm (Fin (n + 1))) :
    (cwSelectedExactInterfaceTerm K q term hmultiplicity).StructureRelabeling :=
  (cwChunkPartitionedTensor K q depth).selectEncodedExactInterfaceTermPositionRelabeling
    (fun _c ↦ cwChunkSplitWord depth) term hmultiplicity sigma

/-- Every exact recursive interface term is an actual restriction of the corresponding power of
the concrete CW chunk tensor. -/
theorem cwSelectedExactInterfaceTerm_restricts {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :
    Restricts
      (Tensor.power (cwChunkPartitionedTensor K q depth).realize (n + 1))
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize :=
  Tensor.Restricts.power_selectEncodedExactInterfaceTerm
    (cwChunkPartitionedTensor K q depth) (fun _c ↦ cwChunkSplitWord depth)
    term hmultiplicity

end


end AlgebraicComplexity.Examples
