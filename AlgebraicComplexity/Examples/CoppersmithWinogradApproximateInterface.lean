/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradInterface
import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorApproximateRealization

/-!
# Approximate Coppersmith--Winograd interface terms

This module instantiates the generic approximate complete-split selector for the native CW chunk
partition.  It is the source tensor used by the recursive constituent theorem: every selected
parent chunk has the fixed constituent coordinate, while the empirical split law on each leg may
range over the prescribed `L∞` neighborhood.

The resulting tensor is constructed directly by three variable zero-outs from a flat power of
`CW_q`.  In particular, no degeneration of an independently assembled child product is accepted
as a premise.  Exact interface terms embed into their normalized approximate counterparts, and
the full parent-position symmetric-group action is retained.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

section

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- The CW chunk tensor with the approximately prescribed semantic profile selected on all
three legs. -/
noncomputable def cwSelectedApproximateInterfaceTerm {depth n : ℕ}
    (term : InterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (epsilon : ℝ) :=
  (cwChunkPartitionedTensor K q depth).selectEncodedApproximateInterfaceTerm
    (fun _c ↦ cwChunkSplitWord depth) term hmultiplicity epsilon

/-- A flat source power restricts to every approximate CW interface term. -/
theorem cwFlatPower_selectedApproximateInterfaceTerm_restricts {depth n : ℕ}
    (term : InterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (epsilon : ℝ) :
    Restricts
      (Tensor.power (cwPartitionedTensor K q).realize (2 ^ depth * (n + 1)))
      (cwSelectedApproximateInterfaceTerm
        K q term hmultiplicity epsilon).realize := by
  have hflatten : Restricts
      (Tensor.power (cwPartitionedTensor K q).realize (2 ^ depth * (n + 1)))
      (Tensor.power
        (Tensor.power (cwPartitionedTensor K q).realize (2 ^ depth)) (n + 1)) :=
    (Tensor.Isomorphic.power_power_mul_comm
      (cwPartitionedTensor K q).realize (2 ^ depth) (n + 1)).symm.restricts
  have hchunk : Restricts
      (Tensor.power
        (Tensor.power (cwPartitionedTensor K q).realize (2 ^ depth)) (n + 1))
      (Tensor.power (cwChunkPartitionedTensor K q depth).realize (n + 1)) :=
    (cwChunkPartitionedTensor_isomorphic_power K q depth).restricts.power (n + 1)
  exact hflatten.trans (hchunk.trans
    (Tensor.Restricts.power_selectEncodedApproximateInterfaceTerm
      (cwChunkPartitionedTensor K q depth) (fun _c ↦ cwChunkSplitWord depth)
        term hmultiplicity epsilon))

/-- Approximate CW interface terms are invariant under arbitrary parent-position
permutations. -/
noncomputable def cwSelectedApproximateInterfaceTermPositionRelabeling {depth n : ℕ}
    (term : InterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (epsilon : ℝ)
    (sigma : Equiv.Perm (Fin (n + 1))) :
    (cwSelectedApproximateInterfaceTerm
      K q term hmultiplicity epsilon).StructureRelabeling :=
  (cwChunkPartitionedTensor K q depth).selectEncodedApproximateInterfaceTermPositionRelabeling
      (fun _c ↦ cwChunkSplitWord depth) term hmultiplicity epsilon sigma

/-- The concrete approximate-interface relabeling acts on native CW chunk words by the
advertised parent-position permutation. -/
@[simp] theorem cwSelectedApproximateInterfaceTermPositionRelabeling_partEquiv
    {depth n : ℕ}
    (term : InterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (epsilon : ℝ)
    (sigma : Equiv.Perm (Fin (n + 1))) (physicalLeg : Leg) :
    (cwSelectedApproximateInterfaceTermPositionRelabeling
      K q term hmultiplicity epsilon sigma).partEquiv physicalLeg =
      positiveWordPositionEquiv
        (PositiveWord CWBlock (2 ^ depth - 1)) n sigma := by
  unfold cwSelectedApproximateInterfaceTermPositionRelabeling
  exact
    Tensor.PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling_partEquiv
        (cwChunkPartitionedTensor K q depth) n sigma physicalLeg

/-- Every exact CW interface support lies in the corresponding approximate semantic interface
support at nonnegative tolerance. -/
theorem cwSelectedExactInterfaceTerm_support_subset_approximate {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    (cwSelectedExactInterfaceTerm K q term hmultiplicity).support ⊆
      (cwSelectedApproximateInterfaceTerm K q
        (term.toSemantic (hmultiplicity.symm ▸ Nat.zero_lt_succ n))
        (by simpa using hmultiplicity) epsilon).support :=
  Tensor.PartitionedTensor.selectEncodedExactInterfaceTerm_support_subset_approximate
    (cwChunkPartitionedTensor K q depth) (fun _c ↦ cwChunkSplitWord depth)
      term hmultiplicity hepsilon

end

end AlgebraicComplexity.Examples
