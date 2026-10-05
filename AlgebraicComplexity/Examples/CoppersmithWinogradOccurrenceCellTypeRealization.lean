/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradOrientedCellEncoding
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightOccurrenceClients

/-!
# Realizing recursive occurrence profiles as coarse CW addresses

Every ordered recursive state contributes two labelled child occurrences, left and right.  The
full tagged coarse-cell type induced by such a profile therefore has exactly twice the mass of the
state profile.  The labels remain distinct even when the two underlying child states coincide.

Combining this mass identity with the oriented-cell encoding produces the concrete reference
address required by the compatibility extraction.  The construction is finite and exact: it does
not use a hash seed, an asymptotic type estimate, or a tensor restriction.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- The full cell type contains one left and one right occurrence of every unit of state mass.

In particular, a self-complementary state still contributes twice: the two occurrences have
different `ComplementarySide` labels before the profile is pushed to coarse cells. -/
theorem profileMass_cwRecursiveOccurrenceFullCellType
    {State : Type u} [Fintype State]
    {Part : Type v} [Fintype Part]
    (depth : ℕ) (profile : State → ℕ)
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (htotal : ∀ occurrence,
      (coarseOf occurrence).x + (coarseOf occurrence).y +
        (coarseOf occurrence).z = coarseTotal depth) :
    WordType.profileMass
        (cwRecursiveOccurrenceFullCellType depth profile coarseOf htotal) =
      2 * WordType.profileMass profile := by
  classical
  unfold cwRecursiveOccurrenceFullCellType
  rw [WordType.profileMass_mappedType]
  exact ComplementaryOccurrence.sum_integralMass profile

/-- The recursive occurrence full-cell profile is a legal word type at twice the state-profile
mass. -/
theorem cwRecursiveOccurrenceFullCellType_mem_types
    {State : Type u} [Fintype State]
    {Part : Type v} [Fintype Part]
    (depth : ℕ) (profile : State → ℕ)
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (htotal : ∀ occurrence,
      (coarseOf occurrence).x + (coarseOf occurrence).y +
        (coarseOf occurrence).z = coarseTotal depth) :
    cwRecursiveOccurrenceFullCellType depth profile coarseOf htotal ∈
      WordType.types (CWOrientedCoarseCell Part depth)
        (2 * WordType.profileMass profile) := by
  rw [WordType.mem_types]
  exact profileMass_cwRecursiveOccurrenceFullCellType depth profile coarseOf htotal

/-- Repeating the state profile `k` times gives a legal full-cell word type at the correspondingly
repeated length. -/
theorem proportional_cwRecursiveOccurrenceFullCellType_mem_types
    {State : Type u} [Fintype State]
    {Part : Type v} [Fintype Part]
    (depth : ℕ) (profile : State → ℕ)
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (htotal : ∀ occurrence,
      (coarseOf occurrence).x + (coarseOf occurrence).y +
        (coarseOf occurrence).z = coarseTotal depth)
    (k : ℕ) :
    WordType.proportionalCounts
        (cwRecursiveOccurrenceFullCellType depth profile coarseOf htotal) k ∈
      WordType.types (CWOrientedCoarseCell Part depth)
        ((2 * WordType.profileMass profile) * k) := by
  have hlegal := WordType.proportionalCounts_mem_types
    (cwRecursiveOccurrenceFullCellType depth profile coarseOf htotal) k
  rw [profileMass_cwRecursiveOccurrenceFullCellType depth profile coarseOf htotal] at hlegal
  exact hlegal

/-- An exact sample-length equation turns the occurrence full-cell type into a concrete
identity-oriented position labelling and coarse address. -/
theorem exists_recursiveOccurrenceReference
    {State : Type u} [Fintype State]
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (profile : State → ℕ)
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (htotal : ∀ occurrence,
      (coarseOf occurrence).x + (coarseOf occurrence).y +
        (coarseOf occurrence).z = coarseTotal depth)
    (hsamples : n + 1 = 2 * WordType.profileMass profile) :
    ∃ (partAt : Fin (n + 1) → Part)
        (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)),
      WordType.multiplicity
          (cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) reference) =
        cwRecursiveOccurrenceFullCellType depth profile coarseOf htotal := by
  apply exists_partAt_address_multiplicity_eq_of_mem_types
  rw [hsamples]
  exact cwRecursiveOccurrenceFullCellType_mem_types depth profile coarseOf htotal

/-- Proportional form of `exists_recursiveOccurrenceReference`.  This is the finite realization
consumed by a proportional compatibility stage. -/
theorem exists_proportionalRecursiveOccurrenceReference
    {State : Type u} [Fintype State]
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (profile : State → ℕ)
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (htotal : ∀ occurrence,
      (coarseOf occurrence).x + (coarseOf occurrence).y +
        (coarseOf occurrence).z = coarseTotal depth)
    (k : ℕ) (hsamples : n + 1 = (2 * WordType.profileMass profile) * k) :
    ∃ (partAt : Fin (n + 1) → Part)
        (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)),
      WordType.multiplicity
          (cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) reference) =
        WordType.proportionalCounts
          (cwRecursiveOccurrenceFullCellType depth profile coarseOf htotal) k := by
  apply exists_partAt_address_multiplicity_eq_of_mem_types
  rw [hsamples]
  exact proportional_cwRecursiveOccurrenceFullCellType_mem_types
    depth profile coarseOf htotal k

/-- For a one-region recursive node, the position labelling is canonically constant and only the
coarse address needs to be chosen. -/
theorem exists_proportionalRecursiveOccurrenceReference_pUnit
    {State : Type u} [Fintype State]
    (depth n : ℕ) (profile : State → ℕ)
    (coarseOf : ComplementaryOccurrence State → CoarseIndex PUnit)
    (htotal : ∀ occurrence,
      (coarseOf occurrence).x + (coarseOf occurrence).y +
        (coarseOf occurrence).z = coarseTotal depth)
    (k : ℕ) (hsamples : n + 1 = (2 * WordType.profileMass profile) * k) :
    ∃ reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n),
      WordType.multiplicity
          (cwOrientedFiniteCellSequence depth n (fun _ ↦ PUnit.unit)
            (Equiv.refl Leg) reference) =
        WordType.proportionalCounts
          (cwRecursiveOccurrenceFullCellType depth profile coarseOf htotal) k := by
  apply exists_address_multiplicity_eq_of_mem_types_pUnit
  rw [hsamples]
  exact proportional_cwRecursiveOccurrenceFullCellType_mem_types
    depth profile coarseOf htotal k

end AlgebraicComplexity.Examples
