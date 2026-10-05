/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.ComplementaryOccurrenceCellProjection

set_option autoImplicit false

/-!
# Injective cell quotients of complementary occurrence laws

Pooling labelled child occurrences through an injective cell map changes only the name of each
state.  This module records that elementary fact at every level used by parent-consistency
arguments: exact joint rows, row masses, normalized child laws, the full conditional-product
reference, and arbitrary pushed parent laws.

The statements include zero-mass states.  Both the cell-quotiented and identity-state models use
the same irrelevant point mass there, so no full-support hypothesis is needed.
-/

namespace AlgebraicComplexity
namespace ComplementaryOccurrenceLaw

universe u v w x

variable {State : Type u} [Fintype State] [DecidableEq State]
variable {Symbol : Type v} [Fintype Symbol] [DecidableEq Symbol] [Nonempty Symbol]
variable {Cell : Type w} [Fintype Cell] [DecidableEq Cell]
variable {profile : State → ℕ}

omit [DecidableEq Symbol] [Nonempty Symbol] [Fintype Cell] in
/-- At a reachable injective cell, the pooled exact symbol row is the identity-state row. -/
theorem cellJointProfile_apply_of_injective
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (hcell : Function.Injective cellOf) (state : State) (symbol : Symbol) :
    law.cellJointProfile complement cellOf (cellOf state, symbol) =
      law.cellJointProfile complement id (state, symbol) := by
  classical
  unfold cellJointProfile
  apply Finset.sum_congr rfl
  intro occurrence _
  by_cases hstate : occurrence.childState complement = state
  · simp [hstate]
  · have hcellNe : cellOf (occurrence.childState complement) ≠ cellOf state :=
      fun heq ↦ hstate (hcell heq)
    simp [hstate, hcellNe]

omit [DecidableEq Symbol] [Nonempty Symbol] in
/-- An injective reachable cell has exactly the two-labelled-occurrence mass of its state. -/
theorem complementaryOccurrenceCellProfile_apply_of_injective
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (hcell : Function.Injective cellOf) (state : State) :
    complementaryOccurrenceCellProfile profile complement cellOf (cellOf state) =
      childOccurrenceMass profile complement state := by
  calc
    complementaryOccurrenceCellProfile profile complement cellOf (cellOf state) =
        ∑ symbol, law.cellJointProfile complement cellOf (cellOf state, symbol) :=
      (law.sum_cellJointProfile complement cellOf (cellOf state)).symm
    _ = ∑ symbol, law.cellJointProfile complement id (state, symbol) := by
      apply Finset.sum_congr rfl
      intro symbol _
      exact law.cellJointProfile_apply_of_injective
        complement cellOf hcell state symbol
    _ = childOccurrenceMass profile complement state :=
      law.sum_cellJointProfile_id complement state

/-- Normalizing after an injective cell quotient gives the identity-state child law. -/
theorem normalizedCellChildLaw_apply_of_injective
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (hcell : Function.Injective cellOf) (state : State) :
    law.normalizedCellChildLaw complement cellOf (cellOf state) =
      law.normalizedChildLaw complement state := by
  classical
  have hmass := law.complementaryOccurrenceCellProfile_apply_of_injective
    complement cellOf hcell state
  apply ProbabilityVector.ext
  funext symbol
  by_cases hpositive : 0 < childOccurrenceMass profile complement state
  · have hcellPositive :
        0 < complementaryOccurrenceCellProfile profile complement cellOf (cellOf state) := by
      rw [hmass]
      exact hpositive
    rw [law.normalizedCellChildLaw_weight_of_pos
        complement cellOf (cellOf state) hcellPositive,
      law.normalizedChildLaw_weight_of_pos complement state hpositive,
      law.cellJointProfile_apply_of_injective complement cellOf hcell state symbol,
      hmass]
  · have hcellNotPositive :
        ¬ 0 < complementaryOccurrenceCellProfile profile complement cellOf (cellOf state) := by
      rw [hmass]
      exact hpositive
    simp only [normalizedCellChildLaw, normalizedChildLaw,
      hcellNotPositive, hpositive, dite_false]

/-- The conditional-product reference is unchanged by an injective cell relabelling. -/
theorem toCellProductProjectionModel_reference_eq_identity_of_injective
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (hcell : Function.Injective cellOf)
    (hmass : 0 < WordType.profileMass profile) :
    (law.toCellProductProjectionModel complement cellOf hmass).reference =
      (law.toComplementaryProductProjectionModel complement hmass).reference := by
  apply ProbabilityVector.ext
  funext sample
  change
    (WordType.normalizedProfileProbability profile hmass).weight sample.1 *
        ((law.normalizedCellChildLaw complement cellOf (cellOf sample.1)).weight sample.2.1 *
          (law.normalizedCellChildLaw complement cellOf
            (cellOf (complement sample.1))).weight sample.2.2) =
      (WordType.normalizedProfileProbability profile hmass).weight sample.1 *
        ((law.normalizedChildLaw complement sample.1).weight sample.2.1 *
          (law.normalizedChildLaw complement (complement sample.1)).weight sample.2.2)
  rw [law.normalizedCellChildLaw_apply_of_injective complement cellOf hcell sample.1,
    law.normalizedCellChildLaw_apply_of_injective
      complement cellOf hcell (complement sample.1)]

/-- Consequently every parent statistic has the same pushed law before and after an injective
cell relabelling. -/
theorem toCellProductProjectionModel_parentLaw_eq_identity_of_injective
    {Parent : Type x} [Fintype Parent] [DecidableEq Parent]
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (hcell : Function.Injective cellOf)
    (hmass : 0 < WordType.profileMass profile)
    (join : Symbol × Symbol → Parent) :
    (law.toCellProductProjectionModel complement cellOf hmass).parentLaw join =
      (law.toComplementaryProductProjectionModel complement hmass).parentLaw join := by
  unfold ComplementaryProductProjectionModel.parentLaw
  rw [law.toCellProductProjectionModel_reference_eq_identity_of_injective
    complement cellOf hcell hmass]

end ComplementaryOccurrenceLaw
end AlgebraicComplexity
