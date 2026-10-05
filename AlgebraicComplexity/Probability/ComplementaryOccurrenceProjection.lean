/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ComplementaryOccurrenceLaw
import AlgebraicComplexity.Probability.ComplementaryProductProjectionMarginals
import AlgebraicComplexity.Probability.IntegralProfileProbabilityCore
import AlgebraicComplexity.Probability.ReindexBasic

/-!
# Normalizing exact complementary-occurrence tables

An integral ordered-state profile and a labelled complementary-occurrence law determine the
finite probability model used by pooled-parent concentration.  The ordered state is normalized
directly.  At a child state `u`, the child-symbol law is the normalized sum of the labelled left
occurrences at `u` and labelled right occurrences whose child is `u`.

Zero occurrence rows are filled by an arbitrary point mass.  They carry zero weight in both
labelled marginals, and the theorems below prove that this convention disappears from every
observable pooled count.  Self-complementary states retain both labelled occurrences.
-/

open scoped BigOperators

namespace AlgebraicComplexity
namespace ComplementaryOccurrenceLaw

universe u v

variable {State : Type u} [Fintype State] [DecidableEq State]
variable {Symbol : Type v} [Fintype Symbol] [DecidableEq Symbol] [Nonempty Symbol]
variable {profile : State → ℕ}

/-- Integral mass of the two labelled occurrences whose child state is `state`. -/
def childOccurrenceMass (profile : State → ℕ)
    (complement : Equiv.Perm State) (state : State) : ℕ :=
  profile state + profile (complement.symm state)

/-- With the identity cell map, the pushed occurrence profile is the literal complementary
occurrence mass. -/
theorem complementaryOccurrenceCellProfile_id
    (profile : State → ℕ) (complement : Equiv.Perm State) (state : State) :
    complementaryOccurrenceCellProfile profile complement id state =
      childOccurrenceMass profile complement state := by
  classical
  rw [complementaryOccurrenceCellProfile_eq_evaluator]
  simp [evaluatorComplementaryCellProfile, childOccurrenceMass]

omit [DecidableEq Symbol] [Nonempty Symbol] in
/-- The exact pooled symbol row at a child state has the corresponding labelled-occurrence
mass. -/
theorem sum_cellJointProfile_id
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (state : State) :
    (∑ symbol, law.cellJointProfile complement id (state, symbol)) =
      childOccurrenceMass profile complement state := by
  calc
    (∑ symbol, law.cellJointProfile complement id (state, symbol)) =
        WordType.mappedType Prod.fst (law.cellJointProfile complement id) state :=
      (mappedType_fst_apply _ _).symm
    _ = complementaryOccurrenceCellProfile profile complement id state :=
      congrFun (law.mappedType_fst_cellJointProfile complement id) state
    _ = childOccurrenceMass profile complement state :=
      complementaryOccurrenceCellProfile_id profile complement state

omit [DecidableEq Symbol] [Nonempty Symbol] in
/-- The pooled symbol row, viewed as an integral profile, has the expected mass. -/
theorem profileMass_cellJointProfile_id
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (state : State) :
    WordType.profileMass (fun symbol ↦
      law.cellJointProfile complement id (state, symbol)) =
        childOccurrenceMass profile complement state := by
  exact sum_cellJointProfile_id law complement state

/-- Normalize one pooled child-symbol row.  A zero row receives an irrelevant point mass. -/
noncomputable def normalizedChildLaw
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (state : State) : ProbabilityVector Symbol := by
  classical
  by_cases hmass : 0 < childOccurrenceMass profile complement state
  · exact WordType.normalizedProfileProbability
      (fun symbol ↦ law.cellJointProfile complement id (state, symbol)) (by
        rw [profileMass_cellJointProfile_id]
        exact hmass)
  · exact ProbabilityVector.pointMass (Classical.choice inferInstance)

/-- Positive pooled rows normalize by their literal occurrence mass. -/
theorem normalizedChildLaw_weight_of_pos
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (state : State)
    (hmass : 0 < childOccurrenceMass profile complement state) (symbol : Symbol) :
    (law.normalizedChildLaw complement state).weight symbol =
      (law.cellJointProfile complement id (state, symbol) : ℝ) /
        childOccurrenceMass profile complement state := by
  classical
  simp only [normalizedChildLaw, hmass, dite_true,
    WordType.normalizedProfileProbability_weight]
  rw [profileMass_cellJointProfile_id]

/-- Multiplying a normalized child law by its occurrence mass recovers the exact integer row.
This statement also covers structural-zero rows. -/
theorem childOccurrenceMass_mul_normalizedChildLaw_weight
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (state : State) (symbol : Symbol) :
    (childOccurrenceMass profile complement state : ℝ) *
        (law.normalizedChildLaw complement state).weight symbol =
      law.cellJointProfile complement id (state, symbol) := by
  classical
  by_cases hmass : 0 < childOccurrenceMass profile complement state
  · rw [normalizedChildLaw_weight_of_pos law complement state hmass]
    field_simp
  · have hzero : childOccurrenceMass profile complement state = 0 :=
      Nat.eq_zero_of_not_pos hmass
    have hrow : law.cellJointProfile complement id (state, symbol) = 0 := by
      have hle : law.cellJointProfile complement id (state, symbol) ≤
          ∑ z, law.cellJointProfile complement id (state, z) :=
        Finset.single_le_sum
          (s := Finset.univ)
          (f := fun z ↦ law.cellJointProfile complement id (state, z))
          (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_univ symbol)
      rw [sum_cellJointProfile_id, hzero] at hle
      omega
    simp [hzero, hrow]

/-- Exact integral occurrence data normalized as a complementary-product projection model. -/
noncomputable def toComplementaryProductProjectionModel
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State)
    (hmass : 0 < WordType.profileMass profile) :
    ComplementaryProductProjectionModel State State Symbol where
  stateLaw := WordType.normalizedProfileProbability profile hmass
  complement := complement
  cellOf := id
  childLaw := law.normalizedChildLaw complement

@[simp] theorem toComplementaryProductProjectionModel_stateLaw_weight
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State)
    (hmass : 0 < WordType.profileMass profile) (state : State) :
    (law.toComplementaryProductProjectionModel complement hmass).stateLaw.weight state =
      (profile state : ℝ) / WordType.profileMass profile :=
  rfl

@[simp] theorem toComplementaryProductProjectionModel_complement
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State)
    (hmass : 0 < WordType.profileMass profile) :
    (law.toComplementaryProductProjectionModel complement hmass).complement = complement :=
  rfl

@[simp] theorem toComplementaryProductProjectionModel_cellOf
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State)
    (hmass : 0 < WordType.profileMass profile) :
    (law.toComplementaryProductProjectionModel complement hmass).cellOf = id :=
  rfl

@[simp] theorem toComplementaryProductProjectionModel_childLaw
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State)
    (hmass : 0 < WordType.profileMass profile) (state : State) :
    (law.toComplementaryProductProjectionModel complement hmass).childLaw state =
      law.normalizedChildLaw complement state :=
  rfl

/-- The normalized model's pooled labelled-feature marginal is exactly the normalized integral
occurrence/symbol table. -/
theorem toComplementaryProductProjectionModel_reference_pooledFeature_weight
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State)
    (hmass : 0 < WordType.profileMass profile)
    (state : State) (symbol : Symbol) :
    let M := law.toComplementaryProductProjectionModel complement hmass
    (M.reference.pushforward M.leftFeature).weight (state, symbol) +
        (M.reference.pushforward M.rightFeature).weight (state, symbol) =
      (law.cellJointProfile complement id (state, symbol) : ℝ) /
        WordType.profileMass profile := by
  classical
  let M := law.toComplementaryProductProjectionModel complement hmass
  change (M.reference.pushforward M.leftFeature).weight (state, symbol) +
      (M.reference.pushforward M.rightFeature).weight (state, symbol) = _
  rw [M.reference_pooledFeature_weight]
  have hid : (M.stateLaw.pushforward M.cellOf).weight state =
      M.stateLaw.weight state := by
    change (M.stateLaw.pushforward id).weight state = M.stateLaw.weight state
    rw [ProbabilityVector.pushforward_weight]
    simp
  have hcomplement :
      (M.stateLaw.pushforward (M.cellOf ∘ M.complement)).weight state =
        M.stateLaw.weight (complement.symm state) := by
    change (M.stateLaw.pushforward complement).weight state = _
    rw [← ProbabilityVector.reindex_eq_pushforward complement]
    rfl
  rw [hid, hcomplement]
  change (((profile state : ℝ) / WordType.profileMass profile) +
      ((profile (complement.symm state) : ℝ) /
        WordType.profileMass profile)) *
      (law.normalizedChildLaw complement state).weight symbol = _
  rw [← add_div]
  rw [← Nat.cast_add]
  change ((childOccurrenceMass profile complement state : ℝ) /
      WordType.profileMass profile) *
        (law.normalizedChildLaw complement state).weight symbol = _
  rw [div_mul_eq_mul_div,
    childOccurrenceMass_mul_normalizedChildLaw_weight]

end ComplementaryOccurrenceLaw
end AlgebraicComplexity
