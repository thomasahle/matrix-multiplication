/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.ComplementaryOccurrenceProjection

/-!
# Normalizing complementary occurrences after a finite cell quotient

An exact labelled-occurrence table may be indexed more finely than the compatibility alphabet
used by a recursive tensor construction.  This module normalizes the table after an arbitrary
finite map from ordered child states to cells.  The resulting complementary-product reference has
exactly the normalized pooled cell/symbol marginal of the integral table.

Zero cell rows are filled by an arbitrary point mass, but their cell mass is zero, so the choice
does not affect the reference.  Both labelled occurrences remain present at a fixed point of the
complement permutation.
-/

open scoped BigOperators

namespace AlgebraicComplexity
namespace ComplementaryOccurrenceLaw

universe u v w

variable {State : Type u} [Fintype State] [DecidableEq State]
variable {Symbol : Type v} [Fintype Symbol] [DecidableEq Symbol] [Nonempty Symbol]
variable {Cell : Type w} [Fintype Cell] [DecidableEq Cell]
variable {profile : State → ℕ}

omit [DecidableEq State] [DecidableEq Symbol] [Nonempty Symbol] [Fintype Cell] in
/-- The two ordinary state pushforwards are the labelled complementary-occurrence cell profile. -/
theorem mappedType_add_mappedType_comp_complement
    (profile : State → ℕ) (complement : Equiv.Perm State)
    (cellOf : State → Cell) (cell : Cell) :
    WordType.mappedType cellOf profile cell +
        WordType.mappedType (cellOf ∘ complement) profile cell =
      complementaryOccurrenceCellProfile profile complement cellOf cell := by
  classical
  have hreindex :
      (∑ state, if cellOf (complement state) = cell then profile state else 0) =
        ∑ child, if cellOf child = cell then
          profile (complement.symm child) else 0 := by
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.sum_comp complement
        (fun child ↦ if cellOf child = cell then
          profile (complement.symm child) else 0))
  rw [WordType.mappedType_eq_sum_ite, WordType.mappedType_eq_sum_ite,
    complementaryOccurrenceCellProfile_eq_evaluator]
  unfold evaluatorComplementaryCellProfile
  change
    (∑ state, if cellOf state = cell then profile state else 0) +
        (∑ state, if cellOf (complement state) = cell then profile state else 0) = _
  rw [hreindex, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro child _
  by_cases hcell : cellOf child = cell <;> simp [hcell]

omit [DecidableEq State] [DecidableEq Symbol] [Nonempty Symbol] in
/-- The mass of a pooled cell/symbol row is its complementary-occurrence cell mass. -/
theorem sum_cellJointProfile
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell) (cell : Cell) :
    (∑ symbol, law.cellJointProfile complement cellOf (cell, symbol)) =
      complementaryOccurrenceCellProfile profile complement cellOf cell := by
  calc
    (∑ symbol, law.cellJointProfile complement cellOf (cell, symbol)) =
        WordType.mappedType Prod.fst
          (law.cellJointProfile complement cellOf) cell :=
      (mappedType_fst_apply _ _).symm
    _ = complementaryOccurrenceCellProfile profile complement cellOf cell :=
      congrFun (law.mappedType_fst_cellJointProfile complement cellOf) cell

omit [DecidableEq State] [DecidableEq Symbol] [Nonempty Symbol] in
/-- The pooled row, viewed as an integral symbol profile, has the expected cell mass. -/
theorem profileMass_cellJointProfile
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell) (cell : Cell) :
    WordType.profileMass
        (fun symbol ↦ law.cellJointProfile complement cellOf (cell, symbol)) =
      complementaryOccurrenceCellProfile profile complement cellOf cell := by
  exact sum_cellJointProfile law complement cellOf cell

/-- Normalize one pooled cell/symbol row.  A zero row receives an irrelevant point mass. -/
noncomputable def normalizedCellChildLaw
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (cell : Cell) : ProbabilityVector Symbol := by
  classical
  by_cases hmass :
      0 < complementaryOccurrenceCellProfile profile complement cellOf cell
  · exact WordType.normalizedProfileProbability
      (fun symbol ↦ law.cellJointProfile complement cellOf (cell, symbol)) (by
        rw [profileMass_cellJointProfile]
        exact hmass)
  · exact ProbabilityVector.pointMass (Classical.choice inferInstance)

omit [DecidableEq State] in
/-- Positive pooled rows normalize by their literal complementary-occurrence cell mass. -/
theorem normalizedCellChildLaw_weight_of_pos
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell) (cell : Cell)
    (hmass : 0 < complementaryOccurrenceCellProfile profile complement cellOf cell)
    (symbol : Symbol) :
    (law.normalizedCellChildLaw complement cellOf cell).weight symbol =
      (law.cellJointProfile complement cellOf (cell, symbol) : ℝ) /
        complementaryOccurrenceCellProfile profile complement cellOf cell := by
  classical
  simp only [normalizedCellChildLaw, hmass, dite_true,
    WordType.normalizedProfileProbability_weight]
  rw [profileMass_cellJointProfile]

omit [DecidableEq State] in
/-- Multiplying a normalized cell law by its cell mass recovers the exact integer row,
including when that row is structurally zero. -/
theorem cellMass_mul_normalizedCellChildLaw_weight
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (cell : Cell) (symbol : Symbol) :
    (complementaryOccurrenceCellProfile profile complement cellOf cell : ℝ) *
        (law.normalizedCellChildLaw complement cellOf cell).weight symbol =
      law.cellJointProfile complement cellOf (cell, symbol) := by
  classical
  by_cases hmass :
      0 < complementaryOccurrenceCellProfile profile complement cellOf cell
  · rw [normalizedCellChildLaw_weight_of_pos law complement cellOf cell hmass]
    field_simp
  · have hzero :
        complementaryOccurrenceCellProfile profile complement cellOf cell = 0 :=
      Nat.eq_zero_of_not_pos hmass
    have hrow : law.cellJointProfile complement cellOf (cell, symbol) = 0 := by
      have hle : law.cellJointProfile complement cellOf (cell, symbol) ≤
          ∑ z, law.cellJointProfile complement cellOf (cell, z) :=
        Finset.single_le_sum
          (s := Finset.univ)
          (f := fun z ↦ law.cellJointProfile complement cellOf (cell, z))
          (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_univ symbol)
      rw [sum_cellJointProfile, hzero] at hle
      omega
    simp [hzero, hrow]

/-- Exact integral occurrence data normalized after an arbitrary finite cell quotient. -/
noncomputable def toCellProductProjectionModel
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (hmass : 0 < WordType.profileMass profile) :
    ComplementaryProductProjectionModel State Cell Symbol where
  stateLaw := WordType.normalizedProfileProbability profile hmass
  complement := complement
  cellOf := cellOf
  childLaw := law.normalizedCellChildLaw complement cellOf

omit [DecidableEq State] in
@[simp] theorem toCellProductProjectionModel_stateLaw_weight
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (hmass : 0 < WordType.profileMass profile) (state : State) :
    (law.toCellProductProjectionModel complement cellOf hmass).stateLaw.weight state =
      (profile state : ℝ) / WordType.profileMass profile :=
  rfl

omit [DecidableEq State] in
@[simp] theorem toCellProductProjectionModel_complement
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (hmass : 0 < WordType.profileMass profile) :
    (law.toCellProductProjectionModel complement cellOf hmass).complement = complement :=
  rfl

omit [DecidableEq State] in
@[simp] theorem toCellProductProjectionModel_cellOf
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (hmass : 0 < WordType.profileMass profile) :
    (law.toCellProductProjectionModel complement cellOf hmass).cellOf = cellOf :=
  rfl

omit [DecidableEq State] in
@[simp] theorem toCellProductProjectionModel_childLaw
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (hmass : 0 < WordType.profileMass profile) (cell : Cell) :
    (law.toCellProductProjectionModel complement cellOf hmass).childLaw cell =
      law.normalizedCellChildLaw complement cellOf cell :=
  rfl

/-- The cell-quotiented reference has exactly the normalized integral pooled occurrence table. -/
theorem toCellProductProjectionModel_reference_pooledFeature_weight
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (hmass : 0 < WordType.profileMass profile)
    (cell : Cell) (symbol : Symbol) :
    let M := law.toCellProductProjectionModel complement cellOf hmass
    (M.reference.pushforward M.leftFeature).weight (cell, symbol) +
        (M.reference.pushforward M.rightFeature).weight (cell, symbol) =
      (law.cellJointProfile complement cellOf (cell, symbol) : ℝ) /
        WordType.profileMass profile := by
  classical
  let M := law.toCellProductProjectionModel complement cellOf hmass
  change (M.reference.pushforward M.leftFeature).weight (cell, symbol) +
      (M.reference.pushforward M.rightFeature).weight (cell, symbol) = _
  rw [M.reference_pooledFeature_weight]
  have hcellMass :
      (M.stateLaw.pushforward M.cellOf).weight cell +
          (M.stateLaw.pushforward (M.cellOf ∘ M.complement)).weight cell =
        (complementaryOccurrenceCellProfile profile complement cellOf cell : ℝ) /
          WordType.profileMass profile := by
    change
      ((WordType.normalizedProfileProbability profile hmass).pushforward
          cellOf).weight cell +
        ((WordType.normalizedProfileProbability profile hmass).pushforward
          (cellOf ∘ complement)).weight cell = _
    rw [WordType.normalizedProfileProbability_pushforward_weight,
      WordType.normalizedProfileProbability_pushforward_weight]
    rw [← add_div, ← Nat.cast_add,
      mappedType_add_mappedType_comp_complement]
  rw [hcellMass]
  change
    ((complementaryOccurrenceCellProfile profile complement cellOf cell : ℝ) /
        WordType.profileMass profile) *
      (law.normalizedCellChildLaw complement cellOf cell).weight symbol = _
  rw [div_mul_eq_mul_div, cellMass_mul_normalizedCellChildLaw_weight]

end ComplementaryOccurrenceLaw
end AlgebraicComplexity
