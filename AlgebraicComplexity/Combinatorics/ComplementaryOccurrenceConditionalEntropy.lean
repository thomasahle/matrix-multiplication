/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.ConditionalLegFiberGrowth
import AlgebraicComplexity.Combinatorics.ComplementaryOccurrenceProfile
import AlgebraicComplexity.Combinatorics.IdentityOrientationCompetitorCount
import AlgebraicComplexity.Probability.ComplementaryProductProjectionEntropy
import AlgebraicComplexity.Probability.ComplementaryOccurrenceCellProjection

set_option autoImplicit false

/-!
# Conditional entropy of labelled complementary occurrences

An ordered state contributes two labelled child occurrences.  Pooling those occurrences by a
finite cell map produces an integral cell/symbol table, while normalizing the same data produces
the complementary-product reference used by parent-profile concentration.  This file proves that
the two descriptions have exactly the same conditional entropy exponent.

The result is independent of Coppersmith--Winograd tensors.  It also records the total
twice-mass law, proportional scaling, and the exact type of a doubled cell word.  These identities
are the reusable bridge between finite conditional type counting and information-projection
models.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v w

namespace WordType

variable {Cell : Type u} {Feature : Type v}
variable [Fintype Cell] [Fintype Feature]

/-- Proportional scaling multiplies the conditional entropy exponent by the scale. -/
theorem conditionalProfileEntropyBase_proportionalCounts
    (cellProfile : Cell → ℕ) (jointProfile : Cell × Feature → ℕ)
    (hmargin : mappedType Prod.fst jointProfile = cellProfile)
    (hmass : 0 < profileMass cellProfile)
    (k : ℕ) (hk : 0 < k) :
    conditionalProfileEntropyBase
        (proportionalCounts cellProfile k)
        (proportionalCounts jointProfile k) =
      conditionalProfileEntropyBase cellProfile jointProfile ^ k := by
  have hjointMass : profileMass jointProfile = profileMass cellProfile := by
    rw [← hmargin]
    exact (profileMass_mappedType Prod.fst jointProfile).symm
  have hjointMassPos : 0 < profileMass jointProfile := by
    rw [hjointMass]
    exact hmass
  have hcellMassScale :
      profileMass (proportionalCounts cellProfile k) =
        profileMass cellProfile * k := by
    simp [profileMass, proportionalCounts, Finset.sum_mul]
  have hjointMassScale :
      profileMass (proportionalCounts jointProfile k) =
        profileMass jointProfile * k := by
    simp [profileMass, proportionalCounts, Finset.sum_mul]
  unfold conditionalProfileEntropyBase
  rw [← Real.exp_nat_mul, hcellMassScale, hjointMassScale,
    profileEntropyNats_proportionalCounts cellProfile hmass k hk,
    profileEntropyNats_proportionalCounts jointProfile hjointMassPos k hk]
  congr 1
  push_cast
  ring

end WordType

namespace ComplementaryOccurrenceLaw

variable {State : Type u} [Fintype State] [DecidableEq State]
variable {Symbol : Type v} [Fintype Symbol] [DecidableEq Symbol] [Nonempty Symbol]
variable {Cell : Type w} [Fintype Cell] [DecidableEq Cell]
variable {profile : State → ℕ}

omit [DecidableEq State] in
/-- A pushed integral profile has the same weighted sums as the original profile. -/
private theorem sum_natCast_mappedType_mul
    (f : State → Cell) (profile : State → ℕ) (value : Cell → ℝ) :
    (∑ cell, (WordType.mappedType f profile cell : ℝ) * value cell) =
      ∑ state, (profile state : ℝ) * value (f state) := by
  classical
  simp only [WordType.mappedType_eq_sum_ite, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_zero]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro state _
  simp [eq_comm]

omit [DecidableEq State] [DecidableEq Cell] in
/-- The complementary cell profile has twice the mass of the ordered-state profile. -/
theorem profileMass_complementaryOccurrenceCellProfile
    (profile : State → ℕ) (complement : Equiv.Perm State)
    (cellOf : State → Cell) :
    WordType.profileMass
        (complementaryOccurrenceCellProfile profile complement cellOf) =
      2 * WordType.profileMass profile := by
  unfold complementaryOccurrenceCellProfile
  rw [WordType.profileMass_mappedType]
  exact ComplementaryOccurrence.sum_integralMass profile

omit [DecidableEq State] [Fintype Cell] [DecidableEq Cell] in
/-- Repeating the ordered-state profile repeats its labelled-occurrence cell profile. -/
theorem complementaryOccurrenceCellProfile_proportionalCounts
    (profile : State → ℕ) (complement : Equiv.Perm State)
    (cellOf : State → Cell) (k : ℕ) :
    complementaryOccurrenceCellProfile
        (WordType.proportionalCounts profile k) complement cellOf =
      WordType.proportionalCounts
        (complementaryOccurrenceCellProfile profile complement cellOf) k := by
  unfold complementaryOccurrenceCellProfile
  change
    WordType.mappedType
        (fun occurrence : ComplementaryOccurrence State ↦
          cellOf (occurrence.childState complement))
        (WordType.proportionalCounts
          (fun occurrence : ComplementaryOccurrence State ↦
            occurrence.integralMass profile) k) =
      WordType.proportionalCounts
        (WordType.mappedType
          (fun occurrence : ComplementaryOccurrence State ↦
            cellOf (occurrence.childState complement))
          (fun occurrence : ComplementaryOccurrence State ↦
            occurrence.integralMass profile)) k
  exact WordType.mappedType_proportionalCounts _ _ _

omit [DecidableEq State] in
/-- Appending the left cell word and its complement-transported right cell word realizes the
proportional labelled-occurrence cell profile exactly. -/
theorem multiplicity_append_cellOf_complement
    (profile : State → ℕ) (complement : Equiv.Perm State)
    (cellOf : State → Cell) (k n : ℕ)
    (state : Fin n → State)
    (hstate : WordType.multiplicity state =
      WordType.proportionalCounts profile k) :
    WordType.multiplicity
        (Fin.append (cellOf ∘ state) (cellOf ∘ complement ∘ state)) =
      WordType.proportionalCounts
        (complementaryOccurrenceCellProfile profile complement cellOf) k := by
  have hleft :
      WordType.multiplicity (cellOf ∘ state) =
        WordType.proportionalCounts (WordType.mappedType cellOf profile) k := by
    rw [WordType.multiplicity_comp_eq_mappedType, hstate,
      WordType.mappedType_proportionalCounts]
  have hright :
      WordType.multiplicity (cellOf ∘ complement ∘ state) =
        WordType.proportionalCounts
          (WordType.mappedType (cellOf ∘ complement) profile) k := by
    rw [show cellOf ∘ complement ∘ state = (cellOf ∘ complement) ∘ state by rfl,
      WordType.multiplicity_comp_eq_mappedType, hstate,
      WordType.mappedType_proportionalCounts]
  rw [WordType.multiplicity_append, hleft, hright]
  funext cell
  simp only [Pi.add_apply, WordType.proportionalCounts]
  rw [← Nat.add_mul]
  exact congrArg (· * k)
    (mappedType_add_mappedType_comp_complement profile complement cellOf cell)

omit [DecidableEq State] in
/-- The normalized pooled child law has the entropy of its literal integral row, including for a
structurally zero row. -/
theorem normalizedCellChildLaw_entropy
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell) (cell : Cell) :
    (law.normalizedCellChildLaw complement cellOf cell).entropy =
      WordType.profileEntropyNats
        (fun symbol ↦ law.cellJointProfile complement cellOf (cell, symbol)) := by
  classical
  by_cases hmass :
      0 < complementaryOccurrenceCellProfile profile complement cellOf cell
  · simp only [normalizedCellChildLaw, hmass, dite_true]
    exact WordType.normalizedProfileProbability_entropy _ (by
      rw [profileMass_cellJointProfile]
      exact hmass)
  · have hzero :
        complementaryOccurrenceCellProfile profile complement cellOf cell = 0 :=
      Nat.eq_zero_of_not_pos hmass
    have hrow : ∀ symbol,
        law.cellJointProfile complement cellOf (cell, symbol) = 0 := by
      intro symbol
      have hle : law.cellJointProfile complement cellOf (cell, symbol) ≤
          ∑ z, law.cellJointProfile complement cellOf (cell, z) :=
        Finset.single_le_sum
          (s := Finset.univ)
          (f := fun z ↦ law.cellJointProfile complement cellOf (cell, z))
          (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_univ symbol)
      rw [sum_cellJointProfile, hzero] at hle
      omega
    simp [normalizedCellChildLaw, hmass, WordType.profileEntropyNats, hrow]

/-- Multiplying the complementary-product reference's conditional entropy by the source mass
gives the mass-weighted entropy of the pooled cell rows. -/
theorem profileMass_mul_reference_conditionalEntropy_coarse
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (hmass : 0 < WordType.profileMass profile) :
    let M := law.toCellProductProjectionModel complement cellOf hmass
    (WordType.profileMass profile : ℝ) *
        M.reference.conditionalEntropy M.coarse =
      ∑ cell,
        (complementaryOccurrenceCellProfile profile complement cellOf cell : ℝ) *
          (M.childLaw cell).entropy := by
  classical
  dsimp only
  let M := law.toCellProductProjectionModel complement cellOf hmass
  let value : Cell → ℝ :=
    fun cell ↦ (law.normalizedCellChildLaw complement cellOf cell).entropy
  have hmassReal : (WordType.profileMass profile : ℝ) ≠ 0 := by
    exact_mod_cast hmass.ne'
  rw [ComplementaryProductProjectionModel.reference_conditionalEntropy_coarse]
  change
    (WordType.profileMass profile : ℝ) *
        (∑ state, ((profile state : ℝ) / WordType.profileMass profile) *
          (value (cellOf state) + value (cellOf (complement state)))) =
      ∑ cell,
        (complementaryOccurrenceCellProfile profile complement cellOf cell : ℝ) *
          value cell
  rw [Finset.mul_sum]
  have hcancel (state : State) (x : ℝ) :
      (WordType.profileMass profile : ℝ) *
          (((profile state : ℝ) / WordType.profileMass profile) * x) =
        (profile state : ℝ) * x := by
    field_simp
  simp_rw [hcancel, mul_add]
  rw [Finset.sum_add_distrib,
    ← sum_natCast_mappedType_mul cellOf profile value]
  have hrightSum :
      (∑ state, (profile state : ℝ) * value (cellOf (complement state))) =
        ∑ cell,
          (WordType.mappedType (cellOf ∘ complement) profile cell : ℝ) *
            value cell := by
    simpa only [Function.comp_apply] using
      (sum_natCast_mappedType_mul (cellOf ∘ complement) profile value).symm
  rw [hrightSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro cell _
  rw [← add_mul, ← Nat.cast_add,
    mappedType_add_mappedType_comp_complement profile complement cellOf cell]

/-- **Conditional entropy bridge for labelled complementary occurrences.**

The exact conditional-type base of the pooled integral cell/symbol table is the exponential of
the ordered-state mass times the conditional entropy of the normalized complementary-product
reference.  Labelled fixed points of the complement are counted twice on both sides. -/
theorem conditionalProfileEntropyBase_cellJointProfile
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (hmass : 0 < WordType.profileMass profile) :
    let M := law.toCellProductProjectionModel complement cellOf hmass
    WordType.conditionalProfileEntropyBase
        (complementaryOccurrenceCellProfile profile complement cellOf)
        (law.cellJointProfile complement cellOf) =
      Real.exp ((WordType.profileMass profile : ℝ) *
        M.reference.conditionalEntropy M.coarse) := by
  classical
  let M := law.toCellProductProjectionModel complement cellOf hmass
  rw [WordType.conditionalProfileEntropyBase_eq_prod_cellBase
    (complementaryOccurrenceCellProfile profile complement cellOf)
    (law.cellJointProfile complement cellOf)
    (law.mappedType_fst_cellJointProfile complement cellOf)]
  rw [← Real.exp_sum]
  congr 1
  rw [profileMass_mul_reference_conditionalEntropy_coarse
    law complement cellOf hmass]
  apply Finset.sum_congr rfl
  intro cell _
  rw [ComplementaryOccurrenceLaw.toCellProductProjectionModel_childLaw,
    normalizedCellChildLaw_entropy law complement cellOf cell]

end ComplementaryOccurrenceLaw

end AlgebraicComplexity
