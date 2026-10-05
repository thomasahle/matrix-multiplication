/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.ComplementaryProductProjectionPairedWordFamily
import AlgebraicComplexity.Combinatorics.ComplementaryOccurrenceCellPairedWord

/-!
# Actual-family counts from cell-quotiented paired occurrence profiles

Claim 6.18 of Alman--Duan--Vassilevska Williams--Xu--Xu--Zhou,
*More Asymmetry Yields Faster Matrix Multiplication*, fixes one paired fine word and counts the
actual ordered-parent words whose state type and combined labelled child-occurrence table match
the prescribed reference.

This module presents that step entirely in exact integral data.  Each candidate state word must
have the reference state multiplicity, and its left and complemented-right child occurrences,
after the chosen cell quotient, must together have the reference occurrence multiplicity.  The
two labelled tables are never fixed separately, and a self-complementary state contributes once
on each labelled side.

The proof composes the denominator-free paired-word profile bridge with the actual-family pooled
information-projection count.  It formalizes the finite numerator estimate in
[alman2025more, Claim 6.18], `papers/sources/2404.16349/constituent.tex:388-436`, especially
lines 402--429.  No compatibility relation, hashing extraction, tensor restriction, asymptotic
limit, or certificate-specific constant is introduced here.
-/

set_option autoImplicit false

open scoped BigOperators

namespace AlgebraicComplexity
namespace ComplementaryOccurrenceLaw

universe u v w

variable {State : Type u} [Fintype State] [DecidableEq State]
variable {Symbol : Type v} [Fintype Symbol] [DecidableEq Symbol] [Nonempty Symbol]
variable {Cell : Type w} [Fintype Cell] [DecidableEq Cell]
variable {profile : State → ℕ}

/-- Count an actual family of ordered-parent words from its two exact Claim 6.18 profile
equalities.

For every candidate `target`, `hstate` fixes the ordered-state multiplicity and `hchildren` fixes
the single combined table of the labelled left and complemented-right cell/child occurrences.
The conclusion retains the method-of-types polynomial factor and uses the entropy of the
cell-quotiented complementary-product reference.

Proof sketch: the exact state and combined child equations instantiate
`isPooledMarginalProfile_of_cellPairWords`.  The integral pooled-profile actual-family theorem
then normalizes those counts and applies the complementary-product information projection. -/
theorem card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_cellPairProfiles
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (hprofileMass : 0 < WordType.profileMass profile)
    (sourceProfile : Symbol × Symbol → ℕ) (k : ℕ)
    (source : Fin (WordType.profileMass sourceProfile * k) → Symbol × Symbol)
    (words : Finset (Fin (WordType.profileMass sourceProfile * k) → State))
    (hsourceMass : 0 < WordType.profileMass sourceProfile) (hk : 0 < k)
    (hsource : WordType.multiplicity source =
      WordType.proportionalCounts sourceProfile k)
    (hstate : ∀ target ∈ words, WordType.multiplicity target = profile)
    (hchildren : ∀ target ∈ words,
      WordType.multiplicity
          (Fin.append
            (fun i ↦ (cellOf (target i), (source i).1))
            (fun i ↦ (cellOf (complement (target i)), (source i).2))) =
        law.cellJointProfile complement cellOf) :
    let M := law.toCellProductProjectionModel complement cellOf hprofileMass
    (words.card : ℝ) ≤
      WordType.conditionalFeatureEntropyLoss State sourceProfile k *
        WordType.conditionalFeatureEntropyPenaltyBase sourceProfile
          ((WordType.profileMass sourceProfile : ℝ) * Real.log 2 *
            (M.stateLaw.entropyBits +
              ∑ state, M.stateLaw.weight state *
                ((M.childLaw (M.cellOf state)).entropyBits +
                  (M.childLaw (M.cellOf (M.complement state))).entropyBits))) ^ k := by
  let M := law.toCellProductProjectionModel complement cellOf hprofileMass
  apply
    WordType.card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_pairedPooledProfile
      M sourceProfile k source words hsourceMass hk hsource
  intro target htarget
  simpa only [M] using
    law.isPooledMarginalProfile_of_cellPairWords complement cellOf hprofileMass
      target (fun i ↦ (source i).1) (fun i ↦ (source i).2)
      (hstate target htarget) (hchildren target htarget)

/-! The private singleton instance below applies the public theorem to a nonempty actual family,
showing that all data-carrying hypotheses can hold simultaneously. -/

private def cellFamilyTinyProfile : Unit → ℕ := fun _ ↦ 1

private def cellFamilyTinyLaw :
    ComplementaryOccurrenceLaw cellFamilyTinyProfile Unit where
  count := fun _ _ ↦ 1
  rowSum := by
    intro occurrence
    simp [cellFamilyTinyProfile]

private def cellFamilyTinySourceProfile : Unit × Unit → ℕ := fun _ ↦ 1

private def cellFamilyTinySource :
    Fin (WordType.profileMass cellFamilyTinySourceProfile * 1) → Unit × Unit :=
  fun _ ↦ ((), ())

private def cellFamilyTinyWords :
    Finset (Fin (WordType.profileMass cellFamilyTinySourceProfile * 1) → Unit) :=
  Finset.univ

private theorem cellFamilyTiny_card_complementarySide :
    Fintype.card ComplementarySide = 2 := by
  change ({.left, .right} : Finset ComplementarySide).card = 2
  simp

private theorem cellFamilyTinyProfile_mass_pos :
    0 < WordType.profileMass cellFamilyTinyProfile := by
  simp [cellFamilyTinyProfile, WordType.profileMass]

private theorem cellFamilyTinySourceProfile_mass_pos :
    0 < WordType.profileMass cellFamilyTinySourceProfile := by
  simp [cellFamilyTinySourceProfile, WordType.profileMass, Finset.sum_const,
    Fintype.card_prod]

private theorem cellFamilyTinySource_multiplicity :
    WordType.multiplicity cellFamilyTinySource =
      WordType.proportionalCounts cellFamilyTinySourceProfile 1 := by
  classical
  funext pair
  have hpair : pair = ((), ()) := Subsingleton.elim _ _
  subst pair
  rw [show cellFamilyTinySource = fun _ ↦ ((), ()) by rfl,
    WordType.multiplicity_const]
  simp [cellFamilyTinySourceProfile, WordType.proportionalCounts,
    WordType.profileMass, Finset.sum_const, Fintype.card_prod]

private theorem cellFamilyTinyState_multiplicity
    (target : Fin (WordType.profileMass cellFamilyTinySourceProfile * 1) → Unit) :
    WordType.multiplicity target = cellFamilyTinyProfile := by
  classical
  have htarget : target = fun _ ↦ () := by
    funext i
    exact Subsingleton.elim _ _
  rw [htarget]
  funext state
  have hstate : state = () := Subsingleton.elim _ _
  subst state
  rw [WordType.multiplicity_const]
  simp [cellFamilyTinyProfile, cellFamilyTinySourceProfile,
    WordType.profileMass, Finset.sum_const, Fintype.card_prod]

private theorem cellFamilyTinyChildren_multiplicity
    (target : Fin (WordType.profileMass cellFamilyTinySourceProfile * 1) → Unit) :
    WordType.multiplicity
        (Fin.append
          (fun i ↦ ((fun _ : Unit ↦ ()) (target i), (cellFamilyTinySource i).1))
          (fun i ↦
            ((fun _ : Unit ↦ ()) ((Equiv.refl Unit) (target i)),
              (cellFamilyTinySource i).2))) =
      cellFamilyTinyLaw.cellJointProfile (Equiv.refl Unit) (fun _ ↦ ()) := by
  classical
  funext entry
  have hentry : entry = ((), ()) := Subsingleton.elim _ _
  subst entry
  rw [show Fin.append
      (fun i ↦ ((fun _ : Unit ↦ ()) (target i), (cellFamilyTinySource i).1))
      (fun i ↦
        ((fun _ : Unit ↦ ()) ((Equiv.refl Unit) (target i)),
          (cellFamilyTinySource i).2)) = fun _ ↦ ((), ()) by
        funext i
        exact Subsingleton.elim _ _]
  rw [WordType.multiplicity_const]
  simp [cellFamilyTinyLaw, ComplementaryOccurrenceLaw.cellJointProfile,
    cellFamilyTinySourceProfile, WordType.profileMass, Finset.sum_const,
    Fintype.card_prod, cellFamilyTiny_card_complementarySide]

private example :
    cellFamilyTinyWords.Nonempty ∧
      let M := cellFamilyTinyLaw.toCellProductProjectionModel
        (Equiv.refl Unit) (fun _ ↦ ()) cellFamilyTinyProfile_mass_pos
      (cellFamilyTinyWords.card : ℝ) ≤
        WordType.conditionalFeatureEntropyLoss Unit cellFamilyTinySourceProfile 1 *
          WordType.conditionalFeatureEntropyPenaltyBase cellFamilyTinySourceProfile
            ((WordType.profileMass cellFamilyTinySourceProfile : ℝ) * Real.log 2 *
              (M.stateLaw.entropyBits +
                ∑ state, M.stateLaw.weight state *
                  ((M.childLaw (M.cellOf state)).entropyBits +
                    (M.childLaw (M.cellOf (M.complement state))).entropyBits))) ^ 1 := by
  constructor
  · exact ⟨fun _ ↦ (), by simp [cellFamilyTinyWords]⟩
  · apply card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_cellPairProfiles
      cellFamilyTinyLaw (Equiv.refl Unit) (fun _ ↦ ()) cellFamilyTinyProfile_mass_pos
        cellFamilyTinySourceProfile 1 cellFamilyTinySource cellFamilyTinyWords
        cellFamilyTinySourceProfile_mass_pos Nat.zero_lt_one
        cellFamilyTinySource_multiplicity
    · intro target _
      exact cellFamilyTinyState_multiplicity target
    · intro target _
      exact cellFamilyTinyChildren_multiplicity target

end ComplementaryOccurrenceLaw
end AlgebraicComplexity
