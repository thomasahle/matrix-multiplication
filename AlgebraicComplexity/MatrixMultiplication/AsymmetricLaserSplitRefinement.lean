/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymmetricLaserSplitProfile

/-!
# Finite split checks imply refinement and legal letters

This transcribes [duan2023faster], `global_value.tex:32-51,75-82`, the integral
normalization and ordered-letter condition in `def:global-compatible` and `def:useful_g`.
The complete native row sums and common denominator multiples are finite checks.
They imply the existing `SplitRequirements.RefinesType` premise at every scale.
No word space is enumerated, and the existing counting engine remains the consumer.

Every letter of an actually useful word has positive multiplicity. The decoder is zero
outside its declared alphabet, so that letter belongs to the declared alphabet. When the
alphabet is the checked ordered-split alphabet, its digits have the prescribed total.
This gives native letter support, not a tensor extraction, readable zero-out, or good seed.
Zero repetition and zero primal entries remain permitted.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.AsymmetricLaserData

open scoped BigOperators

universe u v

/-- Native row normalization and finite common-denominator multiples imply refinement.
The hypotheses range only over the finite component and letter alphabets. -/
theorem splitRequirementsFromProfiles_refinesType (coarse : FiniteLaw)
    (profiles : Fin coarse.counts.length → LegProfile) {L : Type u} [Fintype L]
    {Z : Type v} (zIndex : Fin coarse.counts.length → Z)
    (boundary : Fin coarse.counts.length → Bool) (encode : L → List Nat)
    (common : Nat) (scales : Fin coarse.counts.length → Nat)
    (hden : ∀ c, 0 < coarse.denominator * (profiles c).law.denominator)
    (hrows : ∀ c, (∑ letter, (profiles c).countAt (encode letter)) =
      (profiles c).law.denominator)
    (hperiod : ∀ c, (profiles c).law.denominator * scales c = common) :
    (splitRequirementsFromProfiles coarse profiles zIndex boundary encode
      (coarse.denominator * common)).RefinesType
        (WordType.proportionalCounts coarse.profile common) := by
  intro c
  change (∑ letter, (splitRequirementsFromProfiles coarse profiles zIndex boundary encode
    (coarse.denominator * common)).splitCount c letter) = coarse.profile c * common
  have hproduct : coarse.denominator * common =
      coarse.denominator * (profiles c).law.denominator * scales c := by
    rw [← hperiod c, Nat.mul_assoc]
  calc
    _ = ∑ letter, (profiles c).countAt (encode letter) * (coarse.profile c * scales c) := by
      apply Finset.sum_congr rfl
      intro letter _
      exact splitRequirementsFromProfiles_splitCount_of_period coarse profiles zIndex
        boundary encode _ c letter (scales c) (hden c) hproduct
    _ = (∑ letter, (profiles c).countAt (encode letter)) *
        (coarse.profile c * scales c) := (Finset.sum_mul _ _ _).symm
    _ = coarse.profile c * common := by
      rw [hrows c, ← hperiod c]
      ac_rfl

/-- A letter occurring in a useful word belongs to its component's declared native alphabet.
This follows from actual multiplicity, including at zero-count and zero-period boundaries. -/
theorem splitRequirementsFromProfiles_isUseful_mem_alphabet (coarse : FiniteLaw)
    (profiles : Fin coarse.counts.length → LegProfile) {L : Type u} {Z : Type v}
    (zIndex : Fin coarse.counts.length → Z) (boundary : Fin coarse.counts.length → Bool)
    (encode : L → List Nat) (period : Nat) {N : Nat}
    (comp : Fin N → Fin coarse.counts.length) (word : Fin N → L)
    (huseful : (splitRequirementsFromProfiles coarse profiles zIndex boundary encode
        period).IsUseful comp word) (position : Fin N) :
    encode (word position) ∈ (profiles (comp position)).alphabet := by
  classical
  by_contra hnot
  have hzero := (profiles (comp position)).countAt_eq_zero_of_not_mem
    (encode (word position)) hnot
  have hcount := congrFun huseful (comp position, word position)
  have hnonzero := WordType.multiplicity_apply_ne_zero (WordType.jointWord comp word) position
  apply hnonzero
  calc
    _ = (splitRequirementsFromProfiles coarse profiles zIndex boundary encode
        period).splitCount (comp position) (word position) := hcount
    _ = 0 := by simp only [splitRequirementsFromProfiles, hzero, Nat.mul_zero, Nat.zero_div]

/-- Every declared ordered-split letter has the prescribed total degree. -/
theorem orderedSplitAlphabet_degree_of_mem {digitBound degree : Nat} {word : List Nat}
    (hword : word ∈ orderedSplitAlphabet digitBound degree) : word.sum = degree := by
  obtain ⟨left, hleft, rfl⟩ := List.mem_map.mp hword
  have hle : left ≤ degree := (of_decide_eq_true (List.mem_filter.mp hleft).2).1
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
  exact (Nat.add_comm left (degree - left)).trans (Nat.sub_add_cancel hle)

end AlgebraicComplexity.AsymmetricLaserData
