import AlgebraicComplexity.Analysis.ConditionalFeatureTypeCountingGrowth

/-!
# Conditional entropy bounds for arbitrary finite word families

A compatibility injection often lands in a strict subfamily of a visible-feature type class.
The strict subfamily may carry support or marginal invariants that are false for the surrounding
class.  This module counts such a family without extending those invariants to unrealized words.

The proof partitions the supplied finite family by the complete empirical type of the joint word
with a fixed source.  Only nonempty fibers need an entropy bound, so the quantitative premise is
required only for joint types realized by actual members.  Each fiber is contained in an ordinary
conditional type class.  The existing structural-zero estimate and polynomial type-selection
loss therefore give the same conditional entropy subtraction as visible-feature counting.

No compatibility relation, tensor, probability certificate, or particular finite alphabet occurs
in this file.
-/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

universe u v

/-- An arbitrary finite family of target words is controlled by a joint-entropy ceiling required
only on its actual members.

The source word has a fixed proportional type.  Partitioning `words` by the empirical type of
`jointWord source target` costs the usual polynomial number of joint types.  A nonempty fiber is
contained in the corresponding conditional type class, where the structural-zero multinomial
bound subtracts the entropy exponent of the fixed source. -/
theorem card_words_le_conditionalFeatureEntropyLoss_mul_exp
    {S : Type u} {T : Type v} [Fintype S] [Fintype T]
    (sourceProfile : S → ℕ) (k : ℕ)
    (source : Fin (profileMass sourceProfile * k) → S)
    (words : Finset (Fin (profileMass sourceProfile * k) → T))
    (jointExponentUpper : ℝ)
    (hmass : 0 < profileMass sourceProfile) (hk : 0 < k)
    (hsource : multiplicity source = proportionalCounts sourceProfile k)
    (hexponent : ∀ target ∈ words,
      (profileMass (multiplicity (jointWord source target)) : ℝ) *
          profileEntropyNats (multiplicity (jointWord source target)) ≤
        jointExponentUpper) :
    (words.card : ℝ) ≤
      conditionalFeatureEntropyLoss T sourceProfile k *
        Real.exp
          (jointExponentUpper -
            (k : ℝ) * (profileMass sourceProfile : ℝ) *
              profileEntropyNats sourceProfile) := by
  classical
  let n : ℕ := profileMass sourceProfile * k
  let sourceExponent : ℝ :=
    (k : ℝ) * (profileMass sourceProfile : ℝ) *
      profileEntropyNats sourceProfile
  let fineBound : ℝ :=
    structuralZeroMultinomialLoss sourceProfile k *
      Real.exp (jointExponentUpper - sourceExponent)
  have hpartition : words.card =
      ∑ jointType ∈ types (S × T) n,
        (words.filter fun target ↦
          multiplicity (jointWord source target) = jointType).card := by
    exact Finset.card_eq_sum_card_fiberwise fun target _htarget ↦
      multiplicity_mem_types (jointWord source target)
  have hfiber : ∀ jointType ∈ types (S × T) n,
      (((words.filter fun target ↦
        multiplicity (jointWord source target) = jointType).card : ℕ) : ℝ) ≤
        fineBound := by
    intro jointType hjointType
    by_cases hempty : (words.filter fun target ↦
        multiplicity (jointWord source target) = jointType).Nonempty
    · obtain ⟨target, htarget⟩ := hempty
      have htargetData := Finset.mem_filter.mp htarget
      have hjointEq : multiplicity (jointWord source target) = jointType :=
        htargetData.2
      have hmap : mappedType Prod.fst jointType = multiplicity source := by
        rw [← hjointEq, ← multiplicity_comp_eq_mappedType]
        rfl
      have hconditional :=
        card_conditionalTypeClass_le_structuralZeroLoss_mul_exp_entropyDifference
          sourceProfile k source jointType hmass hk hsource hjointType hmap
      have hsubset :
          words.filter (fun other ↦
            multiplicity (jointWord source other) = jointType) ⊆
            conditionalTypeClass source jointType := by
        intro other hother
        exact mem_conditionalTypeClass.mpr (Finset.mem_filter.mp hother).2
      have htargetExponent := hexponent target htargetData.1
      rw [hjointEq] at htargetExponent
      calc
        (((words.filter fun other ↦
            multiplicity (jointWord source other) = jointType).card : ℕ) : ℝ) ≤
            ((conditionalTypeClass source jointType).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsubset
        _ ≤ structuralZeroMultinomialLoss sourceProfile k *
              Real.exp
                ((profileMass jointType : ℝ) * profileEntropyNats jointType -
                  sourceExponent) := by
          simpa only [sourceExponent] using hconditional
        _ ≤ structuralZeroMultinomialLoss sourceProfile k *
              Real.exp (jointExponentUpper - sourceExponent) := by
          exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr
              (sub_le_sub_right htargetExponent sourceExponent))
            (structuralZeroMultinomialLoss_pos sourceProfile k).le
        _ = fineBound := rfl
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hempty,
        Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (structuralZeroMultinomialLoss_pos sourceProfile k).le
        (Real.exp_nonneg _)
  have htypeCount :
      ((types (S × T) n).card : ℝ) ≤
        conditionalFeatureTypeSelectionLoss S T n := by
    unfold conditionalFeatureTypeSelectionLoss
    exact_mod_cast card_types_le (S × T) n
  have hfineNonneg : 0 ≤ fineBound := by
    unfold fineBound
    exact mul_nonneg (structuralZeroMultinomialLoss_pos sourceProfile k).le
      (Real.exp_nonneg _)
  calc
    (words.card : ℝ) =
        ∑ jointType ∈ types (S × T) n,
          (((words.filter fun target ↦
            multiplicity (jointWord source target) = jointType).card : ℕ) : ℝ) := by
      exact_mod_cast hpartition
    _ ≤ ∑ _jointType ∈ types (S × T) n, fineBound := by
      exact Finset.sum_le_sum fun jointType hjointType ↦ hfiber jointType hjointType
    _ = ((types (S × T) n).card : ℝ) * fineBound := by simp
    _ ≤ conditionalFeatureTypeSelectionLoss S T n * fineBound :=
      mul_le_mul_of_nonneg_right htypeCount hfineNonneg
    _ = (conditionalFeatureTypeSelectionLoss S T n *
          structuralZeroMultinomialLoss sourceProfile k) *
        Real.exp (jointExponentUpper - sourceExponent) := by
      simp only [fineBound]
      ring
    _ ≤ conditionalFeatureEntropyLoss T sourceProfile k *
        Real.exp (jointExponentUpper - sourceExponent) := by
      exact mul_le_mul_of_nonneg_right
        (by
          simpa only [n] using
            conditionalFeatureTypeSelection_mul_structuralZeroLoss_le_entropyLoss
              T sourceProfile k)
        (Real.exp_nonneg _)
    _ = conditionalFeatureEntropyLoss T sourceProfile k *
        Real.exp
          (jointExponentUpper -
            (k : ℝ) * (profileMass sourceProfile : ℝ) *
              profileEntropyNats sourceProfile) := rfl

/-- Sequence-ready form of
`card_words_le_conditionalFeatureEntropyLoss_mul_exp`: a witness-local joint-entropy bound linear
in the repetition count leaves one fixed conditional penalty base raised to `k`. -/
theorem card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow
    {S : Type u} {T : Type v} [Fintype S] [Fintype T]
    (sourceProfile : S → ℕ) (k : ℕ)
    (source : Fin (profileMass sourceProfile * k) → S)
    (words : Finset (Fin (profileMass sourceProfile * k) → T))
    (jointExponentPerRepetition : ℝ)
    (hmass : 0 < profileMass sourceProfile) (hk : 0 < k)
    (hsource : multiplicity source = proportionalCounts sourceProfile k)
    (hexponent : ∀ target ∈ words,
      (profileMass (multiplicity (jointWord source target)) : ℝ) *
          profileEntropyNats (multiplicity (jointWord source target)) ≤
        (k : ℝ) * jointExponentPerRepetition) :
    (words.card : ℝ) ≤
      conditionalFeatureEntropyLoss T sourceProfile k *
        conditionalFeatureEntropyPenaltyBase sourceProfile
          jointExponentPerRepetition ^ k := by
  have hfinite := card_words_le_conditionalFeatureEntropyLoss_mul_exp
    sourceProfile k source words ((k : ℝ) * jointExponentPerRepetition)
      hmass hk hsource hexponent
  calc
    (words.card : ℝ) ≤
        conditionalFeatureEntropyLoss T sourceProfile k *
          Real.exp
            ((k : ℝ) * jointExponentPerRepetition -
              (k : ℝ) * (profileMass sourceProfile : ℝ) *
                profileEntropyNats sourceProfile) := hfinite
    _ = conditionalFeatureEntropyLoss T sourceProfile k *
        conditionalFeatureEntropyPenaltyBase sourceProfile
          jointExponentPerRepetition ^ k := by
      congr 1
      unfold conditionalFeatureEntropyPenaltyBase
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- A witness-local empirical conditional-entropy bound controls an arbitrary finite family of
target words.

For every realized target, the premise bounds the integral-profile expression

`(H(source, target) - H(source)) / log 2`

by `conditionalUpper`.  Because `hsource` fixes the source type, this is exactly
`H(target | source)` in bits.  Supplying the resulting joint exponent to
`card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow` cancels the fixed-source entropy
once and leaves the stated conditional-entropy base.

This formulation deliberately stays in the integral-profile counting layer.  A probability-
vector client can rewrite its conditional entropy to this expression before applying the theorem,
without making the generic method-of-types module import the probability entropy API.

Proof sketch: convert the entropy-difference bound from bits to nats, restore the empirical profile
mass, and apply the existing witness-local joint-entropy theorem. -/
theorem card_words_le_conditionalFeatureEntropyLoss_mul_profileConditionalEntropyBitsBase_pow
    {S : Type u} {T : Type v} [Fintype S] [Fintype T]
    (sourceProfile : S → ℕ) (k : ℕ)
    (source : Fin (profileMass sourceProfile * k) → S)
    (words : Finset (Fin (profileMass sourceProfile * k) → T))
    (conditionalUpper : ℝ)
    (hmass : 0 < profileMass sourceProfile) (hk : 0 < k)
    (hsource : multiplicity source = proportionalCounts sourceProfile k)
    (hconditional : ∀ target ∈ words,
      (profileEntropyNats (multiplicity (jointWord source target)) -
          profileEntropyNats sourceProfile) / Real.log 2 ≤ conditionalUpper) :
    (words.card : ℝ) ≤
      conditionalFeatureEntropyLoss T sourceProfile k *
        (Real.exp
          ((profileMass sourceProfile : ℝ) * Real.log 2 * conditionalUpper)) ^ k := by
  classical
  let jointExponentPerRepetition :=
    (profileMass sourceProfile : ℝ) *
      (profileEntropyNats sourceProfile + Real.log 2 * conditionalUpper)
  have hexponent : ∀ target ∈ words,
      (profileMass (multiplicity (jointWord source target)) : ℝ) *
          profileEntropyNats (multiplicity (jointWord source target)) ≤
        (k : ℝ) * jointExponentPerRepetition := by
    intro target htarget
    let jointProfile := multiplicity (jointWord source target)
    have hjointMass :
        profileMass jointProfile = profileMass sourceProfile * k := by
      simpa only [jointProfile, profileMass] using
        (sum_multiplicity (jointWord source target))
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hconditionalNats :
        profileEntropyNats jointProfile - profileEntropyNats sourceProfile ≤
          Real.log 2 * conditionalUpper := by
      simpa only [jointProfile, mul_comm] using
        (div_le_iff₀ hlogTwo).mp (hconditional target htarget)
    have hprofileEntropy :
        profileEntropyNats jointProfile ≤
          profileEntropyNats sourceProfile + Real.log 2 * conditionalUpper := by
      have := (sub_le_iff_le_add).mp hconditionalNats
      simpa only [add_comm] using this
    calc
      (profileMass (multiplicity (jointWord source target)) : ℝ) *
            profileEntropyNats (multiplicity (jointWord source target)) =
          (profileMass jointProfile : ℝ) * profileEntropyNats jointProfile := rfl
      _ ≤ (profileMass jointProfile : ℝ) *
            (profileEntropyNats sourceProfile + Real.log 2 * conditionalUpper) :=
        mul_le_mul_of_nonneg_left hprofileEntropy (Nat.cast_nonneg _)
      _ = (k : ℝ) * jointExponentPerRepetition := by
        rw [hjointMass, Nat.cast_mul]
        unfold jointExponentPerRepetition
        ring
  have hcount :=
    card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow
      sourceProfile k source words jointExponentPerRepetition hmass hk hsource hexponent
  have hbase :
      conditionalFeatureEntropyPenaltyBase sourceProfile jointExponentPerRepetition =
        Real.exp
          ((profileMass sourceProfile : ℝ) * Real.log 2 * conditionalUpper) := by
    unfold conditionalFeatureEntropyPenaltyBase jointExponentPerRepetition
    congr 1
    ring
  simpa only [hbase] using hcount

end AlgebraicComplexity.WordType
