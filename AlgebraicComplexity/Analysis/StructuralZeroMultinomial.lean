import AlgebraicComplexity.Analysis.StructuralZeroMultinomialCore
import AlgebraicComplexity.Combinatorics.ConditionalFeatureWordType

/-!
# Visible-feature method of types with structural zeroes

This compatibility module adds the finite-union visible-feature bounds to the lightweight
structural-zero multinomial core.
-/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

open Real

universe u v w

/-- Uniform maximum-entropy bound for a visible-feature conditional class.  The hypotheses may
be discharged by any certificate proving an upper bound on the empirical entropy exponent of
every feasible fine joint type.  Forgetting that fine type costs only the explicit polynomial
`conditionalFeatureTypeSelectionLoss`; structural zeroes in the fixed source profile are handled
by `structuralZeroMultinomialLoss`.

This is the quantitative bridge used by compatibility counting: the visible compatibility-cell
profile need not determine the complete fine joint type. -/
theorem card_conditionalFeatureTypeClass_le_uniform_entropy
    {S : Type u} {T : Type v} {C : Type w}
    [Fintype S] [Fintype T] [Fintype C]
    (sourceProfile : S → ℕ) (k : ℕ)
    (source : Fin (profileMass sourceProfile * k) → S)
    (feature : T → C) (featureProfile : S × C → ℕ)
    (jointExponentUpper : ℝ)
    (hmass : 0 < profileMass sourceProfile) (hk : 0 < k)
    (hsource : multiplicity source = proportionalCounts sourceProfile k)
    (hmap : ∀ jointType ∈ feasibleConditionalFeatureTypes feature featureProfile
        (profileMass sourceProfile * k),
      mappedType Prod.fst jointType = multiplicity source)
    (hexponent : ∀ jointType ∈ feasibleConditionalFeatureTypes feature featureProfile
        (profileMass sourceProfile * k),
      (profileMass jointType : ℝ) * profileEntropyNats jointType ≤
        jointExponentUpper) :
    ((conditionalFeatureTypeClass source feature featureProfile).card : ℝ) ≤
      conditionalFeatureTypeSelectionLoss S T (profileMass sourceProfile * k) *
        structuralZeroMultinomialLoss sourceProfile k *
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
  have hclassNat := card_conditionalFeatureTypeClass_le_sum_conditionalTypeClasses
    source feature featureProfile
  have hclass :
      ((conditionalFeatureTypeClass source feature featureProfile).card : ℝ) ≤
        ∑ jointType ∈ feasibleConditionalFeatureTypes feature featureProfile n,
          ((conditionalTypeClass source jointType).card : ℝ) := by
    dsimp [n]
    exact_mod_cast hclassNat
  have hfine : ∀ jointType ∈
      feasibleConditionalFeatureTypes feature featureProfile n,
      ((conditionalTypeClass source jointType).card : ℝ) ≤ fineBound := by
    intro jointType hjointType
    have hjoint := (mem_feasibleConditionalFeatureTypes.mp hjointType).1
    have hconditional :=
      card_conditionalTypeClass_le_structuralZeroLoss_mul_exp_entropyDifference
        sourceProfile k source jointType hmass hk hsource hjoint
          (hmap jointType (by simpa [n] using hjointType))
    calc
      ((conditionalTypeClass source jointType).card : ℝ) ≤
          structuralZeroMultinomialLoss sourceProfile k *
            Real.exp
              ((profileMass jointType : ℝ) * profileEntropyNats jointType -
                sourceExponent) := by
        simpa [sourceExponent] using hconditional
      _ ≤ structuralZeroMultinomialLoss sourceProfile k *
            Real.exp (jointExponentUpper - sourceExponent) := by
        apply mul_le_mul_of_nonneg_left
        · exact Real.exp_le_exp.mpr
            (sub_le_sub_right
              (hexponent jointType (by simpa [n] using hjointType)) sourceExponent)
        · exact (structuralZeroMultinomialLoss_pos sourceProfile k).le
      _ = fineBound := rfl
  have htypeCountNat :
      (feasibleConditionalFeatureTypes feature featureProfile n).card ≤
        (n + 1) ^ Fintype.card (S × T) := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (card_types_le (S × T) n)
  have htypeCount :
      ((feasibleConditionalFeatureTypes feature featureProfile n).card : ℝ) ≤
        conditionalFeatureTypeSelectionLoss S T n := by
    unfold conditionalFeatureTypeSelectionLoss
    exact_mod_cast htypeCountNat
  have hfineNonneg : 0 ≤ fineBound := by
    unfold fineBound
    exact mul_nonneg (structuralZeroMultinomialLoss_pos sourceProfile k).le
      (Real.exp_nonneg _)
  calc
    ((conditionalFeatureTypeClass source feature featureProfile).card : ℝ) ≤
        ∑ jointType ∈ feasibleConditionalFeatureTypes feature featureProfile n,
          ((conditionalTypeClass source jointType).card : ℝ) := hclass
    _ ≤ ∑ _jointType ∈ feasibleConditionalFeatureTypes feature featureProfile n,
          fineBound := by
      apply Finset.sum_le_sum
      intro jointType hjointType
      exact hfine jointType hjointType
    _ = ((feasibleConditionalFeatureTypes feature featureProfile n).card : ℝ) *
          fineBound := by simp
    _ ≤ conditionalFeatureTypeSelectionLoss S T n * fineBound :=
      mul_le_mul_of_nonneg_right htypeCount hfineNonneg
    _ = conditionalFeatureTypeSelectionLoss S T (profileMass sourceProfile * k) *
          structuralZeroMultinomialLoss sourceProfile k *
            Real.exp
              (jointExponentUpper -
                (k : ℝ) * (profileMass sourceProfile : ℝ) *
                  profileEntropyNats sourceProfile) := by
      simp only [n, fineBound, sourceExponent]
      ring

/-- Source-marginal form of `card_conditionalFeatureTypeClass_le_uniform_entropy`.  The client
checks the source marginal only once on the visible feature profile; functoriality of finite
type pushforward supplies the fine marginal condition for every feasible joint type. -/
theorem card_conditionalFeatureTypeClass_le_uniform_entropy_of_sourceMarginal
    {S : Type u} {T : Type v} {C : Type w}
    [Fintype S] [Fintype T] [Fintype C]
    (sourceProfile : S → ℕ) (k : ℕ)
    (source : Fin (profileMass sourceProfile * k) → S)
    (feature : T → C) (featureProfile : S × C → ℕ)
    (jointExponentUpper : ℝ)
    (hmass : 0 < profileMass sourceProfile) (hk : 0 < k)
    (hsource : multiplicity source = proportionalCounts sourceProfile k)
    (hfeatureSource : mappedType Prod.fst featureProfile = multiplicity source)
    (hexponent : ∀ jointType ∈ feasibleConditionalFeatureTypes feature featureProfile
        (profileMass sourceProfile * k),
      (profileMass jointType : ℝ) * profileEntropyNats jointType ≤
        jointExponentUpper) :
    ((conditionalFeatureTypeClass source feature featureProfile).card : ℝ) ≤
      conditionalFeatureTypeSelectionLoss S T (profileMass sourceProfile * k) *
        structuralZeroMultinomialLoss sourceProfile k *
          Real.exp
            (jointExponentUpper -
              (k : ℝ) * (profileMass sourceProfile : ℝ) *
                profileEntropyNats sourceProfile) := by
  apply card_conditionalFeatureTypeClass_le_uniform_entropy
    sourceProfile k source feature featureProfile jointExponentUpper
      hmass hk hsource
  · intro jointType hjointType
    exact mappedType_fst_eq_of_mem_feasibleConditionalFeatureTypes
      feature featureProfile (profileMass sourceProfile * k)
        (multiplicity source) hfeatureSource hjointType
  · exact hexponent

end AlgebraicComplexity.WordType
