import AlgebraicComplexity.Analysis.StructuralZeroMultinomial

/-!
# Subexponential loss for conditional visible-feature counting

Compatibility counting fixes a source profile and a visible feature profile while allowing the
full target type to vary.  `card_conditionalFeatureTypeClass_le_uniform_entropy` bounds that
family by a type-selection polynomial, a structural-zero multinomial loss, and the certified
entropy-difference exponential.  This file packages the first two factors into one positive
subexponential sequence along proportional repetitions.
-/

namespace AlgebraicComplexity.WordType

universe u v

variable {S : Type u} [Fintype S]
variable (T : Type v) [Fintype T]

/-- Positive polynomial loss for a conditional visible-feature class at repetition `k`. -/
noncomputable def conditionalFeatureEntropyLoss
    (sourceProfile : S → ℕ) (k : ℕ) : ℝ :=
  ((((profileMass sourceProfile + 1) ^ Fintype.card (S × T) : ℕ) : ℝ)) *
    ((((k + 1) ^ Fintype.card (S × T) : ℕ) : ℝ)) *
      structuralZeroMultinomialLoss sourceProfile k

/-- The packaged conditional-feature loss is strictly positive. -/
theorem conditionalFeatureEntropyLoss_pos
    (sourceProfile : S → ℕ) (k : ℕ) :
    0 < conditionalFeatureEntropyLoss T sourceProfile k := by
  unfold conditionalFeatureEntropyLoss
  have hsource : 0 < (profileMass sourceProfile + 1) ^ Fintype.card (S × T) :=
    pow_pos (Nat.succ_pos _) _
  have hk : 0 < (k + 1) ^ Fintype.card (S × T) :=
    pow_pos (Nat.succ_pos _) _
  exact mul_pos (mul_pos (by exact_mod_cast hsource) (by exact_mod_cast hk))
    (structuralZeroMultinomialLoss_pos sourceProfile k)

/-- The literal type-selection and structural-zero factors are dominated by the separated
proportional loss. -/
theorem conditionalFeatureTypeSelection_mul_structuralZeroLoss_le_entropyLoss
    (sourceProfile : S → ℕ) (k : ℕ) :
    conditionalFeatureTypeSelectionLoss S T (profileMass sourceProfile * k) *
        structuralZeroMultinomialLoss sourceProfile k ≤
      conditionalFeatureEntropyLoss T sourceProfile k := by
  let d := Fintype.card (S × T)
  have hbase : profileMass sourceProfile * k + 1 ≤
      (profileMass sourceProfile + 1) * (k + 1) := by
    nlinarith [Nat.zero_le (profileMass sourceProfile), Nat.zero_le k]
  have hpow : (profileMass sourceProfile * k + 1) ^ d ≤
      (profileMass sourceProfile + 1) ^ d * (k + 1) ^ d := by
    simpa only [mul_pow] using pow_le_pow_left' hbase d
  have hpowReal :
      (((profileMass sourceProfile * k + 1 : ℕ) : ℝ)) ^ d ≤
        ((((profileMass sourceProfile + 1) ^ d : ℕ) : ℝ)) *
          ((((k + 1) ^ d : ℕ) : ℝ)) := by
    simpa only [Nat.cast_pow, Nat.cast_mul] using (show
      ((((profileMass sourceProfile * k + 1) ^ d : ℕ) : ℝ)) ≤
        ((((profileMass sourceProfile + 1) ^ d * (k + 1) ^ d : ℕ) : ℝ)) by
          exact_mod_cast hpow)
  unfold conditionalFeatureTypeSelectionLoss conditionalFeatureEntropyLoss
  dsimp only [d] at hpowReal
  exact mul_le_mul_of_nonneg_right hpowReal
    (le_of_lt (structuralZeroMultinomialLoss_pos sourceProfile k))

/-- For fixed source and target alphabets, the conditional-feature loss is subexponential. -/
theorem conditionalFeatureEntropyLoss_subexponential
    (sourceProfile : S → ℕ) :
    Growth.Subexponential (conditionalFeatureEntropyLoss T sourceProfile) := by
  let constant : ℝ :=
    ((((profileMass sourceProfile + 1) ^ Fintype.card (S × T) : ℕ) : ℝ))
  have htype : Growth.Subexponential (fun k : ℕ ↦
      constant * ((((k + 1) ^ Fintype.card (S × T) : ℕ) : ℝ))) := by
    simpa only [constant, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
      (Growth.Subexponential.natCast_succ_pow
        (Fintype.card (S × T))).const_mul (show 0 ≤ constant by positivity)
  have hzero := structuralZeroMultinomialLoss_subexponential sourceProfile
  change Growth.Subexponential (fun k ↦
    ((((profileMass sourceProfile + 1) ^ Fintype.card (S × T) : ℕ) : ℝ)) *
      ((((k + 1) ^ Fintype.card (S × T) : ℕ) : ℝ)) *
        structuralZeroMultinomialLoss sourceProfile k)
  exact htype.mul hzero

/-- Uniform entropy-bound theorem with all polynomial factors absorbed into the packaged loss. -/
theorem card_conditionalFeatureTypeClass_le_entropyLoss_mul_exp
    {C : Type*} [Fintype C]
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
      conditionalFeatureEntropyLoss T sourceProfile k *
        Real.exp
          (jointExponentUpper -
            (k : ℝ) * (profileMass sourceProfile : ℝ) *
              profileEntropyNats sourceProfile) := by
  have hfinite := card_conditionalFeatureTypeClass_le_uniform_entropy
    sourceProfile k source feature featureProfile jointExponentUpper
      hmass hk hsource hmap hexponent
  exact hfinite.trans (mul_le_mul_of_nonneg_right
    (conditionalFeatureTypeSelection_mul_structuralZeroLoss_le_entropyLoss
      T sourceProfile k) (Real.exp_nonneg _))

/-- Exponential base left by a per-repetition upper bound on the joint entropy exponent.

If a conditional joint type at repetition `k` has entropy exponent at most `k * U`, then its
size relative to the source type class is controlled by the `k`-th power of this base, up to the
explicit subexponential loss `conditionalFeatureEntropyLoss`. -/
noncomputable def conditionalFeatureEntropyPenaltyBase
    (sourceProfile : S → ℕ) (jointExponentPerRepetition : ℝ) : ℝ :=
  Real.exp
    (jointExponentPerRepetition -
      (profileMass sourceProfile : ℝ) * profileEntropyNats sourceProfile)

/-- The per-repetition conditional entropy penalty base is strictly positive. -/
theorem conditionalFeatureEntropyPenaltyBase_pos
    (sourceProfile : S → ℕ) (jointExponentPerRepetition : ℝ) :
    0 < conditionalFeatureEntropyPenaltyBase sourceProfile jointExponentPerRepetition := by
  exact Real.exp_pos _

/-- Sequence-ready conditional-feature count from a uniform entropy bound per repetition.

All polynomial and structural-zero losses are isolated in the positive subexponential sequence
`conditionalFeatureEntropyLoss`; the remaining exponential contribution is the `k`-th power of
one fixed base. -/
theorem card_conditionalFeatureTypeClass_le_entropyLoss_mul_penaltyBase_pow
    {C : Type*} [Fintype C]
    (sourceProfile : S → ℕ) (k : ℕ)
    (source : Fin (profileMass sourceProfile * k) → S)
    (feature : T → C) (featureProfile : S × C → ℕ)
    (jointExponentPerRepetition : ℝ)
    (hmass : 0 < profileMass sourceProfile) (hk : 0 < k)
    (hsource : multiplicity source = proportionalCounts sourceProfile k)
    (hmap : ∀ jointType ∈ feasibleConditionalFeatureTypes feature featureProfile
        (profileMass sourceProfile * k),
      mappedType Prod.fst jointType = multiplicity source)
    (hexponent : ∀ jointType ∈ feasibleConditionalFeatureTypes feature featureProfile
        (profileMass sourceProfile * k),
      (profileMass jointType : ℝ) * profileEntropyNats jointType ≤
        (k : ℝ) * jointExponentPerRepetition) :
    ((conditionalFeatureTypeClass source feature featureProfile).card : ℝ) ≤
      conditionalFeatureEntropyLoss T sourceProfile k *
        conditionalFeatureEntropyPenaltyBase sourceProfile
          jointExponentPerRepetition ^ k := by
  have hfinite := card_conditionalFeatureTypeClass_le_entropyLoss_mul_exp
    T sourceProfile k source feature featureProfile
      ((k : ℝ) * jointExponentPerRepetition)
      hmass hk hsource hmap hexponent
  calc
    ((conditionalFeatureTypeClass source feature featureProfile).card : ℝ) ≤
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

end AlgebraicComplexity.WordType
