import AlgebraicComplexity.Analysis.MaximumEntropyTypeCounting

/-!
# Subexponential loss for maximum-entropy mapped-type counting

The finite maximum-entropy counting theorem has two polynomial factors: the number of empirical
types and the structural-zero multinomial loss of the reference profile.  This file packages a
single positive subexponential majorant for their product along proportional repetitions.
-/

namespace AlgebraicComplexity.WordType

universe u

variable {I : Type u} [Fintype I]

/-- A convenient positive loss dominating both mapped-fiber type selection and the zero-safe
multinomial comparison for the proportional profile `reference * k`. -/
noncomputable def maximumEntropyMappedFiberLoss (reference : I → ℕ) (k : ℕ) : ℝ :=
  ((((profileMass reference + 1) ^ Fintype.card I : ℕ) : ℝ)) *
    ((((k + 1) ^ Fintype.card I : ℕ) : ℝ)) *
      structuralZeroMultinomialLoss reference k

/-- The packaged mapped-fiber loss is strictly positive at every repetition. -/
theorem maximumEntropyMappedFiberLoss_pos (reference : I → ℕ) (k : ℕ) :
    0 < maximumEntropyMappedFiberLoss reference k := by
  unfold maximumEntropyMappedFiberLoss
  have hreference : 0 < (profileMass reference + 1) ^ Fintype.card I :=
    pow_pos (Nat.succ_pos _) _
  have hk : 0 < (k + 1) ^ Fintype.card I := pow_pos (Nat.succ_pos _) _
  exact mul_pos (mul_pos (by exact_mod_cast hreference) (by exact_mod_cast hk))
    (structuralZeroMultinomialLoss_pos reference k)

/-- The exact empirical-type factor is bounded by the separated proportional loss. -/
theorem typeCount_mul_structuralZeroLoss_le_maximumEntropyMappedFiberLoss
    (reference : I → ℕ) (k : ℕ) :
    (((((profileMass reference * k + 1) ^ Fintype.card I : ℕ) : ℝ)) *
        structuralZeroMultinomialLoss reference k) ≤
      maximumEntropyMappedFiberLoss reference k := by
  have hbase : profileMass reference * k + 1 ≤
      (profileMass reference + 1) * (k + 1) := by
    nlinarith [Nat.zero_le (profileMass reference), Nat.zero_le k]
  have hpow : (profileMass reference * k + 1) ^ Fintype.card I ≤
      ((profileMass reference + 1) * (k + 1)) ^ Fintype.card I := by
    exact pow_le_pow_left' hbase _
  have hpow' : (profileMass reference * k + 1) ^ Fintype.card I ≤
      (profileMass reference + 1) ^ Fintype.card I *
        (k + 1) ^ Fintype.card I := by
    simpa only [mul_pow] using hpow
  have hpowReal :
      ((((profileMass reference * k + 1) ^ Fintype.card I : ℕ) : ℝ)) ≤
        ((((profileMass reference + 1) ^ Fintype.card I : ℕ) : ℝ)) *
          ((((k + 1) ^ Fintype.card I : ℕ) : ℝ)) := by
    exact_mod_cast hpow'
  unfold maximumEntropyMappedFiberLoss
  exact mul_le_mul_of_nonneg_right hpowReal
    (le_of_lt (structuralZeroMultinomialLoss_pos reference k))

/-- For a fixed alphabet and integral profile, the combined mapped-fiber loss is
subexponential in the proportional repetition. -/
theorem maximumEntropyMappedFiberLoss_subexponential (reference : I → ℕ) :
    Growth.Subexponential (maximumEntropyMappedFiberLoss reference) := by
  let constant : ℝ :=
    ((((profileMass reference + 1) ^ Fintype.card I : ℕ) : ℝ))
  have htype : Growth.Subexponential (fun k : ℕ ↦
      constant * ((((k + 1) ^ Fintype.card I : ℕ) : ℝ))) := by
    simpa only [constant, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
      (Growth.Subexponential.natCast_succ_pow
        (Fintype.card I)).const_mul (show 0 ≤ constant by positivity)
  have hzero := structuralZeroMultinomialLoss_subexponential reference
  change Growth.Subexponential (fun k ↦
    ((((profileMass reference + 1) ^ Fintype.card I : ℕ) : ℝ)) *
      ((((k + 1) ^ Fintype.card I : ℕ) : ℝ)) *
        structuralZeroMultinomialLoss reference k)
  exact htype.mul hzero

/-- Proportional specialization of the division-free maximum-entropy fiber estimate, with every
polynomial factor absorbed into `maximumEntropyMappedFiberLoss`. -/
theorem card_words_le_maximumEntropyMappedFiberLoss_mul_referenceTypeClass
    {C : Type*} [Fintype C]
    {A : C → Type*} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (coordinate : ∀ c, I → A c)
    (reference : I → ℕ) (hrefMass : 0 < profileMass reference)
    (hmaximum : IsMaximumEntropyInMappedFiber coordinate
      (normalizedProfileProbability reference hrefMass))
    (k : ℕ) (hk : 0 < k)
    (words : Finset (Fin (profileMass reference * k) → I))
    (hwords : ∀ word ∈ words, ∀ c,
      mappedType (coordinate c) (multiplicity word) =
        mappedType (coordinate c) (proportionalCounts reference k)) :
    (words.card : ℝ) ≤ maximumEntropyMappedFiberLoss reference k *
      (Nat.multinomial Finset.univ (proportionalCounts reference k) : ℝ) := by
  have hfinite := card_words_le_typeCount_mul_structuralZeroLoss_mul_referenceTypeClass
    coordinate reference hrefMass hmaximum hk rfl words hwords
  exact hfinite.trans (mul_le_mul_of_nonneg_right
    (typeCount_mul_structuralZeroLoss_le_maximumEntropyMappedFiberLoss reference k)
    (by positivity))

end AlgebraicComplexity.WordType
