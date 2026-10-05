import AlgebraicComplexity.Analysis.StructuralZeroEntropyIdentity

/-! # Structural-zero multinomial lower bound -/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

open Real

universe u

variable {I : Type u} [Fintype I]

/-- Polynomial loss in the lower bound for a fixed integral profile.  The `+1` in every factor
is what makes the expression valid when that profile coordinate is structurally zero. -/
noncomputable def structuralZeroMultinomialLoss (a : I → ℕ) (k : ℕ) : ℝ :=
  (Real.exp 1) ^ Fintype.card I * ∏ i, (((a i * k + 1 : ℕ) : ℝ))

/-- The zero-safe loss is positive at every repetition. -/
theorem structuralZeroMultinomialLoss_pos (a : I → ℕ) (k : ℕ) :
    0 < structuralZeroMultinomialLoss a k := by
  unfold structuralZeroMultinomialLoss
  positivity

/-- Zero-safe factorial upper bound used in the denominator of the multinomial coefficient. -/
private theorem factorial_le_exp_mul_succ_mul_factorialEntropyTerm (d : ℕ) :
    (d.factorial : ℝ) ≤
      Real.exp 1 * ((d + 1 : ℕ) : ℝ) * factorialEntropyTerm d := by
  cases d with
  | zero =>
      simp only [Nat.factorial_zero, Nat.cast_one, Nat.zero_add, factorialEntropyTerm,
        pow_zero, mul_one]
      exact Real.one_le_exp (by norm_num)
  | succ d =>
      change ((d + 1).factorial : ℝ) ≤
        Real.exp 1 * (((d + 1 + 1 : ℕ) : ℝ)) *
          ((((d + 1 : ℕ) : ℝ) / Real.exp 1) ^ (d + 1))
      calc
        ((d + 1).factorial : ℝ) ≤
            Real.exp 1 * (((d + 1 : ℕ) : ℝ)) *
              ((((d + 1 : ℕ) : ℝ) / Real.exp 1) ^ (d + 1)) :=
          factorial_le_exp_mul_self_mul (Nat.succ_pos d)
        _ ≤ Real.exp 1 * (((d + 1 + 1 : ℕ) : ℝ)) *
              ((((d + 1 : ℕ) : ℝ) / Real.exp 1) ^ (d + 1)) := by
          gcongr
          norm_num

/-- The Stirling exponential term is a lower bound for every factorial, including `0!`. -/
private theorem factorialEntropyTerm_le_factorial_zeroSafe (d : ℕ) :
    factorialEntropyTerm d ≤ (d.factorial : ℝ) := by
  cases d with
  | zero => simp [factorialEntropyTerm]
  | succ d => exact pow_div_exp_le_factorial (Nat.succ_pos d)

/-- A fixed integral type, with arbitrary structural zeroes, attains its entropy base up to the
explicit polynomial loss. -/
theorem proportionalEntropyBase_pow_le_structuralZeroLoss_mul_multinomial
    (a : I → ℕ) (k : ℕ) :
    proportionalEntropyBase a ^ k ≤
      structuralZeroMultinomialLoss a k *
        (Nat.multinomial Finset.univ (proportionalCounts a k) : ℝ) := by
  classical
  have hspec :
      (∏ i, (((a i * k).factorial : ℕ) : ℝ)) *
          (Nat.multinomial Finset.univ (proportionalCounts a k) : ℝ) =
        (((profileMass a * k).factorial : ℕ) : ℝ) := by
    exact_mod_cast proportionalMultinomial_spec a k
  have hdenUpper :
      (∏ i, (((a i * k).factorial : ℕ) : ℝ)) ≤
        structuralZeroMultinomialLoss a k *
          ∏ i, factorialEntropyTerm (a i * k) := by
    calc
      _ ≤ ∏ i, Real.exp 1 * (((a i * k + 1 : ℕ) : ℝ)) *
          factorialEntropyTerm (a i * k) := by
        apply Finset.prod_le_prod
        · intro i _
          positivity
        · intro i _
          exact factorial_le_exp_mul_succ_mul_factorialEntropyTerm (a i * k)
      _ = structuralZeroMultinomialLoss a k *
          ∏ i, factorialEntropyTerm (a i * k) := by
        unfold structuralZeroMultinomialLoss
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
          Finset.prod_const, Finset.card_univ]
  have hterms : 0 < ∏ i, factorialEntropyTerm (a i * k) := by
    exact Finset.prod_pos fun i _ ↦ factorialEntropyTerm_pos_zeroSafe (a i * k)
  have hraw :
      proportionalEntropyBase a ^ k *
          (∏ i, factorialEntropyTerm (a i * k)) ≤
        (structuralZeroMultinomialLoss a k *
          (Nat.multinomial Finset.univ (proportionalCounts a k) : ℝ)) *
            (∏ i, factorialEntropyTerm (a i * k)) := by
    calc
      proportionalEntropyBase a ^ k *
          (∏ i, factorialEntropyTerm (a i * k)) =
          factorialEntropyTerm (profileMass a * k) :=
        proportionalEntropyBase_mul_scaled_terms a k
      _ ≤ (((profileMass a * k).factorial : ℕ) : ℝ) :=
        factorialEntropyTerm_le_factorial_zeroSafe (profileMass a * k)
      _ = (∏ i, (((a i * k).factorial : ℕ) : ℝ)) *
          (Nat.multinomial Finset.univ (proportionalCounts a k) : ℝ) := hspec.symm
      _ ≤ (structuralZeroMultinomialLoss a k *
          ∏ i, factorialEntropyTerm (a i * k)) *
            (Nat.multinomial Finset.univ (proportionalCounts a k) : ℝ) := by
        exact mul_le_mul_of_nonneg_right hdenUpper (by positivity)
      _ = (structuralZeroMultinomialLoss a k *
          (Nat.multinomial Finset.univ (proportionalCounts a k) : ℝ)) *
            (∏ i, factorialEntropyTerm (a i * k)) := by ring
  exact le_of_mul_le_mul_right hraw hterms

/-- The proportional entropy base is the exponential of the empirical entropy, even when the
profile has structural zeroes. -/
theorem proportionalEntropyBase_eq_exp_profileEntropy
    (a : I → ℕ) (hmass : 0 < profileMass a) :
    proportionalEntropyBase a =
      Real.exp ((profileMass a : ℝ) * profileEntropyNats a) := by
  have hbasePos : 0 < proportionalEntropyBase a := by
    unfold proportionalEntropyBase
    exact div_pos (factorialEntropyTerm_pos_zeroSafe _)
      (Finset.prod_pos fun i _ ↦ factorialEntropyTerm_pos_zeroSafe _)
  rw [← Real.exp_log hbasePos, log_proportionalEntropyBase_of_profileMass_pos a hmass]

end AlgebraicComplexity.WordType
