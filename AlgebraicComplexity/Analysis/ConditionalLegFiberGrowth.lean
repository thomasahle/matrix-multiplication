import AlgebraicComplexity.Combinatorics.PushedProfileFiberGrowth

/-!
# Lower growth of exact conditional type classes

This module supplies the zero-safe lower counterpart to the existing conditional type-class
upper bound.  It is the denominator estimate needed when a stabilizer-orbit double count bounds
a competitor fiber by `ambient / conditional-class`.
-/

namespace AlgebraicComplexity.WordType

universe u v

variable {Cell : Type u} {Feature : Type v}
variable [Fintype Cell] [Fintype Feature]

/-- Length-transport wrapper for the uniform pushed-type-fiber lower bound. -/
theorem pushedTypeFiberEntropyBase_pow_le_loss_mul_card_typedFiber_of_length_eq
    {A : Type*} {B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (profile : A → ℕ) (hmass : 0 < profileMass profile)
    (k : ℕ) (hk : 0 < k) {n : ℕ}
    (hlen : profileMass profile * k = n)
    (target : Fin n → B)
    (htarget : target ∈ typeClass n
      (proportionalCounts (mappedType f profile) k)) :
    pushedTypeFiberEntropyBase f profile ^ k ≤
      pushedTypeFiberLoss profile k *
        ((typedWordMapFiber f (proportionalCounts profile k) target).card : ℝ) := by
  subst n
  exact pushedTypeFiberEntropyBase_pow_le_loss_mul_card_typedFiber
    f profile hmass k hk target htarget

/-- The conditional entropy base is the quotient of the joint and source entropy bases. -/
theorem conditionalProfileEntropyBase_eq_div
    (sourceProfile : Cell → ℕ) (jointProfile : Cell × Feature → ℕ)
    (hmargin : mappedType Prod.fst jointProfile = sourceProfile)
    (hsourceMass : 0 < profileMass sourceProfile) :
    conditionalProfileEntropyBase sourceProfile jointProfile =
      proportionalEntropyBase jointProfile /
        proportionalEntropyBase sourceProfile := by
  have hjointMass : profileMass jointProfile = profileMass sourceProfile := by
    rw [← hmargin]
    exact (profileMass_mappedType Prod.fst jointProfile).symm
  have hjointMassPos : 0 < profileMass jointProfile := by
    rw [hjointMass]
    exact hsourceMass
  unfold conditionalProfileEntropyBase
  rw [proportionalEntropyBase_eq_exp_profileEntropy jointProfile hjointMassPos,
    proportionalEntropyBase_eq_exp_profileEntropy sourceProfile hsourceMass,
    ← Real.exp_sub, hjointMass]

/-- Zero-safe lower bound for an exact proportional conditional type class.  The only loss is
the structural-zero loss of the joint profile; no positivity of individual cells is required. -/
theorem conditionalProfileEntropyBase_pow_le_structuralZeroLoss_mul_card
    (sourceProfile : Cell → ℕ) (jointProfile : Cell × Feature → ℕ)
    (hmargin : mappedType Prod.fst jointProfile = sourceProfile)
    (hsourceMass : 0 < profileMass sourceProfile)
    (k : ℕ) (hk : 0 < k)
    (source : Fin (profileMass sourceProfile * k) → Cell)
    (hsource : multiplicity source = proportionalCounts sourceProfile k) :
    conditionalProfileEntropyBase sourceProfile jointProfile ^ k ≤
      structuralZeroMultinomialLoss jointProfile k *
        ((conditionalTypeClass source
          (proportionalCounts jointProfile k)).card : ℝ) := by
  have hjointMass : profileMass jointProfile = profileMass sourceProfile := by
    rw [← hmargin]
    exact (profileMass_mappedType Prod.fst jointProfile).symm
  have hjointLower :=
    proportionalEntropyBase_pow_le_structuralZeroLoss_mul_card_typeClass
      jointProfile k
  have hsourceUpper := card_proportionalTypeClass_le_entropyBase_pow
    sourceProfile hsourceMass k hk
  have hfactorNat := multinomial_cell_mul_card_proportionalConditionalTypeClass
    sourceProfile jointProfile hmargin k source hsource
  rw [hsource] at hfactorNat
  have hfactor :
      ((typeClass (profileMass sourceProfile * k)
          (proportionalCounts sourceProfile k)).card : ℝ) *
        ((conditionalTypeClass source
          (proportionalCounts jointProfile k)).card : ℝ) =
      ((typeClass (profileMass sourceProfile * k)
          (proportionalCounts jointProfile k)).card : ℝ) := by
    rw [card_typeClass_eq_multinomial _
      (proportionalCounts_mem_types sourceProfile k)]
    rw [card_typeClass_eq_multinomial]
    · exact_mod_cast hfactorNat
    · simpa only [hjointMass] using proportionalCounts_mem_types jointProfile k
  have hcombined : proportionalEntropyBase jointProfile ^ k ≤
      structuralZeroMultinomialLoss jointProfile k *
        (proportionalEntropyBase sourceProfile ^ k *
          ((conditionalTypeClass source
            (proportionalCounts jointProfile k)).card : ℝ)) := by
    calc
      proportionalEntropyBase jointProfile ^ k ≤
          structuralZeroMultinomialLoss jointProfile k *
            ((typeClass (profileMass jointProfile * k)
              (proportionalCounts jointProfile k)).card : ℝ) := hjointLower
      _ = structuralZeroMultinomialLoss jointProfile k *
          (((typeClass (profileMass sourceProfile * k)
              (proportionalCounts sourceProfile k)).card : ℝ) *
            ((conditionalTypeClass source
              (proportionalCounts jointProfile k)).card : ℝ)) := by
        rw [hjointMass, hfactor]
      _ ≤ structuralZeroMultinomialLoss jointProfile k *
          (proportionalEntropyBase sourceProfile ^ k *
            ((conditionalTypeClass source
              (proportionalCounts jointProfile k)).card : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsourceUpper (by positivity))
          (structuralZeroMultinomialLoss_pos jointProfile k).le
  rw [conditionalProfileEntropyBase_eq_div
    sourceProfile jointProfile hmargin hsourceMass, div_pow]
  apply (div_le_iff₀
    (pow_pos (proportionalEntropyBase_pos_zeroSafe sourceProfile) k)).2
  calc
    proportionalEntropyBase jointProfile ^ k ≤
        structuralZeroMultinomialLoss jointProfile k *
          (proportionalEntropyBase sourceProfile ^ k *
            ((conditionalTypeClass source
              (proportionalCounts jointProfile k)).card : ℝ)) := hcombined
    _ = (structuralZeroMultinomialLoss jointProfile k *
          ((conditionalTypeClass source
            (proportionalCounts jointProfile k)).card : ℝ)) *
        proportionalEntropyBase sourceProfile ^ k := by ring

/-- Length-transport wrapper for
`conditionalProfileEntropyBase_pow_le_structuralZeroLoss_mul_card`.  Concrete tensor powers are
usually indexed by `Fin (n + 1)`, while proportional type lemmas naturally use
`Fin (profileMass sourceProfile * k)`; an exact length equation is all that is needed to pass
between the two interfaces. -/
theorem conditionalProfileEntropyBase_pow_le_structuralZeroLoss_mul_card_of_length_eq
    (sourceProfile : Cell → ℕ) (jointProfile : Cell × Feature → ℕ)
    (hmargin : mappedType Prod.fst jointProfile = sourceProfile)
    (hsourceMass : 0 < profileMass sourceProfile)
    (k : ℕ) (hk : 0 < k) {n : ℕ}
    (hlen : profileMass sourceProfile * k = n)
    (source : Fin n → Cell)
    (hsource : multiplicity source = proportionalCounts sourceProfile k) :
    conditionalProfileEntropyBase sourceProfile jointProfile ^ k ≤
      structuralZeroMultinomialLoss jointProfile k *
        ((conditionalTypeClass source
          (proportionalCounts jointProfile k)).card : ℝ) := by
  subst n
  exact conditionalProfileEntropyBase_pow_le_structuralZeroLoss_mul_card
    sourceProfile jointProfile hmargin hsourceMass k hk source hsource

/-- The conditional lower-bound loss is positive and subexponential. -/
theorem conditionalProfileLowerLoss_subexponential
    (jointProfile : Cell × Feature → ℕ) :
    Growth.Subexponential (structuralZeroMultinomialLoss jointProfile) :=
  structuralZeroMultinomialLoss_subexponential jointProfile

/-- Division-free conditional orbit counting, converted to an exponential fiber bound.

This is the reusable arithmetic core of the stabilizer argument.  `conditionalCard * fiberCard`
is bounded by the ambient family, the exact conditional type class has exponential lower base
`conditionalBase`, and the ambient family has exponential upper base `ambientBase`.  Therefore
the competitor fiber has quotient base `ambientBase / conditionalBase`.  Keeping this lemma over
arbitrary natural cardinalities makes it usable for both word-type stabilizers and other finite
group actions. -/
theorem fiberCard_le_mul_div_pow_of_conditional_mul_fiber_le
    (conditionalBase ambientBase conditionalLoss ambientLoss : ℝ)
    (k conditionalCard fiberCard ambientCard : ℕ)
    (hconditionalBase : 0 < conditionalBase)
    (hconditionalLoss : 0 ≤ conditionalLoss)
    (hconditional : conditionalBase ^ k ≤
      conditionalLoss * (conditionalCard : ℝ))
    (hdouble : conditionalCard * fiberCard ≤ ambientCard)
    (hambient : (ambientCard : ℝ) ≤ ambientLoss * ambientBase ^ k) :
    (fiberCard : ℝ) ≤
      (conditionalLoss * ambientLoss) * (ambientBase / conditionalBase) ^ k := by
  have hdoubleReal : (conditionalCard : ℝ) * (fiberCard : ℝ) ≤
      (ambientCard : ℝ) := by
    exact_mod_cast hdouble
  have hwithConditional : conditionalBase ^ k * (fiberCard : ℝ) ≤
      conditionalLoss * (ambientCard : ℝ) := by
    calc
      conditionalBase ^ k * (fiberCard : ℝ) ≤
          (conditionalLoss * (conditionalCard : ℝ)) * (fiberCard : ℝ) :=
        mul_le_mul_of_nonneg_right hconditional (by positivity)
      _ = conditionalLoss *
          ((conditionalCard : ℝ) * (fiberCard : ℝ)) := by ring
      _ ≤ conditionalLoss * (ambientCard : ℝ) :=
        mul_le_mul_of_nonneg_left hdoubleReal hconditionalLoss
  have hcombined : conditionalBase ^ k * (fiberCard : ℝ) ≤
      (conditionalLoss * ambientLoss) * ambientBase ^ k := by
    exact hwithConditional.trans <| by
      calc
        conditionalLoss * (ambientCard : ℝ) ≤
            conditionalLoss * (ambientLoss * ambientBase ^ k) :=
          mul_le_mul_of_nonneg_left hambient hconditionalLoss
        _ = (conditionalLoss * ambientLoss) * ambientBase ^ k := by ring
  rw [div_pow, ← mul_div_assoc]
  exact (le_div_iff₀ (pow_pos hconditionalBase k)).2 (by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hcombined)

end AlgebraicComplexity.WordType
