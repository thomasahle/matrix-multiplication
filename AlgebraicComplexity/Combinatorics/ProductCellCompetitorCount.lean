/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.IdentityOrientationCompetitorCount
import AlgebraicComplexity.Probability.EntropyChainRule

/-!
# Conditional type counts over product compatibility cells

Two-letter extraction keeps the interfaces of both letters visible.  Its compatibility statistic
is therefore a pair of one-letter cells, and its fine symbol is a pair of one-letter symbols.
This file specializes the exact conditional method of types to those product alphabets.

The result is deliberately finite and paper-independent.  In particular it neither assumes a
tensor restriction nor identifies a concrete competitor family with the displayed conditional
type class.  A construction-specific client must provide that injection.  Once it does, the
theorems here show that the compatible-degree exponent is the conditional entropy of the actual
paired fine-symbol law after revealing the actual pair of compatibility cells.
-/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

universe u v w x

variable {C₁ : Type u} {C₂ : Type v} {F₁ : Type w} {F₂ : Type x}
variable [Fintype C₁] [Fintype C₂] [Fintype F₁] [Fintype F₂]

/-! ## Exact finite product-cell count -/

/-- The conditional type class over paired cells and paired fine symbols factors exactly over
the two cell coordinates.  There is no asymptotic error and no independence assumption on the
joint fine-symbol table. -/
theorem card_productCellConditionalTypeClass_eq_prod_multinomial
    {n : ℕ} (source : Fin n → C₁ × C₂)
    (jointType : (C₁ × C₂) × (F₁ × F₂) → ℕ)
    (hjoint : jointType ∈ types ((C₁ × C₂) × (F₁ × F₂)) n)
    (hmap : mappedType Prod.fst jointType = multiplicity source) :
    (conditionalTypeClass source jointType).card =
      ∏ c₁, ∏ c₂, Nat.multinomial Finset.univ fun f : F₁ × F₂ ↦
        jointType ((c₁, c₂), f) := by
  rw [card_conditionalTypeClass_eq_prod_multinomial source jointType hjoint hmap]
  exact Fintype.prod_prod_type fun c : C₁ × C₂ ↦
    Nat.multinomial Finset.univ fun f : F₁ × F₂ ↦ jointType (c, f)

/-- Row-law form of the exact product-cell count.  The sole hypothesis says that every paired
cell row has the multiplicity prescribed by the fixed paired-cell source word. -/
theorem card_productCellConditionalTypeClass_eq_prod_multinomial_of_law
    {n : ℕ} (source : Fin n → C₁ × C₂)
    (law : C₁ → C₂ → F₁ × F₂ → ℕ)
    (hlaw : ∀ c₁ c₂, ∑ f, law c₁ c₂ f = multiplicity source (c₁, c₂)) :
    (conditionalTypeClass source fun entry ↦
        law entry.1.1 entry.1.2 entry.2).card =
      ∏ c₁, ∏ c₂, Nat.multinomial Finset.univ (law c₁ c₂) := by
  let pairedLaw : C₁ × C₂ → F₁ × F₂ → ℕ :=
    fun c f ↦ law c.1 c.2 f
  have hcount := card_conditionalTypeClass_eq_prod_multinomial_of_law
    source pairedLaw (fun c ↦ hlaw c.1 c.2)
  change (conditionalTypeClass source fun entry ↦
      law entry.1.1 entry.1.2 entry.2).card = _ at hcount
  rw [hcount]
  exact Fintype.prod_prod_type fun c : C₁ × C₂ ↦
    Nat.multinomial Finset.univ (law c.1 c.2)

/-! ## Entropy and proportional sequence forms -/

/-- The product-cell conditional-entropy base is the product of the entropy bases of the paired
fine-symbol rows.  Correlation inside a row is retained; only the cell pair is conditioned on. -/
theorem conditionalProfileEntropyBase_eq_prod_productCellBase
    (cellProfile : C₁ × C₂ → ℕ)
    (jointProfile : (C₁ × C₂) × (F₁ × F₂) → ℕ)
    (hmargin : mappedType Prod.fst jointProfile = cellProfile) :
    conditionalProfileEntropyBase cellProfile jointProfile =
      ∏ c₁, ∏ c₂, Real.exp ((cellProfile (c₁, c₂) : ℝ) *
        profileEntropyNats fun f : F₁ × F₂ ↦ jointProfile ((c₁, c₂), f)) := by
  rw [conditionalProfileEntropyBase_eq_prod_cellBase cellProfile jointProfile hmargin]
  exact Fintype.prod_prod_type fun c : C₁ × C₂ ↦
    Real.exp ((cellProfile c : ℝ) *
      profileEntropyNats fun f : F₁ × F₂ ↦ jointProfile (c, f))

/-- Product-cell Claim-6.18 form for an exact proportional paired profile.  Its only overhead is
the existing positive subexponential source-profile loss. -/
theorem card_proportionalProductCellConditionalTypeClass_le
    (cellProfile : C₁ × C₂ → ℕ)
    (jointProfile : (C₁ × C₂) × (F₁ × F₂) → ℕ)
    (hmargin : mappedType Prod.fst jointProfile = cellProfile)
    (hmass : 0 < profileMass cellProfile) (k : ℕ) (hk : 0 < k)
    (source : Fin (profileMass cellProfile * k) → C₁ × C₂)
    (hsource : multiplicity source = proportionalCounts cellProfile k) :
    ((conditionalTypeClass source (proportionalCounts jointProfile k)).card : ℝ) ≤
      pushedConditionalTypeLoss cellProfile k *
        (∏ c₁, ∏ c₂, Real.exp ((cellProfile (c₁, c₂) : ℝ) *
          profileEntropyNats fun f : F₁ × F₂ ↦
            jointProfile ((c₁, c₂), f))) ^ k := by
  have h := card_proportionalConditionalTypeClass_le_loss_mul_entropyBase_pow
    cellProfile jointProfile hmargin hmass k hk source hsource
  rwa [conditionalProfileEntropyBase_eq_prod_productCellBase
    cellProfile jointProfile hmargin] at h

/-! ## Normalized probability interpretation -/

variable [DecidableEq C₁] [DecidableEq C₂]

/-- Normalizing an integral paired profile commutes with taking its paired-cell marginal. -/
theorem normalizedProfileProbability_pushforward_fst_eq
    (jointProfile : (C₁ × C₂) × (F₁ × F₂) → ℕ)
    (hmass : 0 < profileMass jointProfile) :
    (normalizedProfileProbability jointProfile hmass).pushforward Prod.fst =
      normalizedProfileProbability (mappedType Prod.fst jointProfile) (by
        simpa only [profileMass_mappedType] using hmass) := by
  apply ProbabilityVector.ext
  funext c
  rw [normalizedProfileProbability_pushforward_weight,
    normalizedProfileProbability_weight, profileMass_mappedType]

/-- The logarithm of the exact product-cell counting base is the paired conditional entropy in
bits, multiplied by the integral profile mass.  This is the bridge from finite type counting to
the two-letter information identities in `Probability.TwoLetter`. -/
theorem log_two_conditionalProfileEntropyBase_eq_mass_mul_conditionalEntropyBits
    (cellProfile : C₁ × C₂ → ℕ)
    (jointProfile : (C₁ × C₂) × (F₁ × F₂) → ℕ)
    (hmargin : mappedType Prod.fst jointProfile = cellProfile)
    (hmass : 0 < profileMass cellProfile) :
    Real.log (conditionalProfileEntropyBase cellProfile jointProfile) / Real.log 2 =
      (profileMass cellProfile : ℝ) *
        (normalizedProfileProbability jointProfile (by
          rw [show profileMass jointProfile = profileMass cellProfile by
            rw [← hmargin, profileMass_mappedType]]
          exact hmass)).conditionalEntropyBits Prod.fst := by
  have hjointMass : profileMass jointProfile = profileMass cellProfile := by
    rw [← hmargin, profileMass_mappedType]
  have hpositive : 0 < profileMass jointProfile := by
    rw [hjointMass]
    exact hmass
  have hpush := normalizedProfileProbability_pushforward_fst_eq jointProfile hpositive
  simp only [hmargin] at hpush
  unfold conditionalProfileEntropyBase ProbabilityVector.conditionalEntropyBits
  rw [Real.log_exp, ProbabilityVector.conditionalEntropy, hpush,
    normalizedProfileProbability_entropy, normalizedProfileProbability_entropy]
  rw [hjointMass]
  ring

end AlgebraicComplexity.WordType
