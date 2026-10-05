import AlgebraicComplexity.Analysis.MaximumEntropyTypeCountingGrowth
import AlgebraicComplexity.Combinatorics.PushedProfileTypeCounting
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeaf

/-!
# Type-class growth for rational typed leaves

The finite tensor theorem for a `RationalTypedLeaf` uses exact integral profiles.  This file
connects its three interface marginals to method-of-types growth without mentioning a particular
tensor or a particular entropy formula.

For each leg, the integral marginal profile is the pushforward of the joint count table.  Its
normalized probability law is exactly `RationalTypedLeaf.marginal`, its entropy base is the
exponential of the stored marginal entropy rate, and its proportional type classes attain that
base up to the standard structural-zero polynomial loss.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

namespace RationalTypedLeaf

variable {I : Type u} [Fintype I] [Nonempty I]
variable {A : Leg → Type v} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

/-- Exact integral profile of one interface coordinate. -/
noncomputable def marginalProfile (leaf : RationalTypedLeaf I A) (c : Leg) : A c → ℕ :=
  WordType.mappedType (leaf.coordinate c) leaf.profile.count

omit [Nonempty I] [∀ c, DecidableEq (A c)] in
/-- Pushing to an interface coordinate preserves the denominator of the rational profile. -/
theorem profileMass_marginalProfile
    (leaf : RationalTypedLeaf I A) (c : Leg) :
    WordType.profileMass (leaf.marginalProfile c) = leaf.profile.mass := by
  unfold marginalProfile PositiveIntegralProfile.mass
  exact WordType.profileMass_mappedType (leaf.coordinate c) leaf.profile.count

omit [∀ c, DecidableEq (A c)] in
/-- Every interface marginal has positive total mass, even if some interface labels have zero
weight. -/
theorem profileMass_marginalProfile_pos
    (leaf : RationalTypedLeaf I A) (c : Leg) :
    0 < WordType.profileMass (leaf.marginalProfile c) := by
  rw [profileMass_marginalProfile]
  exact leaf.profile.mass_pos

/-- The probability law obtained by normalizing the integral marginal profile is definitionally
the typed leaf's probabilistic interface marginal. -/
theorem marginal_eq_normalizedProfileProbability
    (leaf : RationalTypedLeaf I A) (c : Leg) :
    leaf.marginal c =
      WordType.normalizedProfileProbability (leaf.marginalProfile c)
        (leaf.profileMass_marginalProfile_pos c) := by
  apply ProbabilityVector.ext
  funext a
  rw [WordType.normalizedProfileProbability_weight]
  unfold marginal distribution marginalProfile
  rw [PositiveIntegralProfile.pushforward_weight,
    WordType.profileMass_mappedType]
  rfl

/-- Natural-log profile entropy and the typed leaf's base-two marginal entropy are the same
quantity in their respective units. -/
theorem profileEntropyNats_marginalProfile
    (leaf : RationalTypedLeaf I A) (c : Leg) :
    WordType.profileEntropyNats (leaf.marginalProfile c) =
      leaf.marginalEntropyBits c * Real.log 2 := by
  have hentropy := congrArg ProbabilityVector.entropy
    (leaf.marginal_eq_normalizedProfileProbability c)
  rw [WordType.normalizedProfileProbability_entropy] at hentropy
  unfold marginalEntropyBits ProbabilityVector.entropyBits
  rw [hentropy]
  field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

/-- Exponential growth base of one exact interface marginal type. -/
noncomputable def marginalEntropyBase
    (leaf : RationalTypedLeaf I A) (c : Leg) : ℝ :=
  WordType.proportionalEntropyBase (leaf.marginalProfile c)

omit [Nonempty I] [∀ c, DecidableEq (A c)] in
theorem marginalEntropyBase_pos
    (leaf : RationalTypedLeaf I A) (c : Leg) :
    0 < leaf.marginalEntropyBase c :=
  WordType.proportionalEntropyBase_pos_zeroSafe (leaf.marginalProfile c)

/-- The exact finite entropy base equals the exponential of the base-two marginal entropy rate
times the primitive profile mass. -/
theorem marginalEntropyBase_eq_exp
    (leaf : RationalTypedLeaf I A) (c : Leg) :
    leaf.marginalEntropyBase c =
      Real.exp ((leaf.profile.mass : ℝ) * Real.log 2 *
        leaf.marginalEntropyBits c) := by
  unfold marginalEntropyBase
  rw [WordType.proportionalEntropyBase_eq_exp_profileEntropy
    (leaf.marginalProfile c) (leaf.profileMass_marginalProfile_pos c),
    leaf.profileMass_marginalProfile,
    leaf.profileEntropyNats_marginalProfile]
  congr 1
  ring

/-- Explicit polynomial loss for one rational typed-leaf marginal. -/
noncomputable def marginalTypeLoss
    (leaf : RationalTypedLeaf I A) (c : Leg) (k : ℕ) : ℝ :=
  WordType.structuralZeroMultinomialLoss (leaf.marginalProfile c) k

omit [Nonempty I] [∀ c, DecidableEq (A c)] in
theorem marginalTypeLoss_pos
    (leaf : RationalTypedLeaf I A) (c : Leg) (k : ℕ) :
    0 < leaf.marginalTypeLoss c k :=
  WordType.structuralZeroMultinomialLoss_pos (leaf.marginalProfile c) k

omit [Nonempty I] [∀ c, DecidableEq (A c)] in
/-- Marginal type-class losses are subexponential for every fixed rational typed leaf. -/
theorem marginalTypeLoss_subexponential
    (leaf : RationalTypedLeaf I A) (c : Leg) :
    Growth.Subexponential (leaf.marginalTypeLoss c) :=
  WordType.structuralZeroMultinomialLoss_subexponential (leaf.marginalProfile c)

omit [Nonempty I] [∀ c, DecidableEq (A c)] in
/-- Sequence-ready lower bound for an exact proportional marginal type class. -/
theorem marginalEntropyBase_pow_le_loss_mul_card_typeClass
    (leaf : RationalTypedLeaf I A) (c : Leg) (k : ℕ) :
    leaf.marginalEntropyBase c ^ k ≤
      leaf.marginalTypeLoss c k *
        ((WordType.typeClass (leaf.profile.mass * k)
          (WordType.proportionalCounts (leaf.marginalProfile c) k)).card : ℝ) := by
  rw [← leaf.profileMass_marginalProfile c]
  exact WordType.proportionalEntropyBase_pow_le_structuralZeroLoss_mul_card_typeClass
    (leaf.marginalProfile c) k

/-- Maximum-entropy control of an arbitrary finite family with the leaf's three proportional
interface types.  The reference exact joint type appears on the right; every other factor is a
fixed positive subexponential loss. -/
theorem card_words_le_maximumEntropyLoss_mul_jointTypeClass
    (leaf : RationalTypedLeaf I A)
    (hmaximum : leaf.IsMaximumEntropyBits leaf.distribution)
    (k : ℕ) (hk : 0 < k)
    (words : Finset (Fin (leaf.profile.mass * k) → I))
    (hwords : ∀ word ∈ words, ∀ c,
      WordType.mappedType (leaf.coordinate c) (WordType.multiplicity word) =
        WordType.mappedType (leaf.coordinate c)
          (WordType.proportionalCounts leaf.profile.count k)) :
    (words.card : ℝ) ≤
      WordType.maximumEntropyMappedFiberLoss leaf.profile.count k *
        (Nat.multinomial Finset.univ
          (WordType.proportionalCounts leaf.profile.count k) : ℝ) := by
  exact WordType.card_words_le_maximumEntropyMappedFiberLoss_mul_referenceTypeClass
    leaf.coordinate leaf.profile.count leaf.profile.mass_pos
      hmaximum.isMaximumEntropyInMappedFiber k hk words hwords

end RationalTypedLeaf

end AlgebraicComplexity
