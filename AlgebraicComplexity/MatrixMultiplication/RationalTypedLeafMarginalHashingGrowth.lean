import AlgebraicComplexity.Combinatorics.PrimeFieldSizing
import AlgebraicComplexity.Combinatorics.PushedProfileFiberGrowth
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafMarginalHashing
import AlgebraicComplexity.Probability.EntropyMonotonicity

/-!
# Asymptotic field sizing for fixed-marginal typed-leaf hashing

This module turns the exact finite quantities in `RationalTypedLeafMarginalHashing` into
exponential growth bounds.  A maximum-entropy rational typed leaf has

* a marked joint type class with base `jointEntropyBase`;
* an ambient fixed-marginal family at most a subexponential factor larger than that class; and
* an exact leg-fiber size obtained by dividing the ambient family by one marginal type class.

Consequently, when all three marginal entropy bases agree with `marginalBase`, the finite field
requirement grows with base `jointEntropyBase / marginalBase`, up to an explicit positive
subexponential loss.  This is the reusable source of the positive marginal-entropy sign in the
modern cyclic-value proof: marked hashing retains the joint-type base divided by the field base,
namely `marginalBase`.

No tensor relation, named CW constituent, prime choice, or numerical entropy formula occurs here.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v

namespace RationalTypedLeaf

variable {A : Leg → Type v} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {support : Finset (BlockAddress A)} [Nonempty support]

/-- Exponential base of the exact proportional joint type selected by a rational typed leaf. -/
noncomputable def jointEntropyBase (leaf : RationalTypedLeaf support A) : ℝ :=
  WordType.proportionalEntropyBase leaf.profile.count

/-- Polynomial loss in the lower bound for the marked proportional joint type class. -/
noncomputable def jointTypeLoss
    (leaf : RationalTypedLeaf support A) (k : ℕ) : ℝ :=
  WordType.structuralZeroMultinomialLoss leaf.profile.count k

/-- The joint entropy base is strictly positive. -/
theorem jointEntropyBase_pos (leaf : RationalTypedLeaf support A) :
    0 < leaf.jointEntropyBase :=
  WordType.proportionalEntropyBase_pos_zeroSafe leaf.profile.count

/-- A deterministic visible marginal has no larger entropy base than the joint typed-leaf law.

Proof sketch: rewrite both exact method-of-types bases as exponentials of the corresponding
Shannon entropies.  `ProbabilityVector.entropy_pushforward_le` compares those entropies, and the
common positive profile mass preserves the inequality. -/
theorem marginalEntropyBase_le_jointEntropyBase
    (leaf : RationalTypedLeaf support A) (c : Leg) :
    leaf.marginalEntropyBase c ≤ leaf.jointEntropyBase := by
  have hentropy : (leaf.marginal c).entropy ≤ leaf.distribution.entropy :=
    leaf.distribution.entropy_pushforward_le (leaf.coordinate c)
  have hjoint : leaf.jointEntropyBase =
      Real.exp ((leaf.profile.mass : ℝ) * leaf.distribution.entropy) := by
    unfold jointEntropyBase
    rw [WordType.proportionalEntropyBase_eq_exp_profileEntropy
      leaf.profile.count leaf.profile.mass_pos]
    congr 1
  have hmarginal : leaf.marginalEntropyBase c =
      Real.exp ((leaf.profile.mass : ℝ) * (leaf.marginal c).entropy) := by
    rw [leaf.marginalEntropyBase_eq_exp]
    unfold marginalEntropyBits ProbabilityVector.entropyBits
    congr 1
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  rw [hjoint, hmarginal]
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hentropy (Nat.cast_nonneg _))

/-- The entropy quotient governing a deterministic marginal fiber is at least one. -/
theorem one_le_jointEntropyBase_div_marginalEntropyBase
    (leaf : RationalTypedLeaf support A) (c : Leg) :
    1 ≤ leaf.jointEntropyBase / leaf.marginalEntropyBase c :=
  (one_le_div (leaf.marginalEntropyBase_pos c)).2
    (leaf.marginalEntropyBase_le_jointEntropyBase c)

/-- The marked joint-type loss is strictly positive at every repetition. -/
theorem jointTypeLoss_pos (leaf : RationalTypedLeaf support A) (k : ℕ) :
    0 < leaf.jointTypeLoss k :=
  WordType.structuralZeroMultinomialLoss_pos leaf.profile.count k

/-- The marked joint-type loss is subexponential. -/
theorem jointTypeLoss_subexponential (leaf : RationalTypedLeaf support A) :
    Growth.Subexponential leaf.jointTypeLoss :=
  WordType.structuralZeroMultinomialLoss_subexponential leaf.profile.count

/-- The marked proportional family attains the joint entropy base up to its standard polynomial
loss.

Proof sketch: `markedWords` is a positive-word presentation of the ordinary proportional type
class.  At positive repetition its recursive depth plus one is exactly `profile.mass * k`, so the
generic structural-zero multinomial lower bound applies verbatim. -/
theorem jointEntropyBase_pow_le_jointTypeLoss_mul_card_markedWords
    (leaf : RationalTypedLeaf support A) {k : ℕ} (hk : 0 < k) :
    leaf.jointEntropyBase ^ k ≤
      leaf.jointTypeLoss k * (leaf.markedWords k).card := by
  unfold jointEntropyBase jointTypeLoss markedWords
  rw [card_positiveTypeClass, leaf.proportionalDepth_add_one hk]
  exact WordType.proportionalEntropyBase_pow_le_structuralZeroLoss_mul_card_typeClass
    leaf.profile.count k

/-- The exact marked proportional family is at most its joint entropy exponential. -/
theorem card_markedWords_le_jointEntropyBase_pow
    (leaf : RationalTypedLeaf support A) {k : ℕ} (hk : 0 < k) :
    ((leaf.markedWords k).card : ℝ) ≤ leaf.jointEntropyBase ^ k := by
  unfold jointEntropyBase markedWords
  rw [card_positiveTypeClass, leaf.proportionalDepth_add_one hk]
  exact WordType.card_proportionalTypeClass_le_entropyBase_pow
    leaf.profile.count leaf.profile.mass_pos k hk

/-- Ordinary-function presentation of the positive-word ambient marginal family. -/
noncomputable def ambientFunctionWords
    (leaf : RationalTypedLeaf support A) (k : ℕ) :
    Finset (Fin (leaf.proportionalDepth k + 1) → support) :=
  (leaf.ambientWords k).image (positiveWordEquiv support (leaf.proportionalDepth k))

/-- Passing from positive words to ordinary finite words preserves the ambient cardinality. -/
@[simp] theorem card_ambientFunctionWords
    (leaf : RationalTypedLeaf support A) (k : ℕ) :
    (leaf.ambientFunctionWords k).card = (leaf.ambientWords k).card := by
  unfold ambientFunctionWords
  exact Finset.card_image_of_injective _
    (positiveWordEquiv support (leaf.proportionalDepth k)).injective

/-- A maximum-entropy marked profile controls the entire three-marginal ambient family by a
positive subexponential factor.

Proof sketch: transport ambient positive words through `positiveWordEquiv`.  Their defining three
multiplicity equations become the mapped-type equations required by maximum-entropy type
counting.  The reference multinomial is exactly the cardinality of `markedWords`. -/
theorem card_ambientWords_le_maximumEntropyLoss_mul_card_markedWords
    (leaf : RationalTypedLeaf support A)
    (hcoordinate : leaf.IsSupportCoordinate)
    (hmaximum : leaf.IsMaximumEntropyBits leaf.distribution)
    {k : ℕ} (hk : 0 < k) :
    ((leaf.ambientWords k).card : ℝ) ≤
      WordType.maximumEntropyMappedFiberLoss leaf.profile.count k *
        (leaf.markedWords k).card := by
  classical
  let words := leaf.ambientFunctionWords k
  have hwords : ∀ word ∈ words, ∀ c,
      WordType.mappedType (leaf.coordinate c) (WordType.multiplicity word) =
        WordType.mappedType (leaf.coordinate c)
          (WordType.proportionalCounts leaf.profile.count k) := by
    intro ordinary hord c
    rcases Finset.mem_image.mp hord with ⟨word, hword, rfl⟩
    have hc := (leaf.mem_ambientWords_iff k word).mp hword c
    unfold KeepsMarginal marginalProfile at hc
    rw [PartitionHashEncoding.positiveWordEquiv_supportWordAddress] at hc
    change WordType.multiplicity
        ((fun s : support ↦ s.1 c) ∘
          positiveWordEquiv support (leaf.proportionalDepth k) word) = _ at hc
    have hmap : (fun s : support ↦ s.1 c) = leaf.coordinate c := by
      funext s
      exact (hcoordinate c s).symm
    rw [hmap, WordType.multiplicity_comp_eq_mappedType,
      ← WordType.mappedType_proportionalCounts] at hc
    exact hc
  have hfinite :=
    WordType.card_words_le_typeCount_mul_structuralZeroLoss_mul_referenceTypeClass
      leaf.coordinate leaf.profile.count leaf.profile.mass_pos
      hmaximum.isMaximumEntropyInMappedFiber hk
      (leaf.proportionalDepth_add_one hk) words hwords
  have hfactor :=
    WordType.typeCount_mul_structuralZeroLoss_le_maximumEntropyMappedFiberLoss
      leaf.profile.count k
  have hfactor' :
      (((((leaf.proportionalDepth k + 1 + 1) ^ Fintype.card support : ℕ) : ℝ)) *
          WordType.structuralZeroMultinomialLoss leaf.profile.count k) ≤
        WordType.maximumEntropyMappedFiberLoss leaf.profile.count k := by
    rw [leaf.proportionalDepth_add_one hk]
    exact hfactor
  have hmarked :
      Nat.multinomial Finset.univ
          (WordType.proportionalCounts leaf.profile.count k) =
        (leaf.markedWords k).card := by
    symm
    unfold markedWords
    exact card_positiveTypeClass_eq_multinomial _ _ (leaf.markedProfile_mem_types hk)
  calc
    ((leaf.ambientWords k).card : ℝ) = (words.card : ℝ) := by
      rw [show words = leaf.ambientFunctionWords k by rfl,
        leaf.card_ambientFunctionWords]
    _ ≤ ((((leaf.proportionalDepth k + 1 + 1) ^ Fintype.card support : ℕ) : ℝ)) *
          WordType.structuralZeroMultinomialLoss leaf.profile.count k *
            Nat.multinomial Finset.univ
              (WordType.proportionalCounts leaf.profile.count k) := hfinite
    _ ≤ WordType.maximumEntropyMappedFiberLoss leaf.profile.count k *
          Nat.multinomial Finset.univ
            (WordType.proportionalCounts leaf.profile.count k) :=
      mul_le_mul_of_nonneg_right hfactor' (by positivity)
    _ = WordType.maximumEntropyMappedFiberLoss leaf.profile.count k *
          (leaf.markedWords k).card := by rw [hmarked]

/-- Exponential upper bound for one exact ambient leg fiber.

The numerator is the maximum-entropy ambient family, while the denominator is the exact marginal
type class.  The division is performed through the proved natural-cardinality factorization, so
no rounding or positivity premise is hidden. -/
theorem ambientFiberSize_cast_le_entropyQuotient
    (leaf : RationalTypedLeaf support A)
    (hcoordinate : leaf.IsSupportCoordinate)
    (hmaximum : leaf.IsMaximumEntropyBits leaf.distribution)
    {k : ℕ} (hk : 0 < k) (c : Leg) :
    (leaf.ambientFiberSize k c : ℝ) ≤
      (WordType.maximumEntropyMappedFiberLoss leaf.profile.count k *
          leaf.marginalTypeLoss c k) *
        (leaf.jointEntropyBase / leaf.marginalEntropyBase c) ^ k := by
  classical
  let marginalWords := positiveTypeClass (A c) (leaf.proportionalDepth k)
    (WordType.proportionalCounts (leaf.marginalProfile c) k)
  have hmarginalWords : marginalWords.Nonempty := by
    rw [← Finset.card_pos]
    unfold marginalWords
    rw [card_positiveTypeClass]
    exact Finset.card_pos.mpr
      (WordType.typeClass_nonempty _ (leaf.marginalProfile_mem_types hk c))
  let target := Classical.choose hmarginalWords
  have htarget : target ∈ marginalWords := Classical.choose_spec hmarginalWords
  have hfactorNat := leaf.marginalCard_mul_ambientFiber k c target (by
    simpa only [marginalWords] using htarget)
  have hfiber := leaf.card_ambient_sourceWordLegFiber hk c target (by
    simpa only [marginalWords] using htarget)
  rw [hfiber] at hfactorNat
  have hfactor :
      ((marginalWords.card : ℕ) : ℝ) * (leaf.ambientFiberSize k c : ℝ) =
        (leaf.ambientWords k).card := by
    exact_mod_cast (show marginalWords.card * leaf.ambientFiberSize k c =
      (leaf.ambientWords k).card by simpa only [marginalWords] using hfactorNat)
  have hmarginal : leaf.marginalEntropyBase c ^ k ≤
      leaf.marginalTypeLoss c k * (marginalWords.card : ℝ) := by
    unfold marginalWords
    rw [card_positiveTypeClass, leaf.proportionalDepth_add_one hk]
    exact leaf.marginalEntropyBase_pow_le_loss_mul_card_typeClass c k
  have hambient := leaf.card_ambientWords_le_maximumEntropyLoss_mul_card_markedWords
    hcoordinate hmaximum hk
  have hjoint := leaf.card_markedWords_le_jointEntropyBase_pow hk
  have hmul :
      (leaf.ambientFiberSize k c : ℝ) * leaf.marginalEntropyBase c ^ k ≤
        (WordType.maximumEntropyMappedFiberLoss leaf.profile.count k *
          leaf.marginalTypeLoss c k) * leaf.jointEntropyBase ^ k := by
    calc
      (leaf.ambientFiberSize k c : ℝ) * leaf.marginalEntropyBase c ^ k ≤
          (leaf.ambientFiberSize k c : ℝ) *
            (leaf.marginalTypeLoss c k * (marginalWords.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hmarginal (by positivity)
      _ = leaf.marginalTypeLoss c k * (leaf.ambientWords k).card := by
        rw [← hfactor]
        ring
      _ ≤ leaf.marginalTypeLoss c k *
          (WordType.maximumEntropyMappedFiberLoss leaf.profile.count k *
            (leaf.markedWords k).card) :=
        mul_le_mul_of_nonneg_left hambient (leaf.marginalTypeLoss_pos c k).le
      _ ≤ leaf.marginalTypeLoss c k *
          (WordType.maximumEntropyMappedFiberLoss leaf.profile.count k *
            leaf.jointEntropyBase ^ k) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hjoint
            (WordType.maximumEntropyMappedFiberLoss_pos
              leaf.profile.count k).le)
          (leaf.marginalTypeLoss_pos c k).le
      _ = (WordType.maximumEntropyMappedFiberLoss leaf.profile.count k *
          leaf.marginalTypeLoss c k) * leaf.jointEntropyBase ^ k := by ring
  have hmarginalPos : 0 < leaf.marginalEntropyBase c ^ k :=
    pow_pos (leaf.marginalEntropyBase_pos c) k
  have hdiv : (leaf.ambientFiberSize k c : ℝ) ≤
      ((WordType.maximumEntropyMappedFiberLoss leaf.profile.count k *
          leaf.marginalTypeLoss c k) * leaf.jointEntropyBase ^ k) /
        leaf.marginalEntropyBase c ^ k :=
    (le_div_iff₀ hmarginalPos).2 hmul
  calc
    (leaf.ambientFiberSize k c : ℝ) ≤
        ((WordType.maximumEntropyMappedFiberLoss leaf.profile.count k *
          leaf.marginalTypeLoss c k) * leaf.jointEntropyBase ^ k) /
          leaf.marginalEntropyBase c ^ k := hdiv
    _ = (WordType.maximumEntropyMappedFiberLoss leaf.profile.count k *
          leaf.marginalTypeLoss c k) *
        (leaf.jointEntropyBase / leaf.marginalEntropyBase c) ^ k := by
      rw [div_pow]
      ring

/-- Positive subexponential loss controlling the exact finite hashing field requirement. -/
noncomputable def hashingRequirementLoss
    (leaf : RationalTypedLeaf support A) (k : ℕ) : ℝ :=
  4 * WordType.maximumEntropyMappedFiberLoss leaf.profile.count k *
    ∑ c, leaf.marginalTypeLoss c k

/-- The field-requirement loss is positive at every repetition. -/
theorem hashingRequirementLoss_pos
    (leaf : RationalTypedLeaf support A) (k : ℕ) :
    0 < leaf.hashingRequirementLoss k := by
  unfold hashingRequirementLoss
  have hsum : 0 < ∑ c, leaf.marginalTypeLoss c k := by
    exact Finset.sum_pos (fun c _ ↦ (leaf.marginalTypeLoss_pos c k))
      ⟨.X, Finset.mem_univ _⟩
  exact mul_pos (mul_pos (by norm_num)
    (WordType.maximumEntropyMappedFiberLoss_pos leaf.profile.count k)) hsum

/-- The field-requirement loss is subexponential. -/
theorem hashingRequirementLoss_subexponential
    (leaf : RationalTypedLeaf support A) :
    Growth.Subexponential leaf.hashingRequirementLoss := by
  have hmarginal : Growth.Subexponential
      (fun k ↦ ∑ c, leaf.marginalTypeLoss c k) :=
    Growth.Subexponential.fintype_sum
      (fun c k ↦ leaf.marginalTypeLoss c k)
      (fun c ↦ leaf.marginalTypeLoss_subexponential c)
  have hmaximum :=
    WordType.maximumEntropyMappedFiberLoss_subexponential leaf.profile.count
  have hproduct := hmaximum.mul hmarginal
  unfold hashingRequirementLoss
  convert hproduct.const_mul (show (0 : ℝ) ≤ 4 by norm_num) using 1
  funext k
  ring

/-- If the three visible marginal entropy bases coincide, the exact field requirement has
exponential base `jointEntropyBase / marginalBase` and only the packaged subexponential loss.

Proof sketch: apply `ambientFiberSize_cast_le_entropyQuotient` to all three legs, sum the bounds,
and factor out the common entropy quotient. -/
theorem hashingRequirement_cast_le_loss_mul_entropyQuotient_pow
    (leaf : RationalTypedLeaf support A)
    (hcoordinate : leaf.IsSupportCoordinate)
    (hmaximum : leaf.IsMaximumEntropyBits leaf.distribution)
    (marginalBase : ℝ)
    (hcommon : ∀ c, leaf.marginalEntropyBase c = marginalBase)
    {k : ℕ} (hk : 0 < k) :
    (leaf.hashingRequirement k : ℝ) ≤
      leaf.hashingRequirementLoss k *
        (leaf.jointEntropyBase / marginalBase) ^ k := by
  have hfibers : ∑ c, (leaf.ambientFiberSize k c : ℝ) ≤
      ∑ c, (WordType.maximumEntropyMappedFiberLoss leaf.profile.count k *
          leaf.marginalTypeLoss c k) *
        (leaf.jointEntropyBase / marginalBase) ^ k := by
    apply Finset.sum_le_sum
    intro c _
    simpa only [hcommon c] using
      leaf.ambientFiberSize_cast_le_entropyQuotient hcoordinate hmaximum hk c
  change ((4 * ∑ c, leaf.ambientFiberSize k c : ℕ) : ℝ) ≤ _
  push_cast
  calc
    4 * ∑ c, (leaf.ambientFiberSize k c : ℝ) ≤
        4 * ∑ c, (WordType.maximumEntropyMappedFiberLoss leaf.profile.count k *
            leaf.marginalTypeLoss c k) *
          (leaf.jointEntropyBase / marginalBase) ^ k :=
      mul_le_mul_of_nonneg_left hfibers (by norm_num)
    _ = leaf.hashingRequirementLoss k *
        (leaf.jointEntropyBase / marginalBase) ^ k := by
      unfold hashingRequirementLoss
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      ring

/-- Subexponential loss after choosing the next safe prime above the exact hashing requirement. -/
noncomputable def hashingModulusLoss
    (leaf : RationalTypedLeaf support A) (k : ℕ) : ℝ :=
  PrimeFieldSizing.loss 27 leaf.hashingRequirementLoss k

/-- Canonical prime-field selection preserves subexponentiality of the hashing loss. -/
theorem hashingModulusLoss_subexponential
    (leaf : RationalTypedLeaf support A) :
    Growth.Subexponential leaf.hashingModulusLoss :=
  PrimeFieldSizing.loss_subexponential 27 leaf.hashingRequirementLoss_subexponential

/-- The canonical prime selected above the exact requirement has the same entropy quotient base.

The mild premise `1 ≤ jointEntropyBase / marginalBase` is automatic when the visible coordinate
does not increase entropy; clients may prove it from their explicit entropy formulas. -/
theorem hashingModulus_cast_le_loss_mul_entropyQuotient_pow
    (leaf : RationalTypedLeaf support A)
    (hcoordinate : leaf.IsSupportCoordinate)
    (hmaximum : leaf.IsMaximumEntropyBits leaf.distribution)
    (marginalBase : ℝ)
    (hcommon : ∀ c, leaf.marginalEntropyBase c = marginalBase)
    (hbase : 1 ≤ leaf.jointEntropyBase / marginalBase)
    {k : ℕ} (hk : 0 < k) :
    (PrimeFieldSizing.modulus 27 (leaf.hashingRequirement k) : ℝ) ≤
      leaf.hashingModulusLoss k *
        (leaf.jointEntropyBase / marginalBase) ^ k := by
  simpa only [hashingModulusLoss, PrimeFieldSizing.loss, add_assoc] using
    (PrimeFieldSizing.modulus_cast_le_loss_mul_pow
      27 (leaf.hashingRequirement k) k (leaf.hashingRequirementLoss k)
      (leaf.jointEntropyBase / marginalBase) hbase
      (leaf.hashingRequirement_cast_le_loss_mul_entropyQuotient_pow
        hcoordinate hmaximum marginalBase hcommon hk))

end RationalTypedLeaf

end AlgebraicComplexity
