/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.MaximumEntropyTypeCounting
import AlgebraicComplexity.Examples.CoppersmithWinogradSquareCounting
import AlgebraicComplexity.Probability.KullbackLeiblerBasic

/-!
# Maximum entropy of the symmetric CW-square joint type

Equation (12) of Coppersmith--Winograd (1990) sums over all joint contingency tables on the
fifteen degree-four addresses with fixed three marginals.  Equation (13) states that the symmetric
four-orbit table is the maximum term.  This module proves the corresponding exact entropy fact for
every positive integral orbit profile `(a,b,c,d)`.

The proof is an information-projection certificate.  The normalized symmetric law is strictly
positive, and its log-density is a sum of one potential from each tensor leg.  Any competing law
with the same three marginals therefore has the same expected reference log-density.  Gibbs'
inequality makes the entropy gap equal to a nonnegative KL divergence.

The final cardinality theorem applies the generic maximum-entropy type-counting layer: the entire
ambient three-marginal word family is only a polynomial factor larger than the marked symmetric
joint type class.  This is the rigorous replacement for the paper's suppressed `N^{-p}` factor.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

/-- Primitive fifteen-letter symmetric profile, before proportional repetition. -/
abbrev cwSquareBaseProfile (a b c d : ℕ) : CWSquareSupport → ℕ :=
  cwSquareNaturalType a b c d 1

/-- The primitive profile has mass `3a+6b+3c+3d`. -/
theorem cwSquareBaseProfile_profileMass (a b c d : ℕ) :
    WordType.profileMass (cwSquareBaseProfile a b c d) =
      cwSquareStride a b c d := by
  simpa [cwSquareBaseProfile, WordType.profileMass, cwSquareNaturalType] using
    sum_cwSquareNaturalType a b c d 1

/-- Every coordinate of the primitive fifteen-letter profile is positive when all four orbit
counts are positive. -/
theorem cwSquareBaseProfile_pos
    {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (s : CWSquareSupport) : 0 < cwSquareBaseProfile a b c d s := by
  have hs : s.1 ∈
      cwSquare004Orbit ∪ cwSquare013Orbit ∪ cwSquare022Orbit ∪ cwSquare112Orbit := by
    rw [← cwSquareSupport_eq_classOrbits]
    exact s.2
  by_cases h004 : s.1 ∈ cwSquare004Orbit
  · simp [cwSquareBaseProfile, cwSquareNaturalType, cwSquareClassCount, h004, ha]
  by_cases h013 : s.1 ∈ cwSquare013Orbit
  · simp [cwSquareBaseProfile, cwSquareNaturalType, cwSquareClassCount, h004, h013, hb]
  by_cases h022 : s.1 ∈ cwSquare022Orbit
  · simp [cwSquareBaseProfile, cwSquareNaturalType, cwSquareClassCount,
      h004, h013, h022, hc]
  have h112 : s.1 ∈ cwSquare112Orbit := by
    simp only [Finset.mem_union] at hs
    aesop
  simp [cwSquareBaseProfile, cwSquareNaturalType, cwSquareClassCount,
    h004, h013, h022, h112, hd]

/-- Coordinate map from a supported square address to its block degree on one leg. -/
abbrev cwSquareCoordinate (leg : Leg) (s : CWSquareSupport) : Fin 5 := s.1 leg

/-- Log-probability assigned to one `004` address. -/
noncomputable def cwSquareLogA (a b c d : ℕ) : ℝ :=
  Real.log ((a : ℝ) / (cwSquareStride a b c d : ℝ))

/-- Log-probability assigned to one `013` address. -/
noncomputable def cwSquareLogB (a b c d : ℕ) : ℝ :=
  Real.log ((b : ℝ) / (cwSquareStride a b c d : ℝ))

/-- Log-probability assigned to one `022` address. -/
noncomputable def cwSquareLogC (a b c d : ℕ) : ℝ :=
  Real.log ((c : ℝ) / (cwSquareStride a b c d : ℝ))

/-- Log-probability assigned to one `112` address. -/
noncomputable def cwSquareLogD (a b c d : ℕ) : ℝ :=
  Real.log ((d : ℝ) / (cwSquareStride a b c d : ℝ))

/-- Constant term in a log-linear factorization of the symmetric joint law. -/
noncomputable def cwSquareLogKappa (a b c d : ℕ) : ℝ :=
  2 * cwSquareLogD a b c d - cwSquareLogC a b c d

/-- One-coordinate potential whose three-leg sum, together with `cwSquareLogKappa`, gives the
log-density of the symmetric square law. -/
noncomputable def cwSquareLogPotential (a b c d : ℕ) : Fin 5 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => cwSquareLogD a b c d - cwSquareLogKappa a b c d
  | 3 => cwSquareLogB a b c d - cwSquareLogKappa a b c d
  | 4 => cwSquareLogA a b c d - cwSquareLogKappa a b c d

/-- The symmetric square law has a three-marginal log-linear density.

Proof sketch: inspect the four permutation orbits.  On `004`, `013`, `022`, and `112`, the
potential sum simplifies respectively to `log(a/N)`, `log(b/N)`, `log(c/N)`, and `log(d/N)`.
The orbit profile definition gives exactly the same four values for the normalized law. -/
theorem cwSquare_log_normalizedProfileProbability_weight
    {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (s : CWSquareSupport) :
    Real.log ((WordType.normalizedProfileProbability
      (cwSquareBaseProfile a b c d) (by
        rw [cwSquareBaseProfile_profileMass]
        unfold cwSquareStride
        positivity)).weight s) =
      (cwSquareLogKappa a b c d + cwSquareLogPotential a b c d (s.1 .X)) +
        (cwSquareLogPotential a b c d (s.1 .Y) +
          cwSquareLogPotential a b c d (s.1 .Z)) := by
  rcases s with ⟨s, hsupp⟩
  have hs : s ∈
      cwSquare004Orbit ∪ cwSquare013Orbit ∪ cwSquare022Orbit ∪ cwSquare112Orbit := by
    rw [← cwSquareSupport_eq_classOrbits]
    exact hsupp
  by_cases h004 : s ∈ cwSquare004Orbit
  · simp only [cwSquare004Orbit, Finset.mem_insert, Finset.mem_singleton] at h004
    rcases h004 with rfl | rfl | rfl <;>
      simp [WordType.normalizedProfileProbability_weight,
        cwSquareBaseProfile_profileMass, cwSquareBaseProfile, cwSquareNaturalType,
        cwSquareClassCount, cwSquare004Orbit, cwSquare013Orbit, cwSquare022Orbit,
        cwSquare112Orbit, cwSquareLogPotential, cwSquareLogKappa, cwSquareLogA,
        cwSquareLogB, cwSquareLogC, cwSquareLogD] <;> ring
  by_cases h013 : s ∈ cwSquare013Orbit
  · simp only [cwSquare013Orbit, Finset.mem_insert, Finset.mem_singleton] at h013
    rcases h013 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [WordType.normalizedProfileProbability_weight,
        cwSquareBaseProfile_profileMass, cwSquareBaseProfile, cwSquareNaturalType,
        cwSquareClassCount, cwSquare004Orbit, cwSquare013Orbit, cwSquare022Orbit,
        cwSquare112Orbit, cwSquareLogPotential, cwSquareLogKappa, cwSquareLogA,
        cwSquareLogB, cwSquareLogC, cwSquareLogD] <;> ring
  by_cases h022 : s ∈ cwSquare022Orbit
  · simp only [cwSquare022Orbit, Finset.mem_insert, Finset.mem_singleton] at h022
    rcases h022 with rfl | rfl | rfl <;>
      simp [WordType.normalizedProfileProbability_weight,
        cwSquareBaseProfile_profileMass, cwSquareBaseProfile, cwSquareNaturalType,
        cwSquareClassCount, cwSquare004Orbit, cwSquare013Orbit, cwSquare022Orbit,
        cwSquare112Orbit, cwSquareLogPotential, cwSquareLogKappa, cwSquareLogA,
        cwSquareLogB, cwSquareLogC, cwSquareLogD] <;> ring
  have h112 : s ∈ cwSquare112Orbit := by
    simp only [Finset.mem_union] at hs
    aesop
  simp only [cwSquare112Orbit, Finset.mem_insert, Finset.mem_singleton] at h112
  rcases h112 with rfl | rfl | rfl <;>
    simp [WordType.normalizedProfileProbability_weight,
      cwSquareBaseProfile_profileMass, cwSquareBaseProfile, cwSquareNaturalType,
      cwSquareClassCount, cwSquare004Orbit, cwSquare013Orbit, cwSquare022Orbit,
      cwSquare112Orbit, cwSquareLogPotential, cwSquareLogKappa, cwSquareLogA,
      cwSquareLogB, cwSquareLogC, cwSquareLogD] <;> ring

/-- The normalized symmetric orbit profile maximizes entropy among all laws with the same three
coordinate marginals.

Proof sketch: the preceding log-linear identity makes the expected reference log-density depend
only on the three coordinate pushforwards.  For a competitor in the same mapped fiber this
expectation therefore agrees with the reference expectation.  KL divergence is the reference
entropy minus competitor entropy and is nonnegative. -/
theorem cwSquareBaseProfile_isMaximumEntropy
    {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    WordType.IsMaximumEntropyInMappedFiber cwSquareCoordinate
      (WordType.normalizedProfileProbability
        (cwSquareBaseProfile a b c d) (by
          rw [cwSquareBaseProfile_profileMass]
          unfold cwSquareStride
          positivity)) := by
  let p := WordType.normalizedProfileProbability
    (cwSquareBaseProfile a b c d) (by
      rw [cwSquareBaseProfile_profileMass]
      unfold cwSquareStride
      positivity)
  intro q hq
  change ∀ c, q.pushforward (cwSquareCoordinate c) =
    p.pushforward (cwSquareCoordinate c) at hq
  have hp : ∀ s, 0 < p.weight s := by
    intro s
    exact div_pos (by exact_mod_cast cwSquareBaseProfile_pos ha hb hc hd s)
      (by
        rw [cwSquareBaseProfile_profileMass]
        exact_mod_cast (show 0 < cwSquareStride a b c d by
          unfold cwSquareStride
          positivity))
  let xPot : CWSquareSupport → ℝ :=
    (fun i ↦ cwSquareLogKappa a b c d + cwSquareLogPotential a b c d i) ∘
      cwSquareCoordinate .X
  let yPot : CWSquareSupport → ℝ :=
    cwSquareLogPotential a b c d ∘ cwSquareCoordinate .Y
  let zPot : CWSquareSupport → ℝ :=
    cwSquareLogPotential a b c d ∘ cwSquareCoordinate .Z
  have hx : q.expectation xPot = p.expectation xPot := by
    exact ProbabilityVector.expectation_comp_eq_of_pushforward_eq
      (cwSquareCoordinate .X) q p (hq .X)
      (fun i ↦ cwSquareLogKappa a b c d + cwSquareLogPotential a b c d i)
  have hy : q.expectation yPot = p.expectation yPot := by
    exact ProbabilityVector.expectation_comp_eq_of_pushforward_eq
      (cwSquareCoordinate .Y) q p (hq .Y) (cwSquareLogPotential a b c d)
  have hz : q.expectation zPot = p.expectation zPot := by
    exact ProbabilityVector.expectation_comp_eq_of_pushforward_eq
      (cwSquareCoordinate .Z) q p (hq .Z) (cwSquareLogPotential a b c d)
  have hlog : q.expectation (fun s ↦ Real.log (p.weight s)) =
      p.expectation (fun s ↦ Real.log (p.weight s)) := by
    calc
      q.expectation (fun s ↦ Real.log (p.weight s)) =
          q.expectation (fun s ↦ xPot s + (yPot s + zPot s)) :=
        q.expectation_congr fun s ↦
          by simpa only [xPot, yPot, zPot, Function.comp_apply] using
            cwSquare_log_normalizedProfileProbability_weight ha hb hc hd s
      _ = q.expectation xPot + (q.expectation yPot + q.expectation zPot) := by
        rw [ProbabilityVector.expectation_add q xPot
          (fun s ↦ yPot s + zPot s),
          ProbabilityVector.expectation_add q yPot zPot]
      _ = p.expectation xPot + (p.expectation yPot + p.expectation zPot) := by
        rw [hx, hy, hz]
      _ = p.expectation (fun s ↦ xPot s + (yPot s + zPot s)) := by
        rw [ProbabilityVector.expectation_add p xPot
          (fun s ↦ yPot s + zPot s),
          ProbabilityVector.expectation_add p yPot zPot]
      _ = p.expectation (fun s ↦ Real.log (p.weight s)) :=
        p.expectation_congr fun s ↦
          by simpa only [xPot, yPot, zPot, Function.comp_apply] using
            (cwSquare_log_normalizedProfileProbability_weight ha hb hc hd s).symm
  have hgap := ProbabilityVector.klDiv_eq_entropy_sub_of_expectation_log_eq q p hp hlog
  have hnonneg := ProbabilityVector.klDiv_nonneg q p hp
  linarith

/-! ## Finite ambient-to-marked comparison -/

/-- Scaling the primitive orbit profile by `k` gives the marked square profile used in the
finite extraction. -/
theorem cwSquareNaturalType_eq_proportionalCounts (a b c d k : ℕ) :
    cwSquareNaturalType a b c d k =
      WordType.proportionalCounts (cwSquareBaseProfile a b c d) k := by
  funext s
  simp [cwSquareBaseProfile, cwSquareNaturalType, WordType.proportionalCounts]

/-- Function-word presentation of the ambient CW-square marginal fiber.

The tensor implementation uses recursively parenthesized positive words, while the reusable
method-of-types theorem uses functions on `Fin n`.  This definition is only their canonical
finite-set transport. -/
noncomputable def cwSquareAmbientFunctionWords (a b c d k : ℕ) :
    Finset (Fin (cwSquareDepth a b c d k + 1) → CWSquareSupport) :=
  (cwSquareAmbientWords a b c d k).map
    (positiveWordEquiv CWSquareSupport (cwSquareDepth a b c d k)).toEmbedding

/-- Transporting the ambient family to function words does not change its cardinality. -/
@[simp] theorem card_cwSquareAmbientFunctionWords (a b c d k : ℕ) :
    (cwSquareAmbientFunctionWords a b c d k).card =
      (cwSquareAmbientWords a b c d k).card := by
  simp [cwSquareAmbientFunctionWords]

/-- Every function word in the ambient CW-square family has the mapped types of the marked
proportional joint profile.

Proof sketch: decode the function word through `positiveWordEquiv`.  Ambient membership gives
the prescribed multiplicity after projection to each tensor leg.  Multiplicity commutes with
letterwise projection, and the symmetric marked joint profile has exactly those marginals. -/
theorem cwSquareAmbientFunctionWord_mappedType
    (a b c d k : ℕ)
    (word : Fin (cwSquareDepth a b c d k + 1) → CWSquareSupport)
    (hword : word ∈ cwSquareAmbientFunctionWords a b c d k) (leg : Leg) :
    WordType.mappedType (cwSquareCoordinate leg) (WordType.multiplicity word) =
      WordType.mappedType (cwSquareCoordinate leg)
        (WordType.proportionalCounts (cwSquareBaseProfile a b c d) k) := by
  classical
  rw [cwSquareAmbientFunctionWords, Finset.mem_map] at hword
  obtain ⟨source, hsource, rfl⟩ := hword
  have hkeep :=
    (mem_cwSquareAmbientWords_iff_keepMarginals a b c d k source).mp hsource leg
  unfold cwSquareKeepMarginal at hkeep
  rw [PartitionHashEncoding.positiveWordEquiv_supportWordAddress
    (A := fun _ : Leg ↦ Fin 5) (support := cwSquareSupport)] at hkeep
  change WordType.multiplicity
      (cwSquareCoordinate leg ∘
        positiveWordEquiv CWSquareSupport (cwSquareDepth a b c d k) source) =
    cwSquareMarginalType a b c d k at hkeep
  rw [WordType.multiplicity_comp_eq_mappedType] at hkeep
  calc
    WordType.mappedType (cwSquareCoordinate leg)
        (WordType.multiplicity
          (positiveWordEquiv CWSquareSupport (cwSquareDepth a b c d k) source)) =
        cwSquareMarginalType a b c d k := hkeep
    _ = WordType.mappedType (cwSquareCoordinate leg)
        (cwSquareNaturalType a b c d k) :=
      (cwSquare_mappedType_eq_marginal a b c d k leg).symm
    _ = WordType.mappedType (cwSquareCoordinate leg)
        (WordType.proportionalCounts (cwSquareBaseProfile a b c d) k) := by
      rw [cwSquareNaturalType_eq_proportionalCounts]

/-- Explicit polynomial loss comparing the ambient three-marginal family with the marked joint
type class. -/
noncomputable def cwSquareOuterTypeLoss (a b c d k : ℕ) : ℝ :=
  (((cwSquareStride a b c d * k + 1) ^ 15 : ℕ) : ℝ) *
    WordType.structuralZeroMultinomialLoss (cwSquareBaseProfile a b c d) k

/-- The explicit outer type-selection loss is subexponential in the proportional repetition. -/
theorem cwSquareOuterTypeLoss_subexponential (a b c d : ℕ) :
    Growth.Subexponential (cwSquareOuterTypeLoss a b c d) := by
  let stride := cwSquareStride a b c d
  have htype : Growth.Subexponential
      (fun k ↦ (((stride * k + 1) ^ 15 : ℕ) : ℝ)) := by
    have hmajor := (Growth.Subexponential.natCast_succ_pow 15).const_mul
      (show (0 : ℝ) ≤ (stride + 1 : ℕ) ^ 15 by positivity)
    apply hmajor.mono
    · intro k
      positivity
    · intro k
      have hbase : stride * k + 1 ≤ (stride + 1) * (k + 1) := by
        nlinarith
      calc
        (((stride * k + 1) ^ 15 : ℕ) : ℝ) ≤
            ((((stride + 1) * (k + 1)) ^ 15 : ℕ) : ℝ) := by
          exact_mod_cast Nat.pow_le_pow_left hbase 15
        _ = ((stride + 1 : ℕ) : ℝ) ^ 15 *
            ((k + 1 : ℕ) : ℝ) ^ 15 := by
          push_cast
          rw [mul_pow]
  have hproduct := htype.mul
    (WordType.structuralZeroMultinomialLoss_subexponential
      (cwSquareBaseProfile a b c d))
  change Growth.Subexponential (fun k ↦
    (((cwSquareStride a b c d * k + 1) ^ 15 : ℕ) : ℝ) *
      WordType.structuralZeroMultinomialLoss (cwSquareBaseProfile a b c d) k)
  simpa only [stride] using hproduct

/-- The explicit outer type-selection loss is strictly positive. -/
theorem cwSquareOuterTypeLoss_pos (a b c d k : ℕ) :
    0 < cwSquareOuterTypeLoss a b c d k := by
  unfold cwSquareOuterTypeLoss
  exact mul_pos (by positivity)
    (WordType.structuralZeroMultinomialLoss_pos _ _)

/-- The entire ambient three-marginal family is at most an explicit polynomial factor larger
than the marked symmetric joint type class.

This is the finite, division-free form of the global CW type-counting estimate.  It retains all
structural-zero safeguards even though the present positive-orbit specialization has none.

Proof sketch: transport recursive words to functions, apply the generic maximum-entropy fiber
bound, identify the fifteen-letter profile and its proportional scaling, and use the exact
multinomial cardinality of the marked type class. -/
theorem card_cwSquareAmbientWords_le_outerTypeLoss_mul_markedWords
    {a b c d k : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hk : 0 < k) :
    ((cwSquareAmbientWords a b c d k).card : ℝ) ≤
      cwSquareOuterTypeLoss a b c d k *
        (cwSquareMarkedWords a b c d k).card := by
  have hstride : 0 < cwSquareStride a b c d := by
    unfold cwSquareStride
    positivity
  have hrefMass : 0 < WordType.profileMass (cwSquareBaseProfile a b c d) := by
    rw [cwSquareBaseProfile_profileMass]
    exact hstride
  have hambient :=
    WordType.card_words_le_typeCount_mul_structuralZeroLoss_mul_referenceTypeClass
      cwSquareCoordinate (cwSquareBaseProfile a b c d) hrefMass
      (cwSquareBaseProfile_isMaximumEntropy ha hb hc hd) hk
      (by
        rw [cwSquareBaseProfile_profileMass]
        exact cwSquareDepth_add_one hstride hk)
      (cwSquareAmbientFunctionWords a b c d k)
      (cwSquareAmbientFunctionWord_mappedType a b c d k)
  have hsupportCard : Fintype.card CWSquareSupport = 15 := by
    simpa using card_cwSquareSupport
  have htype : cwSquareNaturalType a b c d k ∈
      WordType.types CWSquareSupport (cwSquareDepth a b c d k + 1) :=
    cwSquareNaturalType_mem_types hstride hk
  have hmarked : (cwSquareMarkedWords a b c d k).card =
      Nat.multinomial Finset.univ
        (WordType.proportionalCounts (cwSquareBaseProfile a b c d) k) := by
    rw [← cwSquareNaturalType_eq_proportionalCounts]
    exact card_positiveTypeClass_eq_multinomial _ _ htype
  rw [card_cwSquareAmbientFunctionWords, hsupportCard,
    cwSquareDepth_add_one hstride hk, ← hmarked] at hambient
  simpa only [cwSquareOuterTypeLoss, Nat.cast_mul] using hambient

end AlgebraicComplexity.Examples
