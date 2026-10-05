/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.MaximumEntropyMappedFiber
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafCore
import AlgebraicComplexity.Probability.IntegralProfileCore

/-!
# Rational typed leaves for laser-method constructions

This module separates the reusable typed-leaf calculation from every named tensor and numerical
certificate.  A positive integral profile represents an exact rational distribution.  A typed
leaf then records three coordinate projections and one positive matrix dimension per coordinate
and support letter.  From this data we obtain:

* exact matrix-multiplication dimensions for every proportional finite type;
* the three marginal entropy rates and the common combination-loss correction;
* expected logarithmic matrix dimensions; and
* equivariance and heterogeneous branchwise assembly under arbitrary leg permutations.

The normalization is deliberately integral rather than real.  Every rational certificate type is
represented exactly after restricting away zero coordinates, while all finite tensor statements
remain denominator-free.  Approximation of arbitrary real types is a separate continuity layer.
-/

open scoped BigOperators

namespace AlgebraicComplexity

open Tensor

universe u v w x y

namespace PositiveIntegralProfile

variable {I : Type u} [Fintype I] [Nonempty I]

/-- Total denominator of the normalized rational profile. -/
def mass (profile : PositiveIntegralProfile I) : ℕ :=
  WordType.profileMass profile.count

theorem mass_pos (profile : PositiveIntegralProfile I) : 0 < profile.mass := by
  unfold mass WordType.profileMass
  exact Finset.sum_pos (fun i _ ↦ profile.count_pos i) Finset.univ_nonempty

/-- Exact real probability vector represented by an integral profile. -/
noncomputable def probability (profile : PositiveIntegralProfile I) : ProbabilityVector I where
  weight i := (profile.count i : ℝ) / (profile.mass : ℝ)
  nonneg i := div_nonneg (by positivity) (by positivity)
  total := by
    rw [← Finset.sum_div]
    have hsum : (∑ i, (profile.count i : ℝ)) = (profile.mass : ℝ) := by
      exact_mod_cast (rfl : (∑ i, profile.count i) = profile.mass)
    rw [hsum, div_self]
    exact_mod_cast profile.mass_pos.ne'

@[simp] theorem probability_weight (profile : PositiveIntegralProfile I) (i : I) :
    profile.probability.weight i =
      (profile.count i : ℝ) / (profile.mass : ℝ) :=
  rfl

/-- The profile has full support, as expected after zero coordinates have been removed. -/
theorem probability_weight_pos (profile : PositiveIntegralProfile I) (i : I) :
    0 < profile.probability.weight i := by
  exact div_pos (by exact_mod_cast profile.count_pos i)
    (by exact_mod_cast profile.mass_pos)

/-- Scaling an integral profile does not change its normalized rational law. -/
theorem proportional_probability_weight (profile : PositiveIntegralProfile I)
    {k : ℕ} (hk : 0 < k) (i : I) :
    ((WordType.proportionalCounts profile.count k i : ℕ) : ℝ) /
        (WordType.profileMass (WordType.proportionalCounts profile.count k) : ℝ) =
      profile.probability.weight i := by
  have hmass :
      WordType.profileMass (WordType.proportionalCounts profile.count k) =
        profile.mass * k := by
    simp [WordType.profileMass, WordType.proportionalCounts, mass, Finset.sum_mul]
  rw [hmass]
  simp only [WordType.proportionalCounts, probability_weight]
  push_cast
  have hkReal : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp [hkReal, profile.mass_pos.ne']

/-- Pushforward of the normalized profile has the normalized mapped integral counts. -/
theorem pushforward_weight
    {J : Type v} [Fintype J] [DecidableEq J]
    (profile : PositiveIntegralProfile I) (coordinate : I → J) (j : J) :
    (profile.probability.pushforward coordinate).weight j =
      (WordType.mappedType coordinate profile.count j : ℝ) /
        (profile.mass : ℝ) := by
  rw [ProbabilityVector.pushforward_weight]
  unfold WordType.mappedType WordType.letterFiber
  rw [Finset.sum_filter]
  have hterm (i : I) :
      (if coordinate i = j then profile.probability.weight i else 0) =
        (if coordinate i = j then (profile.count i : ℝ) else 0) /
          (profile.mass : ℝ) := by
    by_cases h : coordinate i = j <;> simp [h, probability_weight]
  simp_rw [hterm]
  rw [← Finset.sum_div]
  congr 1
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : coordinate i = j <;> simp [h]

end PositiveIntegralProfile

namespace RationalTypedLeaf

variable {I : Type u} [Fintype I] [Nonempty I]
variable {A : Leg → Type v} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

/-- Rational distribution on leaf letters. -/
noncomputable def distribution (leaf : RationalTypedLeaf I A) : ProbabilityVector I :=
  leaf.profile.probability

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- A typed leaf's rational law is the generic normalization of its exact integral count table. -/
theorem distribution_eq_normalizedProfileProbability
    (leaf : RationalTypedLeaf I A) :
    leaf.distribution =
      WordType.normalizedProfileProbability leaf.profile.count leaf.profile.mass_pos := by
  apply ProbabilityVector.ext
  funext i
  rfl

/-- Coordinate marginal of the rational leaf type. -/
noncomputable def marginal (leaf : RationalTypedLeaf I A) (c : Leg) :
    ProbabilityVector (A c) :=
  leaf.distribution.pushforward (leaf.coordinate c)

/-- Two laws on a typed leaf have the same three interface marginals. -/
def SameMarginals (leaf : RationalTypedLeaf I A)
    (p q : ProbabilityVector I) : Prop :=
  ∀ c, p.pushforward (leaf.coordinate c) = q.pushforward (leaf.coordinate c)

/-- A law is rigid in the three-marginal fiber when no other law has the same interfaces. -/
def IsMarginalRigid (leaf : RationalTypedLeaf I A) (p : ProbabilityVector I) : Prop :=
  ∀ q, leaf.SameMarginals p q → q = p

/-- A law maximizes base-two entropy in its three-marginal fiber. -/
def IsMaximumEntropyBits (leaf : RationalTypedLeaf I A) (p : ProbabilityVector I) : Prop :=
  ∀ q, leaf.SameMarginals p q → q.entropyBits ≤ p.entropyBits

/-- Marginal rigidity is a certificate of maximum entropy; no optimization is needed. -/
theorem IsMarginalRigid.isMaximumEntropyBits
    {leaf : RationalTypedLeaf I A} {p : ProbabilityVector I}
    (h : leaf.IsMarginalRigid p) : leaf.IsMaximumEntropyBits p := by
  intro q hq
  rw [h q hq]

/-- Convert the typed-leaf maximum-entropy predicate in bits to the generic natural-log
mapped-fiber predicate.  This semantic bridge is independent of finite type counting. -/
theorem IsMaximumEntropyBits.isMaximumEntropyInMappedFiber
    {leaf : RationalTypedLeaf I A}
    (hmaximum : leaf.IsMaximumEntropyBits leaf.distribution) :
    WordType.IsMaximumEntropyInMappedFiber leaf.coordinate
      (WordType.normalizedProfileProbability
        leaf.profile.count leaf.profile.mass_pos) := by
  intro candidate hcandidates
  have hdistribution := leaf.distribution_eq_normalizedProfileProbability
  have hbits : candidate.entropyBits ≤ leaf.distribution.entropyBits := by
    apply hmaximum candidate
    intro c
    rw [hdistribution]
    exact (hcandidates c).symm
  unfold ProbabilityVector.entropyBits at hbits
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (div_le_div_iff_of_pos_right hlogTwo).mp (by
    simpa only [hdistribution] using hbits)

/-- Entropy of a coordinate marginal, in bits per source letter. -/
noncomputable def marginalEntropyBits (leaf : RationalTypedLeaf I A) (c : Leg) : ℝ :=
  (leaf.marginal c).entropyBits

/-- Common combination loss of a supplied type relative to a maximum-entropy value in its
three-coordinate marginal fiber. -/
noncomputable def combinationLossBits
    (leaf : RationalTypedLeaf I A) (maximumEntropyBits : ℝ) : ℝ :=
  maximumEntropyBits - leaf.distribution.entropyBits

/-- Branchwise retained exponent.  The same joint-type combination loss is subtracted from each
coordinate marginal entropy. -/
noncomputable def retainedRateBits
    (leaf : RationalTypedLeaf I A) (maximumEntropyBits : ℝ) (c : Leg) : ℝ :=
  leaf.marginalEntropyBits c - leaf.combinationLossBits maximumEntropyBits

/-- Every exact dimension product of a rational typed leaf is strictly positive.

Proof sketch: each constituent dimension is positive by the typed-leaf contract, hence so is
every natural power and their finite product. -/
theorem dimensionProduct_pos (leaf : RationalTypedLeaf I A) (c : Leg) :
    0 < leaf.dimensionProduct c := by
  unfold dimensionProduct
  apply Finset.prod_pos
  intro i _hi
  exact pow_pos (leaf.dimension_pos i c) _

/-- Expected base-two logarithmic matrix dimension per source letter. -/
noncomputable def dimensionRateBits (leaf : RationalTypedLeaf I A) (c : Leg) : ℝ :=
  leaf.distribution.expectation fun i ↦
    Real.log (leaf.dimension i c) / Real.log 2

/-- The logarithm of the exact finite dimension product is the profile mass times its expected
logarithmic dimension. -/
theorem log_dimensionProduct_div_logTwo
    (leaf : RationalTypedLeaf I A) (c : Leg) :
    Real.log (leaf.dimensionProduct c : ℝ) / Real.log 2 =
      (leaf.profile.mass : ℝ) * leaf.dimensionRateBits c := by
  have hfactor (i : I) : (0 : ℝ) < leaf.dimension i c := by
    exact_mod_cast leaf.dimension_pos i c
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold dimensionProduct dimensionRateBits distribution ProbabilityVector.expectation
  rw [← leaf.profile.alphabet_eq_univ]
  rw [Nat.cast_prod, Real.log_prod]
  · simp_rw [Nat.cast_pow, Real.log_pow, PositiveIntegralProfile.probability_weight]
    have hmass : (leaf.profile.mass : ℝ) ≠ 0 := by
      exact_mod_cast leaf.profile.mass_pos.ne'
    rw [Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hmass, hlogTwo]
  · intro i _
    exact_mod_cast pow_ne_zero (leaf.profile.count i)
      (Nat.ne_of_gt (leaf.dimension_pos i c))

end RationalTypedLeaf

/-! ## Orientation and heterogeneous branchwise assembly -/

/-- Transport a three-coordinate quantity through an arbitrary leg permutation. -/
def permuteLegValues {R : Type*} (sigma : Equiv.Perm Leg) (value : Leg → R) : Leg → R :=
  fun c ↦ value (sigma.symm c)

@[simp] theorem permuteLegValues_apply {R : Type*}
    (sigma : Equiv.Perm Leg) (value : Leg → R) (c : Leg) :
    permuteLegValues sigma value c = value (sigma.symm c) :=
  rfl

/-- Permuting coordinates does not change their sum. -/
theorem sum_permuteLegValues
    {R : Type*} [AddCommMonoid R] (sigma : Equiv.Perm Leg) (value : Leg → R) :
    (∑ c, permuteLegValues sigma value c) = ∑ c, value c := by
  simpa [permuteLegValues] using sigma.symm.sum_comp value

/-- Coordinatewise weighted total of a heterogeneous leaf family. -/
def weightedLegTotal
    {J : Type*} [Fintype J]
    (weight : J → ℝ) (value : J → Leg → ℝ) (c : Leg) : ℝ :=
  ∑ j, weight j * value j c

/-- Arbitrary repeated orientations commute with heterogeneous coordinatewise assembly. -/
theorem weightedLegTotal_permute
    {J : Type*} [Fintype J]
    (weight : J → ℝ) (sigma : J → Equiv.Perm Leg)
    (value : J → Leg → ℝ) (c : Leg) :
    weightedLegTotal weight (fun j ↦ permuteLegValues (sigma j) (value j)) c =
      ∑ j, weight j * value j ((sigma j).symm c) := by
  rfl

/-- Bottleneck among three assembled coordinate branches.  Clients must apply this *after*
forming `weightedLegTotal`; summing leafwise minima would discard useful asymmetry. -/
def minimumLegValue (value : Leg → ℝ) : ℝ :=
  min (value .X) (min (value .Y) (value .Z))

/-! ## Branch-first aggregation -/

/-- Aggregating directional values before taking the bottleneck is never worse than taking the
per-leaf bottleneck first.  This elementary inequality is the order-theoretic reason that a
heterogeneous typed-leaf family must be assembled branchwise: `min (∑ v_X, ∑ v_Y, ∑ v_Z)`
dominates `∑ min (v_X, v_Y, v_Z)` for nonnegative weights. -/
theorem sum_weighted_minimumLegValue_le_minimumLegValue_weightedLegTotal
    {J : Type*} [Fintype J]
    (weight : J → ℝ) (value : J → Leg → ℝ)
    (hweight : ∀ j, 0 ≤ weight j) :
    (∑ j, weight j * minimumLegValue (value j)) ≤
      minimumLegValue (weightedLegTotal weight value) := by
  unfold minimumLegValue weightedLegTotal
  refine le_min ?_ ?_
  · exact Finset.sum_le_sum fun j _hj ↦
      mul_le_mul_of_nonneg_left
        (min_le_left (value j .X) (min (value j .Y) (value j .Z))) (hweight j)
  · refine le_min ?_ ?_
    · exact Finset.sum_le_sum fun j _hj ↦
        mul_le_mul_of_nonneg_left
          (le_trans (min_le_right (value j .X) (min (value j .Y) (value j .Z)))
            (min_le_left (value j .Y) (value j .Z))) (hweight j)
    · exact Finset.sum_le_sum fun j _hj ↦
        mul_le_mul_of_nonneg_left
          (le_trans (min_le_right (value j .X) (min (value j .Y) (value j .Z)))
            (min_le_right (value j .Y) (value j .Z))) (hweight j)

end AlgebraicComplexity
