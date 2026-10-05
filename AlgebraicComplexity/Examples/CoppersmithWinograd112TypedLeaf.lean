/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112CTensor
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeaf
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafExtraction

/-!
# The rational typed-leaf interface for the exceptional CW constituent

This module is the named-tensor corollary of the paper-independent rational typed-leaf theorem.
For positive integers `L` and `G`, the four supported addresses have exact multiplicities
`(L,L,G,G)`.  Writing

`mu = L / (2 * (L + G))`,

the two binary block marginals have entropy one and the ternary marginal has entropy
`H(mu, mu, 1 - 2 * mu)`.  The exact rectangular matrix-multiplication tensor carried by one
primitive type is

`<q^(2G), q^(2L), q^(2G)>`.

The finite restriction theorem at the end is obtained by instantiating
`RationalTypedLeaf.positivePower_constituent_matrixMultiplication_proportional`; it does not
duplicate the tensor-product argument.  Coordinate permutations needed by the three positive
level-two shapes are intentionally downstream of this canonical `112` orientation.
-/

open scoped BigOperators

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

instance cw112BlockSupport_nonempty : Nonempty cw112BlockSupport :=
  ⟨cw112DiagonalFirstS⟩

/-- Exact positive profile `(L,L,G,G)` on the four-address CW `112` support. -/
def cw112IntegralProfile (L G : ℕ) (hL : 0 < L) (hG : 0 < G) :
    PositiveIntegralProfile cw112BlockSupport where
  alphabet := Finset.univ
  complete := by simp
  count := cw112NaturalType L G
  count_pos s := by
    rcases s with ⟨s, hs⟩
    simp only [cw112BlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl <;>
      simp [cw112NaturalType, cw112DiagonalFirstAddress,
        cw112DiagonalSecondAddress, cw112CrossFirstAddress,
        cw112CrossSecondAddress, cw112BlockAddress, hL, hG]

/-- The denominator of the normalized `(L,L,G,G)` law is `2(L+G)`. -/
@[simp] theorem cw112IntegralProfile_mass
    (L G : ℕ) (hL : 0 < L) (hG : 0 < G) :
    (cw112IntegralProfile L G hL hG).mass = 2 * (L + G) := by
  unfold PositiveIntegralProfile.mass WordType.profileMass cw112IntegralProfile
  rw [sum_cw112BlockSupportSubtype]
  simp [cw112NaturalType, cw112DiagonalFirstAddress,
    cw112DiagonalSecondAddress, cw112CrossFirstAddress,
    cw112CrossSecondAddress, cw112BlockAddress]
  omega

/-- Canonical matrix-multiplication dimension attached to one supported address. -/
def cw112LeafDimension (q : ℕ) (s : cw112BlockSupport) : Leg → ℕ
  | .X => match s.1 .Z with
    | .grid => q
    | _ => 1
  | .Y => match s.1 .Z with
    | .grid => 1
    | _ => q
  | .Z => match s.1 .Z with
    | .grid => q
    | _ => 1

theorem cw112LeafDimension_pos {q : ℕ} (hq : 0 < q)
    (s : cw112BlockSupport) (c : Leg) :
    0 < cw112LeafDimension q s c := by
  rcases s with ⟨s, hs⟩
  simp only [cw112BlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl <;> cases c <;>
    simp [cw112LeafDimension, cw112DiagonalFirstAddress,
      cw112DiagonalSecondAddress, cw112CrossFirstAddress,
      cw112CrossSecondAddress, cw112BlockAddress, hq]

/-- The canonical CW `112` rational typed leaf. -/
def cw112RationalTypedLeaf (q L G : ℕ)
    (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    RationalTypedLeaf cw112BlockSupport CW112Block where
  profile := cw112IntegralProfile L G hL hG
  coordinate c s := s.1 c
  dimension := cw112LeafDimension q
  dimension_pos := cw112LeafDimension_pos hq

/-- The scalar parameter used by the recursive CW literature, represented exactly. -/
noncomputable def cw112Mu (L G : ℕ) : ℝ :=
  (L : ℝ) / (2 * (L + G) : ℕ)

/-- Base-two ternary entropy `H(mu,mu,1-2mu)`. -/
noncomputable def cw112MuEntropyBits (L G : ℕ) : ℝ :=
  (2 * Real.negMulLog (cw112Mu L G) +
      Real.negMulLog (1 - 2 * cw112Mu L G)) / Real.log 2

/-- Base-two logarithm of the CW parameter `q`. -/
noncomputable def cw112LogQBits (q : ℕ) : ℝ :=
  Real.log q / Real.log 2

/-- Exact marginal weights, before simplifying the three named coordinate types. -/
theorem cw112RationalTypedLeaf_marginal_weight
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (c : Leg) (b : CW112Block c) :
    ((cw112RationalTypedLeaf q L G hq hL hG).marginal c).weight b =
      (cw112MarginalType L G c b : ℝ) / (2 * (L + G) : ℕ) := by
  unfold RationalTypedLeaf.marginal RationalTypedLeaf.distribution
  rw [PositiveIntegralProfile.pushforward_weight]
  change (WordType.mappedType (fun s : cw112BlockSupport ↦ s.1 c)
      (cw112NaturalType L G) b : ℝ) /
        ((cw112IntegralProfile L G hL hG).mass : ℝ) = _
  rw [cw112_mappedType_eq_marginal, cw112IntegralProfile_mass]

private theorem sum_cw112BlockSupport_real
    (f : cw112BlockSupport → ℝ) :
    ∑ s, f s =
      f cw112DiagonalFirstS + f cw112DiagonalSecondS +
        f cw112CrossFirstS + f cw112CrossSecondS := by
  rw [show (Finset.univ : Finset cw112BlockSupport) =
    {cw112DiagonalFirstS, cw112DiagonalSecondS,
      cw112CrossFirstS, cw112CrossSecondS} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- Expand one coordinate pushforward on the four-address support. -/
theorem cw112_pushforward_weight_expansion
    (p : ProbabilityVector cw112BlockSupport) (c : Leg) (b : CW112Block c) :
    (p.pushforward (fun s : cw112BlockSupport ↦ s.1 c)).weight b =
      (if cw112DiagonalFirstS.1 c = b then p.weight cw112DiagonalFirstS else 0) +
      (if cw112DiagonalSecondS.1 c = b then p.weight cw112DiagonalSecondS else 0) +
      (if cw112CrossFirstS.1 c = b then p.weight cw112CrossFirstS else 0) +
      (if cw112CrossSecondS.1 c = b then p.weight cw112CrossSecondS else 0) := by
  rw [ProbabilityVector.pushforward_weight, sum_cw112BlockSupport_real]

/-- The three labelled marginals determine every probability law on the CW `112` support.
This is a structural statement about the four-address support, independent of `q`, `L`, or `G`. -/
theorem cw112_coordinateMarginals_injective
    {p q : ProbabilityVector cw112BlockSupport}
    (h : ∀ c, p.pushforward (fun s : cw112BlockSupport ↦ s.1 c) =
      q.pushforward (fun s : cw112BlockSupport ↦ s.1 c)) :
    p = q := by
  have hDiagonalFirst := congrArg (fun law ↦ law.weight CW112ZBlock.firstCorner) (h .Z)
  have hDiagonalSecond := congrArg (fun law ↦ law.weight CW112ZBlock.secondCorner) (h .Z)
  have hXFirst := congrArg (fun law ↦ law.weight CW112Side.first) (h .X)
  have hYFirst := congrArg (fun law ↦ law.weight CW112Side.first) (h .Y)
  rw [cw112_pushforward_weight_expansion, cw112_pushforward_weight_expansion]
    at hDiagonalFirst hDiagonalSecond hXFirst hYFirst
  simp [cw112DiagonalFirstAddress, cw112DiagonalSecondAddress,
    cw112CrossFirstAddress, cw112CrossSecondAddress, cw112BlockAddress,
    ofLegs_X, ofLegs_Y, ofLegs_Z] at hDiagonalFirst hDiagonalSecond hXFirst hYFirst
  have hCrossFirst : p.weight cw112CrossFirstS = q.weight cw112CrossFirstS := by
    linarith
  have hCrossSecond : p.weight cw112CrossSecondS = q.weight cw112CrossSecondS := by
    linarith
  apply ProbabilityVector.ext
  funext s
  rcases s with ⟨s, hs⟩
  simp only [cw112BlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact hDiagonalFirst
  · exact hDiagonalSecond
  · exact hCrossFirst
  · exact hCrossSecond

/-- The rational CW `112` law is rigid in its marginal fiber. -/
theorem cw112RationalTypedLeaf_isMarginalRigid
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (cw112RationalTypedLeaf q L G hq hL hG).IsMarginalRigid
      (cw112RationalTypedLeaf q L G hq hL hG).distribution := by
  intro p hp
  exact cw112_coordinateMarginals_injective hp |>.symm

/-- Hence the exact joint entropy is the maximum entropy in the prescribed marginal fiber. -/
theorem cw112RationalTypedLeaf_isMaximumEntropyBits
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (cw112RationalTypedLeaf q L G hq hL hG).IsMaximumEntropyBits
      (cw112RationalTypedLeaf q L G hq hL hG).distribution :=
  (cw112RationalTypedLeaf_isMarginalRigid q L G hq hL hG).isMaximumEntropyBits

theorem cw112RationalTypedLeaf_side_weight
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (c : Leg) (hc : c = .X ∨ c = .Y) (b : CW112Block c) :
    ((cw112RationalTypedLeaf q L G hq hL hG).marginal c).weight b = 1 / 2 := by
  rcases hc with rfl | rfl <;>
    rw [cw112RationalTypedLeaf_marginal_weight] <;>
    cases b <;> simp only [cw112MarginalType, cw112SideMarginalType] <;>
    push_cast <;> field_simp

@[simp] theorem cw112RationalTypedLeaf_z_first_weight
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    ((cw112RationalTypedLeaf q L G hq hL hG).marginal .Z).weight
        .firstCorner = cw112Mu L G := by
  rw [cw112RationalTypedLeaf_marginal_weight]
  rfl

@[simp] theorem cw112RationalTypedLeaf_z_second_weight
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    ((cw112RationalTypedLeaf q L G hq hL hG).marginal .Z).weight
        .secondCorner = cw112Mu L G := by
  rw [cw112RationalTypedLeaf_marginal_weight]
  rfl

@[simp] theorem cw112RationalTypedLeaf_z_grid_weight
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    ((cw112RationalTypedLeaf q L G hq hL hG).marginal .Z).weight .grid =
      1 - 2 * cw112Mu L G := by
  rw [cw112RationalTypedLeaf_marginal_weight]
  simp only [cw112MarginalType, cw112ZMarginalType, cw112Mu]
  push_cast
  have hsum : (0 : ℝ) < L + G := by exact_mod_cast Nat.add_pos_left hL G
  field_simp [hsum.ne']
  ring

private theorem sum_cw112Side_real (f : CW112Side → ℝ) :
    ∑ b, f b = f .first + f .second := by
  rw [show (Finset.univ : Finset CW112Side) = {.first, .second} by decide]
  simp

private theorem sum_cw112ZBlock_real (f : CW112ZBlock → ℝ) :
    ∑ b, f b = f .firstCorner + f .secondCorner + f .grid := by
  rw [show (Finset.univ : Finset CW112ZBlock) =
    {.firstCorner, .secondCorner, .grid} by decide]
  simp [add_assoc]

/-- The two binary interface marginals have exactly one bit of entropy. -/
theorem cw112RationalTypedLeaf_side_entropyBits
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (c : Leg) (hc : c = .X ∨ c = .Y) :
    (cw112RationalTypedLeaf q L G hq hL hG).marginalEntropyBits c = 1 := by
  have halfEntropy :
      (Real.negMulLog (1 / 2) + Real.negMulLog (1 / 2)) / Real.log 2 = 1 := by
    have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    rw [Real.negMulLog_eq_neg]
    change (-((1 / 2 : ℝ) * Real.log (1 / 2)) +
        -((1 / 2 : ℝ) * Real.log (1 / 2))) / Real.log 2 = 1
    rw [hhalf]
    field_simp [hlogTwo]
    ring
  rcases hc with rfl | rfl
  ·
    unfold RationalTypedLeaf.marginalEntropyBits ProbabilityVector.entropyBits
      ProbabilityVector.entropy
    rw [sum_cw112Side_real]
    simp_rw [cw112RationalTypedLeaf_side_weight _ _ _ _ _ _ _ (Or.inl rfl)]
    exact halfEntropy
  ·
    unfold RationalTypedLeaf.marginalEntropyBits ProbabilityVector.entropyBits
      ProbabilityVector.entropy
    rw [sum_cw112Side_real]
    simp_rw [cw112RationalTypedLeaf_side_weight _ _ _ _ _ _ _ (Or.inr rfl)]
    exact halfEntropy

/-- The remaining interface marginal is exactly `H(mu,mu,1-2mu)`. -/
theorem cw112RationalTypedLeaf_z_entropyBits
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (cw112RationalTypedLeaf q L G hq hL hG).marginalEntropyBits .Z =
      cw112MuEntropyBits L G := by
  unfold RationalTypedLeaf.marginalEntropyBits ProbabilityVector.entropyBits
    ProbabilityVector.entropy cw112MuEntropyBits
  rw [sum_cw112ZBlock_real]
  simp only [cw112RationalTypedLeaf_z_first_weight,
    cw112RationalTypedLeaf_z_second_weight,
    cw112RationalTypedLeaf_z_grid_weight]
  ring

/-- Canonical retained-rate tuple in the CW `112` orientation.  At this leaf the three
marginals determine the joint law, so the combination-loss term is zero; the equality here is
stated using that exact maximum-entropy value. -/
theorem cw112RationalTypedLeaf_retainedRateBits
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) (c : Leg) :
    (cw112RationalTypedLeaf q L G hq hL hG).retainedRateBits
        (cw112RationalTypedLeaf q L G hq hL hG).distribution.entropyBits c =
      match c with
      | .X => 1
      | .Y => 1
      | .Z => cw112MuEntropyBits L G := by
  unfold RationalTypedLeaf.retainedRateBits RationalTypedLeaf.combinationLossBits
  simp only [sub_self, sub_zero]
  cases c with
  | X => exact cw112RationalTypedLeaf_side_entropyBits q L G hq hL hG .X (Or.inl rfl)
  | Y => exact cw112RationalTypedLeaf_side_entropyBits q L G hq hL hG .Y (Or.inr rfl)
  | Z => exact cw112RationalTypedLeaf_z_entropyBits q L G hq hL hG

/-- Exact primitive rectangular dimension product on the X coordinate. -/
@[simp] theorem cw112RationalTypedLeaf_dimensionProduct_X
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (cw112RationalTypedLeaf q L G hq hL hG).dimensionProduct .X = q ^ (2 * G) := by
  unfold RationalTypedLeaf.dimensionProduct cw112RationalTypedLeaf
  simp only [cw112IntegralProfile]
  rw [prod_cw112BlockSupportSubtype]
  simp [cw112LeafDimension, cw112NaturalType,
    cw112DiagonalFirstAddress, cw112DiagonalSecondAddress,
    cw112CrossFirstAddress, cw112CrossSecondAddress, cw112BlockAddress,
    ← pow_add, two_mul]

/-- Exact primitive rectangular dimension product on the Y coordinate. -/
@[simp] theorem cw112RationalTypedLeaf_dimensionProduct_Y
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (cw112RationalTypedLeaf q L G hq hL hG).dimensionProduct .Y = q ^ (2 * L) := by
  unfold RationalTypedLeaf.dimensionProduct cw112RationalTypedLeaf
  simp only [cw112IntegralProfile]
  rw [prod_cw112BlockSupportSubtype]
  simp [cw112LeafDimension, cw112NaturalType,
    cw112DiagonalFirstAddress, cw112DiagonalSecondAddress,
    cw112CrossFirstAddress, cw112CrossSecondAddress, cw112BlockAddress,
    ← pow_add, two_mul]

/-- Exact primitive rectangular dimension product on the Z coordinate. -/
@[simp] theorem cw112RationalTypedLeaf_dimensionProduct_Z
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (cw112RationalTypedLeaf q L G hq hL hG).dimensionProduct .Z = q ^ (2 * G) := by
  unfold RationalTypedLeaf.dimensionProduct cw112RationalTypedLeaf
  simp only [cw112IntegralProfile]
  rw [prod_cw112BlockSupportSubtype]
  simp [cw112LeafDimension, cw112NaturalType,
    cw112DiagonalFirstAddress, cw112DiagonalSecondAddress,
    cw112CrossFirstAddress, cw112CrossSecondAddress, cw112BlockAddress,
    ← pow_add, two_mul]

/-- Canonical first rectangular dimension rate: `(1-2mu) log₂ q`. -/
theorem cw112RationalTypedLeaf_dimensionRateBits_X
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (cw112RationalTypedLeaf q L G hq hL hG).dimensionRateBits .X =
      (1 - 2 * cw112Mu L G) * cw112LogQBits q := by
  have h := (cw112RationalTypedLeaf q L G hq hL hG).log_dimensionProduct_div_logTwo .X
  rw [cw112RationalTypedLeaf_dimensionProduct_X, Nat.cast_pow, Real.log_pow] at h
  change _ = ((cw112IntegralProfile L G hL hG).mass : ℝ) * _ at h
  rw [cw112IntegralProfile_mass] at h
  unfold cw112Mu cw112LogQBits
  push_cast at h ⊢
  have hsum : (0 : ℝ) < L + G := by exact_mod_cast Nat.add_pos_left hL G
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp [hsum.ne', hlogTwo] at h ⊢
  nlinarith

/-- Canonical middle rectangular dimension rate: `2mu log₂ q`. -/
theorem cw112RationalTypedLeaf_dimensionRateBits_Y
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (cw112RationalTypedLeaf q L G hq hL hG).dimensionRateBits .Y =
      2 * cw112Mu L G * cw112LogQBits q := by
  have h := (cw112RationalTypedLeaf q L G hq hL hG).log_dimensionProduct_div_logTwo .Y
  rw [cw112RationalTypedLeaf_dimensionProduct_Y, Nat.cast_pow, Real.log_pow] at h
  change _ = ((cw112IntegralProfile L G hL hG).mass : ℝ) * _ at h
  rw [cw112IntegralProfile_mass] at h
  unfold cw112Mu cw112LogQBits
  push_cast at h ⊢
  have hsum : (0 : ℝ) < L + G := by exact_mod_cast Nat.add_pos_left hL G
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp [hsum.ne', hlogTwo] at h ⊢
  nlinarith

/-- Canonical third rectangular dimension rate: `(1-2mu) log₂ q`. -/
theorem cw112RationalTypedLeaf_dimensionRateBits_Z
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (cw112RationalTypedLeaf q L G hq hL hG).dimensionRateBits .Z =
      (1 - 2 * cw112Mu L G) * cw112LogQBits q := by
  have h := (cw112RationalTypedLeaf q L G hq hL hG).log_dimensionProduct_div_logTwo .Z
  rw [cw112RationalTypedLeaf_dimensionProduct_Z, Nat.cast_pow, Real.log_pow] at h
  change _ = ((cw112IntegralProfile L G hL hG).mass : ℝ) * _ at h
  rw [cw112IntegralProfile_mass] at h
  unfold cw112Mu cw112LogQBits
  push_cast at h ⊢
  have hsum : (0 : ℝ) < L + G := by exact_mod_cast Nat.add_pos_left hL G
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp [hsum.ne', hlogTwo] at h ⊢
  nlinarith

/-- Every proportional `(L,L,G,G)` type specializes the generic typed-leaf theorem and yields
the exact rectangular dimensions, without a fresh tensor-product proof. -/
theorem cw112_positivePower_constituent_matrixMultiplication_proportional
    {K : Type u} [CommRing K]
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    {r k : ℕ}
    (word : PositiveWord (cw112PartitionedTensor K q).support r)
    (hword : word ∈ positiveTypeClass (cw112PartitionedTensor K q).support r
      (WordType.proportionalCounts (cw112NaturalType L G) k)) :
    Restricts (((cw112PartitionedTensor K q).positivePower r).constituent
        (positiveSupportWordBlockAddress (cw112PartitionedTensor K q).support r word))
      (matrixMultiplication (K := K)
        ((q ^ (2 * G)) ^ k) ((q ^ (2 * L)) ^ k) ((q ^ (2 * G)) ^ k)) := by
  letI : Fintype (cw112PartitionedTensor K q).support :=
    inferInstanceAs (Fintype cw112BlockSupport)
  letI : Nonempty (cw112PartitionedTensor K q).support := by
    simpa using cw112BlockSupport_nonempty
  have h := RationalTypedLeaf.positivePower_constituent_matrixMultiplication_proportional.{
      0, u, 0, u}
    (cw112PartitionedTensor K q) (cw112RationalTypedLeaf q L G hq hL hG)
      (cw112SupportedConstituent_restricts K q) word hword
  have hx := cw112RationalTypedLeaf_dimensionProduct_X q L G hq hL hG
  have hy := cw112RationalTypedLeaf_dimensionProduct_Y q L G hq hL hG
  have hz := cw112RationalTypedLeaf_dimensionProduct_Z q L G hq hL hG
  exact h.trans
    (Tensor.Isomorphic.matrixMultiplication_congr (K := K)
      (congrArg (fun n : ℕ ↦ n ^ k) hx)
      (congrArg (fun n : ℕ ↦ n ^ k) hy)
      (congrArg (fun n : ℕ ↦ n ^ k) hz)).restricts

end AlgebraicComplexity.Examples
