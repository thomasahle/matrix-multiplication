/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.AsymptoticRank

/-!
# Coefficient extraction and Bini interpolation

A constructive border-rank certificate is a sum of polynomial pure tensors.  Extracting one
coefficient expands each summand into only polynomially many ordinary pure tensors.  Keeping the
leading degree explicit makes this overhead stable under tensor powers and supplies the algebraic
core of Bini's interpolation principle.
-/

namespace AlgebraicComplexity.Tensor

universe u v

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]

namespace PolynomialVector

/-- Supported degrees no larger than `d`. -/
def boundedSupport {M : Type*} [Zero M] (P : PolynomialVector M) (d : ℕ) : Finset ℕ :=
  P.support.filter (· ≤ d)

theorem card_boundedSupport_le {M : Type*} [Zero M]
    (P : PolynomialVector M) (d : ℕ) : (boundedSupport P d).card ≤ d + 1 := by
  calc
    (boundedSupport P d).card ≤ (Finset.range (d + 1)).card := by
      apply Finset.card_le_card
      intro e he
      simp only [boundedSupport, Finset.mem_filter] at he
      simp only [Finset.mem_range]
      omega
    _ = d + 1 := Finset.card_range _

end PolynomialVector

open PolynomialVector

/-- Coefficient `d` of a polynomial pure tensor, with irrelevant degrees filtered away. -/
theorem polynomialPure_coeff_eq_bounded_sum
    (x : ∀ c, PolynomialVector (V c)) (d : ℕ) :
    polynomialPure (K := K) x d =
      ∑ dx ∈ boundedSupport (x .X) d,
        ∑ dy ∈ boundedSupport (x .Y) d,
          ∑ dz ∈ boundedSupport (x .Z) d,
            if dx + dy + dz = d then
              pure (K := K) (ofLegs (x .X dx) (x .Y dy) (x .Z dz))
            else 0 := by
  classical
  simp only [polynomialPure, PolynomialVector.monomial, Finsupp.sum_apply,
    Finsupp.single_apply, eq_comm, boundedSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro dx hdx
  by_cases hdxle : dx ≤ d
  · simp only [if_pos hdxle]
    apply Finset.sum_congr rfl
    intro dy hdy
    by_cases hdyle : dy ≤ d
    · simp only [if_pos hdyle]
      apply Finset.sum_congr rfl
      intro dz hdz
      by_cases hdzle : dz ≤ d
      · simp only [if_pos hdzle]
      · have hne : d ≠ dx + dy + dz := by omega
        simp [hdzle, hne]
    · simp only [if_neg hdyle]
      symm
      simp only [Finsupp.sum]
      apply Finset.sum_eq_zero
      intro dz hdz
      have hne : d ≠ dx + dy + dz := by omega
      simp [hne]
  · simp only [if_neg hdxle]
    symm
    simp only [Finsupp.sum]
    apply Finset.sum_eq_zero
    intro dy hdy
    apply Finset.sum_eq_zero
    intro dz hdz
    have hne : d ≠ dx + dy + dz := by omega
    simp [hne]

/-- One coefficient of one polynomial pure tensor has rank at most `(d + 1)^3`. -/
theorem rankLE_polynomialPure_coeff
    (x : ∀ c, PolynomialVector (V c)) (d : ℕ) :
    RankLE ((d + 1) ^ 3) (polynomialPure (K := K) x d) := by
  classical
  rw [polynomialPure_coeff_eq_bounded_sum]
  let sx := boundedSupport (x .X) d
  let sy := boundedSupport (x .Y) d
  let sz := boundedSupport (x .Z) d
  have hterm (dx dy dz : ℕ) :
      RankLE 1 (if dx + dy + dz = d then
        pure (K := K) (ofLegs (x .X dx) (x .Y dy) (x .Z dz)) else 0) := by
    by_cases hsum : dx + dy + dz = d
    · simpa [hsum] using RankLE.pure_tensor (K := K)
        (ofLegs (x .X dx) (x .Y dy) (x .Z dz))
    · simpa [hsum] using
        (RankLE.zero (K := K) (V := V)).mono (Nat.zero_le 1)
  have hz (dx dy : ℕ) :
      RankLE (d + 1) (∑ dz ∈ sz,
        if dx + dy + dz = d then
          pure (K := K) (ofLegs (x .X dx) (x .Y dy) (x .Z dz)) else 0) := by
    apply (RankLE.finset_sum sz _ 1 (fun dz _ ↦ hterm dx dy dz)).mono
    simpa using card_boundedSupport_le (x .Z) d
  have hy (dx : ℕ) :
      RankLE ((d + 1) ^ 2) (∑ dy ∈ sy, ∑ dz ∈ sz,
        if dx + dy + dz = d then
          pure (K := K) (ofLegs (x .X dx) (x .Y dy) (x .Z dz)) else 0) := by
    apply (RankLE.finset_sum sy _ (d + 1) (fun dy _ ↦ hz dx dy)).mono
    simpa [sy, pow_two] using
      Nat.mul_le_mul_right (d + 1) (card_boundedSupport_le (x .Y) d)
  apply (RankLE.finset_sum sx _ ((d + 1) ^ 2) (fun dx _ ↦ hy dx)).mono
  calc
    sx.card * (d + 1) ^ 2 ≤ (d + 1) * (d + 1) ^ 2 := by
      exact Nat.mul_le_mul_right ((d + 1) ^ 2)
        (by simpa [sx] using card_boundedSupport_le (x .X) d)
    _ = (d + 1) ^ 3 := by ring

namespace RankLE

/-- An exact rank certificate is a degree-zero border certificate with the same terms. -/
theorem toBorderRankLEAt {r : ℕ} {T : Tensor3 K V} (h : RankLE r T) :
    BorderRankLEAt r 0 T := by
  rcases h with ⟨terms, hlen, hsum⟩
  let polynomialTerms : List (∀ c, PolynomialVector (V c)) :=
    terms.map fun x c ↦ PolynomialVector.constant (x c)
  refine ⟨polynomialTerms, by simpa [polynomialTerms] using hlen, ?_⟩
  have hpath :
      (polynomialTerms.map (polynomialPure (K := K))).sum =
        PolynomialVector.constant (terms.map (pure (K := K))).sum := by
    clear hlen hsum T r
    simp only [polynomialTerms, List.map_map]
    induction terms with
    | nil => simp [PolynomialVector.constant]
    | cons x terms ih =>
        dsimp at ih
        simp only [List.map_cons, List.sum_cons, Function.comp_apply]
        rw [polynomialPure_constant_family, ih]
        exact (PolynomialVector.monomial_add 0
          (pure (K := K) x) (terms.map (pure (K := K))).sum).symm
  rw [hpath, ← hsum]
  exact HasLeadingTerm.monomial 0 T

end RankLE

namespace BorderRankLEAt

/-- Extracting the certified leading coefficient costs at most `(d + 1)^3` pure tensors per
polynomial pure summand. -/
theorem toRankLE {r d : ℕ} {T : Tensor3 K V}
    (h : BorderRankLEAt r d T) : RankLE (r * (d + 1) ^ 3) T := by
  rcases h with ⟨terms, hlen, hlead⟩
  let coefficients : List (Tensor3 K V) :=
    terms.map fun x ↦ polynomialPure (K := K) x d
  have hcoefficients : RankLE (coefficients.length * (d + 1) ^ 3) coefficients.sum := by
    apply RankLE.list_sum coefficients ((d + 1) ^ 3)
    intro S hS
    rcases List.mem_map.mp hS with ⟨x, hx, rfl⟩
    exact rankLE_polynomialPure_coeff x d
  have hpath :
      coefficients.sum = (terms.map (polynomialPure (K := K))).sum d := by
    clear hlen hlead hcoefficients T r
    simp only [coefficients]
    induction terms with
    | nil => simp
    | cons x terms ih =>
        simp [ih]
  rw [hpath, hlead.coeff] at hcoefficients
  apply hcoefficients.mono
  simpa only [coefficients, List.length_map] using
    Nat.mul_le_mul_right ((d + 1) ^ 3) hlen

/-- Transport to the canonical first-power leg spaces preserves the leading degree. -/
theorem powerOne {r d : ℕ} {T : Tensor3 K V}
    (h : BorderRankLEAt r d T) : BorderRankLEAt r d (Tensor.powerOne T) := by
  simpa [Tensor.powerOne] using h.map
    (fun c ↦ (powerOneEquiv (K := K) (V := V) c).symm.toLinearMap)

/-- Multiplication of canonical tensor powers adds leading degrees. -/
theorem powerMul {n m r s d e : ℕ}
    {T : Tensor3 K (PowerSpace K V n)}
    {S : Tensor3 K (PowerSpace K V m)}
    (hT : BorderRankLEAt r d T) (hS : BorderRankLEAt s e S) :
    BorderRankLEAt (r * s) (d + e) (Tensor.powerMul n m T S) := by
  simpa [Tensor.powerMul] using (hT.external hS).map
    (fun c ↦ (powerMulEquiv (K := K) (V := V) n m c).toLinearMap)

/-- An `r`-term degree-`d` border certificate tensors to `r^n` terms in degree `n*d`. -/
theorem power {r d : ℕ} {T : Tensor3 K V}
    (h : BorderRankLEAt r d T) (n : ℕ) :
    BorderRankLEAt (r ^ n) (n * d) (Tensor.power T n) := by
  induction n with
  | zero =>
      simpa using BorderRankLEAt.pure_tensor (K := K)
        (V := PowerSpace K V 0) (powerUnit (K := K) (V := V))
  | succ n ih =>
      simpa [pow_succ, Nat.succ_mul] using ih.powerMul h.powerOne

end BorderRankLEAt

/-- Explicit ordinary-rank bound obtained by coefficient extraction from a powered border-rank
certificate.  The multiplicative overhead is cubic in the total leading degree. -/
theorem rank_power_le_of_borderRankLEAt {r d : ℕ} {T : Tensor3 K V}
    (h : BorderRankLEAt r d T) (n : ℕ) :
    rank (Tensor.power T n) ≤ r ^ n * (n * d + 1) ^ 3 := by
  exact rank_le_iff.mpr (h.power n).toRankLE

/-- Coefficient extraction after powering a degree-`d` degeneration compares optimized ranks of
the two tensor powers, with only a cubic polynomial overhead. -/
theorem rank_power_le_of_polynomialDegeneratesAt
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    {d : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (h : PolynomialDegeneratesAt d T S) (n : ℕ) :
    rank (Tensor.power S n) ≤
      rank (Tensor.power T n) * (n * d + 1) ^ 3 := by
  exact rank_le_iff.mpr
    ((rank_spec (Tensor.power T n)).borderAt_of_polynomialDegeneratesAt (h.power n)).toRankLE

/-- Bini interpolation: a fixed constructive border-rank certificate bounds ordinary asymptotic
rank by its number of summands. -/
theorem asymptoticRank_le_of_borderRankLEAt {r d : ℕ} {T : Tensor3 K V}
    (h : BorderRankLEAt r d T) : asymptoticRank T ≤ r := by
  unfold asymptoticRank
  apply Growth.exponentialRate_le_of_le_pow_mul_affine _ r d 3
  exact rank_power_le_of_borderRankLEAt h

theorem asymptoticRank_le_of_borderRankLE {r : ℕ} {T : Tensor3 K V}
    (h : BorderRankLE r T) : asymptoticRank T ≤ r := by
  rcases h.exists_at with ⟨d, hd⟩
  exact asymptoticRank_le_of_borderRankLEAt hd

/-- Ordinary asymptotic rank is monotone under a degree-aware polynomial degeneration.  The
proof retains optimized rank certificates for every source power and absorbs the interpolation
cost into the exponential rate. -/
theorem asymptoticRank_polynomialDegeneratesAt_le
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    {d : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (h : PolynomialDegeneratesAt d T S) :
    asymptoticRank S ≤ asymptoticRank T := by
  unfold asymptoticRank
  apply Growth.exponentialRate_le_of_le_mul_affine d 3
  · intro n
    simpa [rankPowerSequence] using rank_power_le_of_polynomialDegeneratesAt h n
  · exact ⟨rank T, rank_exponentialBound T⟩

/-- Ordinary asymptotic rank is monotone under constructive polynomial degeneration. -/
theorem asymptoticRank_polynomialDegenerates_le
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    {T : Tensor3 K V} {S : Tensor3 K W}
    (h : PolynomialDegenerates T S) : asymptoticRank S ≤ asymptoticRank T := by
  rcases h.exists_at with ⟨d, hd⟩
  exact asymptoticRank_polynomialDegeneratesAt_le hd

/-- Ordinary asymptotic rank is bounded by constructive border rank. -/
theorem asymptoticRank_le_borderRank (T : Tensor3 K V) :
    asymptoticRank T ≤ borderRank T :=
  asymptoticRank_le_of_borderRankLE (borderRank_spec T)

end AlgebraicComplexity.Tensor
