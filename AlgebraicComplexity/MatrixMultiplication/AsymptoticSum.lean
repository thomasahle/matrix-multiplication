/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymptoticSumDefs
import AlgebraicComplexity.MatrixMultiplication.Compression
import AlgebraicComplexity.MatrixMultiplication.DirectSum
import AlgebraicComplexity.MatrixMultiplication.Exponent
import AlgebraicComplexity.Tensor.PolynomialInterpolation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Direct sums of matrix-multiplication tensors and the asymptotic-sum interface

This module proves Schönhage's asymptotic sum inequality from finite multinomial type selection,
cyclic multiple compression, and the definition of the matrix-multiplication exponent.  The
named proposition remains as the stable interface consumed by laser-method clients.
-/

namespace AlgebraicComplexity

open Tensor Growth
open scoped DirectSum

universe u v w

variable (K : Type u) [CommSemiring K]
variable {ι : Type w} [Fintype ι]

private theorem prod_rpow_pow_eq
    (v : ι → ℕ) (τ : ℝ) (a : ι → ℕ) :
    (∏ i, ((v i : ℝ) ^ τ) ^ a i) =
      (((∏ i, v i ^ a i : ℕ) : ℝ) ^ τ) := by
  calc
    (∏ i, ((v i : ℝ) ^ τ) ^ a i) =
        ∏ i, ((v i : ℝ) ^ a i) ^ τ := by
      apply Finset.prod_congr rfl
      intro i _
      exact Real.rpow_pow_comm (by positivity) τ (a i)
    _ = (∏ i, ((v i : ℝ) ^ a i)) ^ τ :=
      Real.finsetProd_rpow Finset.univ (fun i ↦ (v i : ℝ) ^ a i)
        (fun i _ ↦ by positivity) τ
    _ = (((∏ i, v i ^ a i : ℕ) : ℝ) ^ τ) := by
      congr 1
      push_cast
      rfl

/-- Convert the factor-two lower estimate for a square algorithm's side length into the
weighted type-class estimate used by multiple compression. -/
private theorem typeClassCard_le_slotWeight
    {E q : ℕ} {C γ : ℝ}
    (hE : 1 ≤ E) (hC : 0 < C) (hγ : 0 < γ)
    (hq : (((E ^ 3 : ℕ) : ℝ) / C) ^ γ⁻¹ / 2 < q) :
    (E : ℝ) ≤
      ((2 : ℝ) ^ (γ / 3) * C ^ ((3 : ℝ)⁻¹) *
        (q : ℝ) ^ (γ / 3)) := by
  have hEpos : (0 : ℝ) < E := by exact_mod_cast (Nat.zero_lt_of_lt hE)
  have hqpos : (0 : ℝ) < q := lt_of_le_of_lt (by positivity) hq
  let z : ℝ := (((E ^ 3 : ℕ) : ℝ) / C)
  have hzpos : 0 < z := by dsimp [z]; positivity
  have hzroot : z ^ γ⁻¹ ≤ 2 * q := by
    dsimp [z] at hq ⊢
    linarith
  have hrootpow : (z ^ γ⁻¹) ^ (γ / 3) ≤
      ((2 : ℝ) * q) ^ (γ / 3) :=
    Real.rpow_le_rpow (by positivity) hzroot (by positivity)
  have hleft : (z ^ γ⁻¹) ^ (γ / 3) = z ^ ((3 : ℝ)⁻¹) := by
    rw [← Real.rpow_mul hzpos.le]
    congr 2
    field_simp
  have hright : ((2 : ℝ) * q) ^ (γ / 3) =
      (2 : ℝ) ^ (γ / 3) * (q : ℝ) ^ (γ / 3) := by
    exact Real.mul_rpow (by positivity) (by positivity)
  rw [hleft, hright] at hrootpow
  have hrecover : C ^ ((3 : ℝ)⁻¹) * z ^ ((3 : ℝ)⁻¹) = E := by
    rw [← Real.mul_rpow hC.le hzpos.le]
    have hmul : C * z = (E : ℝ) ^ 3 := by
      dsimp [z]
      push_cast
      field_simp
    rw [hmul]
    exact Real.pow_rpow_inv_natCast hEpos.le (by norm_num : (3 : ℕ) ≠ 0)
  rw [← hrecover]
  calc
    C ^ ((3 : ℝ)⁻¹) * z ^ ((3 : ℝ)⁻¹) ≤
        C ^ ((3 : ℝ)⁻¹) *
          ((2 : ℝ) ^ (γ / 3) * (q : ℝ) ^ (γ / 3)) :=
      mul_le_mul_of_nonneg_left hrootpow (Real.rpow_nonneg hC.le _)
    _ = (2 : ℝ) ^ (γ / 3) * C ^ ((3 : ℝ)⁻¹) *
        (q : ℝ) ^ (γ / 3) := by ring

/-- A multiplicity type captures the full powered volume sum up to the polynomial number of
types.  The selected coefficient is expressed using the actual index type consumed by the
finite compression theorem. -/
theorem exists_positiveType_large_volume_term [Nonempty ι]
    (m n p : ι → ℕ) (τ : ℝ) (s : ℕ) :
    ∃ a ∈ WordType.types ι (s + 1),
      (matrixMultiplicationVolumePowerSum m n p τ) ^ (s + 1) ≤
        (((s + 2) ^ Fintype.card ι : ℕ) : ℝ) *
          (Fintype.card (Tensor.positiveTypeClass ι s a) : ℝ) *
          ((
            (∏ i, m i ^ a i) * (∏ i, n i ^ a i) *
              (∏ i, p i ^ a i) : ℕ) : ℝ) ^ τ := by
  let v : ι → ℕ := fun i ↦ matrixMultiplicationVolume m n p i
  obtain ⟨a, ha, hlarge⟩ := WordType.exists_type_large_weighted_term
    (x := fun i ↦ (v i : ℝ) ^ τ) (fun i ↦ by positivity) (s + 1)
  refine ⟨a, ha, ?_⟩
  rw [show matrixMultiplicationVolumePowerSum m n p τ =
      ∑ i, (v i : ℝ) ^ τ by rfl]
  apply hlarge.trans_eq
  unfold WordType.weightedClassTerm
  rw [← Tensor.card_positiveTypeClass (I := ι) s a]
  rw [prod_rpow_pow_eq v τ a]
  have hv : (∏ i, v i ^ a i) =
      (∏ i, m i ^ a i) * (∏ i, n i ^ a i) * (∏ i, p i ^ a i) := by
    simpa [v, matrixMultiplicationVolume] using
      (productDimensions_eq_product_volume m n p a).symm
  rw [hv]
  simp only [Fintype.card_coe, Nat.cast_mul]
  ring

/-- Global interface for the asymptotic sum inequality using this library's constructive
degeneration and asymptotic-rank notions.  The proposition is proved below and retained as a
convenient argument type for downstream APIs.

Schönhage's Theorem 7.1 proves the total-matrix-multiplication case over an arbitrary field.  We
also state positivity of all three dimensions explicitly: it is part of the classical meaning of
`⟨m,n,p⟩` in this theorem and avoids the special value `0 ^ 0` before a separate lower bound on
`omega` has been developed. -/
def AsymptoticSumInequality (F : Type u) [Field F] : Prop :=
  ∀ (ι : Type w) [Fintype ι]
      (V : Leg → Type v) [∀ c, AddCommMonoid (V c)] [∀ c, Module F (V c)]
      (T : Tensor3 F V) (m n p : ι → ℕ),
    (∀ i, 0 < m i) → (∀ i, 0 < n i) → (∀ i, 0 < p i) →
      PolynomialDegenerates T (matrixMultiplicationDirectSum F m n p) →
        asymptoticSum F m n p ≤ asymptoticRank T

section Field

variable (F : Type u) [Field F]

/-- Quantitative output of one finite Schönhage type-compression step.  If a power of a direct
sum has rank at most `r`, and the selected type supplies enough independent slots for a
rank-`E³` algorithm at side `q`, then the compressed side `qP` satisfies
`(qP)^(ω/3) ≤ r`.

This theorem contains no limiting argument; all quantities are finite and certificate-facing. -/
theorem selectedType_compression_rpow_le
    {I : Type*} [Fintype I] {r q : ℕ}
    (m n p : I → ℕ) (s : ℕ) (a : I → ℕ)
    (hpower : RankLE r
      (Tensor.power
        (Tensor.indexedDirectSum
          (matrixMultiplicationTensorFamily (K := F) m n p)) (s + 1)))
    (hslots : RankLE
      ((Fintype.card (Tensor.positiveTypeClass I s a)) ^ 3)
      (matrixMultiplication (K := F) q q q))
    (hside : 0 < q *
      ((∏ i, m i ^ a i) * (∏ i, n i ^ a i) * (∏ i, p i ^ a i))) :
    ((q * ((∏ i, m i ^ a i) * (∏ i, n i ^ a i) *
      (∏ i, p i ^ a i)) : ℕ) : ℝ) ^ (omega F / 3) ≤ r := by
  let side := q *
    ((∏ i, m i ^ a i) * (∏ i, n i ^ a i) * (∏ i, p i ^ a i))
  have hcompressed : RankLE (r ^ 3)
      (matrixMultiplication (K := F) side side side) := by
    simpa [side] using
      (Tensor.RankLE.matrixMultiplicationDirectSum_type_compression
        m n p s a hpower hslots)
  have hrCube : 1 ≤ r ^ 3 := by
    have hlower : side * side ≤ r ^ 3 :=
      matrixMultiplication_rank_lower_X (K := F) hside hcompressed
    exact (Nat.one_le_iff_ne_zero.mpr (by positivity : side * side ≠ 0)).trans hlower
  have hr : 1 ≤ r := by
    by_contra hrnot
    have hrzero : r = 0 := Nat.eq_zero_of_not_pos hrnot
    simp [hrzero] at hrCube
  simpa [side] using
    matrixMultiplication_side_rpow_omega_div_three_le_of_rankLE_cube_of_pos
      F hside hr hcompressed

/-- Raise the square-side inequality furnished by compression from exponent `omega / 3` to any
nearby exponent `γ / 3`, paying the corresponding power `γ / omega` on rank. -/
private theorem higher_side_power_le_rank_power
    {γ : ℝ} (hγ : omega F < γ) {side r : ℕ}
    (_hside : 0 < side)
    (h : (side : ℝ) ^ (omega F / 3) ≤ r) :
    (side : ℝ) ^ (γ / 3) ≤ (r : ℝ) ^ (γ / omega F) := by
  have hwpos : 0 < omega F := lt_of_lt_of_le (by norm_num) (two_le_omega F)
  have hγpos : 0 < γ := hwpos.trans hγ
  have hepos : 0 ≤ γ / omega F := by positivity
  calc
    (side : ℝ) ^ (γ / 3) =
        ((side : ℝ) ^ (omega F / 3)) ^ (γ / omega F) := by
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ side)]
      congr 2
      field_simp
    _ ≤ (r : ℝ) ^ (γ / omega F) :=
      Real.rpow_le_rpow (by positivity) h hepos

/-- Quantitative finite form of Schönhage's argument.  For every `γ > omega`, the corrected
`γ / 3` volume sum has a geometric lower bound on ranks of all positive powers of the direct
sum, up to the polynomial number of multiplicity types.

This theorem exposes the exact finite estimate beneath the limiting asymptotic-sum inequality
and is useful for auditing alternative type-selection or compression implementations. -/
theorem matrixMultiplicationDirectSum_power_growth_bound
    {I : Type*} [Fintype I] [Nonempty I]
    (m n p : I → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (hp : ∀ i, 0 < p i)
    {γ : ℝ} (hγ : omega F < γ) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℕ,
      ((matrixMultiplicationVolumePowerSum m n p (γ / 3)) ^
          (omega F / γ)) ^ (s + 1) ≤
        A * ((s + 2 : ℕ) : ℝ) ^ Fintype.card I *
          Tensor.rankPowerSequence
            (matrixMultiplicationDirectSum F m n p) (s + 1) := by
  have hwpos : 0 < omega F := lt_of_lt_of_le (by norm_num) (two_le_omega F)
  have hγpos : 0 < γ := hwpos.trans hγ
  have htpos : 0 < omega F / γ := div_pos hwpos hγpos
  have htle : omega F / γ ≤ 1 := (div_le_one hγpos).mpr hγ.le
  obtain ⟨C, hC, hslot⟩ :=
    exists_rankLE_with_large_side_all_budgets_of_omega_lt F hγ
  let A : ℝ :=
    ((2 : ℝ) ^ (γ / 3) * C ^ ((3 : ℝ)⁻¹)) ^ (omega F / γ)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro s
  obtain ⟨a, ha, hweighted⟩ :=
    exists_positiveType_large_volume_term m n p (γ / 3) s
  let E : ℕ := Fintype.card (Tensor.positiveTypeClass I s a)
  let P : ℕ :=
    (∏ i, m i ^ a i) * (∏ i, n i ^ a i) * (∏ i, p i ^ a i)
  let r : ℕ := Tensor.rankPowerSequence
    (matrixMultiplicationDirectSum F m n p) (s + 1)
  have hE : 1 ≤ E := by
    dsimp [E]
    rw [Fintype.card_coe, Tensor.card_positiveTypeClass]
    exact Finset.card_pos.mpr (WordType.typeClass_nonempty a ha)
  obtain ⟨q, hqone, hqrank, hqlower⟩ :=
    hslot (E ^ 3) (Nat.one_le_pow 3 E hE)
  have hP : 0 < P := by
    dsimp [P]
    have hmprod : 0 < ∏ i, m i ^ a i :=
      Finset.prod_pos fun i _ ↦ pow_pos (hm i) _
    have hnprod : 0 < ∏ i, n i ^ a i :=
      Finset.prod_pos fun i _ ↦ pow_pos (hn i) _
    have hpprod : 0 < ∏ i, p i ^ a i :=
      Finset.prod_pos fun i _ ↦ pow_pos (hp i) _
    positivity
  have hside : 0 < q * P := Nat.mul_pos (Nat.zero_lt_of_lt hqone) hP
  have hpower : RankLE r
      (Tensor.power
        (Tensor.indexedDirectSum
          (matrixMultiplicationTensorFamily (K := F) m n p)) (s + 1)) := by
    exact Tensor.rank_spec _
  have hcompressed : ((q * P : ℕ) : ℝ) ^ (omega F / 3) ≤ r := by
    simpa [P, r, matrixMultiplicationDirectSum] using
      selectedType_compression_rpow_le F m n p s a hpower hqrank hside
  have hhigher : ((q * P : ℕ) : ℝ) ^ (γ / 3) ≤
      (r : ℝ) ^ (γ / omega F) :=
    higher_side_power_le_rank_power F hγ hside hcompressed
  have hEweight : (E : ℝ) ≤
      ((2 : ℝ) ^ (γ / 3) * C ^ ((3 : ℝ)⁻¹) *
        (q : ℝ) ^ (γ / 3)) :=
    typeClassCard_le_slotWeight hE (zero_lt_one.trans_le hC) hγpos hqlower
  have hselected :
      (matrixMultiplicationVolumePowerSum m n p (γ / 3)) ^ (s + 1) ≤
        ((s + 2 : ℕ) : ℝ) ^ Fintype.card I *
          ((2 : ℝ) ^ (γ / 3) * C ^ ((3 : ℝ)⁻¹)) *
          (r : ℝ) ^ (γ / omega F) := by
    calc
      (matrixMultiplicationVolumePowerSum m n p (γ / 3)) ^ (s + 1) ≤
          (((s + 2) ^ Fintype.card I : ℕ) : ℝ) * (E : ℝ) *
            (P : ℝ) ^ (γ / 3) := by
        change _ ≤ (((s + 2) ^ Fintype.card I : ℕ) : ℝ) * (E : ℝ) *
          (P : ℝ) ^ (γ / 3) at hweighted
        exact hweighted
      _ ≤ (((s + 2) ^ Fintype.card I : ℕ) : ℝ) *
          (((2 : ℝ) ^ (γ / 3) * C ^ ((3 : ℝ)⁻¹) *
            (q : ℝ) ^ (γ / 3))) * (P : ℝ) ^ (γ / 3) := by
        gcongr
      _ = ((s + 2 : ℕ) : ℝ) ^ Fintype.card I *
          ((2 : ℝ) ^ (γ / 3) * C ^ ((3 : ℝ)⁻¹)) *
          ((q * P : ℕ) : ℝ) ^ (γ / 3) := by
        push_cast
        rw [Real.mul_rpow (by positivity) (by positivity)]
        ring
      _ ≤ ((s + 2 : ℕ) : ℝ) ^ Fintype.card I *
          ((2 : ℝ) ^ (γ / 3) * C ^ ((3 : ℝ)⁻¹)) *
          (r : ℝ) ^ (γ / omega F) := by gcongr
  have hBnonneg : 0 ≤ matrixMultiplicationVolumePowerSum m n p (γ / 3) := by
    unfold matrixMultiplicationVolumePowerSum
    apply Finset.sum_nonneg
    intro i _
    exact Real.rpow_nonneg (by positivity) _
  have hQone : 1 ≤ ((s + 2 : ℕ) : ℝ) ^ Fintype.card I := by
    apply one_le_pow₀
    exact_mod_cast (by omega : 1 ≤ s + 2)
  have hraux :
      (((r : ℝ) ^ (γ / omega F)) ^ (omega F / γ)) = r := by
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ r)]
    convert Real.rpow_one (r : ℝ) using 2
    field_simp
  calc
    ((matrixMultiplicationVolumePowerSum m n p (γ / 3)) ^
        (omega F / γ)) ^ (s + 1) =
        ((matrixMultiplicationVolumePowerSum m n p (γ / 3)) ^ (s + 1)) ^
          (omega F / γ) := by
      exact Real.rpow_pow_comm hBnonneg (omega F / γ) (s + 1)
    _ ≤ ((((s + 2 : ℕ) : ℝ) ^ Fintype.card I *
          ((2 : ℝ) ^ (γ / 3) * C ^ ((3 : ℝ)⁻¹)) *
          (r : ℝ) ^ (γ / omega F))) ^ (omega F / γ) :=
      Real.rpow_le_rpow (by positivity) hselected htpos.le
    _ = ((((s + 2 : ℕ) : ℝ) ^ Fintype.card I) ^ (omega F / γ)) *
        A * r := by
      dsimp [A]
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity), hraux]
    _ ≤ ((s + 2 : ℕ) : ℝ) ^ Fintype.card I * A * r := by
      gcongr
      exact Real.rpow_le_self_of_one_le hQone htle
    _ = A * ((s + 2 : ℕ) : ℝ) ^ Fintype.card I *
        Tensor.rankPowerSequence
          (matrixMultiplicationDirectSum F m n p) (s + 1) := by
      dsimp [r]
      ring

/-- For every `γ > omega`, finite multiple compression bounds the corrected `γ / 3` volume
sum by the asymptotic rank of the rectangular direct sum. -/
theorem matrixMultiplicationVolumePowerSum_rpow_le_asymptoticRank
    {I : Type*} [Fintype I] [Nonempty I]
    (m n p : I → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (hp : ∀ i, 0 < p i)
    {γ : ℝ} (hγ : omega F < γ) :
    (matrixMultiplicationVolumePowerSum m n p (γ / 3)) ^ (omega F / γ) ≤
      Tensor.asymptoticRank (matrixMultiplicationDirectSum F m n p) := by
  obtain ⟨A, hA, hbound⟩ :=
    matrixMultiplicationDirectSum_power_growth_bound F m n p hm hn hp hγ
  unfold Tensor.asymptoticRank
  apply Growth.le_exponentialRate_of_pow_succ_le_mul_polynomial
    ⟨Tensor.rank (matrixMultiplicationDirectSum F m n p),
      Tensor.rank_exponentialBound (matrixMultiplicationDirectSum F m n p)⟩ hA
  exact hbound

/-- Schönhage's asymptotic sum inequality for a direct sum of positive rectangular
matrix-multiplication tensors.  The one-sided limit `γ ↓ omega` removes the temporary exponent
slack required to fill each finite type-class slot budget. -/
theorem asymptoticSum_le_asymptoticRank_directSum
    {I : Type*} [Fintype I] [Nonempty I]
    (m n p : I → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (hp : ∀ i, 0 < p i) :
    asymptoticSum F m n p ≤
      Tensor.asymptoticRank (matrixMultiplicationDirectSum F m n p) := by
  let w : ℝ := omega F
  let g : ℝ → ℝ := fun γ ↦
    (matrixMultiplicationVolumePowerSum m n p (γ / 3)) ^ (w / γ)
  have hwpos : 0 < w := by
    dsimp [w]
    exact lt_of_lt_of_le (by norm_num) (two_le_omega F)
  have hvolumePos (i : I) : 0 < matrixMultiplicationVolume m n p i := by
    simp only [matrixMultiplicationVolume]
    exact Nat.mul_pos (Nat.mul_pos (hm i) (hn i)) (hp i)
  have hsumContinuous : Continuous fun γ : ℝ ↦
      matrixMultiplicationVolumePowerSum m n p (γ / 3) := by
    unfold matrixMultiplicationVolumePowerSum
    simpa only [id_eq] using
      (continuous_finsetSum (Finset.univ : Finset I) fun i _ ↦
        continuous_const.rpow (continuous_id.div_const 3)
          (fun _ ↦ Or.inl (by
            exact_mod_cast (Nat.ne_of_gt (hvolumePos i)))))
  have hsumPos : 0 < matrixMultiplicationVolumePowerSum m n p (w / 3) := by
    unfold matrixMultiplicationVolumePowerSum
    apply Finset.sum_pos
    · intro i _
      exact Real.rpow_pos_of_pos (by exact_mod_cast hvolumePos i) _
    · exact Finset.univ_nonempty
  have hexponentContinuous : ContinuousAt (fun γ : ℝ ↦ w / γ) w :=
    continuousAt_const.div continuousAt_id hwpos.ne'
  have hgContinuous : ContinuousAt g w := by
    exact hsumContinuous.continuousAt.rpow hexponentContinuous
      (Or.inl hsumPos.ne')
  have hseq : Filter.Tendsto (fun s : ℕ ↦ w + (1 : ℝ) / (s + 1))
      Filter.atTop (nhds w) := by
    simpa using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlimit : g w ≤
      Tensor.asymptoticRank (matrixMultiplicationDirectSum F m n p) := by
    apply le_of_tendsto' (hgContinuous.tendsto.comp hseq)
    intro s
    apply matrixMultiplicationVolumePowerSum_rpow_le_asymptoticRank
      F m n p hm hn hp
    dsimp [w]
    have hpos : 0 < (1 : ℝ) / (s + 1) := by positivity
    linarith
  simpa [g, w, asymptoticSum, div_self (ne_of_gt hwpos)] using hlimit

/-- **Schönhage's asymptotic sum inequality.**  Over a field, a constructive polynomial
degeneration from `T` to a finite direct sum of positive rectangular matrix-multiplication
tensors implies

`∑ i, (m i * n i * p i) ^ (omega / 3) ≤ asymptoticRank T`.

No additivity conjecture for ordinary tensor rank is assumed: the proof uses independent blocks
from a multinomial type, three cyclic copies, and finite multiple compression. -/
theorem asymptoticSumInequality : AsymptoticSumInequality F := by
  intro I _ V _ _ T m n p hm hn hp hdeg
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
      letI := hI
      simpa [asymptoticSum, matrixMultiplicationVolumePowerSum] using
        Tensor.asymptoticRank_nonneg T
  | inr hI =>
      letI := hI
      exact (asymptoticSum_le_asymptoticRank_directSum F m n p hm hn hp).trans
        (Tensor.asymptoticRank_polynomialDegenerates_le hdeg)

/-- The asymptotic-sum conclusion with ordinary constructive border rank on the right. -/
theorem asymptoticSum_le_borderRank
    {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module F (V c)]
    (T : Tensor3 F V) (m n p : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (hp : ∀ i, 0 < p i)
    (hdeg : PolynomialDegenerates T (matrixMultiplicationDirectSum F m n p)) :
    asymptoticSum F m n p ≤ borderRank T := by
  exact (asymptoticSumInequality F ι V T m n p hm hn hp hdeg).trans
    (asymptoticRank_le_borderRank T)

/-- A constructive border-rank certificate turns the asymptotic-sum conclusion into a numerical
upper bound. -/
theorem asymptoticSum_le_of_borderRankLE
    {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module F (V c)]
    {T : Tensor3 F V} {r : ℕ} (m n p : ι → ℕ)
    (hr : BorderRankLE r T)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (hp : ∀ i, 0 < p i)
    (hdeg : PolynomialDegenerates T (matrixMultiplicationDirectSum F m n p)) :
    asymptoticSum F m n p ≤ r := by
  apply (asymptoticSum_le_borderRank F T m n p hm hn hp hdeg).trans
  exact_mod_cast (borderRank_le_iff.mpr hr)

end Field

end AlgebraicComplexity
