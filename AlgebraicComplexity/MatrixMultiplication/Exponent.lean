/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ExponentDefs
import AlgebraicComplexity.Asymptotics
import AlgebraicComplexity.MatrixMultiplication.Concise
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Nat.Log

/-!
# The matrix-multiplication exponent

The exponent is defined over a coefficient semiring as the least real exponent giving a uniform
polynomial upper bound on ranks of square matrix-multiplication tensors.  Keeping the coefficient
type explicit allows later results to state their characteristic hypotheses honestly.
-/

namespace AlgebraicComplexity

open Tensor Growth

universe u

variable (K : Type u) [CommSemiring K]

/-- The exponent is nonnegative: it is an infimum of nonnegative polynomial-bound exponents. -/
theorem matrixMultiplicationExponent_nonneg : 0 ≤ matrixMultiplicationExponent K :=
  polynomialExponent_nonneg _

/-- `0 ≤ ω`, restated for the conventional name. -/
theorem omega_nonneg : 0 ≤ omega K := matrixMultiplicationExponent_nonneg K

/-- A concrete polynomial rank bound gives an upper bound on the exponent. -/
theorem matrixMultiplicationExponent_le {τ : ℝ} (h : MatrixExponentLE K τ) :
    matrixMultiplicationExponent K ≤ τ :=
  polynomialExponent_le h

/-- A concrete polynomial rank bound at `τ` gives `ω ≤ τ`, restated for the conventional name. -/
theorem omega_le {τ : ℝ} (h : MatrixExponentLE K τ) : omega K ≤ τ :=
  matrixMultiplicationExponent_le K h

/-- The defining `n³` decomposition bounds square matrix-multiplication rank. -/
theorem squareMatrixRankSequence_le_cube (n : ℕ) :
    squareMatrixRankSequence K n ≤ n ^ 3 := by
  apply rank_le_iff.mpr
  simpa [pow_succ, Nat.mul_assoc] using
    (matrixMultiplication_rankLE (K := K) n n n)

/-- The elementary algorithm gives `ω ≤ 3` over every commutative semiring. -/
theorem matrixMultiplicationExponent_le_three : matrixMultiplicationExponent K ≤ 3 := by
  apply matrixMultiplicationExponent_le
  exact PolynomialBound.of_le_pow _ 3 (squareMatrixRankSequence_le_cube K)

/-- `ω ≤ 3` over every commutative semiring, restated for the conventional name. -/
theorem omega_le_three : omega K ≤ 3 := matrixMultiplicationExponent_le_three K

section FieldLowerBound

variable (F : Type u) [Field F]

/-- Flattening on one matrix-coordinate leg gives the pointwise quadratic lower bound for square
matrix-multiplication rank. -/
theorem square_le_squareMatrixRankSequence (n : ℕ) :
    n ^ 2 ≤ squareMatrixRankSequence F n := by
  by_cases hn : n = 0
  · simp [hn]
  · change n ^ 2 ≤ rank (matrixMultiplication (K := F) n n n)
    simpa [pow_two] using
      matrixMultiplication_rank_lower_X (K := F) (Nat.pos_of_ne_zero hn)
        (rank_spec (matrixMultiplication (K := F) n n n))

/-- The standard flattening lower bound implies `2 ≤ ω`. -/
theorem two_le_matrixMultiplicationExponent :
    2 ≤ matrixMultiplicationExponent F := by
  apply natCast_le_polynomialExponent
  · exact ⟨3, PolynomialBound.of_le_pow _ 3
      (squareMatrixRankSequence_le_cube F)⟩
  · exact square_le_squareMatrixRankSequence F

/-- `2 ≤ ω` over a field, restated for the conventional name. -/
theorem two_le_omega : 2 ≤ omega F :=
  two_le_matrixMultiplicationExponent F

end FieldLowerBound

/-- Every real exponent strictly above `omega` is an admissible uniform polynomial rank bound.
This is the usable upper-closure property of the infimum defining `omega`. -/
theorem matrixExponentLE_of_omega_lt {τ : ℝ} (hτ : omega K < τ) :
    MatrixExponentLE K τ := by
  have hnonempty : Set.Nonempty
      {σ : ℝ | PolynomialBound (squareMatrixRankSequence K) σ} :=
    ⟨3, PolynomialBound.of_le_pow _ 3 (squareMatrixRankSequence_le_cube K)⟩
  obtain ⟨σ, hσ, hστ⟩ := exists_lt_of_csInf_lt hnonempty hτ
  exact hσ.mono_exponent hστ.le

/-- A real exponent strictly above `omega` supplies a concrete constant whose polynomial rank
bound can be converted into finite rank certificates under any natural slot budget. -/
theorem exists_rankLE_under_slot_budget_of_omega_lt
    {τ : ℝ} (hτ : omega K < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q L : ℕ), 1 ≤ q →
      C * (q : ℝ) ^ τ ≤ L →
        RankLE L (matrixMultiplication (K := K) q q q) := by
  rcases matrixExponentLE_of_omega_lt K hτ with ⟨_, C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro q L hq hslots
  apply (rank_spec (matrixMultiplication (K := K) q q q)).mono
  have hrankReal : (squareMatrixRankSequence K q : ℝ) ≤ L :=
    (hbound q hq).trans hslots
  exact_mod_cast hrankReal

/-- Uniform version of `exists_rankLE_with_large_side_of_omega_lt` valid for every positive
natural budget.  Enlarging the constant to at least one lets the small-budget branch use the
one-dimensional multiplication tensor, while preserving the same factor-two lower estimate.

This form is convenient in type-compression proofs because a valid multiplicity class is
nonempty but need not yet be large. -/
theorem exists_rankLE_with_large_side_all_budgets_of_omega_lt
    {γ : ℝ} (hγ : omega K < γ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℕ, 1 ≤ L →
      ∃ q : ℕ, 1 ≤ q ∧
        RankLE L (matrixMultiplication (K := K) q q q) ∧
        ((L : ℝ) / C) ^ γ⁻¹ / 2 < q := by
  obtain ⟨C₀, hC₀, hslots⟩ :=
    exists_rankLE_under_slot_budget_of_omega_lt K hγ
  let C : ℝ := max C₀ 1
  have hC : 1 ≤ C := le_max_right _ _
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hC₀C : C₀ ≤ C := le_max_left _ _
  refine ⟨C, hC, ?_⟩
  intro L hL
  by_cases hCL : C ≤ (L : ℝ)
  · let x : ℝ := ((L : ℝ) / C) ^ γ⁻¹
    let q : ℕ := ⌊x⌋₊
    have hγpos : 0 < γ := lt_of_le_of_lt (omega_nonneg K) hγ
    have hratio : 1 ≤ (L : ℝ) / C := by
      rw [le_div_iff₀ hCpos]
      simpa [one_mul] using hCL
    have hxone : 1 ≤ x := by
      dsimp [x]
      exact Real.one_le_rpow hratio (inv_nonneg.mpr hγpos.le)
    have hq : 1 ≤ q := Nat.floor_pos.mpr hxone
    refine ⟨q, hq, ?_, Nat.div_two_lt_floor hxone⟩
    apply hslots q L hq
    have hqx : (q : ℝ) ≤ x := Nat.floor_le (by positivity)
    have hqpow : (q : ℝ) ^ γ ≤ x ^ γ :=
      Real.rpow_le_rpow (by positivity) hqx hγpos.le
    have hxpow : x ^ γ = (L : ℝ) / C := by
      dsimp [x]
      exact Real.rpow_inv_rpow (by positivity) hγpos.ne'
    rw [hxpow] at hqpow
    calc
      C₀ * (q : ℝ) ^ γ ≤ C * (q : ℝ) ^ γ := by gcongr
      _ ≤ C * ((L : ℝ) / C) :=
        mul_le_mul_of_nonneg_left hqpow hCpos.le
      _ = L := by field_simp
  · refine ⟨1, by simp, ?_, ?_⟩
    · exact (matrixMultiplication_rankLE (K := K) 1 1 1).mono (by simpa using hL)
    · have hratioNonneg : 0 ≤ (L : ℝ) / C := by positivity
      have hratioLe : (L : ℝ) / C ≤ 1 := by
        rw [div_le_one hCpos]
        exact le_of_not_ge hCL
      have hpow : ((L : ℝ) / C) ^ γ⁻¹ ≤ 1 :=
        Real.rpow_le_one hratioNonneg hratioLe (inv_nonneg.mpr
          (lt_of_le_of_lt (omega_nonneg K) hγ).le)
      linarith

/-- Fill a natural rank budget of size at least the constant `C` with a square
matrix-multiplication tensor at every exponent strictly above `omega`.  Besides the rank
certificate, the conclusion retains the useful factor-two lower estimate on the chosen side
length.

The hypothesis `C ≤ L` only discards a finite initial range of budgets.  This statement is the
restricted-budget corollary of `exists_rankLE_with_large_side_all_budgets_of_omega_lt`: a
budget of size at least `C ≥ 1` is in particular positive, and the same constant works. -/
theorem exists_rankLE_with_large_side_of_omega_lt
    {γ : ℝ} (hγ : omega K < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, C ≤ L →
      ∃ q : ℕ, 1 ≤ q ∧
        RankLE L (matrixMultiplication (K := K) q q q) ∧
        ((L : ℝ) / C) ^ γ⁻¹ / 2 < q := by
  obtain ⟨C, hC, hbudgets⟩ :=
    exists_rankLE_with_large_side_all_budgets_of_omega_lt K hγ
  refine ⟨C, zero_lt_one.trans_le hC, ?_⟩
  intro L hCL
  exact hbudgets L (by exact_mod_cast hC.trans hCL)

/-- A rank algorithm for `q × q` multiplication bounds every dimension by tensoring to the
next power of `q` and restricting coordinates. -/
theorem squareMatrixRankSequence_le_pow_clog {q r : ℕ} (hq : 1 < q)
    (h : RankLE r (matrixMultiplication (K := K) q q q)) (n : ℕ) :
    squareMatrixRankSequence K n ≤ r ^ Nat.clog q n := by
  apply rank_le_iff.mpr
  exact (h.matrixMultiplication_pow (Nat.clog q n)).of_restricts
    (matrixMultiplication_restricts
      (Nat.le_pow_clog hq n) (Nat.le_pow_clog hq n) (Nat.le_pow_clog hq n))

/-- Analytic ceiling-log estimate for a real exponential base.  This is the bridge from bounds on
`q`-power dimensions to polynomial bounds on all positive dimensions. -/
theorem real_pow_clog_le_mul_rpow {q n : ℕ} {a : ℝ} (hq : 1 < q) (ha : 1 ≤ a)
    (hn : 1 ≤ n) :
    a ^ Nat.clog q n ≤ a * (n : ℝ) ^ (Real.log a / Real.log q) := by
  let τ : ℝ := Real.log a / Real.log q
  have hqReal : (1 : ℝ) < q := by exact_mod_cast hq
  have hqPos : (0 : ℝ) < q := zero_lt_one.trans hqReal
  have haPos : (0 : ℝ) < a := zero_lt_one.trans_le ha
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hqReal
  have hτ : 0 ≤ τ := by
    exact div_nonneg (Real.log_nonneg ha) hlogq.le
  have hqτ : (q : ℝ) ^ τ = a := by
    rw [Real.rpow_def_of_pos hqPos]
    convert Real.exp_log haPos using 1
    dsimp [τ]
    field_simp
  by_cases hnOne : n = 1
  · subst n
    simp [Nat.clog_one_right, ha]
  · have hn' : 1 < n := lt_of_le_of_ne hn (Ne.symm hnOne)
    have hk : 0 < Nat.clog q n := Nat.clog_pos hq hn'
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    have hbaseNat : q ^ j < n := by
      simpa [hj] using Nat.pow_pred_clog_lt_self hq hn'
    have hbase : ((q ^ j : ℕ) : ℝ) ≤ n := by
      exact_mod_cast hbaseNat.le
    have hpowers : a ^ j ≤ (n : ℝ) ^ τ := by
      rw [← hqτ, Real.rpow_pow_comm hqPos.le]
      exact Real.rpow_le_rpow (by positivity) (by simpa using hbase) hτ
    rw [hj, pow_succ]
    dsimp [τ] at hpowers ⊢
    nlinarith [mul_le_mul_of_nonneg_left hpowers haPos.le]

/-- Natural-base specialization used by exact rank algorithms. -/
private theorem pow_clog_le_mul_rpow {q r n : ℕ} (hq : 1 < q) (hr : 1 ≤ r)
    (hn : 1 ≤ n) :
    ((r ^ Nat.clog q n : ℕ) : ℝ) ≤
      r * (n : ℝ) ^ (Real.log r / Real.log q) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    real_pow_clog_le_mul_rpow (a := (r : ℝ)) hq (by exact_mod_cast hr) hn

/-- Any exact rank-`r` algorithm for `q × q` multiplication gives the standard exponent bound
`ω ≤ log(r) / log(q)`. -/
theorem matrixMultiplicationExponent_le_log_of_rankLE {q r : ℕ}
    (hq : 1 < q) (hr : 1 ≤ r)
    (h : RankLE r (matrixMultiplication (K := K) q q q)) :
    matrixMultiplicationExponent K ≤ Real.log r / Real.log q := by
  apply matrixMultiplicationExponent_le
  have hqReal : (1 : ℝ) < q := by exact_mod_cast hq
  have hrReal : (1 : ℝ) ≤ r := by exact_mod_cast hr
  refine ⟨div_nonneg (Real.log_nonneg hrReal) (Real.log_pos hqReal).le,
    r, by positivity, ?_⟩
  intro n hn
  exact (Nat.cast_le.mpr (squareMatrixRankSequence_le_pow_clog K hq h n)).trans
    (pow_clog_le_mul_rpow hq hr hn)

/-- **Strassen's bridge**, in the conventional notation: an exact rank-`r` bilinear algorithm for
`⟨q,q,q⟩` with `1 < q` and `1 ≤ r` forces `ω ≤ log r / log q`.  This is the milestone that turns a
single finite decomposition into a bound on the exponent — Strassen's `r = 7`, `q = 2` certificate
gives `ω ≤ log 7 / log 2` — and it is the form every downstream exact-algorithm client uses.

Proof sketch: a restatement of `matrixMultiplicationExponent_le_log_of_rankLE`, which recursively
applies the certificate `⌈log_q n⌉` times to bound `rank ⟨n,n,n⟩` by `r ^ ⌈log_q n⌉`, and then
compares that with `n ^ (log r / log q)`. -/
theorem omega_le_log_of_rankLE {q r : ℕ}
    (hq : 1 < q) (hr : 1 ≤ r)
    (h : RankLE r (matrixMultiplication (K := K) q q q)) :
    omega K ≤ Real.log r / Real.log q :=
  matrixMultiplicationExponent_le_log_of_rankLE K hq hr h

/-- A fixed exact rank certificate gives the lower inequality
`q ^ omega ≤ r`.  This is the fixed-size form used by Schönhage compression. -/
theorem rpow_omega_le_rank_of_rankLE {q r : ℕ}
    (hq : 1 < q) (hr : 1 ≤ r)
    (h : RankLE r (matrixMultiplication (K := K) q q q)) :
    (q : ℝ) ^ omega K ≤ r := by
  have hqReal : (1 : ℝ) < q := by exact_mod_cast hq
  have hqPos : (0 : ℝ) < q := zero_lt_one.trans hqReal
  have hrPos : (0 : ℝ) < r := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  apply (Real.rpow_le_rpow_of_exponent_le hqReal.le
    (omega_le_log_of_rankLE K hq hr h)).trans_eq
  rw [Real.rpow_def_of_pos hqPos]
  convert Real.exp_log hrPos using 1
  have hlogq : Real.log (q : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hqReal)
  field_simp

namespace Tensor.RankLE

/-- Three cyclic copies of a rectangular rank-`r` algorithm form a square algorithm of rank
`r^3` and side length equal to the rectangular volume. -/
theorem matrixMultiplication_symmetrized {m n p r : ℕ}
    (h : RankLE r (matrixMultiplication (K := K) m n p)) :
    RankLE (r ^ 3)
      (matrixMultiplication (K := K) (m * n * p) (m * n * p) (m * n * p)) := by
  have hpmn : RankLE r (matrixMultiplication (K := K) p m n) :=
    h.matrixMultiplication_cycle
  have hnpm : RankLE r (matrixMultiplication (K := K) n p m) :=
    hpmn.matrixMultiplication_cycle
  have htriple := (h.external hnpm).external hpmn
  have hmapped := htriple.map
    (mmExternal3Map (K := K) m n p n p m p m n)
  rw [map_mmExternal3Map_matrixMultiplication] at hmapped
  have hN : m * n * p = n * p * m := by ac_rfl
  have hP : m * n * p = p * m * n := by ac_rfl
  have hsquare := hmapped.of_restricts
    (matrixMultiplication_restricts (K := K) (le_refl _) hN.le hP.le)
  simpa [pow_succ, Nat.mul_assoc] using hsquare

end Tensor.RankLE

/-- A rank-`r³` certificate for square multiplication at side `q` implies
`q^(ω/3) ≤ r`.  This cube-root form is tailored to the three cyclic copies in
Schönhage's compression argument. -/
theorem matrixMultiplication_side_rpow_omega_div_three_le_of_rankLE_cube
    {q r : ℕ} (hq : 1 < q) (hr : 1 ≤ r)
    (h : RankLE (r ^ 3) (matrixMultiplication (K := K) q q q)) :
    (q : ℝ) ^ (omega K / 3) ≤ r := by
  have hpow : (q : ℝ) ^ omega K ≤ (r ^ 3 : ℕ) :=
    rpow_omega_le_rank_of_rankLE K hq
      (Nat.one_le_pow 3 r (Nat.zero_lt_of_lt hr)) h
  have hxnonneg : 0 ≤ (q : ℝ) ^ (omega K / 3) := by positivity
  have hrnonneg : (0 : ℝ) ≤ r := by positivity
  apply (pow_le_pow_iff_left₀ hxnonneg hrnonneg (by norm_num : 3 ≠ 0)).mp
  calc
    ((q : ℝ) ^ (omega K / 3)) ^ 3 = (q : ℝ) ^ omega K := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ q)]
      congr 2
      ring
    _ ≤ (r ^ 3 : ℕ) := hpow
    _ = (r : ℝ) ^ 3 := by norm_num

/-- Positive-side form of the cube-root fixed-size inequality.  The side-one case is discharged
directly, so callers need not manufacture a strict lower bound when a finite type class is a
singleton. -/
theorem matrixMultiplication_side_rpow_omega_div_three_le_of_rankLE_cube_of_pos
    {q r : ℕ} (hq : 0 < q) (hr : 1 ≤ r)
    (h : RankLE (r ^ 3) (matrixMultiplication (K := K) q q q)) :
    (q : ℝ) ^ (omega K / 3) ≤ r := by
  by_cases hqone : q = 1
  · subst q
    simpa using (show (1 : ℝ) ≤ r by exact_mod_cast hr)
  · apply matrixMultiplication_side_rpow_omega_div_three_le_of_rankLE_cube K
      (lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hq.ne') (Ne.symm hqone)) hr h

/-- Rectangular fixed-size rank inequality.  For positive dimensions, every rank-`r`
decomposition of `⟨m,n,p⟩` satisfies `(m*n*p)^(omega/3) ≤ r`. -/
theorem matrixMultiplication_volume_rpow_omega_div_three_le_of_rankLE
    {m n p r : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) (hr : 1 ≤ r)
    (h : RankLE r (matrixMultiplication (K := K) m n p)) :
    ((m * n * p : ℕ) : ℝ) ^ (omega K / 3) ≤ r := by
  let v := m * n * p
  have hvpos : 0 < v := by
    dsimp [v]
    positivity
  have hvone : 1 ≤ v := hvpos
  have hsquare := h.matrixMultiplication_symmetrized
  change (v : ℝ) ^ (omega K / 3) ≤ r
  by_cases hv : v = 1
  · rw [hv]
    simpa using (show (1 : ℝ) ≤ r by exact_mod_cast hr)
  · exact matrixMultiplication_side_rpow_omega_div_three_le_of_rankLE_cube K
      (lt_of_le_of_ne hvone (Ne.symm hv)) hr (by simpa [v] using hsquare)

/-- The cubic volume of a `q`-power side length, raised to `ω/3`, is the `n`-th power of
`q ^ ω`: `((qⁿ · qⁿ · qⁿ : ℕ) : ℝ) ^ (ω/3) = ((q : ℝ) ^ ω) ^ n`.

This purely arithmetic identity is what turns the volume factor of Schönhage's asymptotic sum
inequality, applied to the `n`-th tensor power of a fixed construction of side `q`, into a
geometric progression in `q ^ ω`.  Laser-method clients instantiate it at their own power
schedule (`n = k`, `n = 9519 · k`, …) instead of repeating the computation.

Proof sketch: the natural volume is `q ^ (3n)`, and since `q > 0`,
`(q ^ (3n)) ^ (ω/3) = exp(3n · log q · ω / 3) = exp(log q · ω) ^ n = ((q : ℝ) ^ ω) ^ n`,
where the outer powers are natural and the `ω`-powers are real. -/
theorem cubeVolume_rpow_omega_div_three (q n : ℕ) (hq : 0 < q) :
    ((((q ^ n) * (q ^ n) * (q ^ n) : ℕ) : ℝ) ^ (matrixMultiplicationExponent K / 3)) =
      (((q : ℝ) ^ matrixMultiplicationExponent K) ^ n) := by
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hvolume : (((q ^ n) * (q ^ n) * (q ^ n) : ℕ) : ℝ) = (q : ℝ) ^ (3 * n) := by
    push_cast
    calc
      (q : ℝ) ^ n * (q : ℝ) ^ n * (q : ℝ) ^ n = ((q : ℝ) ^ n) ^ 3 := by ring
      _ = (q : ℝ) ^ (n * 3) := by rw [pow_mul]
      _ = (q : ℝ) ^ (3 * n) := by rw [Nat.mul_comm]
  rw [hvolume]
  calc
    ((q : ℝ) ^ (3 * n)) ^ (matrixMultiplicationExponent K / 3) =
        Real.exp (Real.log ((q : ℝ) ^ (3 * n)) *
          (matrixMultiplicationExponent K / 3)) :=
      Real.rpow_def_of_pos (pow_pos hqReal _) _
    _ = Real.exp ((n : ℝ) * (Real.log q * matrixMultiplicationExponent K)) := by
      rw [Real.log_pow]
      push_cast
      congr 1
      ring
    _ = (Real.exp (Real.log q * matrixMultiplicationExponent K)) ^ n :=
      Real.exp_nat_mul _ _
    _ = (((q : ℝ) ^ matrixMultiplicationExponent K) ^ n) := by
      rw [Real.rpow_def_of_pos hqReal]

end AlgebraicComplexity
