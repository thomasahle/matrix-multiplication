/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RectangularBini
import AlgebraicComplexity.MatrixMultiplication.Compression
import AlgebraicComplexity.MatrixMultiplication.RectangularInterpolation

/-!
# The rectangular asymptotic sum step for identical constituents

A laser-method extraction hands its client `t` *independent* copies of one rectangular product
`⟨A, A, C⟩` together with a border-rank bound `R` for the whole direct sum.  The naive way to
consume them — compress at the rank-`t` tensor `⟨1,t,1⟩`, i.e. `⊕_t ⟨A,A,C⟩ ⤳ ⟨A, A, t·C⟩` —
loses everything: it is exactly blocking, and returns no information that
`rectangularOmega_le_omega_add_sub_one` does not already give.

Schönhage's device is to compress at a *near-optimal* algorithm instead.  If `τ` is any
admissible exponent for `ω(1,1,κ)` — witnessed by `rank ⟨n, ⌈n^κ⌉, n⟩ ≤ D·n^τ` — then the largest
scale `Q` with `D·Q^τ ≤ t` gives a rank-`t` certificate for `⟨Q, Q, ⌈Q^κ⌉⟩`, and
`Tensor.RankLE.matrixMultiplication_compression_general` substitutes the `t` extracted copies into
its `t` multiplication slots:

`⊕_t ⟨A, A, C⟩ ⤳ ⟨Q·A, Q·A, ⌈Q^κ⌉·C⟩`.

The result is again a `κ`-rectangular product, of outer dimension `Q·A ≈ (t/D)^{1/τ}·A`, so
`rectangularOmega_le_log_of_borderRankLE` returns `(Q·A)^{ω(1,1,κ)} ≤ R`.  Letting `τ ↓ ω(1,1,κ)`
in the client turns this into the asymptotic sum inequality `t · A^{ω(1,1,κ)} ≤ R`.

## Principal results

* `exists_compressionScale`: from an admissible exponent `τ` with constant `D`, and any rank
  budget `t ≥ 1`, a scale `Q ≥ 1` with `RankLE t ⟨Q, Q, ⌈Q^κ⌉⟩` and `(t/D)^{1/τ} ≤ 2·Q`.  The
  factor two is the cost of rounding `(t/D)^{1/τ}` down to an integer, and the degenerate branch
  `(t/D)^{1/τ} < 1` is covered by `Q = 1`, where the certificate is the trivial `⟨1,1,1⟩` one;
* `rpow_rectangularOmega_le_of_indexedDirectSum`: the compression step itself, in the
  multiplicative form the rate arguments consume.

## Design notes

The statement is deliberately *not* self-referential: `τ` and `D` are inputs.  A client that
wants the sharp inequality instantiates `τ` at an arbitrary real above `ω(1,1,κ)` — available
from `rectangularMatrixExponentLE_of_rectangularOmega_lt` — runs the schedule, and only then
lets `τ` decrease to `ω(1,1,κ)`.  Keeping the bootstrap outside this module means nothing here
needs a field, a limit, or a nonvacuity hypothesis.

## References

* A. Schönhage, *Partial and total matrix multiplication*, SIAM J. Comput. 10 (1981) — the
  square asymptotic sum inequality whose proof this mirrors;
* X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity 14 (1998), Section 6.
-/

namespace AlgebraicComplexity

open Tensor Growth

universe u

variable {K : Type u} [CommSemiring K]

/-! ## Choosing the compression scale -/

/-- **The compression scale.**  Given an admissible `κ`-rectangular exponent `τ` with constant
`D` and a rank budget `t ≥ 1`, there is a scale `Q ≥ 1` whose `κ`-rectangular product
`⟨Q, Q, ⌈Q^κ⌉⟩` has rank at most `t`, and which is at least half of the ideal real scale
`(t/D)^{1/τ}`.

Both roundings are explicit: `Q = ⌊(t/D)^{1/τ}⌋₊` when that is at least one — losing at most a
factor two, since `x < ⌊x⌋₊ + 1 ≤ 2⌊x⌋₊` for `x ≥ 1` — and `Q = 1` otherwise, where the trivial
one-term algorithm for `⟨1,1,1⟩` already fits inside the budget. -/
theorem exists_compressionScale {κ τ : ℝ} (hτ : 0 < τ) {D : ℝ} (hD : 0 < D)
    (hbound : ∀ n : ℕ, 1 ≤ n → (rectangularMatrixRankSequence K κ n : ℝ) ≤ D * (n : ℝ) ^ τ)
    {t : ℕ} (ht : 1 ≤ t) :
    ∃ Q : ℕ, 1 ≤ Q ∧ (((t : ℝ) / D) ^ (1 / τ)) ≤ 2 * (Q : ℝ) ∧
      RankLE t (matrixMultiplication (K := K) Q Q (rectangularMiddleDimension κ Q)) := by
  set x : ℝ := ((t : ℝ) / D) ^ (1 / τ) with hxdef
  have hxnonneg : 0 ≤ x := Real.rpow_nonneg (by positivity) _
  by_cases hx1 : 1 ≤ x
  · refine ⟨⌊x⌋₊, Nat.le_floor (by exact_mod_cast hx1), ?_, ?_⟩
    · have hfloor : (1 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
      have hfloorReal : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hfloor
      have hlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      linarith
    · have hfloorle : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hxnonneg
      have hxτ : x ^ τ = (t : ℝ) / D := by
        rw [hxdef, ← Real.rpow_mul (by positivity), one_div,
          inv_mul_cancel₀ hτ.ne', Real.rpow_one]
      have hpow : ((⌊x⌋₊ : ℕ) : ℝ) ^ τ ≤ (t : ℝ) / D := by
        rw [← hxτ]
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) hfloorle hτ.le
      have hDpow : D * ((⌊x⌋₊ : ℕ) : ℝ) ^ τ ≤ (t : ℝ) := by
        have := mul_le_mul_of_nonneg_left hpow hD.le
        rwa [mul_div_cancel₀ _ hD.ne'] at this
      have hrank : (rectangularMatrixRankSequence K κ ⌊x⌋₊ : ℝ) ≤ (t : ℝ) :=
        (hbound ⌊x⌋₊ (Nat.le_floor (by exact_mod_cast hx1))).trans hDpow
      have hrankNat : rectangularMatrixRankSequence K κ ⌊x⌋₊ ≤ t := by exact_mod_cast hrank
      rw [rectangularMatrixRankSequence_eq_rank_outer] at hrankNat
      exact rank_le_iff.mp hrankNat
  · refine ⟨1, le_rfl, ?_, ?_⟩
    · rw [not_le] at hx1
      norm_num
      linarith
    · have hone : rectangularMiddleDimension κ 1 = 1 := by
        unfold rectangularMiddleDimension
        norm_num
      rw [hone]
      exact (matrixMultiplication_rankLE (K := K) 1 1 1).mono (by simpa using ht)

/-! ## The compression step -/

/-- **One step of the rectangular asymptotic sum inequality.**

`Fintype.card ι` independent copies of the `κ`-rectangular product `⟨A, A, C⟩`, carried by a
tensor of border rank at most `R`, are compressed into a single `κ`-rectangular product of outer
dimension `Q·A`, where `Q` is the compression scale of `exists_compressionScale`.  Reading the
resulting certificate through `rectangularOmega_le_log_of_borderRankLE` gives the displayed
bound: the ideal scale `(t/D)^{1/τ}` enters raised to `ω(1, 1, κ)`, at the cost of the rounding
factor `2^{ω(1,1,κ)}`. -/
theorem rpow_rectangularOmega_le_of_indexedDirectSum
    {ι : Type*} [Fintype ι] {κ τ : ℝ} (hκ : 0 ≤ κ) (hτ : 0 < τ) {D : ℝ} (hD : 0 < D)
    (hbound : ∀ n : ℕ, 1 ≤ n → (rectangularMatrixRankSequence K κ n : ℝ) ≤ D * (n : ℝ) ^ τ)
    {A C R : ℕ} (hA : 1 < A) (hR : 1 ≤ R) (hmid : ((A : ℝ)) ^ κ ≤ (C : ℝ))
    (ht : 1 ≤ Fintype.card ι)
    (h : BorderRankLE R
      (Tensor.indexedDirectSum (fun _ : ι ↦ matrixMultiplication (K := K) A A C))) :
    ((((Fintype.card ι : ℝ)) / D) ^ (1 / τ)) ^ (rectangularOmega K κ) *
        ((A : ℝ)) ^ (rectangularOmega K κ) ≤
      (2 : ℝ) ^ (rectangularOmega K κ) * (R : ℝ) := by
  obtain ⟨Q, hQ, hQscale, hQrank⟩ :=
    exists_compressionScale (K := K) (κ := κ) hτ hD hbound ht
  set ω : ℝ := rectangularOmega K κ with hω
  have hωnonneg : 0 ≤ ω := rectangularOmega_nonneg K κ
  have hApos : (0 : ℝ) < A := by
    have : (1 : ℝ) < A := by exact_mod_cast hA
    linarith
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  -- Compression at the near-optimal rectangular algorithm.
  have hres : Restricts
      (Tensor.indexedDirectSum (fun _ : ι ↦ matrixMultiplication (K := K) A A C))
      (matrixMultiplication (K := K) (Q * A) (Q * A)
        (rectangularMiddleDimension κ Q * C)) :=
    Tensor.RankLE.matrixMultiplication_compression_general
      (by simpa using hQrank)
  have hborder : BorderRankLE R
      (matrixMultiplication (K := K) (Q * A) (Q * A)
        (rectangularMiddleDimension κ Q * C)) := h.of_restricts hres
  have hQA : 1 < Q * A := lt_of_lt_of_le hA (Nat.le_mul_of_pos_left A hQ)
  have hmid' : (((Q * A : ℕ) : ℝ)) ^ κ ≤
      ((rectangularMiddleDimension κ Q * C : ℕ) : ℝ) := by
    have hsplit : (((Q * A : ℕ) : ℝ)) ^ κ = ((Q : ℝ)) ^ κ * ((A : ℝ)) ^ κ := by
      push_cast
      exact Real.mul_rpow hQpos.le hApos.le
    rw [hsplit]
    push_cast
    exact mul_le_mul (rpow_le_rectangularMiddleDimension κ Q) hmid
      (Real.rpow_nonneg hApos.le κ) (Nat.cast_nonneg _)
  have hkey : (((Q * A : ℕ) : ℝ)) ^ ω ≤ (R : ℝ) :=
    rpow_rectangularOmega_le_of_borderRankLE (K := K) hQA hR hκ hmid' hborder
  have hsplit : (((Q * A : ℕ) : ℝ)) ^ ω = ((Q : ℝ)) ^ ω * ((A : ℝ)) ^ ω := by
    push_cast
    exact Real.mul_rpow hQpos.le hApos.le
  rw [hsplit] at hkey
  -- Replace `Q` by the ideal real scale, at the cost of `2 ^ ω`.
  have hscale : ((((Fintype.card ι : ℝ)) / D) ^ (1 / τ)) ^ ω ≤ (2 : ℝ) ^ ω * ((Q : ℝ)) ^ ω := by
    have hnn : (0 : ℝ) ≤ (((Fintype.card ι : ℝ)) / D) ^ (1 / τ) :=
      Real.rpow_nonneg (by positivity) _
    calc
      ((((Fintype.card ι : ℝ)) / D) ^ (1 / τ)) ^ ω ≤ (2 * (Q : ℝ)) ^ ω :=
        Real.rpow_le_rpow hnn hQscale hωnonneg
      _ = (2 : ℝ) ^ ω * ((Q : ℝ)) ^ ω := Real.mul_rpow (by norm_num) hQpos.le
  calc
    ((((Fintype.card ι : ℝ)) / D) ^ (1 / τ)) ^ ω * ((A : ℝ)) ^ ω
        ≤ ((2 : ℝ) ^ ω * ((Q : ℝ)) ^ ω) * ((A : ℝ)) ^ ω :=
      mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hApos.le ω)
    _ = (2 : ℝ) ^ ω * (((Q : ℝ)) ^ ω * ((A : ℝ)) ^ ω) := by ring
    _ ≤ (2 : ℝ) ^ ω * (R : ℝ) :=
      mul_le_mul_of_nonneg_left hkey (Real.rpow_nonneg (by norm_num) ω)

end AlgebraicComplexity
