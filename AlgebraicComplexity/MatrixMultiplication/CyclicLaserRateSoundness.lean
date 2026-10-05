/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CyclicLaserRate
import AlgebraicComplexity.MatrixMultiplication.CyclicValueTensor
import AlgebraicComplexity.MatrixMultiplication.AsymptoticSum

/-!
# Soundness of the cyclic laser extraction rate

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `MatrixMultiplication/CyclicLaserRate.lean`
*produces* the relation `HasCyclicLaserExtractionRate K T v`: an extraction of matrix-multiplication
direct sums from powers of the three-orientation product `T ⊗ σT ⊗ σ²T`, normalized by the number
`3 * k` of source copies of `T`.  This module supplies the missing half, the direction that turns
such a rate into information about `omega`.

It is the cyclic counterpart of `HasLaserExtractionRate.le_log_borderRank`
(`MatrixMultiplication/Laser.lean`), and the bridge is the same one DESIGN.md names for the whole
laser layer: Schönhage's asymptotic sum inequality is the soundness direction, not a competing
extraction method.

## Main results

* `HasCyclicLaserExtractionRate.le_log_borderRank`: an achieved cyclic rate never exceeds
  `log R̲(T)`, the logarithm of the constructive border rank of the *source* tensor `T` — not of
  its cyclic product.  This is where the normalization by `3 * k` pays off: the cyclic product of
  `T^k` has border rank at most `R̲(T)^{3k}` (`borderRank_cyclicPowerProduct_le`), so the `3 * k`
  in the definition of the rate cancels exactly against the `3 * k` in that exponent.
* `HasCyclicLaserExtractionRate.le_log_of_borderRank_le`: the same bound against any numerical
  border-rank certificate `R̲(T) ≤ b`, the form a paper client actually has.
* `HasCyclicLaserExtractionRate.omega_le_of_borderRank_le`: the resulting upper bound on `omega`
  when the rate is presented in the copy-base/volume-base coordinates that
  `SubexponentialCyclicLaserVolumeSequence.hasCyclicLaserExtractionRate` produces.  Because
  `omega` occurs inside the rate (the asymptotic-sum weight is `(m*n*p)^(omega/3)`), the
  inequality is *solved* for `omega` here, which is the shape a numerical client needs.
* `CyclicDegenerationCertificate.hasCyclicLaserExtractionRate`: a finite cyclic value certificate
  at exponent `omega/3` achieves the logarithm of its normalized term as a cyclic laser rate.
* `HasCyclicLaserExtractionRate.exp_le_degenerationValue`: conversely, a cyclic laser rate gives
  the regularized lower bound `exp value ≤ degenerationValue T (omega/3)`; the required
  boundedness of the critical value set is proved internally from cyclic-rate soundness.

## Why the hypotheses are what they are

`asymptoticSum_le_of_borderRankLE` (Schönhage's inequality, `MatrixMultiplication/AsymptoticSum.lean`)
needs a field; the whole module therefore lives over `[Field K]`.  Its numerical premise is a
*border-rank certificate for the tensor that was degenerated*, here the cyclic power product, and
that certificate is obtained structurally rather than assumed: `borderRank_cyclicPowerProduct_le`
composes `borderRank_power_le`, `borderRank_permute_cycle_le`, and `borderRank_external_le`.  No
hypothesis of this module asserts a relation from the assembled cyclic source to the assembled
target family; that is exactly the conclusion the extraction interface exists to prove.

## Non-goal

Nothing here derives a *lower* bound on `omega`; the laser method is an upper-bound method, and
  the barrier modules (`MatrixMultiplication/UniversalSliceRankBarrier.lean`) are the other side.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

section Field

variable (K : Type u) [Field K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- The volume power sum inside a positive cyclic certificate is positive.

This small local lemma avoids importing the full unsymmetrized `TauValue` calculus merely for its
corresponding finite-sum positivity theorem. -/
private theorem cyclicCertificate_volumePowerSum_pos
    {T : Tensor3 K V} {τ : ℝ} {Rel : CyclicExtractionRelation K T}
    (certificate : CyclicExtractionCertificate K T τ Rel) :
    0 < matrixMultiplicationVolumePowerSum
      certificate.xSize certificate.ySize certificate.zSize τ := by
  letI : Nonempty (Fin certificate.copies) :=
    ⟨⟨0, certificate.copies_pos⟩⟩
  unfold matrixMultiplicationVolumePowerSum
  refine Finset.sum_pos (fun i _ ↦ ?_) Finset.univ_nonempty
  have hvolume : 0 < matrixMultiplicationVolume
      certificate.xSize certificate.ySize certificate.zSize i :=
    Nat.mul_pos (Nat.mul_pos (certificate.xSize_pos i) (certificate.ySize_pos i))
      (certificate.zSize_pos i)
  exact Real.rpow_pos_of_pos (by exact_mod_cast hvolume) _

/-- Logarithmic form of the cyclic normalization identity.

The factor `3 * power` cancels the reciprocal exponent in the definition of the certificate
term.  Keeping this identity local lets the rate/value bridge depend only on the lightweight
cyclic value core. -/
private theorem cyclicCertificate_mul_log_term
    {T : Tensor3 K V} {τ : ℝ} {Rel : CyclicExtractionRelation K T}
    (certificate : CyclicExtractionCertificate K T τ Rel) :
    (((3 * certificate.power : ℕ) : ℝ)) * Real.log certificate.term =
      Real.log (matrixMultiplicationVolumePowerSum
        certificate.xSize certificate.ySize certificate.zSize τ) := by
  have hsum := cyclicCertificate_volumePowerSum_pos K certificate
  have hpower : (((3 * certificate.power : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num : 3 ≠ 0) certificate.power_pos.ne'
  unfold CyclicExtractionCertificate.term cyclicValueTerm
  rw [Real.log_rpow hsum]
  field_simp

/-- **A finite cyclic degeneration certificate produces a cyclic laser rate.**  At the critical
exponent `omega/3`, the achieved rate is the logarithm of the certificate's normalized value term.

Proof sketch: use the certificate's own positive power and direct-sum degeneration for every
requested loss `ε`.  The logarithmic normalization identity says that `3k * log(term)` is exactly
the logarithm of the asymptotic sum.  Subtracting the positive quantity `3k * ε` proves the rate
inequality. -/
theorem CyclicDegenerationCertificate.hasCyclicLaserExtractionRate
    {T : Tensor3 K V}
    (certificate : CyclicDegenerationCertificate K T (omega K / 3)) :
    HasCyclicLaserExtractionRate K T (Real.log certificate.term) := by
  intro ε hε
  have hsum : 0 < asymptoticSum K
      certificate.xSize certificate.ySize certificate.zSize := by
    simpa only [asymptoticSum] using
      cyclicCertificate_volumePowerSum_pos K certificate
  refine ⟨certificate.power, certificate.copies,
    certificate.xSize, certificate.ySize, certificate.zSize,
    certificate.power_pos, certificate.xSize_pos, certificate.ySize_pos,
    certificate.zSize_pos, certificate.degenerates, hsum, ?_⟩
  have hlog := cyclicCertificate_mul_log_term K certificate
  have hfactor : 0 < (((3 * certificate.power : ℕ) : ℝ)) := by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 3) certificate.power_pos
  change (((3 * certificate.power : ℕ) : ℝ)) *
      (Real.log certificate.term - ε) ≤
        Real.log (matrixMultiplicationVolumePowerSum
          certificate.xSize certificate.ySize certificate.zSize (omega K / 3))
  rw [← hlog]
  nlinarith

/-- **A cyclic laser rate supplies finite degeneration-value lower terms.**  For every positive
`ε`, the polynomial degeneration in the rate witness gives a cyclic certificate whose normalized
term is at least `exp (value - ε)`.

Proof sketch: package the witness as a `CyclicDegenerationCertificate` at `omega/3`.  Its
logarithmic normalization turns the stored rate inequality into
`value - ε ≤ log certificate.term`; exponentiating and taking the supremum gives the claim. -/
theorem HasCyclicLaserExtractionRate.exp_sub_le_degenerationValue_of_bddAbove
    {T : Tensor3 K V} {value ε : ℝ}
    (h : HasCyclicLaserExtractionRate K T value)
    (hbounded : BddAbove (degenerationValueValues K T (omega K / 3)))
    (hε : 0 < ε) :
    Real.exp (value - ε) ≤ degenerationValue K T (omega K / 3) := by
  rcases h ε hε with ⟨k, L, m, n, p, hk, hm, hn, hp, hdeg, hsum, hrate⟩
  have hL : 0 < L := by
    by_contra hL
    have : L = 0 := Nat.eq_zero_of_not_pos hL
    subst L
    simp [asymptoticSum, matrixMultiplicationVolumePowerSum] at hsum
  let certificate : CyclicDegenerationCertificate K T (omega K / 3) :=
    CyclicDegenerationCertificate.of_polynomialDegenerates K
      (omega K / 3) T k L m n p hk hL hm hn hp hdeg
  have hlog := cyclicCertificate_mul_log_term K certificate
  have hfactor : 0 < (((3 * k : ℕ) : ℝ)) := by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 3) hk
  change (((3 * k : ℕ) : ℝ)) * Real.log certificate.term =
    Real.log (asymptoticSum K m n p) at hlog
  have hlogLower : value - ε ≤ Real.log certificate.term := by
    nlinarith
  calc
    Real.exp (value - ε) ≤ Real.exp (Real.log certificate.term) :=
      Real.exp_le_exp.mpr hlogLower
    _ = certificate.term := Real.exp_log certificate.term_pos
    _ ≤ degenerationValue K T (omega K / 3) :=
      certificate.le_degenerationValue K hbounded

/-- **Regularized identification of cyclic laser rates with degeneration value.**  Every achieved
cyclic logarithmic rate `value` satisfies

```text
exp value ≤ degenerationValue T (omega/3).
```

The explicit boundedness premise is the same one required whenever the library reads information
from a supremum; it is not hidden in the definition of `degenerationValue`.

Proof sketch: the preceding theorem gives `exp (value - ε) ≤ degenerationValue` for every
positive `ε`.  The right side is positive (take `ε = 1`), so taking logarithms gives
`value - ε ≤ log degenerationValue`.  Letting `ε` tend to zero via
`le_of_forall_sub_le` and exponentiating proves the closed inequality. -/
theorem HasCyclicLaserExtractionRate.exp_le_degenerationValue_of_bddAbove
    {T : Tensor3 K V} {value : ℝ}
    (h : HasCyclicLaserExtractionRate K T value)
    (hbounded : BddAbove (degenerationValueValues K T (omega K / 3))) :
    Real.exp value ≤ degenerationValue K T (omega K / 3) := by
  have hsub : ∀ ε : ℝ, 0 < ε →
      Real.exp (value - ε) ≤ degenerationValue K T (omega K / 3) :=
    fun ε hε ↦ h.exp_sub_le_degenerationValue_of_bddAbove K hbounded hε
  have hvaluePos : 0 < degenerationValue K T (omega K / 3) :=
    (Real.exp_pos (value - 1)).trans_le (hsub 1 zero_lt_one)
  have hlog : value ≤ Real.log (degenerationValue K T (omega K / 3)) := by
    apply le_of_forall_sub_le
    intro ε hε
    exact (Real.le_log_iff_exp_le hvaluePos).2 (hsub ε hε)
  calc
    Real.exp value ≤ Real.exp (Real.log (degenerationValue K T (omega K / 3))) :=
      Real.exp_le_exp.mpr hlog
    _ = degenerationValue K T (omega K / 3) := Real.exp_log hvaluePos

/-- **Soundness of the cyclic laser rate.**  Any cyclic logarithmic extraction rate achieved by
`T` is at most the logarithm of the constructive border rank of `T` itself.

Proof sketch: suppose `value > log R̲(T)` and take the slack `ε = (value - log R̲(T))/2`.  The rate
witness supplies a power `k > 0` and a polynomial degeneration of `T ⊗ σT ⊗ σ²T` at exponent `k`
onto `⊕_i ⟨m i, n i, p i⟩` with

```text
3k * (value - ε) ≤ log (Σ_i (m i * n i * p i)^(omega/3)).
```

Schönhage's asymptotic sum inequality (`asymptoticSum_le_of_borderRankLE`) bounds that sum by any
border-rank certificate of the degenerated source, and `borderRank_cyclicPowerProduct_le` gives the
certificate `R̲(T)^{3k}` — the three orientations each contribute `R̲(T)^k`, since border rank is
submultiplicative under external products and invariant under leg permutations.  Taking logarithms
turns the right-hand side into `3k * log R̲(T)`; cancelling the positive factor `3k` gives
`value - ε ≤ log R̲(T)`, i.e. `value ≤ log R̲(T) + ε`, which contradicts the choice of `ε`. -/
theorem HasCyclicLaserExtractionRate.le_log_borderRank
    {T : Tensor3 K V} {value : ℝ}
    (h : HasCyclicLaserExtractionRate K T value) :
    value ≤ Real.log (borderRank T) := by
  by_contra hvalue
  have hgap : 0 < value - Real.log (borderRank T) :=
    sub_pos.mpr (lt_of_not_ge hvalue)
  let ε := (value - Real.log (borderRank T)) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  rcases h ε hε with ⟨k, L, m, n, p, hk, hm, hn, hp, hdeg, hsum, hrate⟩
  have hbr : BorderRankLE (borderRank T ^ (3 * k)) (cyclicPowerProduct K T k) :=
    borderRank_le_iff.mp (borderRank_cyclicPowerProduct_le K T k)
  have hasi := asymptoticSum_le_of_borderRankLE (ι := Fin L) K m n p hbr hm hn hp hdeg
  have hlog :
      Real.log (asymptoticSum K m n p) ≤
        Real.log ((borderRank T ^ (3 * k) : ℕ) : ℝ) :=
    Real.log_le_log hsum hasi
  rw [Nat.cast_pow, Real.log_pow] at hlog
  have hrate' := hrate.trans hlog
  have hk_real : (0 : ℝ) < ((3 * k : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 3) hk
  dsimp [ε] at hrate'
  nlinarith

/-- **Critical cyclic degeneration values are automatically bounded above.**  At
`τ = omega/3`, every finite degeneration certificate term is at most
`exp (log (borderRank T))`.

The exponential-logarithm expression deliberately handles `borderRank T = 0` without pretending
that Lean's total real logarithm sends zero to negative infinity.  For positive border rank the
bound simplifies to `borderRank T`.

Proof sketch: a finite certificate achieves the cyclic rate `log certificate.term`; cyclic-rate
soundness bounds that logarithm by `log (borderRank T)`.  Exponentiating recovers the positive
certificate term. -/
theorem degenerationValueValues_bddAbove_omega_div_three (T : Tensor3 K V) :
    BddAbove (degenerationValueValues K T (omega K / 3)) := by
  refine ⟨Real.exp (Real.log (borderRank T)), ?_⟩
  rintro x ⟨certificate, rfl⟩
  have hrate : HasCyclicLaserExtractionRate K T (Real.log certificate.term) :=
    CyclicDegenerationCertificate.hasCyclicLaserExtractionRate K certificate
  have hlog := hrate.le_log_borderRank K
  calc
    certificate.term = Real.exp (Real.log certificate.term) :=
      (Real.exp_log certificate.term_pos).symm
    _ ≤ Real.exp (Real.log (borderRank T)) := Real.exp_le_exp.mpr hlog

/-- Every cyclic laser rate gives finite degeneration-value lower terms arbitrarily close in the
logarithmic scale.  At the critical exponent, boundedness is supplied by cyclic-rate soundness and
need not be assumed by the caller. -/
theorem HasCyclicLaserExtractionRate.exp_sub_le_degenerationValue
    {T : Tensor3 K V} {value ε : ℝ}
    (h : HasCyclicLaserExtractionRate K T value) (hε : 0 < ε) :
    Real.exp (value - ε) ≤ degenerationValue K T (omega K / 3) :=
  h.exp_sub_le_degenerationValue_of_bddAbove K
    (degenerationValueValues_bddAbove_omega_div_three K T) hε

/-- **Unconditional regularized rate-to-value bridge.**  Every achieved cyclic logarithmic rate
is bounded by the polynomial-degeneration value at the critical exponent:

```text
exp value ≤ degenerationValue T (omega/3).
```

Proof sketch: cyclic-rate soundness bounds the complete critical value set, after which the
epsilon-regularization theorem applies. -/
theorem HasCyclicLaserExtractionRate.exp_le_degenerationValue
    {T : Tensor3 K V} {value : ℝ}
    (h : HasCyclicLaserExtractionRate K T value) :
    Real.exp value ≤ degenerationValue K T (omega K / 3) :=
  h.exp_le_degenerationValue_of_bddAbove K
    (degenerationValueValues_bddAbove_omega_div_three K T)

/-- The cyclic rate against a numerical border-rank certificate: if `R̲(T) ≤ b` with `b > 0`, then
every achieved cyclic rate is at most `log b`.

This is the form paper clients use, since a client certifies a concrete border rank (for example
`q + 2` for a Coppersmith--Winograd tensor) rather than computing `R̲(T)` exactly.  The degenerate
case `R̲(T) = 0` (that is, `T = 0`) is handled separately because `Real.log` is not monotone
through `0`. -/
theorem HasCyclicLaserExtractionRate.le_log_of_borderRank_le
    {T : Tensor3 K V} {value : ℝ} {b : ℕ}
    (h : HasCyclicLaserExtractionRate K T value) (hb : 0 < b)
    (hle : borderRank T ≤ b) :
    value ≤ Real.log b := by
  refine (HasCyclicLaserExtractionRate.le_log_borderRank K h).trans ?_
  rcases Nat.eq_zero_or_pos (borderRank T) with h0 | h0
  · rw [h0]
    simpa using Real.log_nonneg (by exact_mod_cast hb : (1 : ℝ) ≤ (b : ℝ))
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hle)

/-- **The numerical exponent bound behind a cyclic laser certificate.**  Suppose `T` achieves the
cyclic rate produced by a copy base `copyBase` and a rectangular-volume base `volumeBase` along a
stride of `stride` source tensors, namely

```text
(log copyBase + (omega/3) * log volumeBase) / (3 * stride),
```

and suppose `R̲(T) ≤ b` and `log volumeBase > 0`.  Then

```text
omega ≤ 3 * (3 * stride * log b - log copyBase) / log volumeBase.
```

Proof sketch: `le_log_of_borderRank_le` bounds the rate by `log b`; clearing the positive
denominator `3 * stride` gives `log copyBase + (omega/3) * log volumeBase ≤ 3 * stride * log b`,
and dividing by the positive `log volumeBase` isolates `omega`.  The hypothesis
`0 < log volumeBase` is what makes the extracted rectangular tensors grow, and is exactly the
condition under which the comparison carries information: a volume base of `1` produces scalars and
constrains nothing. -/
theorem HasCyclicLaserExtractionRate.omega_le_of_borderRank_le
    {T : Tensor3 K V} {stride : ℕ} {copyBase volumeBase : ℝ} {b : ℕ}
    (h : HasCyclicLaserExtractionRate K T
      ((Real.log copyBase + (omega K / 3) * Real.log volumeBase) / (3 * (stride : ℝ))))
    (hstride : 0 < stride) (hb : 0 < b) (hle : borderRank T ≤ b)
    (hvolume : 0 < Real.log volumeBase) :
    omega K ≤
      3 * (3 * (stride : ℝ) * Real.log b - Real.log copyBase) / Real.log volumeBase := by
  have hstrideReal : (0 : ℝ) < (stride : ℝ) := by exact_mod_cast hstride
  have hden : (0 : ℝ) < 3 * (stride : ℝ) := by positivity
  have hmain := HasCyclicLaserExtractionRate.le_log_of_borderRank_le K h hb hle
  rw [div_le_iff₀ hden] at hmain
  rw [le_div_iff₀ hvolume]
  linarith

end Field

end AlgebraicComplexity
