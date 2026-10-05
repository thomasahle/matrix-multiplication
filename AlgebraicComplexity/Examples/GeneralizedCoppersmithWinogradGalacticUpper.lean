/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/
import AlgebraicComplexity.Analysis.LogConstants
import AlgebraicComplexity.Examples.GeneralizedCoppersmithWinogradBorderRank
import AlgebraicComplexity.Examples.GeneralizedCoppersmithWinogradIndependenceLower

/-!
# The Galactic method does reach `f(q)` on a Coppersmith--Winograd tensor

Layer 4 (`AlgebraicComplexity/Examples/`).  This module is milestone **M8** of
`BARRIER_FRAMEWORK.md`: the *upper* bound

```text
ω_g^{coord}(CW_q^σ) ≤ f(q),      f(q) = log_q (4(q+2)³/27),
```

the by-product of the coordinate extraction of milestone M5 that closes the loop around
[AlmanVassilevskaWilliams2018, Definition 4.1].  Together with AVW Theorem 7.1
(`avw_theorem_seven_one`, `2 + 1/15000 ≤ ω_g^{coord}(CW_q^σ)`) it turns the barrier into a
*sandwich*: the coordinate Galactic exponent of a Coppersmith--Winograd tensor is a real number
trapped between an absolute constant above `2` and the classical bound `f(q)`, so Theorem 7.1 is
a statement about a quantity the method genuinely attains rather than a vacuous lower bound.

## Main results

* `coordinateGalacticCertificate_gcwTable_pow`: **the extraction, read on the full table.** The
  milestone-M5 certificates are certificates for `gcwEasyTable`, the table of `CW_q^σ` with the
  coordinate `q + 1` deleted; `CoordinateGalacticCertificate.of_coordinateZeroOut` composes them
  with that deletion into certificates for `gcwTable` itself.
* `coordinateGalacticExponent_gcwTable_le_avwF`: **milestone M8.** For `q ≥ 2` and any `σ` whose
  member of the family has border rank at most `q + 2`,
  `ω_g^{coord}(CW_q^σ) ≤ f(q)`.
* `coordinateGalacticExponent_gcwTable_refl_le_avwF`: the same with the border-rank hypothesis
  discharged, for the classical member `σ = id` of the family.
* `avw_galactic_exponent_gcwTable_sandwich`: the two-sided statement
  `2 + 1/15000 ≤ ω_g^{coord}(CW_q) ≤ f(q)` on the literal index set of AVW Definition 3.1.
* `avwF_six_le`, `avwF_six_ge` and `avw_galactic_exponent_gcwTable_fin_six`: the numeric instance
  `q = 6`, `f(6) ∈ [2.4159, 2.416]` and `2 + 1/15000 ≤ ω_g^{coord}(CW_6) ≤ 2.416`, in exact
  rational arithmetic on the certified logarithm enclosures of `Analysis/LogConstants.lean`.

## The three ingredients

1. **Border rank.**  A certificate value is `3(log R̲(T^{⊗n}) − log F)/log(abc)`, so the upper
   bound needs `R̲((CW_q^σ)^{⊗3k}) ≤ (q+2)^{3k}`, which is `Tensor.borderRank_power_le` applied to
   a bound `R̲(CW_q^σ) ≤ q + 2`.  That bound is a *hypothesis* here, and
   `Examples/GeneralizedCoppersmithWinogradBorderRank.lean` explains why: it is a theorem for
   `σ = id` (`borderRank_genCW_refl_le`) and, by Strassen's commutation equations, **false**
   whenever `σ` is not an involution.  Since the classical bound `f(q)` is what
   [CoppersmithWinograd1990, §6] proves for `CW_q`, that is exactly the case AVW's Definition 4.1
   loop needs.
2. **From the easy table to the full table.**  Milestone M5 extracts from `gcwEasyTable`, a
   zeroing out of `gcwTable`; a coordinate Galactic certificate for a zeroing out is one for the
   source (`CoordinateGalacticCertificate.of_coordinateZeroOut`, proved generically in
   `MatrixMultiplication/IndependenceBarrier.lean`).
3. **The limit.**  `coordinateGalacticExponent` is an infimum, so it suffices to produce, for each
   `ε > 0`, one certificate of value at most `f(q) + ε`.  With `a = b = c = q^k`, `n = 3k` and `F`
   copies the value is `(log R̲ − log F)/(k log q)`, so what is needed is `F ≥ ((27/4)·q^{−ε})^k`
   for one `k`.  That is `Growth.exists_forall_pow_le_copies`
   (`Analysis/BehrendRate.lean`), the copy-count reading of the Behrend rate argument: the hashing
   count `27^k · roth(M/2) ≤ 6k²M²F` with `M ≤ 24·4^k` forces `F ≥ (27/4)^k / loss(k)` with
   subexponential loss, and a subexponential loss is eventually below `q^{εk}`.

The identity that makes the three fit is
`3 log(q+2) − log(27/4) = log(4(q+2)³/27) = f(q) · log q`, i.e. `rpow_avwF` in logarithmic form:
the base `27/4` lost to Behrend and the modulus is exactly the gap between the naive `3 log(q+2)`
and the classical exponent.

## Erratum to [AlmanVassilevskaWilliams2018] carried here

AVW write "Coppersmith and Winograd show that `ω_g(CW_q) ≥ f(q)`"; the inequality is the wrong way
round --- `f(q)` is the exponent bound the method *achieves*, so the correct statement is the `≤`
proved here.  This is already recorded in `BARRIER_FRAMEWORK.md` milestone M and in the module doc
of `Examples/GeneralizedCoppersmithWinogradIndependenceLower.lean`.

## What is *not* claimed

Nothing is claimed about the basis-free `AlgebraicComplexity.galacticExponent`.  The comparison
`galacticExponent_le_coordinateGalacticExponent` transports upper bounds *downwards*, so
`ω_g(CW_q) ≤ ω_g^{coord}(CW_q) ≤ f(q)` does follow
(`galacticExponent_genCW_refl_le_avwF`), but the Theorem 7.1 lower bound does not transport, and
the sandwich is a statement about the coordinate exponent only.

## Position in the library

Layer 4.  It imports `Examples/GeneralizedCoppersmithWinogradBorderRank.lean` and
`Examples/GeneralizedCoppersmithWinogradIndependenceLower.lean` (hence milestones M5--M7, the
Behrend rate module and AVW Theorem 7.1).  Nothing here is imported by a lower layer.

## References

* [AlmanVassilevskaWilliams2018] J. Alman and V. Vassilevska Williams, *Limits on all known (and
  some unknown) approaches to matrix multiplication*, arXiv:1810.08671; Definitions 3.1 and 4.1,
  Theorem 7.1, Section 7.
* [CoppersmithWinograd1990] D. Coppersmith and S. Winograd, *Matrix multiplication via arithmetic
  progressions*, J. Symbolic Comput. 9 (1990); §6.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

section Certificate

/-- **The milestone-M5 extraction, read on the full generalized Coppersmith--Winograd table.**

For every `k ≥ 1` there are a hashing modulus `M ≤ 24·4^k` and a copy count `F` with
`27^k · roth(M/2) ≤ 6k²M²·F` such that `CW_q^σ` has a coordinate Galactic certificate with data
`(3k, q^k, q^k, q^k, F)`.

Proof sketch: `coordinateGalacticCertificate_gcwEasyTable` provides exactly this for the *easy*
table, the zeroing out of `gcwTable K μ σ` deleting the coordinate `q + 1` on every leg; and
`CoordinateGalacticCertificate.of_coordinateZeroOut` composes a certificate for a zeroing out with
that zeroing out into a certificate for the source table. -/
theorem coordinateGalacticCertificate_gcwTable_pow (K : Type u) [CommSemiring K]
    (μ : Type) [Fintype μ] [DecidableEq μ] (σ : Equiv.Perm μ)
    (hq : 0 < Fintype.card μ) {k : ℕ} (hk : 0 < k) :
    ∃ M copies : ℕ, 2 ≤ M ∧ M ≤ 24 * 4 ^ k ∧
      27 ^ k * rothNumberNat (M / 2) ≤ 6 * k ^ 2 * (M * M) * copies ∧
        CoordinateGalacticCertificate K (gcwTable K μ σ) (3 * k)
          (Fintype.card μ ^ k) (Fintype.card μ ^ k) (Fintype.card μ ^ k) copies := by
  obtain ⟨M, copies, hM2, hMub, hrate, hcert⟩ :=
    coordinateGalacticCertificate_gcwEasyTable K μ σ hq hk
  rw [gcwEasyTable] at hcert
  exact ⟨M, copies, hM2, hMub, hrate, hcert.of_coordinateZeroOut K⟩

end Certificate

section Upper

variable (K : Type u) [Field K] (μ : Type) [Fintype μ] [DecidableEq μ]

/-- **Milestone M8 of `BARRIER_FRAMEWORK.md`**: the Galactic method, run on the coefficient table
of a generalized Coppersmith--Winograd tensor of border rank `q + 2`, reaches the classical
Coppersmith--Winograd exponent

```text
ω_g^{coord}(CW_q^σ) ≤ f(q) = log_q (4(q+2)³/27).
```

The border-rank hypothesis is genuinely needed and genuinely restrictive; see
`Examples/GeneralizedCoppersmithWinogradBorderRank.lean`.  It is discharged for the classical
member `σ = id` in `coordinateGalacticExponent_gcwTable_refl_le_avwF`.

Proof sketch.  `coordinateGalacticExponent` is an infimum over certificate values, so by
`le_of_forall_pos_le_add` it suffices to exhibit, for each `ε > 0`, one certificate of value at
most `f(q) + ε`.  Fix `ε` and put `W = (27/4)·q^{−ε} < 27/4`.

The Behrend rate argument in copy-count form
(`AlgebraicComplexity.Growth.exists_forall_pow_le_copies` with `A = 27`, `D = 4`, `E = 24`,
`poly k = 6k²`) yields a threshold `N` beyond which every hashing count of the milestone-M5 shape
forces `W^k ≤ F`.  Take `k = max N 1` and let `M`, `F` be the modulus and copy count of
`coordinateGalacticCertificate_gcwTable_pow` at that `k`; the certificate has data
`(3k, q^k, q^k, q^k, F)`, so its value is

```text
3(log R̲ − log F)/log(q^{3k}) = (log R̲ − log F)/(k log q),
```

with `R̲ = R̲((CW_q^σ)^{⊗3k}) ≤ (q+2)^{3k}` by `Tensor.borderRank_power_le` and the hypothesis.
Since `log F ≥ k(log(27/4) − ε log q)`, the numerator is at most
`k(3 log(q+2) − log(27/4)) + kε log q`, and `3 log(q+2) − log(27/4) = log(4(q+2)³/27)` is
`f(q) · log q` by the definition of `f`.  Dividing by `k log q > 0` gives `f(q) + ε`. -/
theorem coordinateGalacticExponent_gcwTable_le_avwF (σ : Equiv.Perm μ)
    (hq : 2 ≤ Fintype.card μ)
    (hbr : Tensor.borderRank (genCW K μ σ) ≤ Fintype.card μ + 2) :
    coordinateGalacticExponent K (gcwTable K μ σ) ≤ avwF (Fintype.card μ) := by
  classical
  have hqR : (2 : ℝ) ≤ (Fintype.card μ : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) < (Fintype.card μ : ℝ) := by linarith
  have hqpos : (0 : ℝ) < (Fintype.card μ : ℝ) := by linarith
  have hlogq : 0 < Real.log (Fintype.card μ : ℝ) := Real.log_pos hq1
  -- The logarithmic form of the defining property of `f`.
  have havwF : avwF (Fintype.card μ) * Real.log (Fintype.card μ : ℝ) =
      Real.log ((4 / 27 : ℝ) * ((Fintype.card μ + 2 : ℕ) : ℝ) ^ 3) := by
    rw [avwF, div_mul_cancel₀ _ hlogq.ne']
  have hcard2 : (1 : ℝ) ≤ ((Fintype.card μ + 2 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ Fintype.card μ + 2 := by omega
    exact_mod_cast this
  have hlog2nonneg : 0 ≤ Real.log ((Fintype.card μ + 2 : ℕ) : ℝ) := Real.log_nonneg hcard2
  have hsplit : Real.log ((4 / 27 : ℝ) * ((Fintype.card μ + 2 : ℕ) : ℝ) ^ 3) =
      -Real.log (27 / 4 : ℝ) + 3 * Real.log ((Fintype.card μ + 2 : ℕ) : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      show (4 / 27 : ℝ) = (27 / 4 : ℝ)⁻¹ by norm_num, Real.log_inv]
    push_cast
    ring
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  -- The base the copy count has to beat.
  have hrpow : (1 : ℝ) < (Fintype.card μ : ℝ) ^ ε :=
    Real.one_lt_rpow_iff_of_pos hqpos |>.mpr (Or.inl ⟨hq1, hε⟩)
  have hrpowpos : (0 : ℝ) < (Fintype.card μ : ℝ) ^ ε := Real.rpow_pos_of_pos hqpos ε
  have hWpos : (0 : ℝ) < 27 / 4 / (Fintype.card μ : ℝ) ^ ε := by positivity
  have hWlt : 27 / 4 / (Fintype.card μ : ℝ) ^ ε < 27 / 4 := by
    exact div_lt_self (by norm_num) hrpow
  have hlogW : Real.log (27 / 4 / (Fintype.card μ : ℝ) ^ ε) =
      Real.log (27 / 4 : ℝ) - ε * Real.log (Fintype.card μ : ℝ) := by
    rw [Real.log_div (by norm_num) hrpowpos.ne', Real.log_rpow hqpos]
  -- The Behrend threshold.
  obtain ⟨N, hN⟩ := Growth.exists_forall_pow_le_copies
    (A := 27) (D := 4) (E := 24) (W := 27 / 4 / (Fintype.card μ : ℝ) ^ ε)
    (poly := fun k ↦ 6 * (k : ℝ) ^ 2) (by norm_num) (by norm_num)
    ((Growth.Subexponential.natCast_pow 2).const_mul (by norm_num)) hWpos (by norm_num [hWlt])
  set k : ℕ := max N 1 with hkdef
  have hk : 0 < k := lt_of_lt_of_le Nat.one_pos (le_max_right N 1)
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  obtain ⟨M, copies, hM2, hMub, hrate, hcert⟩ :=
    coordinateGalacticCertificate_gcwTable_pow K μ σ (by omega) hk
  -- The Behrend copy-count bound at that `k`.
  have hcopies : (27 / 4 / (Fintype.card μ : ℝ) ^ ε) ^ k ≤ (copies : ℝ) :=
    hN k M copies (le_max_left N 1) hM2 (by exact_mod_cast hMub) (by exact_mod_cast hrate)
  have hcopiespos : (0 : ℝ) < (copies : ℝ) := lt_of_lt_of_le (pow_pos hWpos k) hcopies
  have hF : 1 ≤ copies := by
    rcases Nat.eq_zero_or_pos copies with h0 | h
    · rw [h0] at hcopiespos; norm_num at hcopiespos
    · exact h
  -- Nondegeneracy of the certificate shape.
  have hqk : 2 ≤ Fintype.card μ ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      _ ≤ Fintype.card μ ^ k := Nat.pow_le_pow_left hq k
  have habc : 2 ≤ Fintype.card μ ^ k * Fintype.card μ ^ k * Fintype.card μ ^ k := by
    have h1 : 1 ≤ Fintype.card μ ^ k := le_trans (by norm_num) hqk
    nlinarith
  -- The certificate value is in the value set, so it bounds the infimum.
  have hmem : galacticValue (Fintype.card μ ^ k) (Fintype.card μ ^ k) (Fintype.card μ ^ k) copies
      (Tensor.borderRank (Tensor.power (coordinateTensor (gcwTable K μ σ)) (3 * k))) ∈
      coordinateGalacticValues K (gcwTable K μ σ) :=
    ⟨3 * k, _, _, _, copies, hcert, habc, hF, rfl⟩
  refine le_trans (csInf_le (coordinateGalacticValues_bddBelow K _) hmem) ?_
  -- The value estimate.
  set R : ℕ := Tensor.borderRank (Tensor.power (coordinateTensor (gcwTable K μ σ)) (3 * k))
    with hRdef
  have hRle : R ≤ (Fintype.card μ + 2) ^ (3 * k) := by
    refine le_trans (Tensor.borderRank_power_le _ _) (Nat.pow_le_pow_left ?_ _)
    rw [coordinateTensor_gcwTable]
    exact hbr
  have hlogR : Real.log (R : ℝ) ≤
      3 * (k : ℝ) * Real.log ((Fintype.card μ + 2 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos R with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      positivity
    · have hcast : (R : ℝ) ≤ ((Fintype.card μ + 2 : ℕ) : ℝ) ^ (3 * k) := by
        exact_mod_cast hRle
      calc Real.log (R : ℝ)
          ≤ Real.log (((Fintype.card μ + 2 : ℕ) : ℝ) ^ (3 * k)) :=
            Real.log_le_log (by exact_mod_cast hpos) hcast
        _ = ((3 * k : ℕ) : ℝ) * Real.log ((Fintype.card μ + 2 : ℕ) : ℝ) := Real.log_pow _ _
        _ = 3 * (k : ℝ) * Real.log ((Fintype.card μ + 2 : ℕ) : ℝ) := by push_cast; ring
  have hlogF : (k : ℝ) * (Real.log (27 / 4 : ℝ) - ε * Real.log (Fintype.card μ : ℝ)) ≤
      Real.log (copies : ℝ) := by
    have h := Real.log_le_log (pow_pos hWpos k) hcopies
    rwa [Real.log_pow, hlogW] at h
  -- Now the arithmetic.
  have hden : Real.log ((((Fintype.card μ ^ k) * (Fintype.card μ ^ k) *
      (Fintype.card μ ^ k) : ℕ)) : ℝ) = 3 * (k : ℝ) * Real.log (Fintype.card μ : ℝ) := by
    have hcast : (((Fintype.card μ ^ k) * (Fintype.card μ ^ k) *
        (Fintype.card μ ^ k) : ℕ) : ℝ) = (Fintype.card μ : ℝ) ^ (3 * k) := by
      push_cast
      ring
    rw [hcast, Real.log_pow]
    push_cast
    ring
  have hdenpos : (0 : ℝ) < 3 * (k : ℝ) * Real.log (Fintype.card μ : ℝ) := by positivity
  rw [galacticValue, hden, div_le_iff₀ hdenpos]
  have hrhs : (avwF (Fintype.card μ) + ε) * (3 * (k : ℝ) * Real.log (Fintype.card μ : ℝ)) =
      3 * (k : ℝ) * (-Real.log (27 / 4 : ℝ) +
          3 * Real.log ((Fintype.card μ + 2 : ℕ) : ℝ)) +
        3 * ((k : ℝ) * (ε * Real.log (Fintype.card μ : ℝ))) := by
    rw [← hsplit, ← havwF]
    ring
  rw [hrhs]
  nlinarith [hlogR, hlogF]

/-- **Milestone M8 for the classical Coppersmith--Winograd tensor**: with no hypothesis beyond
`q ≥ 2`,

```text
ω_g^{coord}(CW_q) ≤ f(q) = log_q (4(q+2)³/27).
```

The border-rank hypothesis of `coordinateGalacticExponent_gcwTable_le_avwF` is discharged by
`borderRank_genCW_refl_le`, the classical `q + 2` certificate of [CoppersmithWinograd1990]. -/
theorem coordinateGalacticExponent_gcwTable_refl_le_avwF (hq : 2 ≤ Fintype.card μ) :
    coordinateGalacticExponent K (gcwTable K μ (Equiv.refl μ)) ≤ avwF (Fintype.card μ) :=
  coordinateGalacticExponent_gcwTable_le_avwF K μ (Equiv.refl μ) hq
    (borderRank_genCW_refl_le K μ)

/-- The basis-free Galactic exponent of `CW_q` is also at most `f(q)`: upper bounds transport along
`galacticExponent_le_coordinateGalacticExponent`, unlike the Theorem 7.1 lower bound. -/
theorem galacticExponent_genCW_refl_le_avwF (hq : 2 ≤ Fintype.card μ) :
    galacticExponent K (genCW K μ (Equiv.refl μ)) ≤ avwF (Fintype.card μ) :=
  le_trans (galacticExponent_genCW_le_coordinateGalacticExponent_gcwTable (Equiv.refl μ)
      (coordinateGalacticValues_gcwTable_nonempty K (Equiv.refl μ)))
    (coordinateGalacticExponent_gcwTable_refl_le_avwF K μ hq)

end Upper

section Sandwich

/-- **The Definition 4.1 loop, closed.**  On the literal index set of
[AlmanVassilevskaWilliams2018, Definition 3.1] and for every `q ≥ 2`,

```text
2 + 1/15000 ≤ ω_g^{coord}(CW_q) ≤ f(q) = log_q (4(q+2)³/27).
```

The lower bound is AVW Theorem 7.1 (`avw_theorem_seven_one` with the certified rational bound
`two_add_le_avwTheoremSevenOneConstant`), which holds for *every* member of the family and needs no
hypothesis; the upper bound is milestone M8 for the classical member `σ = id`, the one whose border
rank is `q + 2`.

The point of the sandwich is that Theorem 7.1 is not vacuous: the quantity it bounds from below is
a genuine, attained exponent, equal to the exponent of the classical Coppersmith--Winograd analysis
up to the gap between `f(q)` and `2 + 1/15000`. -/
theorem avw_galactic_exponent_gcwTable_sandwich (K : Type u) [Field K] (q : ℕ) (hq : 2 ≤ q) :
    2 + (1 : ℝ) / 15000 ≤
        coordinateGalacticExponent K (gcwTable K (Fin q) (Equiv.refl (Fin q))) ∧
      coordinateGalacticExponent K (gcwTable K (Fin q) (Equiv.refl (Fin q))) ≤ avwF q := by
  refine ⟨le_trans two_add_le_avwTheoremSevenOneConstant
    (avw_theorem_seven_one K q (Equiv.refl (Fin q))), ?_⟩
  have h := coordinateGalacticExponent_gcwTable_refl_le_avwF K (Fin q) (by simpa using hq)
  rwa [Fintype.card_fin] at h

end Sandwich

/-! ## The numeric instance `q = 6`

`f(6) = log (2048/27) / log 6 = 2.4158253…`.  Both halves of the enclosure are exact rational
arithmetic on the certified atanh bounds of `Analysis/LogConstants.lean`: `log (2048/27)` is
`11 log 2 − 3 log 3` and `log 6` is `log 2 + log 3`, so the four enclosures
`log 2 ∈ [0.693147, 0.693148]` and `log 3 ∈ [1.098611, 1.098614]` bound the quotient.  No floating
point is used anywhere.
-/

section Numeric

open AlgebraicComplexity.Analysis

/-- `f(6) ≤ 2.416`, certified from the `log 2` and `log 3` enclosures of
`Analysis/LogConstants.lean`.  The true value is `2.4159393…`, and the four enclosures pin the
quotient to `[2.4159319, 2.4159485]`. -/
theorem avwF_six_le : avwF 6 ≤ 2416 / 1000 := by
  have hcast : (((6 : ℕ) + 2 : ℕ) : ℝ) = 8 := by norm_num
  have hcast6 : ((6 : ℕ) : ℝ) = 6 := by norm_num
  have hden : (0 : ℝ) < Real.log ((6 : ℕ) : ℝ) := by
    rw [hcast6]; exact Real.log_pos (by norm_num)
  rw [avwF, div_le_iff₀ hden, hcast, hcast6,
    show (4 / 27 : ℝ) * (8 : ℝ) ^ 3 = 2 ^ 11 / 3 ^ 3 by norm_num,
    Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  push_cast
  linarith [log_two_ge, log_two_le, log_three_ge, log_three_le]

/-- `f(6) ≥ 2.4159`, the companion enclosure. -/
theorem avwF_six_ge : (24159 : ℝ) / 10000 ≤ avwF 6 := by
  have hcast : (((6 : ℕ) + 2 : ℕ) : ℝ) = 8 := by norm_num
  have hcast6 : ((6 : ℕ) : ℝ) = 6 := by norm_num
  have hden : (0 : ℝ) < Real.log ((6 : ℕ) : ℝ) := by
    rw [hcast6]; exact Real.log_pos (by norm_num)
  rw [avwF, le_div_iff₀ hden, hcast, hcast6,
    show (4 / 27 : ℝ) * (8 : ℝ) ^ 3 = 2 ^ 11 / 3 ^ 3 by norm_num,
    Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  push_cast
  linarith [log_two_ge, log_two_le, log_three_ge, log_three_le]

/-- **The Definition 4.1 loop at the AVW parameter `q = 6`**:

```text
2 + 1/15000 ≤ ω_g^{coord}(CW_6) ≤ 2.416.
```

The lower bound is AVW Theorem 7.1; the upper bound is milestone M8 together with the certified
enclosure `avwF_six_le`.  (The classical Coppersmith--Winograd bound at `q = 6` is `2.41` for the
three-constituent analysis measured by `f`; the sharper `2.3872` of AVW's own headline comes from
the *six*-constituent first-power analysis, which is a different, smaller certificate value and is
not what `f` records.) -/
theorem avw_galactic_exponent_gcwTable_fin_six (K : Type u) [Field K] :
    2 + (1 : ℝ) / 15000 ≤
        coordinateGalacticExponent K (gcwTable K (Fin 6) (Equiv.refl (Fin 6))) ∧
      coordinateGalacticExponent K (gcwTable K (Fin 6) (Equiv.refl (Fin 6))) ≤ 2416 / 1000 := by
  obtain ⟨h1, h2⟩ := avw_galactic_exponent_gcwTable_sandwich K 6 (by norm_num)
  exact ⟨h1, h2.trans avwF_six_le⟩

end Numeric

end AlgebraicComplexity.Examples
