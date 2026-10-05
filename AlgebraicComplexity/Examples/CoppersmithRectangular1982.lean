/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.LogConstants
import AlgebraicComplexity.Examples.CoppersmithRectangular1982Certificate
import AlgebraicComplexity.MatrixMultiplication.RectangularCertificate

/-!
# Coppersmith 1982: the first positive rectangular exponent `α > 0`

This module proves the theorem of D. Coppersmith, *Rapid multiplication of rectangular matrices*,
SIAM Journal on Computing **11**(3), 467–471 (1982), p. 467: an `N × N` matrix can be multiplied
by an `N × N^α` matrix in `O(N^{2+o(1)})` arithmetic operations for

`α = 2 log 2 / (5 log 5) = 0.1722704…`,

so the dual matrix-multiplication exponent satisfies `α(F) ≥ 2 log 2 / (5 log 5) > 0.17`.  Before
this, `AlgebraicComplexity/MatrixMultiplication/RectangularInterpolation.lean` was vacuously
consistent with `α = 0`.

## The construction

`AlgebraicComplexity/Examples/CoppersmithRectangular1982Certificate.lean` assembles the family of
exact rank certificates

`R(⟨A_t, 2^{2t}, A_t⟩) ≤ 5^{10t} (20t + 1)^3`,   `A_t = 2^{4t} · |Y_t|`,

where `A_t` is the *area* of Schönhage's second design at the multiplicity type `(t, 2t, 2t)`.
The two facts that drive the exponent are proved there:

* `crArea_le` : `A_t ≤ 5^{5t}` — exactly, with no loss, because the area is one term of the
  multinomial expansion of `5^{5t}`;
* `crArea_ge` : `5^{5t} ≤ loss t · A_t` with `loss` subexponential.

Coppersmith's `κ` is defined by `(5^{5t})^κ = 2^{2t}`, i.e. `κ = 2 log 2 / (5 log 5)`
(`cr_five_rpow_kappa`).  The upper bound therefore gives the middle-dimension hypothesis
`A_t^κ ≤ 2^{2t}` of the rectangular packager *without rounding*, and the lower bound gives the
covering hypothesis: choosing the least `t` with `n ≤ A_t` forces `A_{t-1} < n`, hence
`5^{5t} ≤ 5^5 · loss(t-1) · n`, and the certificate size `5^{10t}(20t+1)^3` is at most
`5^{10} · loss(t-1)^2 · (20t+1)^3 · n^2`.  The polynomial-in-`t` prefactor is absorbed into `n^ε`
because `n` itself grows geometrically in `t`; that is
`Growth.Subexponential` applied at the base `5^{5ε} > 1`.

## Principal results

* `coppersmith1982_rectangularOmega_eq_two` : `ω(2 log 2 / (5 log 5)) = 2` over every infinite
  field — the upper bound is Coppersmith's construction, the lower bound the outer flattening;
* `coppersmith1982_rectangularAlpha_ge` : `2 log 2 / (5 log 5) ≤ α(F)`;
* `coppersmith1982_alpha_gt_seventeen_hundredths` : `17/100 < α(F)`, certified by the exact
  integer comparison `5 ^ 85 < 2 ^ 200` (`crKappa_gt_seventeen_hundredths`).

## An abstraction with no prospective client (2026-08-28)

`cr_rectangularOmega_le_two_add` contains, inline, a reusable-looking covering argument: a family
of rank certificates whose sizes are `Θ(G_t^2)` for a geometric `G_t` and whose covered scales
satisfy `G_t / loss t ≤ A_t ≤ G_t` gives `ω(κ) ≤ 2 + ε` for every `ε > 0`.  An earlier note here
proposed promoting it beside `rectangularMatrixExponentLE_of_certificates` in
`MatrixMultiplication/RectangularCertificate.lean` once a second client fixed the hypothesis
shape.  The second client has since arrived and taken a different route: the Huang--Pan tower
(`Examples/CoppersmithWinogradEasyRectangularRate.lean` and its full-CW twin) goes through
`rpow_rectangularOmega_le_of_indexedDirectSum`
(`MatrixMultiplication/RectangularAsymptoticSum.lean`), which reads a single compressed
certificate through `rpow_rectangularOmega_le_of_borderRankLE`, and never covers scales by a
geometric certificate family at all.  The promotion therefore has no prospective client and is
*not* pending; the argument stays inline until some future client actually needs it.

## References

* D. Coppersmith, *Rapid multiplication of rectangular matrices*, SIAM J. Comput. **11**(3),
  467–471 (1982).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor WordType

universe u

/-! ## Coppersmith's exponent -/

/-- **Coppersmith's rectangular exponent** `κ = 2 log 2 / (5 log 5) = 0.1722704…`, defined by
`(5^{5t})^κ = 2^{2t}`: the area of the construction is `5^{5t}` up to a subexponential factor
and its small dimension is `2^{2t}`. -/
noncomputable def crKappa : ℝ := 2 * Real.log 2 / (5 * Real.log 5)

theorem crKappa_pos : 0 < crKappa := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  unfold crKappa
  positivity

theorem crKappa_nonneg : 0 ≤ crKappa := crKappa_pos.le

/-- **The defining equation of `κ`**: `(5^{5t})^κ = 2^{2t}` exactly, for every `t`. -/
theorem cr_five_rpow_kappa (t : ℕ) : ((5 : ℝ) ^ (5 * t)) ^ crKappa = (2 : ℝ) ^ (2 * t) := by
  have h5 : (0 : ℝ) < 5 := by norm_num
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hne : (5 : ℝ) * Real.log 5 ≠ 0 := ne_of_gt (mul_pos h5 hlog5)
  have hk : 5 * Real.log 5 * crKappa = 2 * Real.log 2 := by
    show 5 * Real.log 5 * (2 * Real.log 2 / (5 * Real.log 5)) = 2 * Real.log 2
    field_simp
  rw [← Real.rpow_natCast (5 : ℝ) (5 * t), ← Real.rpow_natCast (2 : ℝ) (2 * t),
    ← Real.rpow_mul h5.le, Real.rpow_def_of_pos h5, Real.rpow_def_of_pos h2]
  congr 1
  push_cast
  linear_combination (t : ℝ) * hk

/-- **The middle-dimension hypothesis of the packager, exactly**: `A_t^κ ≤ 2^{2t}`.

No rounding is lost: `A_t ≤ 5^{5t}` is an exact inequality between naturals and
`(5^{5t})^κ = 2^{2t}` is the definition of `κ`. -/
theorem cr_area_rpow_le (t : ℕ) :
    ((crArea t : ℕ) : ℝ) ^ crKappa ≤ ((2 ^ (2 * t) : ℕ) : ℝ) := by
  have hR : ((crArea t : ℕ) : ℝ) ≤ (5 : ℝ) ^ (5 * t) := by
    have h := crArea_le t
    exact_mod_cast h
  calc ((crArea t : ℕ) : ℝ) ^ crKappa ≤ ((5 : ℝ) ^ (5 * t)) ^ crKappa :=
        Real.rpow_le_rpow (by positivity) hR crKappa_nonneg
    _ = (2 : ℝ) ^ (2 * t) := cr_five_rpow_kappa t
    _ = ((2 ^ (2 * t) : ℕ) : ℝ) := by push_cast; ring

/-! ## The subexponential covering loss -/

/-- The method-of-types loss cubed, times the polynomial degree factor: the whole prefactor that
the covering argument has to absorb into `n^ε`. -/
noncomputable def crCoverLoss (t : ℕ) : ℝ := crLoss t ^ 3 * (((t + 1 : ℕ)) : ℝ) ^ 3

theorem crCoverLoss_subexponential : Growth.Subexponential crCoverLoss := by
  have h3 : Growth.Subexponential (fun t ↦ crLoss t ^ 3) := by
    have heq : (fun t ↦ crLoss t ^ 3) = fun t ↦ crLoss t * crLoss t * crLoss t := by
      funext t; ring
    rw [heq]
    exact (crLoss_subexponential.mul crLoss_subexponential).mul crLoss_subexponential
  exact h3.mul (Growth.Subexponential.natCast_succ_pow 3)

/-! ## The exponent bound -/

/-- **Coppersmith's bound, in `ε`-form**: `ω(κ) ≤ 2 + ε` for every `0 < ε ≤ 1`, over every
infinite field.

Given a scale `n ≥ 1`, take the least `t` with `n ≤ A_t`.  Minimality gives `A_{t-1} < n`, so the
method-of-types lower bound `5^{5(t-1)} ≤ loss(t-1) · A_{t-1}` yields
`5^{5t} ≤ 5^5 · loss(t-1) · n`, hence the certificate size satisfies

`5^{10t} (20t+1)^3 ≤ 5^{10} · loss(t-1)^2 · (20t+1)^3 · n^2`.

The prefactor is subexponential in `t` while `n ≥ 5^{5(t-1)} / loss(t-1)` grows geometrically, so
the prefactor is at most `D · n^ε`; this is exactly `Growth.Subexponential` evaluated at the base
`5^{5ε} > 1`. -/
theorem cr_rectangularOmega_le_two_add (F : Type u) [Field F] [Infinite F]
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    rectangularOmega F crKappa ≤ 2 + ε := by
  classical
  set δ : ℝ := (5 : ℝ) ^ (5 * ε) with hδdef
  have hδ : 1 < δ := by
    have h : (5 : ℝ) ^ (0 : ℝ) < (5 : ℝ) ^ (5 * ε) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    simpa [hδdef] using h
  obtain ⟨Dsub, hDsub, hDsubLe⟩ := crCoverLoss_subexponential.2 δ hδ
  set D : ℝ := max ((5 : ℝ) ^ (10 : ℕ) * 9261 * Dsub) 1 with hDdef
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hDge : (5 : ℝ) ^ (10 : ℕ) * 9261 * Dsub ≤ D := le_max_left _ _
  have hDone : (1 : ℝ) ≤ D := le_max_right _ _
  refine rectangularOmega_le_of_certificates F (A := crArea)
    (C := fun t ↦ 2 ^ (2 * t)) (r := fun t ↦ 5 ^ (10 * t) * (20 * t + 1) ^ 3)
    crKappa_nonneg (by linarith) hD (cr_rankLE F) cr_area_rpow_le ?_
  intro n hn
  obtain ⟨t, htspec, htmin⟩ :
      ∃ t, n ≤ crArea t ∧ ∀ m, m < t → ¬ n ≤ crArea m := by
    have hex : ∃ t, n ≤ crArea t := ⟨n, le_crArea n⟩
    exact ⟨Nat.find hex, Nat.find_spec hex, fun m hm ↦ Nat.find_min hex hm⟩
  refine ⟨t, htspec, ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hnpow : (1 : ℝ) ≤ (n : ℝ) ^ (2 + ε) := by
    have h := Real.rpow_le_rpow zero_le_one hn1 (by linarith : (0 : ℝ) ≤ 2 + ε)
    rwa [Real.one_rpow] at h
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · -- The degenerate scale `n = 1`, covered by the trivial certificate.
    subst ht0
    have hone : ((5 ^ (10 * 0) * (20 * 0 + 1) ^ 3 : ℕ) : ℝ) = 1 := by norm_num
    rw [hone]
    nlinarith [hnpow, hDone]
  · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    set L : ℝ := crLoss t' with hLdef
    set P : ℝ := (((20 * (t' + 1) + 1 : ℕ)) : ℝ) with hPdef
    set Q : ℝ := (((t' + 1 : ℕ)) : ℝ) with hQdef
    have hLpos : 0 < L := crLoss_pos t'
    have hLone : (1 : ℝ) ≤ L := one_le_crLoss t'
    have hnε : (0 : ℝ) ≤ (n : ℝ) ^ ε := Real.rpow_nonneg hnpos.le ε
    -- minimality of `t`
    have hminlt : (crArea t' : ℝ) < (n : ℝ) := by
      have h : crArea t' < n := not_le.mp (htmin t' (by omega))
      exact_mod_cast h
    -- the geometric estimate
    have hstep1 : (5 : ℝ) ^ (5 * t') ≤ (n : ℝ) * L := by
      calc (5 : ℝ) ^ (5 * t') ≤ L * (crArea t' : ℝ) := crArea_ge t'
        _ ≤ L * (n : ℝ) := mul_le_mul_of_nonneg_left hminlt.le hLpos.le
        _ = (n : ℝ) * L := mul_comm _ _
    have hleft : ((5 : ℝ) ^ (5 * t')) ^ ε = δ ^ t' := by
      rw [hδdef, ← Real.rpow_natCast (5 : ℝ) (5 * t'),
        ← Real.rpow_natCast ((5 : ℝ) ^ (5 * ε)) t',
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5)]
      congr 1
      push_cast
      ring
    have hstep2 : δ ^ t' ≤ (n : ℝ) ^ ε * L := by
      have hb : ((5 : ℝ) ^ (5 * t')) ^ ε ≤ ((n : ℝ) * L) ^ ε :=
        Real.rpow_le_rpow (by positivity) hstep1 hε.le
      rw [hleft, Real.mul_rpow hnpos.le hLpos.le] at hb
      refine hb.trans ?_
      have hLe : L ^ ε ≤ L := by
        calc L ^ ε ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hLone hε1
          _ = L := Real.rpow_one _
      exact mul_le_mul_of_nonneg_left hLe hnε
    -- absorb the polynomial prefactor into `n ^ ε`
    have hPle : P ≤ 21 * Q := by
      rw [hPdef, hQdef]; push_cast; linarith
    have hPnn : (0 : ℝ) ≤ P := by rw [hPdef]; positivity
    have hP3 : P ^ 3 ≤ 9261 * Q ^ 3 := by
      have hQnn : (0 : ℝ) ≤ Q := by rw [hQdef]; positivity
      nlinarith [hPnn, hPle, hQnn, sq_nonneg (P - 21 * Q), sq_nonneg (P + 21 * Q)]
    have hcover : L ^ 3 * Q ^ 3 ≤ Dsub * δ ^ t' := hDsubLe t'
    have hcoefnn : (0 : ℝ) ≤ (5 : ℝ) ^ (10 : ℕ) * 9261 * Dsub :=
      mul_nonneg (by positivity) hDsub.le
    have hprodnn : (0 : ℝ) ≤ (n : ℝ) ^ ε * L := mul_nonneg hnε hLpos.le
    have habs : L ^ 2 * (5 : ℝ) ^ (10 : ℕ) * P ^ 3 ≤ D * (n : ℝ) ^ ε := by
      refine le_of_mul_le_mul_right ?_ hLpos
      calc L ^ 2 * (5 : ℝ) ^ (10 : ℕ) * P ^ 3 * L
          = (5 : ℝ) ^ (10 : ℕ) * (L ^ 3 * P ^ 3) := by ring
        _ ≤ (5 : ℝ) ^ (10 : ℕ) * (L ^ 3 * (9261 * Q ^ 3)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hP3 (by positivity)) (by positivity)
        _ = (5 : ℝ) ^ (10 : ℕ) * 9261 * (L ^ 3 * Q ^ 3) := by ring
        _ ≤ (5 : ℝ) ^ (10 : ℕ) * 9261 * (Dsub * δ ^ t') :=
            mul_le_mul_of_nonneg_left hcover (by positivity)
        _ = ((5 : ℝ) ^ (10 : ℕ) * 9261 * Dsub) * δ ^ t' := by ring
        _ ≤ ((5 : ℝ) ^ (10 : ℕ) * 9261 * Dsub) * ((n : ℝ) ^ ε * L) :=
            mul_le_mul_of_nonneg_left hstep2 hcoefnn
        _ ≤ D * ((n : ℝ) ^ ε * L) := mul_le_mul_of_nonneg_right hDge hprodnn
        _ = D * (n : ℝ) ^ ε * L := by ring
    -- assemble
    have hsplit : (n : ℝ) ^ (2 + ε) = (n : ℝ) ^ (2 : ℕ) * (n : ℝ) ^ ε := by
      rw [Real.rpow_add hnpos]
      congr 1
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hcast : ((5 ^ (10 * (t' + 1)) * (20 * (t' + 1) + 1) ^ 3 : ℕ) : ℝ)
        = ((5 : ℝ) ^ (5 * t')) ^ 2 * (5 : ℝ) ^ (10 : ℕ) * P ^ 3 := by
      rw [hPdef]; push_cast; ring
    have hsq : ((5 : ℝ) ^ (5 * t')) ^ 2 ≤ ((n : ℝ) * L) ^ 2 := by
      have h0 : (0 : ℝ) ≤ (5 : ℝ) ^ (5 * t') := by positivity
      nlinarith [hstep1, h0]
    rw [hcast, hsplit]
    calc ((5 : ℝ) ^ (5 * t')) ^ 2 * (5 : ℝ) ^ (10 : ℕ) * P ^ 3
        ≤ ((n : ℝ) * L) ^ 2 * (5 : ℝ) ^ (10 : ℕ) * P ^ 3 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hsq (by positivity)) (by positivity)
      _ = (n : ℝ) ^ (2 : ℕ) * (L ^ 2 * (5 : ℝ) ^ (10 : ℕ) * P ^ 3) := by ring
      _ ≤ (n : ℝ) ^ (2 : ℕ) * (D * (n : ℝ) ^ ε) :=
          mul_le_mul_of_nonneg_left habs (by positivity)
      _ = D * ((n : ℝ) ^ (2 : ℕ) * (n : ℝ) ^ ε) := by ring

/-! ## The theorems of the paper -/

/-- **Coppersmith 1982, p. 467**: over every infinite field the rectangular exponent is optimal at
`κ = 2 log 2 / (5 log 5)`, that is `ω(1, κ, 1) = 2`.

The upper bound is `cr_rectangularOmega_le_two_add` at every `ε > 0`; the lower bound is the
outer flattening `two_le_rectangularOmega`. -/
theorem coppersmith1982_rectangularOmega_eq_two (F : Type u) [Field F] [Infinite F] :
    rectangularOmega F (2 * Real.log 2 / (5 * Real.log 5)) = 2 := by
  have hle : rectangularOmega F crKappa ≤ 2 := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    rcases le_total ε 1 with h | h
    · exact cr_rectangularOmega_le_two_add F hε h
    · exact (cr_rectangularOmega_le_two_add F zero_lt_one le_rfl).trans (by linarith)
  exact le_antisymm hle (two_le_rectangularOmega F crKappa)

/-- **Coppersmith 1982, p. 467, the first `α > 0`**: the dual matrix-multiplication exponent of
every infinite field is at least `2 log 2 / (5 log 5) = 0.1722704…`. -/
theorem coppersmith1982_rectangularAlpha_ge (F : Type u) [Field F] [Infinite F] :
    2 * Real.log 2 / (5 * Real.log 5) ≤ rectangularAlpha F :=
  le_csSup (bddAbove_setOf_rectangularOmega_eq_two F)
    ⟨crKappa_nonneg, coppersmith1982_rectangularOmega_eq_two F⟩

/-- **The numerical certificate** for `κ > 0.17`: `17/100 < 2 log 2 / (5 log 5)` is equivalent to
`85 log 5 < 200 log 2`, that is to the exact integer comparison `5 ^ 85 < 2 ^ 200`, which
`norm_num` checks through `Analysis.mul_log_lt_mul_log_of_pow_lt`.  No floating-point evaluation
of a logarithm is involved. -/
theorem crKappa_gt_seventeen_hundredths : (17 : ℝ) / 100 < crKappa := by
  have hpowNat : (5 : ℕ) ^ 85 < 2 ^ 200 := by norm_num
  have hpow : ((5 : ℝ) ^ (85 : ℕ)) < ((2 : ℝ) ^ (200 : ℕ)) := by exact_mod_cast hpowNat
  have hlog := Analysis.mul_log_lt_mul_log_of_pow_lt (by norm_num : (0 : ℝ) < 5) hpow
  norm_num at hlog
  have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  rw [crKappa, lt_div_iff₀ (by positivity)]
  linarith

/-- **Coppersmith 1982**: `α(F) > 0.17` over every infinite field. -/
theorem coppersmith1982_alpha_gt_seventeen_hundredths (F : Type u) [Field F] [Infinite F] :
    (17 : ℝ) / 100 < rectangularAlpha F :=
  lt_of_lt_of_le crKappa_gt_seventeen_hundredths (coppersmith1982_rectangularAlpha_ge F)

end AlgebraicComplexity.Examples
