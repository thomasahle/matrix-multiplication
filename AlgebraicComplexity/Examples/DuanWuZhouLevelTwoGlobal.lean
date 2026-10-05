/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGlobalArithmetic
import AlgebraicComplexity.MatrixMultiplication.AsymmetricGlobalValue

/-!
# The Duan--Wu--Zhou level-two endpoint `omega < 2.374631`

[DuanWuZhou2022] `global_value.tex` section 6.3 is the fully published second-power record of
*Faster Matrix Multiplication via Asymmetric Hashing*.  This module assembles its numbers: the
`AsymmetricGlobal.GlobalRateData` instance of the section 6.3 parameter table, the exact rational
endpoint comparison against the border-rank budget `64 = (q + 2) ^ 2`, and the resulting bound on
`omega`.

## The routing

`GlobalRateData` has six real fields.  The instance below makes four of them *rationals* --- the
values certified in `Examples/DuanWuZhouLevelTwoGlobalArithmetic.lean` --- and declares the fifth
as `hashLossRate := ambientRate * K` with `K = 1 + 10 ^ (-10)` rational.  The ambient rate
`2 ^ H(alpha)` is then left completely free: it cancels out of the hashing branch,

```text
ambientRate * xRate / hashLossRate = ambientRate * xRate / (ambientRate * K) = xRate / K,
```

so `dwz63RateData` is a *family* of rate data indexed by the ambient rate, all members of which
have the same `globalRate`.  No enclosure of `2 ^ H(alpha)` appears anywhere in the development;
the price is the single Gibbs dual certificate `dwz63_gibbsDeficit_le_log_hashLossMultiplier`,
which is what makes the declared `hashLossRate` an upper bound for
`max_{alpha' in D_alpha} 2 ^ H(alpha')` --- the mandatory field that section 6.3's table omits
(watchlist item 2).

## What is proved, and what is assumed

Proved here, unconditionally:

* `dwz63RateData_globalRate` --- the `ambientRate` cancellation, so the global rate is the exact
  rational `min (xRate / K) (zRate / compatRate) * valRate`;
* `dwz63_rankBudget_lt_globalRate_pow` --- the endpoint
  `Rtilde(sym_6(CW_6 tensor CW_6)) <= 64 ^ 6 = 68719476736 < globalRate ^ 6`;
* `omega_lt_2374631_of_dwzLevelTwoAssembledStage` --- the bound on `omega`, conditional on one
  named hypothesis;
* `dwzLevelTwoAssembledStage_of_repairedStage` --- that hypothesis is exactly what
  `AsymmetricGlobal.omega_lt_three_mul_of_repairedStage` (M-DWZ6) consumes, so the interface is
  the committed one and not a new invention.

**Assumed, in exactly one place:** `DwzLevelTwoAssembledStage`.  It says that the six-symmetrized
source has asymptotic rank at most `64 ^ 6`, and that some power of it carries a `tau`-weight at
least `globalRate ^ (6N)`.  Supplying it is the *count side* of section 6.3 --- the six
method-of-types estimates for `N_alpha`, `N_X`, `N_Z`, `N_triple`, `|compatibleSet|` and
`|typicalSet|`, Bertrand's postulate for a prime modulus in `[M_0, 2 M_0]`, and the
`Analysis/Subexponential.lean` absorption of the polynomial and Behrend losses.  That work is not
in this module and this module does not pretend otherwise: nothing here may be cited as an
unconditional bound on `omega`.

The count side is *reachable*, and in particular is not blocked on the still-open
`p_comp = alphabar_p ^ (n + o(n))` of M-DWZ5: `Analysis/CompatibilityRate.lean`'s
`eight_mul_card_matchableCompatible_le` states the modulus condition in exact finite
cardinalities, so only the loss-free upper half `p_comp <= poly(n) * alphabar_p ^ n` is on the
critical path.  See `better_bound/dwz_endpoint_prep/PREP.md` section 4 for the full chain.

## Position in the library

Layer 4 (a client).  It imports the section 6.3 arithmetic and the M-DWZ6 asymmetric global value
theorem, and nothing else.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via
Asymmetric Hashing*, arXiv:2210.10173, sections 6.2--6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity AsymmetricGlobal Tensor

universe u v

noncomputable section

/-! ## The rate data of section 6.3 -/

/-- **The section 6.3 rate data, in the routing that cancels the ambient rate.**

`ambientRate` is an arbitrary positive real: it is `2 ^ H(alpha) = 7.4877776969...`, but no
property of that number is ever used, because `hashLossRate` is declared as `ambientRate * K` and
the two occurrences cancel (`dwz63RateData_globalRate`).  The remaining four fields are the
rationals certified in `DuanWuZhouLevelTwoGlobalArithmetic.lean`, each in the direction its
position in `M_0 = 8 max (N_triple / N_X, N_alpha p_comp / N_Z)` demands. -/
def dwz63RateData (ambient : ℝ) (hambient : 0 < ambient) : GlobalRateData where
  ambientRate := ambient
  hashLossRate := ambient * dwz63HashLossMultiplier
  xRate := dwz63XRate
  zRate := dwz63ZRate
  compatRate := dwz63CompatRate
  valRate := dwz63ValRate
  ambientRate_pos := hambient
  hashLossRate_pos := mul_pos hambient dwz63HashLossMultiplier_pos
  xRate_pos := dwz63XRate_pos
  zRate_pos := dwz63ZRate_pos
  compatRate_pos := dwz63CompatRate_pos
  valRate_pos := dwz63ValRate_pos

/-- **The ambient rate cancels.**  `[DuanWuZhou2022]`'s

`min (alphabar_nu alphabar_X / max_{alpha'} alphabar_nu', alphabar_Z / alphabar_p) alphabar_val`

is, at this data, the exact rational `min (xRate / K) (zRate / compatRate) * valRate`.  This is
what removes twelve upper-direction enclosures that a "six rational fields" routing would need:
the only surviving obligation attached to the hash loss is the Gibbs dual certificate. -/
theorem dwz63RateData_globalRate (ambient : ℝ) (hambient : 0 < ambient) :
    (dwz63RateData ambient hambient).globalRate =
      min (dwz63XRate / dwz63HashLossMultiplier) (dwz63ZRate / dwz63CompatRate) *
        dwz63ValRate := by
  have hbranch : ambient * dwz63XRate / (ambient * dwz63HashLossMultiplier)
      = dwz63XRate / dwz63HashLossMultiplier := by
    rw [mul_div_mul_left _ _ hambient.ne']
  rw [GlobalRateData.globalRate_eq_min_mul]
  show min (ambient * dwz63XRate / (ambient * dwz63HashLossMultiplier))
      (dwz63ZRate / dwz63CompatRate) * dwz63ValRate = _
  rw [hbranch]

/-- **The endpoint.**  The square border-rank budget is `Rtilde(CW_6 tensor CW_6) = (q + 2) ^ 2
= 64`, so the six-symmetrized source is compared against `64 ^ 6 = 68719476736`, and the section
6.3 global rate clears it.

The margin is relative `1.7246 * 10 ^ (-7)`, which is `98.8 %` of the true margin of the
published parameters --- the shortfall is the `10 ^ (-9)` relative back-off the four rate
rationals carry so that the ten-digit `log 2` constants suffice. -/
theorem dwz63_rankBudget_lt_globalRate_pow (ambient : ℝ) (hambient : 0 < ambient) :
    (68719476736 : ℝ) < (dwz63RateData ambient hambient).globalRate ^ 6 := by
  rw [dwz63RateData_globalRate]
  have h64 : (68719476736 : ℝ) = 64 ^ 6 := by norm_num
  rw [h64]
  exact pow_lt_pow_left₀ dwz63_endpoint_gt_64 (by norm_num) (by norm_num)

/-! ## The composition -/

section Composition

variable {F : Type u} [Field F] {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module F (V c)]

/-- **The one composition input this module does not supply.**

An *assembled stage* for `T` at the rate data `d` consists of

* a bound on the asymptotic rank of the six-symmetrized source by `64 ^ 6` --- for
  `T = CW_6 tensor CW_6` this is `Rtilde(CW_q) <= q + 2` together with submultiplicativity of the
  asymptotic rank under the six external products of `sym_6`; and
* one power `sym_6(T) ^ (tensor N)` carrying a `tau`-weight at least `d.globalRate ^ (6N)`.

The second component is `[DuanWuZhou2022]` section 6's counting argument, run through the
committed machinery: marked two-leg hashing retains `N_alpha / (4M)` good triples, the
compatibility cleanup and the Hole Lemma batch them into `>= N_alpha / (64 s M_0)` intact copies
of the restricted-splitting power, and the six method-of-types estimates identify that count with
`copyRate ^ n` up to a subexponential factor.  `dwzLevelTwoAssembledStage_of_repairedStage` below
shows that the hypothesis is *exactly* what M-DWZ6's
`AsymmetricGlobal.omega_lt_three_mul_of_repairedStage` consumes, so nothing has been weakened or
re-invented in stating it this way.

It is stated as an assumption, and not proved, because the counting half of section 6.3 is not in
this repository yet.  No theorem in this module may be read as an unconditional bound on `omega`
until it is. -/
def DwzLevelTwoAssembledStage (T : Tensor3 F V) (d : GlobalRateData) : Prop :=
  Tensor.asymptoticRank (symSix F T) ≤ 68719476736 ∧
    ∃ (N : ℕ) (value : ℝ), 0 < N ∧ 0 < value ∧
      HasTauWeight F (Tensor.power (symSix F T) N) dwz63Tau value ∧
      d.globalRate ^ (6 * N) ≤ value

/-- **The named hypothesis is the committed M-DWZ6 interface.**  Every premise below is a premise
of `AsymmetricGlobal.omega_lt_three_mul_of_repairedStage`, with the rank budget specialized to
`64 ^ 6` and the exponent to `dwz63Tau`; nothing else is required.  So a future count-side
development has to reach exactly the same place the asymmetric global value theorem already
expects, and no interface has been invented here. -/
theorem dwzLevelTwoAssembledStage_of_repairedStage
    (d : GlobalRateData) {T : Tensor3 F V} {W : Leg → Type v}
    [∀ c, AddCommMonoid (W c)] [∀ c, Module F (W c)]
    {leaf : Tensor3 F W} {leafValue : ℝ}
    (hrank : Tensor.asymptoticRank (symSix F T) ≤ 68719476736)
    (N : ℕ) (hN : 0 < N) (hleafValue : 0 < leafValue)
    {β : Type v} [Fintype β] [DecidableEq β]
    (hstage : Restricts (Tensor.power (symSix F T) N)
      (Tensor.indexedDirectSum (V := fun _ : β ↦ W) fun _ ↦ leaf))
    (hleaf : HasTauWeight F leaf dwz63Tau leafValue)
    (hcount : d.copyRate ^ (6 * N) ≤ (Fintype.card β : ℝ))
    (hvalue : d.valRate ^ (6 * N) ≤ leafValue)
    (hcards : 0 < Fintype.card β) :
    DwzLevelTwoAssembledStage T d := by
  have hcardPos : (0 : ℝ) < (Fintype.card β : ℝ) := by exact_mod_cast hcards
  refine ⟨hrank, N, (Fintype.card β : ℝ) * leafValue, hN, mul_pos hcardPos hleafValue,
    hasTauWeight_of_repairedStage N hstage hleaf, ?_⟩
  rw [GlobalRateData.globalRate, mul_pow]
  exact mul_le_mul hcount hvalue (pow_pos d.valRate_pos _).le (Nat.cast_nonneg _)

/-- **`[DuanWuZhou2022]`'s level-two endpoint, `omega < 2.374631`, over every field** --- modulo
the one named hypothesis.

`tau = 2374631 / 3000000`, so the conclusion is `omega < 3 tau = 2.374631`.  Everything numerical
is discharged: the forty-six directed logarithm enclosures of section 6.3's parameter table, the
Gibbs dual bound on the hash loss, the `ambientRate` cancellation, and the exact rational
comparison `min (xRate / K) (zRate / compatRate) * valRate > 64` against the square border-rank
budget.  What remains is `DwzLevelTwoAssembledStage`, the counting half of section 6. -/
theorem omega_lt_2374631_of_dwzLevelTwoAssembledStage
    {T : Tensor3 F V} {ambient : ℝ} (hambient : 0 < ambient)
    (hstage : DwzLevelTwoAssembledStage T (dwz63RateData ambient hambient)) :
    omega F < (2374631 / 1000000 : ℝ) := by
  obtain ⟨hrank, N, value, hN, hvaluePos, hweight, hgap⟩ := hstage
  have hglobalPos := (dwz63RateData ambient hambient).globalRate_pos
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hroot : ((dwz63RateData ambient hambient).globalRate ^ (6 * N)) ^ ((N : ℝ)⁻¹)
      = (dwz63RateData ambient hambient).globalRate ^ 6 := by
    rw [← Real.rpow_natCast _ (6 * N), ← Real.rpow_mul hglobalPos.le, ← Real.rpow_natCast _ 6]
    congr 1
    push_cast
    field_simp
  have hkey : omega F < 3 * dwz63Tau := by
    refine omega_lt_three_mul_of_hasTauWeight hN hvaluePos hrank hweight ?_
    calc (68719476736 : ℝ)
        < (dwz63RateData ambient hambient).globalRate ^ 6 :=
          dwz63_rankBudget_lt_globalRate_pow ambient hambient
      _ = ((dwz63RateData ambient hambient).globalRate ^ (6 * N)) ^ ((N : ℝ)⁻¹) := hroot.symm
      _ ≤ value ^ ((N : ℝ)⁻¹) :=
          Real.rpow_le_rpow (pow_nonneg hglobalPos.le _) hgap (by positivity)
  rwa [dwz63_three_mul_tau] at hkey

end Composition

end

end AlgebraicComplexity.Examples
