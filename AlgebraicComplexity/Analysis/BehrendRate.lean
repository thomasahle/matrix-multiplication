/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.Subexponential
import Mathlib.Combinatorics.Additive.AP.Three.Behrend

/-!
# Behrend rate arguments

A progression-free hashing extraction produces, for every power `k`, a modulus `M` and a number
`copies` of extracted matrix-multiplication tensors satisfying two inequalities:

* a *copies bound* `A ^ k * rothNumberNat (M / 2) ≤ poly k * M ^ 2 * copies`, coming from the
  hashing count and the fact that the progression-free set inside `ZMod M` has
  `rothNumberNat (M / 2)` elements; and
* a *value bound* `copies * V ^ k ≤ ρ ^ k`, coming from Schönhage's asymptotic sum inequality or
  from an asymptotic-independence certificate.

Behrend's lower bound `N * exp (-4 * √(log N)) ≤ rothNumberNat N` turns the first inequality into
one where the progression-free set has been replaced by an explicit subexponential loss; the
modulus is then cancelled against its own growth bound `M ≤ E * D ^ k` and the limit `k → ∞`
removes every loss, leaving the scalar inequality `A / D * V ≤ ρ`.

This module isolates that argument.  The two statements are increasingly packaged:

* `le_mul_exp_of_mul_rothNumberNat_le` is the modulus cancellation, for a single `M`;
* `le_of_forall_exists_rothNumberNat_copies` is the whole rate argument including the limit;
* `exists_forall_pow_le_copies` reads the same argument as a lower bound on `copies` itself:
  eventually in `k`, the count forces `W ^ k ≤ copies` for every base `W < A / D`.  This is the
  form needed when the copy count appears in the conclusion, as it does in the certificate value
  `3 (log R̲ − log F) / log(abc)` of a Galactic exponent.

The purely analytic ingredient that makes the Behrend loss subexponential in `k` --- the bound
`√(log x) ≤ s * √(k + 1)` for `x ≤ c * G ^ (m * k)` --- mentions no progression-free set and lives
one module down as `Growth.sqrt_log_le_mul_sqrt_succ` in `Analysis/Subexponential.lean`, next to
`Growth.Subexponential.exp_mul_sqrt_succ`.

Current clients of the finite statement are `Examples/CoppersmithWinogradEasyHashing.lean`
(three-constituent CW: `A = 27`, `U = 24 * 4 ^ k`, `ρ = (q + 2) ^ 3`) and
`Examples/CoppersmithWinogradFirstPowerHashing.lean` (six-constituent CW, where the modulus is
cancelled against a type fiber size rather than against a power of `4`); both need the finite
form because both also expose a rate inequality with an explicitly named loss.  The packaged
second statement is the form required by an asymptotic-independence barrier for the easy CW
tensor, where only the limiting scalar inequality is of interest.
-/

namespace AlgebraicComplexity.Growth

/-- Behrend cancellation for a single modulus.

From a copies-style bound `a * rothNumberNat (M / 2) ≤ b * M ^ 2`, Behrend's theorem removes the
progression-free cardinality at the cost of a factor `exp (4 * √(log (M / 2)))`, and one power of
the modulus is cancelled against the growth bound `M ≤ U`.  The remaining exponential factor is
supplied abstractly through `t`, so the caller can use whatever bound on `√(log (M / 2))` its
modulus construction provides (see `sqrt_log_le_mul_sqrt_succ`). -/
theorem le_mul_exp_of_mul_rothNumberNat_le {M : ℕ} {a b U t : ℝ}
    (hM : 2 ≤ M) (ha : 0 ≤ a) (hb : 0 ≤ b) (hMU : (M : ℝ) ≤ U)
    (ht : 4 * √(Real.log ((M / 2 : ℕ) : ℝ)) ≤ t)
    (h : a * (rothNumberNat (M / 2) : ℝ) ≤ b * ((M : ℝ) * (M : ℝ))) :
    a ≤ 3 * b * U * Real.exp t := by
  set L : ℝ := √(Real.log ((M / 2 : ℕ) : ℝ)) with hL
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  have hhalf : (M : ℝ) / 3 ≤ ((M / 2 : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    have hnat : M ≤ M / 2 * 3 := by omega
    exact_mod_cast hnat
  have hbehrend : ((M / 2 : ℕ) : ℝ) * Real.exp (-4 * L) ≤ (rothNumberNat (M / 2) : ℝ) :=
    Behrend.roth_lower_bound
  have hroth : (M : ℝ) / 3 * Real.exp (-4 * L) ≤ (rothNumberNat (M / 2) : ℝ) :=
    (mul_le_mul_of_nonneg_right hhalf (Real.exp_nonneg _)).trans hbehrend
  have hkey : a * ((M : ℝ) / 3 * Real.exp (-4 * L)) ≤ b * ((M : ℝ) * (M : ℝ)) :=
    (mul_le_mul_of_nonneg_left hroth ha).trans h
  have hcancel : a * Real.exp (-4 * L) ≤ 3 * b * (M : ℝ) := by
    refine le_of_mul_le_mul_right ?_ (show (0 : ℝ) < (M : ℝ) / 3 by positivity)
    calc
      a * Real.exp (-4 * L) * ((M : ℝ) / 3)
          = a * ((M : ℝ) / 3 * Real.exp (-4 * L)) := by ring
      _ ≤ b * ((M : ℝ) * (M : ℝ)) := hkey
      _ = 3 * b * (M : ℝ) * ((M : ℝ) / 3) := by ring
  have hexpand : a ≤ 3 * b * (M : ℝ) * Real.exp (4 * L) := by
    have hmul := mul_le_mul_of_nonneg_right hcancel (Real.exp_nonneg (4 * L))
    rwa [mul_assoc, ← Real.exp_add, show -4 * L + 4 * L = 0 by ring, Real.exp_zero,
      mul_one] at hmul
  have hU : (0 : ℝ) ≤ U := hMpos.le.trans hMU
  have h3b : (0 : ℝ) ≤ 3 * b := by linarith
  calc
    a ≤ 3 * b * (M : ℝ) * Real.exp (4 * L) := hexpand
    _ ≤ 3 * b * U * Real.exp (4 * L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMU h3b) (Real.exp_nonneg _)
    _ ≤ 3 * b * U * Real.exp t :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ht) (mul_nonneg h3b hU)

/-- The Behrend rate argument in packaged form.

Assume that for every positive power `k` there are a modulus `M` and a copy count `copies` with

* `M ≤ E * D ^ k` (the modulus is chosen by Bertrand's postulate just above a target size),
* `A ^ k * rothNumberNat (M / 2) ≤ poly k * M ^ 2 * copies` (the hashing copies bound, whose
  non-exponential factor `poly` is only required to be subexponential), and
* `copies * V ^ k ≤ ρ ^ k` (the value bound satisfied by the extracted copies).

Then `A / D * V ≤ ρ`: Behrend's construction, the polynomial hashing losses, and the modulus all
disappear in the limit, and the only surviving trace of the modulus is the division of the
progression base `A` by the modulus growth rate `D`.

This is the limit form for a client that only wants the scalar inequality; intended client:
milestone **M6** (`Examples/CoppersmithWinogradEasyCoordinate.lean`), the
asymptotic-independence barrier for the easy Coppersmith--Winograd tensor
(`A = 27`, `D = 4`, `E = 24`, `poly k = 6 * k ^ 2`).  The two hashing clients in `Examples/`
instead use `le_mul_exp_of_mul_rothNumberNat_le` directly, because they also expose the finite
rate inequality with an explicit named loss. -/
theorem le_of_forall_exists_rothNumberNat_copies
    {A D E V ρ : ℝ} {poly : ℕ → ℝ}
    (hA : 0 ≤ A) (hD : 0 < D) (hE : 0 < E) (hV : 0 ≤ V) (hρ : 0 ≤ ρ)
    (hpoly : Subexponential poly)
    (h : ∀ k : ℕ, 0 < k → ∃ M copies : ℕ,
      2 ≤ M ∧ (M : ℝ) ≤ E * D ^ k ∧
        A ^ k * (rothNumberNat (M / 2) : ℝ) ≤
          poly k * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) ∧
        (copies : ℝ) * V ^ k ≤ ρ ^ k) :
    A / D * V ≤ ρ := by
  set s : ℝ := √(E + D) with hsdef
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = E + D := Real.sq_sqrt (by positivity)
  have hloss : Subexponential
      (fun n : ℕ ↦ 3 * (E * poly n) * Real.exp (4 * s * √(((n + 1 : ℕ) : ℝ)))) :=
    ((hpoly.const_mul hE.le).const_mul (by norm_num : (0 : ℝ) ≤ 3)).mul
      (Subexponential.exp_mul_sqrt_succ (by positivity))
  refine le_of_pow_succ_le_subexponential_mul_pow_succ hρ hloss ?_
  intro n
  obtain ⟨M, copies, hM, hMU, hcount, hcopies⟩ := h (n + 1) (Nat.succ_pos n)
  set k : ℕ := n + 1 with hk
  have hhalfPos : (0 : ℝ) < ((M / 2 : ℕ) : ℝ) := by
    have : 0 < M / 2 := by omega
    exact_mod_cast this
  have hhalfUpper : ((M / 2 : ℕ) : ℝ) ≤ E / 2 * D ^ (1 * k) := by
    calc
      ((M / 2 : ℕ) : ℝ) ≤ (M : ℝ) / 2 := Nat.cast_div_le
      _ ≤ E * D ^ k / 2 := by
        exact div_le_div_of_nonneg_right hMU (by norm_num)
      _ = E / 2 * D ^ (1 * k) := by rw [one_mul]; ring
  have hsqrt := sqrt_log_le_mul_sqrt_succ (x := ((M / 2 : ℕ) : ℝ)) (c := E / 2)
    (G := D) (s := s) (m := 1) (k := k) hhalfPos (by positivity) hD hs hhalfUpper
    (by rw [hs2]; linarith) (by rw [hs2]; push_cast; linarith)
  have ht : 4 * √(Real.log ((M / 2 : ℕ) : ℝ)) ≤ 4 * s * √(((k + 1 : ℕ) : ℝ)) := by
    linarith
  have hpolyM : (0 : ℝ) ≤ poly k * ((M : ℝ) * (M : ℝ)) :=
    mul_nonneg (hpoly.nonneg k) (by positivity)
  have hcnt : A ^ k * V ^ k * (rothNumberNat (M / 2) : ℝ) ≤
      poly k * ρ ^ k * ((M : ℝ) * (M : ℝ)) := by
    calc
      A ^ k * V ^ k * (rothNumberNat (M / 2) : ℝ)
          = A ^ k * (rothNumberNat (M / 2) : ℝ) * V ^ k := by ring
      _ ≤ poly k * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) * V ^ k :=
        mul_le_mul_of_nonneg_right hcount (pow_nonneg hV k)
      _ = poly k * ((M : ℝ) * (M : ℝ)) * ((copies : ℝ) * V ^ k) := by ring
      _ ≤ poly k * ((M : ℝ) * (M : ℝ)) * ρ ^ k :=
        mul_le_mul_of_nonneg_left hcopies hpolyM
      _ = poly k * ρ ^ k * ((M : ℝ) * (M : ℝ)) := by ring
  have hrate := le_mul_exp_of_mul_rothNumberNat_le (M := M) (a := A ^ k * V ^ k)
    (b := poly k * ρ ^ k) (U := E * D ^ k) (t := 4 * s * √(((k + 1 : ℕ) : ℝ)))
    hM (mul_nonneg (pow_nonneg hA k) (pow_nonneg hV k))
    (mul_nonneg (hpoly.nonneg k) (pow_nonneg hρ k)) hMU ht hcnt
  show (A / D * V) ^ k ≤
    3 * (E * poly k) * Real.exp (4 * s * √(((k + 1 : ℕ) : ℝ))) * ρ ^ k
  rw [mul_pow, div_pow, div_mul_eq_mul_div,
    div_le_iff₀ (pow_pos hD k)]
  calc
    A ^ k * V ^ k ≤ 3 * (poly k * ρ ^ k) * (E * D ^ k) *
        Real.exp (4 * s * √(((k + 1 : ℕ) : ℝ))) := hrate
    _ = 3 * (E * poly k) * Real.exp (4 * s * √(((k + 1 : ℕ) : ℝ))) * ρ ^ k * D ^ k := by
      ring

/-- **The Behrend rate argument read as a lower bound on the copy count.**

The same hypotheses as `le_of_forall_exists_rothNumberNat_copies` --- a modulus bounded by
`E * D ^ k` and a hashing count `A ^ k * rothNumberNat (M / 2) ≤ poly k * M ^ 2 * copies` with
`poly` subexponential --- force

```text
(A / D) ^ k ≤ loss k * copies
```

with an explicit subexponential loss.  Since a subexponential loss is eventually below every
exponential of base greater than one (`Subexponential.eventually_le_pow`), *every* base `W`
strictly below `A / D` satisfies `W ^ k ≤ copies` from some power on.

This is the form needed when the copies themselves --- and not only a limiting scalar inequality
--- appear in the conclusion, as in an upper bound on a Galactic exponent, where `copies` is the
number `F` of extracted matrix-multiplication tensors and the certificate value is
`3 (log R̲ − log F) / log(abc)`.

Proof sketch: for fixed `k` apply `le_mul_exp_of_mul_rothNumberNat_le` with `a = A ^ k` and
`b = poly k * copies`, using `sqrt_log_le_mul_sqrt_succ` (with `s = √(E + D)`) to replace
`4√(log (M/2))` by the subexponential exponent `4 s √(k+1)`; dividing by `D ^ k` gives
`(A/D)^k ≤ loss k * copies` for
`loss k = 3 (E · poly k) exp (4 s √(k+1))`.  Choosing `N` with `loss k ≤ ((A/D)/W)^k` for `k ≥ N`
and cancelling the positive factor `(A/D)^k` leaves `W ^ k ≤ copies`. -/
theorem exists_forall_pow_le_copies {A D E W : ℝ} {poly : ℕ → ℝ}
    (hD : 0 < D) (hE : 0 < E) (hpoly : Subexponential poly)
    (hW : 0 < W) (hWA : W < A / D) :
    ∃ N : ℕ, ∀ k M copies : ℕ, N ≤ k → 2 ≤ M → (M : ℝ) ≤ E * D ^ k →
      A ^ k * (rothNumberNat (M / 2) : ℝ) ≤ poly k * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) →
      W ^ k ≤ (copies : ℝ) := by
  have hADpos : 0 < A / D := hW.trans hWA
  have hA : 0 < A := by
    have := mul_pos hADpos hD
    rwa [div_mul_cancel₀ _ hD.ne'] at this
  set s : ℝ := √(E + D) with hsdef
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = E + D := Real.sq_sqrt (by positivity)
  have hloss : Subexponential
      (fun n : ℕ ↦ 3 * (E * poly n) * Real.exp (4 * s * √(((n + 1 : ℕ) : ℝ)))) :=
    ((hpoly.const_mul hE.le).const_mul (by norm_num : (0 : ℝ) ≤ 3)).mul
      (Subexponential.exp_mul_sqrt_succ (by positivity))
  have hδ : 1 < A / D / W := (one_lt_div hW).mpr hWA
  obtain ⟨N, hN⟩ := hloss.eventually_le_pow hδ
  refine ⟨N, fun k M copies hk hM hMU hcount ↦ ?_⟩
  have hhalfPos : (0 : ℝ) < ((M / 2 : ℕ) : ℝ) := by
    have : 0 < M / 2 := by omega
    exact_mod_cast this
  have hhalfUpper : ((M / 2 : ℕ) : ℝ) ≤ E / 2 * D ^ (1 * k) := by
    calc
      ((M / 2 : ℕ) : ℝ) ≤ (M : ℝ) / 2 := Nat.cast_div_le
      _ ≤ E * D ^ k / 2 := div_le_div_of_nonneg_right hMU (by norm_num)
      _ = E / 2 * D ^ (1 * k) := by rw [one_mul]; ring
  have hsqrt := sqrt_log_le_mul_sqrt_succ (x := ((M / 2 : ℕ) : ℝ)) (c := E / 2)
    (G := D) (s := s) (m := 1) (k := k) hhalfPos (by positivity) hD hs hhalfUpper
    (by rw [hs2]; linarith) (by rw [hs2]; push_cast; linarith)
  have ht : 4 * √(Real.log ((M / 2 : ℕ) : ℝ)) ≤ 4 * s * √(((k + 1 : ℕ) : ℝ)) := by linarith
  have hrate := le_mul_exp_of_mul_rothNumberNat_le (M := M) (a := A ^ k)
    (b := poly k * (copies : ℝ)) (U := E * D ^ k) (t := 4 * s * √(((k + 1 : ℕ) : ℝ)))
    hM (pow_nonneg hA.le k) (mul_nonneg (hpoly.nonneg k) (Nat.cast_nonneg _)) hMU ht
    (by rw [show poly k * (copies : ℝ) * ((M : ℝ) * (M : ℝ))
          = poly k * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) from by ring]; exact hcount)
  have hDk : (0 : ℝ) < D ^ k := pow_pos hD k
  have hmain : (A / D) ^ k ≤
      3 * (E * poly k) * Real.exp (4 * s * √(((k + 1 : ℕ) : ℝ))) * (copies : ℝ) := by
    rw [div_pow, div_le_iff₀ hDk]
    calc A ^ k ≤ 3 * (poly k * (copies : ℝ)) * (E * D ^ k) *
          Real.exp (4 * s * √(((k + 1 : ℕ) : ℝ))) := hrate
      _ = 3 * (E * poly k) * Real.exp (4 * s * √(((k + 1 : ℕ) : ℝ))) * (copies : ℝ) * D ^ k := by
        ring
  have hkey : (A / D) ^ k ≤ (A / D) ^ k / W ^ k * (copies : ℝ) := by
    calc (A / D) ^ k ≤
        3 * (E * poly k) * Real.exp (4 * s * √(((k + 1 : ℕ) : ℝ))) * (copies : ℝ) := hmain
      _ ≤ (A / D / W) ^ k * (copies : ℝ) :=
        mul_le_mul_of_nonneg_right (hN k hk) (Nat.cast_nonneg _)
      _ = (A / D) ^ k / W ^ k * (copies : ℝ) := by rw [div_pow]
  rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hW k)] at hkey
  exact le_of_mul_le_mul_left hkey (pow_pos hADpos k)

/-- **Copy growth when the modulus itself has a subexponential prefactor.**

This is the sequence-ready form used by canonical prime-field constructions.  In applications
the exact collision requirement is bounded by `modulusLoss k * D ^ k`, where `modulusLoss` is
polynomial (or otherwise subexponential), rather than by a fixed constant times `D ^ k`.
Every base `W < A / D` is nevertheless eventually attained by the surviving copy count.

Proof sketch: choose an intermediate exponential base `D'` strictly between `D` and `A / W`.
Subexponentiality eventually bounds `modulusLoss k` by `(D' / D)^k`, so the modulus is at most
`D'^k`.  Apply `exists_forall_pow_le_copies` with fixed prefactor one and base `D'`; the choice
`D' < A / W` preserves the strict copy-base inequality needed there. -/
theorem exists_forall_pow_le_copies_of_subexponential_modulus
    {A D W : ℝ} {modulusLoss poly : ℕ → ℝ}
    (hD : 0 < D)
    (hmodulusLoss : Subexponential modulusLoss)
    (hpoly : Subexponential poly)
    (hW : 0 < W) (hWA : W < A / D) :
    ∃ N : ℕ, ∀ k M copies : ℕ, N ≤ k → 2 ≤ M →
      (M : ℝ) ≤ modulusLoss k * D ^ k →
      A ^ k * (rothNumberNat (M / 2) : ℝ) ≤
        poly k * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) →
      W ^ k ≤ (copies : ℝ) := by
  have hDW : D * W < A := by
    have h := (lt_div_iff₀ hD).mp hWA
    nlinarith [h]
  have hDAW : D < A / W := (lt_div_iff₀ hW).2 hDW
  let D' : ℝ := (D + A / W) / 2
  have hDD' : D < D' := by
    dsimp [D']
    linarith
  have hD'AW : D' < A / W := by
    dsimp [D']
    linarith
  have hD' : 0 < D' := hD.trans hDD'
  have hWD' : W < A / D' := by
    apply (lt_div_iff₀ hD').2
    calc
      W * D' < W * (A / W) := mul_lt_mul_of_pos_left hD'AW hW
      _ = A := by field_simp [hW.ne']
  have hdelta : 1 < D' / D := (one_lt_div hD).2 hDD'
  obtain ⟨N₁, hN₁⟩ := hmodulusLoss.eventually_le_pow hdelta
  obtain ⟨N₂, hN₂⟩ := exists_forall_pow_le_copies
    (A := A) (D := D') (E := 1) (W := W) (poly := poly)
    hD' (by norm_num) hpoly hW hWD'
  refine ⟨max N₁ N₂, fun k M copies hk hM hmodulus hcount ↦ ?_⟩
  have hk₁ : N₁ ≤ k := (le_max_left N₁ N₂).trans hk
  have hk₂ : N₂ ≤ k := (le_max_right N₁ N₂).trans hk
  have hloss := hN₁ k hk₁
  have hDpow : 0 ≤ D ^ k := (pow_pos hD k).le
  have hmodulus' : (M : ℝ) ≤ D' ^ k := by
    calc
      (M : ℝ) ≤ modulusLoss k * D ^ k := hmodulus
      _ ≤ (D' / D) ^ k * D ^ k :=
        mul_le_mul_of_nonneg_right hloss hDpow
      _ = D' ^ k := by
        rw [div_pow]
        exact div_mul_cancel₀ (D' ^ k) (pow_ne_zero _ hD.ne')
  exact hN₂ k M copies hk₂ hM (by simpa using hmodulus') hcount

end AlgebraicComplexity.Growth
