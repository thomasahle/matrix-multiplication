/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Asymptotics
import AlgebraicComplexity.Tensor.AsymptoticInvariant
import AlgebraicComplexity.Tensor.IndependenceNumber

/-!
# The asymptotic independence number

This file defines the **asymptotic independence number** `Ī(T)` of a tensor given in coordinates
and proves its elementary calculus, following

> J. Alman and V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to
> Matrix Multiplication*, arXiv:1810.08671, Section 3.5 and Section 4.

AVW define `Ī(T) := limsup_n I(T^{⊗n})^{1/n}` and then use it exclusively through inequalities of
the shape `Ī(T) ≥ I(T^{⊗n})^{1/n}` for a *single* `n` (Corollary 4.1, Lemma 4.4, Theorem 7.3).
With a bare `limsup` every such use has to be re-derived along a subsequence.  Since
`I(T^{⊗m}) · I(T^{⊗n}) ≤ I(T^{⊗(m+n)})` (`independenceNumber_coordinatePower_add_ge`) and
`I(T^{⊗n}) ≤ |κ i|^n` (`independenceNumber_coordinatePower_le_pow`), Fekete's lemma applies and
the `limsup` is a genuine limit equal to the supremum of the roots.  We therefore *define* `Ī` as
that supremum and record the limit as a theorem.

## Main definitions

* `independenceNumberPowerSequence T n = I(T^{⊗n})`, the natural-valued sequence of independence
  numbers of the Kronecker powers of the coefficient table `T` (`coordinatePower` of
  `Tensor/IndependenceNumber.lean`).
* `asymptoticIndependenceNumber T`, the asymptotic independence number `Ī(T)`, defined as
  `Growth.supermultiplicativeLimit` of that sequence --- the supremum of `I(T^{⊗n})^{1/n}` over
  `n ≥ 1`.

## Main results

* `tendsto_asymptoticIndependenceNumber`: `I(T^{⊗n})^{1/n} → Ī(T)`, so the definition agrees with
  AVW's `limsup`.  This is Fekete's lemma, in the `Growth.Supermultiplicative.tendsto_nthRootSeq`
  packaging of `AlgebraicComplexity/Asymptotics.lean`.
* `root_le_asymptoticIndependenceNumber`: `I(T^{⊗n})^{1/n} ≤ Ī(T)` for every `n ≥ 1`.  This is the
  form every application consumes, and it is unconditional because `Ī` is a supremum.
* `independenceNumber_le_asymptoticIndependenceNumber`: `I(T) ≤ Ī(T)`.
* `asymptoticIndependenceNumber_le_card`: `Ī(T) ≤ min{|X|, |Y|, |Z|}` (AVW Section 3.5).
* `asymptoticIndependenceNumber_coordinateZeroOut_le`: `Ī` is monotone under zeroing outs.
* `asymptoticIndependenceNumber_eq_exponentialRate`: `Ī(T)` is the constant-tolerant exponential
  rate `Growth.exponentialRate` of the same sequence.  This is the bridge that makes the
  polynomial-loss lemmas of `AlgebraicComplexity/Asymptotics.lean` --- in particular
  `Growth.le_exponentialRate_of_pow_succ_le_mul_polynomial`, which is exactly the shape of AVW
  Lemma 4.3 --- available for `Ī`; `Tensor/MonomialIndependence.lean` uses it.
* `asymptoticIndependenceNumber_le_of_subexponential_mul_pow`: **the subexponential-loss
  bridge.**  If `I(T^{⊗n}) ≤ loss(n) · M^n` for every `n ≥ 1` with `loss` subexponential, then
  `Ī(T) ≤ M`.  This is the reusable, block-free replacement for the step "and the desired result
  follows" after a bound carrying a `poly(n)` factor; `Tensor/IndependenceBlockEntropy.lean` uses
  it to remove the `(n+1)^{|L|}` factor of Alman's Theorem 5.3.
* `asymptoticIndependenceNumber_coordinateRelabel`: `Ī` is invariant under a legwise bijective
  renaming of the variables (**not** under legwise isomorphism, which is false).
* `asymptoticIndependenceNumber_coordinateExtend`: `Ī` does not see variables that occur in no
  term, so it is unchanged by the zero-extension along a legwise injection --- the shape of the
  target of a monomial degeneration, which leaves the variables of its source in place.
* `asymptoticIndependenceNumber_coordinateDirectSum_const` (**AVW Lemma 4.4, structural half**):
  `Ī(F ⊙ A) = F · Ī(A)` for the block table of `F` disjoint copies of `A`.
* `asymptoticIndependenceNumber_le_asymptoticSubrank` and
  `asymptoticIndependenceNumber_le_asymptoticRank`: over a field,
  `Ī(T) ≤ Q̃(coordinateTensor T) ≤ R̃(coordinateTensor T)` --- the elementary upper bound used
  throughout AVW Section 4.

## Why this is not an instance of the `Tensor3` invariant wrapper

`Tensor/AsymptoticInvariant.lean` provides `asymptoticSuperInvariant`, which applies the same
Fekete engine to a supermultiplicative invariant of *abstract* tensors, and `asymptoticSubrank` is
built with it.  `Ī` cannot be obtained that way: the independence number is **basis-dependent**
(`BARRIER_FRAMEWORK.md` §1 --- over `ℚ`, `I(⟨2⟩) = 2` while the legwise-isomorphic table obtained
from the change of basis `[[1,1],[1,-1]]` has independence number `1`), so it is not a
`NatInvariant`, and no `IsoInvariant` hypothesis is available for it.  What *is* shared is the
underlying sequence engine: `Ī` is `Growth.supermultiplicativeLimit` applied to
`n ↦ I(T^{⊗n})`, the very same construction the tensor wrapper uses, instantiated directly on the
coefficient table.  Fekete's lemma is therefore not reproved here.

* `asymptoticIndependenceNumber_coordinatePower`: **the power law** `Ī(T^{⊗k}) = Ī(T)^k` for
  `k ≥ 1`.  It does not come from a lemma of the sequence engine --- there is none --- but from the
  two inequalities `I(T^{⊗m})^k ≤ I(T^{⊗(mk)})` and `I(T^{⊗(mk)})^{1/(mk)} ≤ Ī(T)` together with
  the identification of iterated Kronecker powers
  (`independenceNumber_coordinatePower_coordinatePower`).

## Non-goals

* `Ī` is **not** claimed monotone under legwise isomorphism or under restriction; both are false
  for `I` and hence unavailable here.  Monotonicity under monomial degeneration (AVW
  Corollary 4.2) is asymptotic and belongs to `Tensor/MonomialIndependence.lean`.

## Position in the library

Layer 1.  It imports `Tensor/IndependenceNumber.lean` for the finite theory of `I` and its
Kronecker powers, and `Tensor/AsymptoticInvariant.lean` for `asymptoticSubrank` and the
`asymptoticRank` bridge; it mentions no named matrix-multiplication construction and no numerical
bound.
-/

namespace AlgebraicComplexity.Tensor

open Filter Topology

universe u v w

section Definition

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- The sequence `n ↦ I(T^{⊗n})` of independence numbers of the Kronecker powers of `T`. -/
noncomputable def independenceNumberPowerSequence (T : (∀ i, κ i) → K) (n : ℕ) : ℕ :=
  independenceNumber (coordinatePower T n)

/-- **The asymptotic independence number** `Ī(T)` of a coefficient table: the supremum, and by
`tendsto_asymptoticIndependenceNumber` also the limit, of `I(T^{⊗n})^{1/n}` over `n ≥ 1`
(Alman--Vassilevska Williams, arXiv:1810.08671, Section 3.5).

It is `Growth.supermultiplicativeLimit` of `n ↦ I(T^{⊗n})`, that is the same sequence engine that
`Tensor/AsymptoticInvariant.lean` runs on abstract tensor invariants; see the module header for
why the `Tensor3` wrapper cannot be used. -/
noncomputable def asymptoticIndependenceNumber (T : (∀ i, κ i) → K) : ℝ :=
  Growth.supermultiplicativeLimit fun n ↦ (independenceNumberPowerSequence T n : ℝ)

omit [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] in
/-- The real power sequence is nonnegative. -/
theorem independenceNumberPowerSequence_nonneg (T : (∀ i, κ i) → K) (n : ℕ) :
    0 ≤ ((independenceNumberPowerSequence T n : ℕ) : ℝ) := by positivity

/-- `I(T^{⊗n}) ≤ |κ i|^n` for every leg `i`, in real form. -/
theorem independenceNumberPowerSequence_le_pow (T : (∀ i, κ i) → K) (i : Leg) (n : ℕ) :
    ((independenceNumberPowerSequence T n : ℕ) : ℝ) ≤ ((Fintype.card (κ i) : ℝ)) ^ n := by
  have h := independenceNumber_coordinatePower_le_pow T n i
  exact_mod_cast h

/-- The roots of the power sequence are bounded above, by `|κ i|` for any leg `i`.  This is the
hypothesis under which the supremum defining `Ī` is finite and is attained as a limit. -/
theorem bddAbove_nthRootSeq_independenceNumberPowerSequence (T : (∀ i, κ i) → K) :
    BddAbove (Growth.nthRootSeq (fun n ↦ ((independenceNumberPowerSequence T n : ℕ) : ℝ)) ''
      Set.Ici 1) :=
  Growth.bddAbove_nthRootSeq_image (C := (Fintype.card (κ Leg.X) : ℝ))
    (independenceNumberPowerSequence_nonneg T)
    (independenceNumberPowerSequence_le_pow T Leg.X)

/-- **Every single power bounds `Ī` from below**: `I(T^{⊗n})^{1/n} ≤ Ī(T)` for `n ≥ 1`.  This is
the inequality AVW use throughout, and it is unconditional here because `Ī` is defined as the
supremum of these roots. -/
theorem root_le_asymptoticIndependenceNumber (T : (∀ i, κ i) → K) {n : ℕ} (hn : 1 ≤ n) :
    ((independenceNumberPowerSequence T n : ℕ) : ℝ) ^ ((n : ℝ)⁻¹) ≤
      asymptoticIndependenceNumber T :=
  Growth.nthRootSeq_le_supermultiplicativeLimit
    (bddAbove_nthRootSeq_independenceNumberPowerSequence T) hn

/-- **`I(T) ≤ Ī(T)`.** -/
theorem independenceNumber_le_asymptoticIndependenceNumber (T : (∀ i, κ i) → K) :
    (independenceNumber T : ℝ) ≤ asymptoticIndependenceNumber T := by
  have h := root_le_asymptoticIndependenceNumber T (n := 1) le_rfl
  rwa [Nat.cast_one, inv_one, Real.rpow_one, independenceNumberPowerSequence,
    independenceNumber_coordinatePower_one] at h

omit [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] in
/-- A geometric upper bound on the independence numbers of the Kronecker powers bounds `Ī`.

Proof sketch: taking `n`th roots turns `I(T^{⊗n}) ≤ c^n` into `I(T^{⊗n})^{1/n} ≤ c`, and `Ī` is
the supremum of those roots. -/
theorem asymptoticIndependenceNumber_le_of_pow {T : (∀ i, κ i) → K} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ n, ((independenceNumberPowerSequence T n : ℕ) : ℝ) ≤ c ^ n) :
    asymptoticIndependenceNumber T ≤ c := by
  refine Growth.supermultiplicativeLimit_le fun n hn ↦ ?_
  calc Growth.nthRootSeq (fun k ↦ ((independenceNumberPowerSequence T k : ℕ) : ℝ)) n
      ≤ Growth.nthRootSeq (fun k ↦ c ^ k) n :=
        Growth.nthRootSeq_mono (independenceNumberPowerSequence_nonneg T) h n
    _ = c := Growth.nthRootSeq_pow hc hn

/-- **`Ī(T) ≤ min{|X|, |Y|, |Z|}`** (AVW Section 3.5): a zeroing out cannot increase the number of
variables on any leg, and a Kronecker power has `|κ i|^n` of them. -/
theorem asymptoticIndependenceNumber_le_card (T : (∀ i, κ i) → K) (i : Leg) :
    asymptoticIndependenceNumber T ≤ (Fintype.card (κ i) : ℝ) :=
  asymptoticIndependenceNumber_le_of_pow (by positivity)
    (independenceNumberPowerSequence_le_pow T i)

/-- `Ī` is nonnegative. -/
theorem asymptoticIndependenceNumber_nonneg (T : (∀ i, κ i) → K) :
    0 ≤ asymptoticIndependenceNumber T :=
  le_trans (by positivity) (independenceNumber_le_asymptoticIndependenceNumber T)

/-- **The converse of `asymptoticIndependenceNumber_le_of_pow`**: a bound on `Ī` bounds every
finite power, `Ī(B) ≤ c → ∀ l, I(B^{⊗l}) ≤ c^l`.

Proof sketch: for `l ≥ 1` the `l`th root `I(B^{⊗l})^{1/l}` is at most `Ī(B) ≤ c`
(`root_le_asymptoticIndependenceNumber`); raising to the `l`th power removes the root.  For
`l = 0` both sides are `1`. -/
theorem independenceNumber_coordinatePower_le_pow_of_asymptotic {B : (∀ i, κ i) → K} {c : ℝ}
    (hc : asymptoticIndependenceNumber B ≤ c) (l : ℕ) :
    ((independenceNumber (coordinatePower B l) : ℕ) : ℝ) ≤ c ^ l := by
  have hc0 : 0 ≤ c := le_trans (asymptoticIndependenceNumber_nonneg B) hc
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · have h : independenceNumber (coordinatePower B 0) ≤ Fintype.card (κ Leg.X) ^ 0 :=
      independenceNumber_coordinatePower_le_pow B 0 Leg.X
    simp only [pow_zero] at h ⊢
    exact_mod_cast h
  · have hx : ((independenceNumber (coordinatePower B l) : ℕ) : ℝ) ^ ((l : ℝ)⁻¹) ≤ c :=
      le_trans (root_le_asymptoticIndependenceNumber B hl) hc
    have h := pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _) hx l
    rwa [Real.rpow_inv_natCast_pow (by positivity) (Nat.pos_iff_ne_zero.mp hl)] at h

end Definition

section Fekete

variable {K : Type u} [CommSemiring K] [NoZeroDivisors K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- The power sequence of independence numbers is supermultiplicative, by
`independenceNumber_coordinatePower_add_ge`. -/
theorem supermultiplicative_independenceNumberPowerSequence (T : (∀ i, κ i) → K) :
    Growth.Supermultiplicative fun n ↦ ((independenceNumberPowerSequence T n : ℕ) : ℝ) := by
  intro m n
  simp only [independenceNumberPowerSequence]
  exact_mod_cast independenceNumber_coordinatePower_add_ge T m n

/-- **Existence of the asymptotic independence number** (Fekete's lemma).  For a nonzero table `T`
over a coefficient ring without zero divisors, `I(T^{⊗n})^{1/n}` converges to `Ī(T)`.  In
particular the definition adopted here agrees with the `limsup` of
Alman--Vassilevska Williams, and the `limsup` is a genuine limit.

Proof sketch: `independenceNumber_coordinatePower_add_ge` makes the sequence supermultiplicative,
`one_le_independenceNumber_coordinatePower` makes it positive, and
`independenceNumber_coordinatePower_le_pow` bounds it by the geometric sequence `|X|^n`; these are
the three hypotheses of `Growth.Supermultiplicative.tendsto_nthRootSeq`, the multiplicative form of
Fekete's lemma proved in `AlgebraicComplexity/Asymptotics.lean`. -/
theorem tendsto_asymptoticIndependenceNumber {T : (∀ i, κ i) → K} {p : ∀ i, κ i} (hp : T p ≠ 0) :
    Tendsto (Growth.nthRootSeq fun n ↦ ((independenceNumberPowerSequence T n : ℕ) : ℝ)) atTop
      (𝓝 (asymptoticIndependenceNumber T)) := by
  refine (supermultiplicative_independenceNumberPowerSequence T).tendsto_nthRootSeq
    (fun n ↦ ?_) (C := (Fintype.card (κ Leg.X) : ℝ)) (independenceNumberPowerSequence_le_pow T _)
  have h : 1 ≤ independenceNumberPowerSequence T n :=
    one_le_independenceNumber_coordinatePower hp n
  exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one h

omit [NoZeroDivisors K] in
/-- **`Ī` is monotone under zeroing outs**: `Ī(T|_{X',Y',Z'}) ≤ Ī(T)`.

Proof sketch: zeroing outs commute with Kronecker powers
(`coordinatePower_coordinateZeroOut`), so the two power sequences compare pointwise; the geometric
bound `I(T^{⊗n}) ≤ |X|^n` for the dominating sequence lets
`Growth.supermultiplicativeLimit_mono` transport the comparison to the suprema. -/
theorem asymptoticIndependenceNumber_coordinateZeroOut_le (T : (∀ i, κ i) → K)
    (A : ∀ i, Finset (κ i)) :
    asymptoticIndependenceNumber (coordinateZeroOut T A) ≤ asymptoticIndependenceNumber T := by
  refine Growth.supermultiplicativeLimit_mono (C := (Fintype.card (κ Leg.X) : ℝ))
    (independenceNumberPowerSequence_nonneg _) (fun n ↦ ?_)
    (independenceNumberPowerSequence_nonneg T) (independenceNumberPowerSequence_le_pow T Leg.X)
  have h := independenceNumber_coordinatePower_coordinateZeroOut_le T A n
  exact_mod_cast h

end Fekete

section ExponentialRate

variable {K : Type u} [CommSemiring K] [NoZeroDivisors K] [Nontrivial K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

omit [NoZeroDivisors K] [Nontrivial K] in
/-- The power sequence always admits an exponential bound, namely `|X|`. -/
theorem exists_exponentialBound_independenceNumberPowerSequence (T : (∀ i, κ i) → K) :
    ∃ ρ, Growth.ExponentialBound (independenceNumberPowerSequence T) ρ :=
  ⟨(Fintype.card (κ Leg.X) : ℝ),
    Growth.ExponentialBound.of_le_pow _ _ fun n ↦
      independenceNumber_coordinatePower_le_pow T n Leg.X⟩

/-- Every admissible exponential base for the power sequence already dominates every single root.

Proof sketch: supermultiplicativity gives `I(T^{⊗n})^k ≤ I(T^{⊗(nk)})`, and an exponential bound
`I(T^{⊗m}) ≤ C·ρ^m` restricted to the multiples of `n` is an exponential bound with base `ρ^n` for
the sequence `k ↦ I(T^{⊗(nk)})`.  `Growth.ExponentialBound.base_le_of_pow_le` --- the elementary
"a constant factor cannot beat a larger base" lemma --- then yields `I(T^{⊗n}) ≤ ρ^n`. -/
theorem independenceNumberPowerSequence_le_pow_of_exponentialBound {T : (∀ i, κ i) → K} {ρ : ℝ}
    (hρ : Growth.ExponentialBound (independenceNumberPowerSequence T) ρ) (n : ℕ) :
    ((independenceNumberPowerSequence T n : ℕ) : ℝ) ≤ ρ ^ n := by
  obtain ⟨hρ0, C, hC, hbound⟩ := hρ
  have hsub : Growth.ExponentialBound
      (fun k ↦ independenceNumberPowerSequence T (n * k)) (ρ ^ n) := by
    refine ⟨pow_nonneg hρ0 n, C, hC, fun k ↦ ?_⟩
    have h := hbound (n * k)
    rwa [pow_mul] at h
  refine Growth.ExponentialBound.base_le_of_pow_le hsub fun k ↦ ?_
  have h : independenceNumber (coordinatePower T n) ^ k ≤
      independenceNumber (coordinatePower T (n * k)) :=
    independenceNumber_coordinatePower_pow_le T n k
  exact_mod_cast h

/-- **`Ī` is the constant-tolerant exponential rate of the same sequence.**

`Growth.exponentialRate a` is the infimum of the bases `ρ` for which `a n ≤ C·ρ^n` holds with a
fixed positive constant `C`; `Ī(T)` is the supremum of the roots `I(T^{⊗n})^{1/n}`.  For a
supermultiplicative sequence the two agree, which is what makes the polynomial-loss lemmas of
`AlgebraicComplexity/Asymptotics.lean` usable for `Ī`.

Proof sketch: `≤` because every admissible base already dominates every root
(`independenceNumberPowerSequence_le_pow_of_exponentialBound`), so `Ī` is a lower bound for the
set whose infimum is the rate; `≥` because `I(T^{⊗n}) ≤ Ī(T)^n` for every `n` --- for `n ≥ 1` by
`root_le_asymptoticIndependenceNumber` and for `n = 0` because `I(T^{⊗0}) = 1` --- so `Ī(T)` is
itself an admissible base, with constant `1`. -/
theorem asymptoticIndependenceNumber_eq_exponentialRate (T : (∀ i, κ i) → K) :
    asymptoticIndependenceNumber T =
      Growth.exponentialRate (independenceNumberPowerSequence T) := by
  refine le_antisymm ?_ ?_
  · refine le_csInf (exists_exponentialBound_independenceNumberPowerSequence T) ?_
    intro ρ hρ
    exact asymptoticIndependenceNumber_le_of_pow hρ.1
      (independenceNumberPowerSequence_le_pow_of_exponentialBound hρ)
  · refine Growth.exponentialRate_le
      ⟨asymptoticIndependenceNumber_nonneg T, 1, one_pos, fun n ↦ ?_⟩
    rw [one_mul]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_zero, independenceNumberPowerSequence, independenceNumber_coordinatePower_zero]
      norm_num
    · have hroot := root_le_asymptoticIndependenceNumber T hn
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      calc ((independenceNumberPowerSequence T n : ℕ) : ℝ)
          = (((independenceNumberPowerSequence T n : ℕ) : ℝ) ^ ((n : ℝ)⁻¹)) ^ n := by
            rw [← Real.rpow_natCast (_ ^ ((n : ℝ)⁻¹)) n, ← Real.rpow_mul
              (independenceNumberPowerSequence_nonneg T n), inv_mul_cancel₀ hnR.ne',
              Real.rpow_one]
        _ ≤ asymptoticIndependenceNumber T ^ n := by
            refine pow_le_pow_left₀ ?_ hroot n
            exact Real.rpow_nonneg (independenceNumberPowerSequence_nonneg T n) _

end ExponentialRate

/-! ## Removing a subexponential multiplicative loss -/

section SubexponentialLoss

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- **A subexponential multiplicative loss does not affect `Ī`.**  If

```
I(T^{⊗n}) ≤ loss(n) · M^n   for every n ≥ 1
```

with `loss` subexponential, then `Ī(T) ≤ M`.  This is the reusable rate-level replacement for
Alman's "and the desired result follows" after a bound with a `poly(n)` factor.

Proof sketch: `Ī` is the constant-tolerant exponential rate of `n ↦ I(T^{⊗n})`
(`asymptoticIndependenceNumber_eq_exponentialRate`, which is where supermultiplicativity, and
hence `NoZeroDivisors` and `Nontrivial`, is used).  For `ε > 0` put `δ = (M+ε)/(M+ε/2) > 1`; then
`loss(n) ≤ C·δ^n` for some `C > 0` and `δ·M ≤ M+ε`, so `M+ε` is an admissible exponential base
with constant `C+1` (the `n = 0` value `I(T^{⊗0}) = 1` is absorbed by the `+1`).  Hence
`Ī(T) ≤ M + ε` for every `ε > 0`. -/
theorem asymptoticIndependenceNumber_le_of_subexponential_mul_pow
    [NoZeroDivisors K] [Nontrivial K] {T : (∀ i, κ i) → K} {M : ℝ} {loss : ℕ → ℝ}
    (hM : 0 ≤ M) (hloss : Growth.Subexponential loss)
    (h : ∀ n, 0 < n → ((independenceNumber (coordinatePower T n) : ℕ) : ℝ) ≤ loss n * M ^ n) :
    asymptoticIndependenceNumber T ≤ M := by
  rw [asymptoticIndependenceNumber_eq_exponentialRate]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hpos2 : 0 < M + ε / 2 := by linarith
  set δ : ℝ := (M + ε) / (M + ε / 2) with hδdef
  have hδ : 1 < δ := by
    rw [hδdef, lt_div_iff₀ hpos2]; linarith
  obtain ⟨C, hC, hlossC⟩ := hloss.2 δ hδ
  have hδM : δ * M ≤ M + ε := by
    rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ hpos2]
    nlinarith
  refine Growth.exponentialRate_le ⟨by linarith, C + 1, by linarith, fun n ↦ ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, mul_one]
    have h0 : independenceNumberPowerSequence T 0 = 1 := by
      rw [independenceNumberPowerSequence, independenceNumber_coordinatePower_zero]
    rw [h0]
    norm_num
    linarith
  · calc ((independenceNumberPowerSequence T n : ℕ) : ℝ) ≤ loss n * M ^ n := h n hn
      _ ≤ (C * δ ^ n) * M ^ n := mul_le_mul_of_nonneg_right (hlossC n) (by positivity)
      _ = C * (δ * M) ^ n := by rw [mul_pow]; ring
      _ ≤ C * (M + ε) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hδM n) hC.le
      _ ≤ (C + 1) * (M + ε) ^ n :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end SubexponentialLoss

section PowerLaw

variable {K : Type u} [CommSemiring K] [NoZeroDivisors K] [Nontrivial K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

omit [NoZeroDivisors K] [Nontrivial K] in
/-- One half of the power law: `Ī(T^{⊗k}) ≤ Ī(T)^k`.

Proof sketch: for `n ≥ 1` the `n`th root of `I((T^{⊗k})^{⊗n}) = I(T^{⊗(nk)})`
(`independenceNumber_coordinatePower_coordinatePower`) is the `k`th power of its `(nk)`th root,
and the latter is at most `Ī(T)` by `root_le_asymptoticIndependenceNumber`. -/
theorem asymptoticIndependenceNumber_coordinatePower_le (T : (∀ i, κ i) → K) {k : ℕ}
    (hk : k ≠ 0) :
    asymptoticIndependenceNumber (coordinatePower T k) ≤ asymptoticIndependenceNumber T ^ k := by
  refine Growth.supermultiplicativeLimit_le fun n hn ↦ ?_
  have hn0 : n ≠ 0 := by omega
  have hnk : 1 ≤ n * k := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hn0 hk)
  have hroot := root_le_asymptoticIndependenceNumber T hnk
  set x := ((independenceNumberPowerSequence T (n * k) : ℕ) : ℝ) with hx
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have hnR : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hkR : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hpow : x ^ ((n : ℝ)⁻¹) = (x ^ (((n * k : ℕ) : ℝ))⁻¹) ^ k := by
    rw [← Real.rpow_natCast (x ^ (((n * k : ℕ) : ℝ))⁻¹) k, ← Real.rpow_mul hx0]
    congr 1
    push_cast
    field_simp
  have hgoal : Growth.nthRootSeq
      (fun m ↦ ((independenceNumberPowerSequence (coordinatePower T k) m : ℕ) : ℝ)) n =
      x ^ ((n : ℝ)⁻¹) := by
    simp only [Growth.nthRootSeq, hx, independenceNumberPowerSequence,
      independenceNumber_coordinatePower_coordinatePower]
  rw [hgoal, hpow]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hx0 _) hroot k

/-- The other half of the power law: `Ī(T)^k ≤ Ī(T^{⊗k})`.

Proof sketch: supermultiplicativity gives `I(T^{⊗m})^k ≤ I(T^{⊗(mk)}) = I((T^{⊗k})^{⊗m})`, so the
`k`th power of the `m`th root of `I(T^{⊗m})` is at most `Ī(T^{⊗k})`; taking `k`th roots bounds
every such root by `Ī(T^{⊗k})^{1/k}`, hence `Ī(T) ≤ Ī(T^{⊗k})^{1/k}`, and raising to the `k`th
power finishes. -/
theorem le_asymptoticIndependenceNumber_coordinatePower (T : (∀ i, κ i) → K) {k : ℕ}
    (hk : k ≠ 0) :
    asymptoticIndependenceNumber T ^ k ≤ asymptoticIndependenceNumber (coordinatePower T k) := by
  set B := asymptoticIndependenceNumber (coordinatePower T k) with hB
  have hB0 : 0 ≤ B := asymptoticIndependenceNumber_nonneg _
  have hle : asymptoticIndependenceNumber T ≤ B ^ ((k : ℝ)⁻¹) := by
    refine Growth.supermultiplicativeLimit_le fun m hm ↦ ?_
    set a := ((independenceNumberPowerSequence T m : ℕ) : ℝ) with ha
    have ha0 : (0 : ℝ) ≤ a := by positivity
    have hroot : ((independenceNumberPowerSequence T (m * k) : ℕ) : ℝ) ^ ((m : ℝ)⁻¹) ≤ B := by
      have h := root_le_asymptoticIndependenceNumber (coordinatePower T k) hm
      simpa only [independenceNumberPowerSequence,
        independenceNumber_coordinatePower_coordinatePower] using h
    have hak : a ^ k ≤ ((independenceNumberPowerSequence T (m * k) : ℕ) : ℝ) := by
      have h : independenceNumber (coordinatePower T m) ^ k ≤
          independenceNumber (coordinatePower T (m * k)) :=
        independenceNumber_coordinatePower_pow_le T m k
      rw [ha]
      simp only [independenceNumberPowerSequence]
      exact_mod_cast h
    have hstep : (a ^ ((m : ℝ)⁻¹)) ^ k ≤ B := by
      have hmono : (a ^ k) ^ ((m : ℝ)⁻¹) ≤
          ((independenceNumberPowerSequence T (m * k) : ℕ) : ℝ) ^ ((m : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) hak (by positivity)
      have heq : (a ^ k) ^ ((m : ℝ)⁻¹) = (a ^ ((m : ℝ)⁻¹)) ^ k := by
        rw [← Real.rpow_natCast a k, ← Real.rpow_natCast (a ^ ((m : ℝ)⁻¹)) k,
          ← Real.rpow_mul ha0, ← Real.rpow_mul ha0, mul_comm]
      rw [heq] at hmono
      exact hmono.trans hroot
    have hgoal : Growth.nthRootSeq
        (fun j ↦ ((independenceNumberPowerSequence T j : ℕ) : ℝ)) m = a ^ ((m : ℝ)⁻¹) := rfl
    rw [hgoal]
    calc a ^ ((m : ℝ)⁻¹) = ((a ^ ((m : ℝ)⁻¹)) ^ k) ^ ((k : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (Real.rpow_nonneg ha0 _) hk).symm
      _ ≤ B ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hstep (by positivity)
  calc asymptoticIndependenceNumber T ^ k ≤ (B ^ ((k : ℝ)⁻¹)) ^ k :=
        pow_le_pow_left₀ (asymptoticIndependenceNumber_nonneg T) hle k
    _ = B := Real.rpow_inv_natCast_pow hB0 hk

/-- **The power law** `Ī(T^{⊗k}) = Ī(T)^k` for `k ≥ 1`.

This is the multiplicativity of `Ī` along Kronecker powers; note that `Ī` is *not* multiplicative
under Kronecker products of different tensors (AVW Example 5.1). -/
theorem asymptoticIndependenceNumber_coordinatePower (T : (∀ i, κ i) → K) {k : ℕ} (hk : k ≠ 0) :
    asymptoticIndependenceNumber (coordinatePower T k) = asymptoticIndependenceNumber T ^ k :=
  le_antisymm (asymptoticIndependenceNumber_coordinatePower_le T hk)
    (le_asymptoticIndependenceNumber_coordinatePower T hk)

end PowerLaw

/-! ## Relabelling, unused variables, and disjoint copies

Three structural laws of `Ī`, each obtained from the corresponding law of `I`
(`Tensor/IndependenceNumber.lean`) by observing that the two power sequences coincide, or differ
by an exactly geometric factor.  None of them is an isomorphism-invariance statement: `Ī` is
basis-dependent, and only *renamings of variables*, *unused variables* and *blocks* are seen
correctly.

`asymptoticIndependenceNumber_coordinateDirectSum_const` is the structural half of AVW Lemma 4.4:
`Ī(F ⊙ A) = F · Ī(A)` for every table `A`, with no matrix-multiplication input.  The arithmetic
half --- `Ī(⟨a,b,c⟩) = abc/max{a,b,c}` --- lives in
`MatrixMultiplication/IndependentDiagonal.lean`, and the two combine there into the displayed
form `Ī(F ⊙ ⟨a,b,c⟩) = F·abc/max{a,b,c}`.
-/


section Relabel

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v} {κ' : Leg → Type w}

/-- **`Ī` is invariant under a legwise bijective renaming of the variables.** -/
theorem asymptoticIndependenceNumber_coordinateRelabel
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    [∀ i, Fintype (κ' i)] [∀ i, DecidableEq (κ' i)]
    (e : ∀ i, κ i ≃ κ' i) (T : (∀ i, κ i) → K) :
    asymptoticIndependenceNumber (coordinateRelabel e T) = asymptoticIndependenceNumber T := by
  have hseq : ∀ k, independenceNumberPowerSequence (coordinateRelabel e T) k
      = independenceNumberPowerSequence T k := by
    intro k
    simp only [independenceNumberPowerSequence]
    rw [coordinatePower_coordinateRelabel, independenceNumber_coordinateRelabel]
  simp only [asymptoticIndependenceNumber, hseq]

end Relabel

section Extend

variable {K : Type u} [CommSemiring K] {α : Leg → Type v} {β : Leg → Type w}
variable [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
variable [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]

/-- **`Ī` does not see unused variables.** -/
theorem asymptoticIndependenceNumber_coordinateExtend {f : ∀ i, α i → β i} {g : ∀ i, β i → α i}
    (hgf : ∀ i x, g i (f i x) = x) (A : (∀ i, α i) → K) :
    asymptoticIndependenceNumber (coordinateExtend f g A) = asymptoticIndependenceNumber A := by
  have hseq : ∀ k, independenceNumberPowerSequence (coordinateExtend f g A) k
      = independenceNumberPowerSequence A k := by
    intro k
    simp only [independenceNumberPowerSequence]
    rw [coordinatePower_coordinateExtend]
    exact independenceNumber_coordinateExtend fun i q ↦ funext fun t ↦ hgf i (q t)
  simp only [asymptoticIndependenceNumber, hseq]

end Extend

section BlockSum

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v} {ι : Type v}
variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- **AVW Lemma 4.4, structural half: `Ī` is exactly additive on `F` disjoint copies**, that is
`Ī(F ⊙ A) = F · Ī(A)`. -/
theorem asymptoticIndependenceNumber_coordinateDirectSum_const (A : (∀ i, κ i) → K) :
    asymptoticIndependenceNumber (coordinateDirectSum (fun _ : ι ↦ A)) =
      (Fintype.card ι : ℝ) * asymptoticIndependenceNumber A := by
  classical
  set c : ℝ := (Fintype.card ι : ℝ) with hc
  have hc0 : 0 ≤ c := by positivity
  have hseq : ∀ k, ((independenceNumberPowerSequence
      (coordinateDirectSum (fun _ : ι ↦ A)) k : ℕ) : ℝ)
      = c ^ k * ((independenceNumberPowerSequence A k : ℕ) : ℝ) := by
    intro k
    simp only [independenceNumberPowerSequence,
      independenceNumber_coordinatePower_coordinateDirectSum_const]
    push_cast
    ring
  have hroot : ∀ n : ℕ, 1 ≤ n →
      Growth.nthRootSeq (fun k ↦ ((independenceNumberPowerSequence
          (coordinateDirectSum (fun _ : ι ↦ A)) k : ℕ) : ℝ)) n
        = c * Growth.nthRootSeq
            (fun k ↦ ((independenceNumberPowerSequence A k : ℕ) : ℝ)) n := by
    intro n hn
    simp only [Growth.nthRootSeq, hseq n]
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.pow_rpow_inv_natCast hc0 (by omega)]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · have hcard : Fintype.card (ι × κ Leg.X) = 0 := by
      rw [Fintype.card_prod, h0, zero_mul]
    have hle := asymptoticIndependenceNumber_le_card
      (coordinateDirectSum (fun _ : ι ↦ A)) Leg.X
    rw [hcard] at hle
    have hge := asymptoticIndependenceNumber_nonneg (coordinateDirectSum (fun _ : ι ↦ A))
    have : asymptoticIndependenceNumber (coordinateDirectSum (fun _ : ι ↦ A)) = 0 := by
      have : ((0 : ℕ) : ℝ) = 0 := by norm_num
      linarith [hle, hge, this]
    rw [this, hc, h0]
    norm_num
  · have hcpos : 0 < c := by
      rw [hc]
      exact_mod_cast hpos
    refine le_antisymm ?_ ?_
    · refine Growth.supermultiplicativeLimit_le fun n hn ↦ ?_
      rw [hroot n hn]
      exact mul_le_mul_of_nonneg_left (root_le_asymptoticIndependenceNumber A hn) hc0
    · have hA : asymptoticIndependenceNumber A ≤
          asymptoticIndependenceNumber (coordinateDirectSum (fun _ : ι ↦ A)) / c := by
        refine Growth.supermultiplicativeLimit_le fun n hn ↦ ?_
        rw [le_div_iff₀ hcpos, mul_comm, ← hroot n hn]
        exact Growth.nthRootSeq_le_supermultiplicativeLimit
          (bddAbove_nthRootSeq_independenceNumberPowerSequence _) hn
      rw [mul_comm]
      exact (le_div_iff₀ hcpos).mp hA

end BlockSum

section FieldBounds

variable {K : Type u} [Field K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- **`Ī(T) ≤ Q̃(coordinateTensor T)`**: the asymptotic independence number of a coefficient table
never exceeds the asymptotic subrank of the tensor it defines.

Proof sketch: at each power, `I(T^{⊗n}) ≤ Q((coordinateTensor T)^{⊗n})` by
`independenceNumber_coordinatePower_le_subrank`; both invariants are read off as suprema of `n`th
roots, so the pointwise comparison suffices, with
`root_le_asymptoticSuperInvariant` supplying the subrank side. -/
theorem asymptoticIndependenceNumber_le_asymptoticSubrank (T : (∀ i, κ i) → K) :
    asymptoticIndependenceNumber T ≤ asymptoticSubrank (coordinateTensor T) := by
  refine Growth.supermultiplicativeLimit_le fun n hn ↦ ?_
  have hstep : ((independenceNumberPowerSequence T n : ℕ) : ℝ) ^ ((n : ℝ)⁻¹) ≤
      ((subrank (Tensor.power (coordinateTensor T) n) : ℕ) : ℝ) ^ ((n : ℝ)⁻¹) := by
    refine Real.rpow_le_rpow (independenceNumberPowerSequence_nonneg T n) ?_ (by positivity)
    exact_mod_cast independenceNumber_coordinatePower_le_subrank T n
  refine hstep.trans ?_
  exact root_le_asymptoticSuperInvariant (subrankInvariant K) (coordinateTensor T)
    (r := rank (coordinateTensor T)) (subrank_power_le_rank_pow _) hn

/-- **`Ī(T) ≤ R̃(coordinateTensor T)`**: the elementary upper bound by asymptotic rank used
throughout AVW Section 4.

Proof sketch: through `asymptoticIndependenceNumber_eq_exponentialRate` both sides are
constant-tolerant exponential rates of natural sequences, and `I(T^{⊗n}) ≤ rank(T^{⊗n})` compares
them pointwise, so `Growth.exponentialRate_mono` applies; the required exponential bound for the
rank sequence is `rank_exponentialBound`. -/
theorem asymptoticIndependenceNumber_le_asymptoticRank (T : (∀ i, κ i) → K) :
    asymptoticIndependenceNumber T ≤ asymptoticRank (coordinateTensor T) := by
  rw [asymptoticIndependenceNumber_eq_exponentialRate, asymptoticRank]
  refine Growth.exponentialRate_mono (fun n ↦ ?_) ⟨_, rank_exponentialBound (coordinateTensor T)⟩
  exact independenceNumber_coordinatePower_le_rank T n

end FieldBounds

end AlgebraicComplexity.Tensor
