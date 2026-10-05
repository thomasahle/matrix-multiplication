/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Asymptotics
import AlgebraicComplexity.Tensor.Power
import AlgebraicComplexity.Tensor.PowerCoherence

/-!
# Asymptotic tensor rank

Asymptotic rank is the exponential growth rate of the ranks of canonical tensor powers.  The
definition permits a fixed multiplicative constant; submultiplicativity makes this equivalent to
the usual infimum/limit of `n`th roots while giving a convenient certificate-facing API.  This
file also proves the unconditional one-tensor power upper bound and, under the explicit
nonvanishing hypothesis on all powers, the equality `R̃(T^{⊗n}) = R̃(T)^n`.  Structural laws
relating different tensors live in `Tensor/AsymptoticRankCalculus.lean`.
-/

namespace AlgebraicComplexity.Tensor

open Growth Filter Topology

universe u v w

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable {W : Leg → Type w}
variable [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]

/-! ## Passing a strict-base estimate to the limiting base -/

/-- A real number bounded by `g b` for every `b` strictly above `a` is bounded by `g a`, provided
`g` is continuous at `a`.

Proof sketch: `𝓝[>] a` is a nontrivial filter on `ℝ`, the hypothesis holds everywhere on it, and
`g` tends to `g a` along it. -/
theorem le_of_forall_gt_le {x a : ℝ} {g : ℝ → ℝ} (hg : ContinuousAt g a)
    (h : ∀ b, a < b → x ≤ g b) : x ≤ g a :=
  ge_of_tendsto (hg.continuousWithinAt (s := Set.Ioi a))
    (eventually_nhdsWithin_of_forall fun b hb ↦ h b hb)

/-- The ordinary-rank sequence of the tensor powers of `T`. -/
noncomputable def rankPowerSequence (T : Tensor3 K V) (n : ℕ) : ℕ :=
  rank (power T n)

/-- Asymptotic tensor rank, as the least exponential base for ordinary ranks of tensor powers. -/
noncomputable def asymptoticRank (T : Tensor3 K V) : ℝ :=
  exponentialRate (rankPowerSequence T)

theorem asymptoticRank_nonneg (T : Tensor3 K V) : 0 ≤ asymptoticRank T :=
  exponentialRate_nonneg _

/-- Any exponential bound on ranks of powers bounds asymptotic rank. -/
theorem asymptoticRank_le {T : Tensor3 K V} {ρ : ℝ}
    (h : ExponentialBound (rankPowerSequence T) ρ) : asymptoticRank T ≤ ρ :=
  exponentialRate_le h

/-- Ordinary rank is always an admissible exponential base for tensor powers. -/
theorem rank_exponentialBound (T : Tensor3 K V) :
    ExponentialBound (rankPowerSequence T) (rank T : ℝ) := by
  apply ExponentialBound.of_le_pow
  exact rank_power_le T

/-- Every base strictly above asymptotic rank gives a uniform exponential bound for the ranks of
all tensor powers. -/
theorem rankPower_exponentialBound_of_asymptoticRank_lt
    {T : Tensor3 K V} {ρ : ℝ} (hρ : asymptoticRank T < ρ) :
    ExponentialBound (rankPowerSequence T) ρ := by
  apply exponentialBound_of_exponentialRate_lt
  · exact ⟨rank T, rank_exponentialBound T⟩
  · exact hρ

/-- A pointwise geometric lower bound for ranks of powers bounds asymptotic rank from below. -/
theorem le_asymptoticRank_of_pow_le
    {T : Tensor3 K V} {b : ℝ}
    (h : ∀ n, b ^ n ≤ rankPowerSequence T n) :
    b ≤ asymptoticRank T := by
  apply le_exponentialRate_of_pow_le
  · exact ⟨rank T, rank_exponentialBound T⟩
  · exact h

theorem asymptoticRank_le_rank (T : Tensor3 K V) : asymptoticRank T ≤ rank T :=
  asymptoticRank_le (rank_exponentialBound T)

/-- Exact restriction decreases the rank of every tensor power. -/
theorem rankPowerSequence_restricts_le {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Restricts T S) (n : ℕ) : rankPowerSequence S n ≤ rankPowerSequence T n := by
  exact rank_restricts_le (h.power n)

/-- Asymptotic rank is monotone under exact restriction. -/
theorem asymptoticRank_restricts_le {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Restricts T S) : asymptoticRank S ≤ asymptoticRank T := by
  apply exponentialRate_mono (rankPowerSequence_restricts_le h)
  exact ⟨rank T, rank_exponentialBound T⟩

/-- Legwise linear isomorphisms preserve asymptotic rank. -/
theorem asymptoticRank_isomorphic {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Isomorphic T S) : asymptoticRank T = asymptoticRank S := by
  apply le_antisymm
  · exact asymptoticRank_restricts_le h.symm.restricts
  · exact asymptoticRank_restricts_le h.restricts

/-! ## The asymptotic rank of a power

Both halves of the multiplicativity law `R̃(T^{⊗n}) = R̃(T)^n` are available here.  The lower bound
`R̃(T)^n ≤ R̃(T^{⊗n})` follows from the infimum characterization of asymptotic rank.  The strict
upper bound first works with every base above `R̃(T)`; continuity then removes that slack and gives
the unconditional equality. -/

section Power

/-- Ranks of canonical tensor powers are submultiplicative in the exponent:
`R(T^{⊗(m+n)}) ≤ R(T^{⊗m}) · R(T^{⊗n})`, because the external product of the two powers is
legwise isomorphic to the `(m+n)`th power. -/
theorem rankPowerSequence_add_le (T : Tensor3 K V) (m n : ℕ) :
    rankPowerSequence T (m + n) ≤ rankPowerSequence T m * rankPowerSequence T n := by
  have hiso : rank (external (power T m) (power T n)) = rank (power T (m + n)) :=
    rank_isomorphic (isomorphic_external_power T m n)
  calc rankPowerSequence T (m + n) = rank (external (power T m) (power T n)) := hiso.symm
    _ ≤ rank (power T m) * rank (power T n) := rank_external_le _ _

/-- The asymptotic rank is dominated by every single normalized power: `R̃(T)^m ≤ R(T^{⊗m})`.

Proof sketch: for a submultiplicative sequence bounded below by one the constant-tolerant
`Growth.exponentialRate` agrees with the infimum of the `m`th roots
(`Growth.exponentialRate_eq_submultiplicativeLimit`), and an infimum of roots is at most each
individual root. -/
theorem asymptoticRank_pow_le_rank_power (T : Tensor3 K V)
    (hone : ∀ m, 1 ≤ rank (power T m)) (m : ℕ) :
    asymptoticRank T ^ m ≤ (rank (power T m) : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using (by exact_mod_cast hone 0 : (1 : ℝ) ≤ (rank (power T 0) : ℝ))
  · have heq : asymptoticRank T =
        Growth.submultiplicativeLimit fun k ↦ ((rankPowerSequence T k : ℕ) : ℝ) :=
      Growth.exponentialRate_eq_submultiplicativeLimit hone (rankPowerSequence_add_le T)
    have hroot : asymptoticRank T ≤ ((rank (power T m) : ℕ) : ℝ) ^ ((m : ℝ)⁻¹) := by
      rw [heq]
      exact Growth.submultiplicativeLimit_le_nthRootSeq (fun k ↦ by positivity) hm
    have h0 : (0 : ℝ) ≤ asymptoticRank T := asymptoticRank_nonneg T
    calc asymptoticRank T ^ m
        ≤ (((rank (power T m) : ℕ) : ℝ) ^ ((m : ℝ)⁻¹)) ^ m := pow_le_pow_left₀ h0 hroot m
      _ = ((rank (power T m) : ℕ) : ℝ) :=
          Real.rpow_inv_natCast_pow (by positivity) (by omega)

/-- **The asymptotic rank of a power dominates the power of the asymptotic rank**,
`R̃(T)^n ≤ R̃(T^{⊗n})`.

This is the lower half of `R̃(T^{⊗n}) = R̃(T)^n`; the upper half is
`asymptoticRank_power_le_pow_of_lt`.

Proof sketch: `asymptoticRank_pow_le_rank_power` bounds `R̃(T)^{n·k}` by `R(T^{⊗(n·k)})`, which is
`R((T^{⊗n})^{⊗k})` by `Isomorphic.power_power`; that is a geometric lower bound with base
`R̃(T)^n` for the rank sequence of the powers of `T^{⊗n}`, and `le_asymptoticRank_of_pow_le`
converts it into a lower bound on `R̃(T^{⊗n})`. -/
theorem asymptoticRank_pow_le_asymptoticRank_power (T : Tensor3 K V)
    (hone : ∀ m, 1 ≤ rank (power T m)) (n : ℕ) :
    asymptoticRank T ^ n ≤ asymptoticRank (power T n) := by
  refine le_asymptoticRank_of_pow_le fun k ↦ ?_
  have hiso : rank (power (power T n) k) = rank (power T (k * n)) :=
    rank_isomorphic (Isomorphic.power_power T n k)
  have hmain := asymptoticRank_pow_le_rank_power T hone (k * n)
  calc (asymptoticRank T ^ n) ^ k = asymptoticRank T ^ (k * n) := by
        rw [← pow_mul, mul_comm]
    _ ≤ ((rank (power T (k * n)) : ℕ) : ℝ) := hmain
    _ = (rankPowerSequence (power T n) k : ℝ) := by
        rw [rankPowerSequence, hiso]

/-- **The asymptotic rank of a power is bounded by the power of any strictly larger base**:
if `R̃(T) < ρ` then `R̃(T^{⊗N}) ≤ ρ^N`.

This is the upper half of the multiplicativity law `R̃(T^{⊗n}) = R̃(T)^n`, in the strict form that
needs no limiting argument; `asymptoticRank_power_le` below removes the slack by letting `ρ`
decrease to `R̃(T)`.

Proof sketch: a base `ρ` strictly above `R̃(T)` bounds every rank `R(T^{⊗m})` by `C · ρ^m` for one
fixed constant `C`.  Reading that bound at the multiples `m = k · N` and identifying
`T^{⊗(k·N)}` with `(T^{⊗N})^{⊗k}` through `Isomorphic.power_power` exhibits `ρ^N` as an admissible
exponential base for the ranks of the powers of `T^{⊗N}`, with the same constant `C`. -/
theorem asymptoticRank_power_le_pow_of_lt {T : Tensor3 K V} {ρ : ℝ}
    (hρ : asymptoticRank T < ρ) (N : ℕ) :
    asymptoticRank (power T N) ≤ ρ ^ N := by
  obtain ⟨hρ0, C, hC, hbound⟩ := rankPower_exponentialBound_of_asymptoticRank_lt hρ
  refine asymptoticRank_le ⟨by positivity, C, hC, fun k ↦ ?_⟩
  have hiso : rank (power (power T N) k) = rank (power T (k * N)) :=
    rank_isomorphic (Isomorphic.power_power T N k)
  calc ((rankPowerSequence (power T N) k : ℕ) : ℝ) = ((rank (power T (k * N)) : ℕ) : ℝ) := by
        rw [rankPowerSequence, hiso]
    _ ≤ C * ρ ^ (k * N) := hbound (k * N)
    _ = C * (ρ ^ N) ^ k := by rw [pow_mul']

/-- **The asymptotic rank of a power is bounded by the power of the asymptotic rank**,
`R̃(T^{⊗n}) ≤ R̃(T)^n`.

Proof sketch: `asymptoticRank_power_le_pow_of_lt` gives `R̃(T^{⊗n}) ≤ α^n` for every base `α`
strictly above `R̃(T)`; letting `α` decrease to `R̃(T)` is `le_of_forall_gt_le` for the continuous
function `x ↦ x^n`. -/
theorem asymptoticRank_power_le (T : Tensor3 K V) (n : ℕ) :
    asymptoticRank (power T n) ≤ asymptoticRank T ^ n :=
  le_of_forall_gt_le (g := fun x : ℝ ↦ x ^ n) (by fun_prop)
    fun _α hα ↦ asymptoticRank_power_le_pow_of_lt hα n

/-- **Multiplicativity of asymptotic rank along powers**, `R̃(T^{⊗n}) = R̃(T)^n`.

The lower bound needs the hypothesis that no tensor power of `T` is zero, in the form
`1 ≤ R(T^{⊗m})`; the upper bound is unconditional. -/
theorem asymptoticRank_power_eq (T : Tensor3 K V)
    (hone : ∀ m, 1 ≤ rank (power T m)) (n : ℕ) :
    asymptoticRank (power T n) = asymptoticRank T ^ n :=
  le_antisymm (asymptoticRank_power_le T n)
    (asymptoticRank_pow_le_asymptoticRank_power T hone n)

end Power

end AlgebraicComplexity.Tensor
