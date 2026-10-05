/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCompetitorBound
import AlgebraicComplexity.Analysis.Subexponential

set_option autoImplicit false

/-!
# `hVdeg` as a cofinal statement, and the one brick it still needs

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoJointHashBranch.lean`
carries `hVdeg : Vb ≤ dwz63PlainSharpDegree K n t`, the finite form of "branch 1 binds".  It is a
*cofinal* statement, and this module states it as one, proves everything about it that the
committed and posted rate lemmas allow, and names the single remaining brick.

## The reduction is exact

`Examples/DuanWuZhouLevelTwoCompetitorBound.lean`'s `dwz63_competitorBound_le_iff` turns `Vb ≤ D`
into the product inequality

`|matchable α K| · |compatibleSet comp₀| ≤ D · |T_K|`,

with no loss.  So `hVdeg` at the sharp degree `D = d` is exactly

`(N_α/N_Z) · p_comp ≤ d`,  i.e.  `ᾱ_p · ᾱ_X ≤ ᾱ_Z · K` at the rate level,

whose per-symbol margin `Examples/DuanWuZhouLevelTwoJointHashBranch.lean` computes as
`−1.1215 · 10⁻⁷`; the exponential factor is `r^n` with `r = 0.99999989 < 1`.

## What is proved here

`dwz63_eventually_subexponential_mul_pow_le_one`: a subexponential factor times `r^n` with
`r < 1` is eventually at most `1`.  This is the whole of the asymptotic step, and it is
unconditional.

`dwz63_cofinal_competitorBound_le_degree`: given

* `hbrick` — `|compatibleSet| ≤ slack N · ᾱ_p^N · |T_K|`, and
* `hcount` — `|matchable| · ᾱ_p^N ≤ rslack N · r^N · d N`,

with `slack`, `rslack` subexponential and `r < 1`, there is a cutoff past which
`|matchable| · |compatibleSet| ≤ d · |T_K|`, hence `Vb ≤ d`.  `hcount` is the count lane's rate
comparison: `|matchable α K| = N_α/N_Z` (`PlainFiberCount`'s fibre identity, `PlainZCeiling`),
`d = N_α′/N_X` (`dwz63PlainSharpDegree`, `PlainRate`'s
`dwz63_exp_entropyX_pow_le_loss_mul_dwz63PlainLegCount` with `subexponential_dwz63PlainLossHash`),
and `r = ᾱ_p ᾱ_X / (ᾱ_Z K)` from `GlobalArithmetic`'s atoms for `H_X`, `H_Z`, `log ᾱ_p` and the
rational `K`.

## STOP: the brick that is not available

`hbrick` is **not** derivable from anything committed.  It is `Dwz63CompatibleFractionUpper`, and
it is precisely the upper half of the statement `Analysis/CompatibilityRate.lean` records as its
non-goal:

> The asymptotic statement `p_comp = ᾱ_p^{n + o(n)}` is likewise not proved here: the
> zero-tolerant method-of-types estimates that it needs (a compatibility profile has structurally
> zero rows at every interior component) are not available in the layer this module may import.

The exact inequality needed, division-free and with the slack explicit, is

`∀ N, ∀ K, ∀ comp₀ ∈ S.matchable αType K,`
`    (|S.compatibleSet comp₀| : ℝ) ≤ slack N · ᾱ_p ^ N · (|S.typicalSet K| : ℝ)`

for some `slack` with `Growth.Subexponential slack`, where `ᾱ_p = Real.exp dwz63LogCompat`.  Only
the **upper** bound is needed — the matching lower bound of `p_comp = ᾱ_p^{n+o(n)}` is not used
anywhere here — and the slack may be as generous as any subexponential function, because
`dwz63_eventually_subexponential_mul_pow_le_one` absorbs it against `r^n` with the margin above.
The target is not weakened: with this brick, `hVdeg` holds cofinally and
`Examples/DuanWuZhouLevelTwoJointHashBranch.lean`'s `dwz63_jointHashBranch` applies past the
cutoff.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.2 (`global_value.tex`), `lemma:pcomp_g`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor ProgressionHash CompatibleSplit
open scoped BigOperators

universe u v w

/-! ## The asymptotic step, unconditional -/

/-- **A subexponential factor is eventually beaten by any `r ^ n` with `r < 1`.** -/
theorem dwz63_eventually_subexponential_mul_pow_le_one {slack : ℕ → ℝ} {r : ℝ}
    (hs : Growth.Subexponential slack) (hr0 : 0 ≤ r) (hr : r < 1) :
    ∃ cutoff : ℕ, ∀ n : ℕ, cutoff ≤ n → slack n * r ^ n ≤ 1 := by
  rcases eq_or_lt_of_le hr0 with hzero | hpos
  · refine ⟨1, fun n hn ↦ ?_⟩
    have hrn : r ^ n = 0 := by
      rw [← hzero]
      exact zero_pow (by omega)
    rw [hrn, mul_zero]
    norm_num
  · have hrne : r ≠ 0 := ne_of_gt hpos
    have hinv : 1 < 1 / r := by
      rw [lt_div_iff₀ hpos]
      linarith
    have hδ1 : 1 < (1 + 1 / r) / 2 := by linarith
    obtain ⟨cutoff, hcutoff⟩ := hs.eventually_le_pow hδ1
    refine ⟨cutoff, fun n hn ↦ ?_⟩
    have hδr : (1 + 1 / r) / 2 * r = (1 + r) / 2 := by
      field_simp
      ring
    have hq0 : (0 : ℝ) ≤ (1 + r) / 2 := by linarith
    have hq1 : (1 + r) / 2 ≤ 1 := by linarith
    calc slack n * r ^ n ≤ ((1 + 1 / r) / 2) ^ n * r ^ n :=
          mul_le_mul_of_nonneg_right (hcutoff n hn) (pow_nonneg hr0 n)
      _ = ((1 + 1 / r) / 2 * r) ^ n := (mul_pow _ _ n).symm
      _ = ((1 + r) / 2) ^ n := by rw [hδr]
      _ ≤ 1 := pow_le_one₀ hq0 hq1

/-! ## The named brick -/

section Brick

variable {C : Type u} [Fintype C] [DecidableEq C]
variable {L : Type v} [Fintype L] [DecidableEq L]
variable {Z : Type w} [Fintype Z] [DecidableEq Z]

/-- **The missing brick**: the upper half of `p_comp = ᾱ_p^{n + o(n)}`, division-free, with an
explicit subexponential slack.  See the module docstring; this is stated, never assumed. -/
def Dwz63CompatibleFractionUpper (S : SplitRequirements C L Z) (αType : C → ℕ)
    (rate : ℝ) (slack : ℕ → ℝ) : Prop :=
  ∀ (N : ℕ) (K : Fin N → Z) (comp₀ : Fin N → C), comp₀ ∈ S.matchable αType K →
    ((S.compatibleSet comp₀).card : ℝ) ≤ slack N * rate ^ N * ((S.typicalSet K).card : ℝ)

end Brick

/-! ## The cofinal statement, from the brick and the count-side rate comparison -/

/-- **`hVdeg`, cofinally.**

The product inequality that `dwz63_competitorBound_le_iff` turns into `Vb ≤ d`, from the two rate
inputs.  `hbrick` is the brick above; `hcount` is the count lane's comparison. -/
theorem dwz63_cofinal_competitorBound_le_degree
    {matchCard compatCard typCard degree : ℕ → ℕ} {rate ratio : ℝ} {slack rslack : ℕ → ℝ}
    (hslack : Growth.Subexponential slack) (hrslack : Growth.Subexponential rslack)
    (hratio0 : 0 ≤ ratio) (hratio : ratio < 1)
    (hbrick : ∀ N, (compatCard N : ℝ) ≤ slack N * rate ^ N * (typCard N : ℝ))
    (hcount : ∀ N, (matchCard N : ℝ) * rate ^ N ≤ rslack N * ratio ^ N * (degree N : ℝ)) :
    ∃ cutoff : ℕ, ∀ N : ℕ, cutoff ≤ N →
      matchCard N * compatCard N ≤ degree N * typCard N := by
  obtain ⟨cutoff, hcut⟩ :=
    dwz63_eventually_subexponential_mul_pow_le_one (hslack.mul hrslack) hratio0 hratio
  refine ⟨cutoff, fun N hN ↦ ?_⟩
  have hM : (0 : ℝ) ≤ (matchCard N : ℝ) := Nat.cast_nonneg _
  have hT : (0 : ℝ) ≤ (typCard N : ℝ) := Nat.cast_nonneg _
  have hD : (0 : ℝ) ≤ (degree N : ℝ) := Nat.cast_nonneg _
  have hs : (0 : ℝ) ≤ slack N := hslack.nonneg N
  have hrs : (0 : ℝ) ≤ rslack N := hrslack.nonneg N
  have hstep : ((matchCard N : ℝ)) * (compatCard N : ℝ) ≤ (degree N : ℝ) * (typCard N : ℝ) := by
    calc (matchCard N : ℝ) * (compatCard N : ℝ)
        ≤ (matchCard N : ℝ) * (slack N * rate ^ N * (typCard N : ℝ)) :=
          mul_le_mul_of_nonneg_left (hbrick N) hM
      _ = ((matchCard N : ℝ) * rate ^ N) * (slack N * (typCard N : ℝ)) := by ring
      _ ≤ (rslack N * ratio ^ N * (degree N : ℝ)) * (slack N * (typCard N : ℝ)) :=
          mul_le_mul_of_nonneg_right (hcount N) (by positivity)
      _ = (slack N * rslack N * ratio ^ N) * ((degree N : ℝ) * (typCard N : ℝ)) := by ring
      _ ≤ 1 * ((degree N : ℝ) * (typCard N : ℝ)) :=
          mul_le_mul_of_nonneg_right (hcut N hN) (by positivity)
      _ = (degree N : ℝ) * (typCard N : ℝ) := one_mul _
  exact_mod_cast hstep

end AlgebraicComplexity.Examples
