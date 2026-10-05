/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGlobalStage

set_option autoImplicit false

/-!
# The count-side residual at an arbitrary rate

Layer 4 (`AlgebraicComplexity/Examples/`).  `DwzLevelTwoCountingStage`
(`Examples/DuanWuZhouLevelTwoGlobalStage.lean`) hard-wires `dwz63TrueGlobalRate`, so a client whose
leaf value is `exp (dwz63LogVal - ε)` rather than `exp dwz63LogVal` cannot state its residual at
all.  This module is the rate-parameterised form.

## Nothing is generalised except the rate

Reading `dwzLevelTwoAssembledStage_of_countingStage`'s proof, the rate enters in exactly one place:
`hgap`, the strict comparison `globalRate < dwz63TrueGlobalRate` supplied by
`dwz63_globalRate_lt_trueGlobalRate`.  Everything after it --- the subexponential absorption, the
cofinal word length, the rank budget --- is indifferent to which rate was used.  So the
parameterised versions take `hgap : globalRate < r` as a hypothesis and are otherwise the committed
proofs verbatim.

The committed statements are recovered as the instances at `r := dwz63TrueGlobalRate`, one line
each (`dwzLevelTwoCountingStageAt_trueGlobalRate`,
`dwzLevelTwoAssembledStage_of_countingStageAt_true`,
`omega_lt_2374631_of_countingStageAt_true`); the accepted module is not re-issued.

## Why the leaf-value base is a parameter too

`exists_value_of_repairedStage_atRate` is the supplier-side companion: it splits the rate as
`dwz63TrueCopyRate * v` and asks for `v ^ (6 n) ≤ leafValue`, so a lane with a shifted leaf value
produces a residual at the shifted rate without touching the copy-count side.  At
`v := exp dwz63LogVal` it is the committed `exists_value_of_repairedStage_true`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity AsymmetricGlobal Tensor

universe u v

section Reduction

variable {F : Type u} [Field F] {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module F (V c)]

/-- **The count-side residual of section 6.3, at an arbitrary global rate `r`.**  Identical to
`DwzLevelTwoCountingStage` with `dwz63TrueGlobalRate` replaced by `r`. -/
def DwzLevelTwoCountingStageAt (r : ℝ) (T : Tensor3 F V) : Prop :=
  ∃ loss : ℕ → ℝ, Growth.Subexponential loss ∧
    ∀ cutoff : ℕ, ∃ n : ℕ, cutoff ≤ n ∧ 0 < n ∧ ∃ value : ℝ, 0 < value ∧
      HasTauWeight F (Tensor.power (symSix F T) n) dwz63Tau value ∧
      r ^ (6 * n) ≤ loss n * value

/-- The committed residual is the instance at the true global rate. -/
theorem dwzLevelTwoCountingStageAt_trueGlobalRate (T : Tensor3 F V) :
    DwzLevelTwoCountingStageAt dwz63TrueGlobalRate T ↔ DwzLevelTwoCountingStage T := Iff.rfl

/-- **One length-`n` repaired stage at a shifted leaf-value base.**  The rate splits as
`dwz63TrueCopyRate * v`; at `v := exp dwz63LogVal` this is the committed
`exists_value_of_repairedStage_true`. -/
theorem exists_value_of_repairedStage_atRate
    {T : Tensor3 F V} {W : Leg → Type v}
    [∀ c, AddCommMonoid (W c)] [∀ c, Module F (W c)]
    {leaf : Tensor3 F W} {leafValue lossN v : ℝ} (n : ℕ)
    {β : Type v} [Fintype β] [DecidableEq β] (hv : 0 ≤ v)
    (hstage : Restricts (Tensor.power (symSix F T) n)
      (Tensor.indexedDirectSum (V := fun _ : β ↦ W) fun _ ↦ leaf))
    (hleaf : HasTauWeight F leaf dwz63Tau leafValue)
    (hleafValue : 0 < leafValue) (hcards : 0 < Fintype.card β)
    (hcount : dwz63TrueCopyRate ^ (6 * n) ≤ lossN * (Fintype.card β : ℝ))
    (hvalue : v ^ (6 * n) ≤ leafValue) :
    ∃ value : ℝ, 0 < value ∧
      HasTauWeight F (Tensor.power (symSix F T) n) dwz63Tau value ∧
      (dwz63TrueCopyRate * v) ^ (6 * n) ≤ lossN * value := by
  have hcardPos : (0 : ℝ) < (Fintype.card β : ℝ) := by exact_mod_cast hcards
  refine ⟨(Fintype.card β : ℝ) * leafValue, mul_pos hcardPos hleafValue,
    hasTauWeight_of_repairedStage n hstage hleaf, ?_⟩
  have hexpand : (dwz63TrueCopyRate * v) ^ (6 * n) =
      dwz63TrueCopyRate ^ (6 * n) * v ^ (6 * n) := by
    rw [mul_pow]
  rw [hexpand]
  calc dwz63TrueCopyRate ^ (6 * n) * v ^ (6 * n)
      ≤ lossN * (Fintype.card β : ℝ) * leafValue :=
        mul_le_mul hcount hvalue (pow_nonneg hv _)
          ((pow_pos dwz63TrueCopyRate_pos _).le.trans hcount)
    _ = lossN * ((Fintype.card β : ℝ) * leafValue) := by ring

/-- **The count-side residual at rate `r` implies the assembled stage**, given the strict gap
`globalRate < r`.  The committed proof verbatim, with `hgap` a hypothesis instead of
`dwz63_globalRate_lt_trueGlobalRate`. -/
theorem dwzLevelTwoAssembledStage_of_countingStageAt {r : ℝ}
    {T : Tensor3 F V} {ambient : ℝ} (hambient : 0 < ambient)
    (hgap : (dwz63RateData ambient hambient).globalRate < r)
    (hrank : Tensor.asymptoticRank (symSix F T) ≤ 68719476736)
    (hcount : DwzLevelTwoCountingStageAt r T) :
    DwzLevelTwoAssembledStage T (dwz63RateData ambient hambient) := by
  obtain ⟨loss, hloss, hstages⟩ := hcount
  have hglobalPos := (dwz63RateData ambient hambient).globalRate_pos
  have hgap6 : (dwz63RateData ambient hambient).globalRate ^ 6 < r ^ 6 :=
    pow_lt_pow_left₀ hgap hglobalPos.le (by norm_num)
  obtain ⟨cutoff, hcutoff⟩ :=
    exists_cutoff_pow_le_of_pow_le_subexponential_mul hloss (pow_pos hglobalPos 6) hgap6
  obtain ⟨n, hn, hnpos, value, hvaluePos, hweight, hbound⟩ := hstages cutoff
  refine ⟨hrank, n, value, hnpos, hvaluePos, hweight, ?_⟩
  have hpow : ∀ x : ℝ, x ^ (6 * n) = (x ^ 6) ^ n := by
    intro x
    rw [← pow_mul]
  rw [hpow] at hbound ⊢
  exact hcutoff n value hn hvaluePos.le hbound

/-- **`omega < 2.374631` from a count-side residual at rate `r`.** -/
theorem omega_lt_2374631_of_countingStageAt {r : ℝ}
    {T : Tensor3 F V} {ambient : ℝ} (hambient : 0 < ambient)
    (hgap : (dwz63RateData ambient hambient).globalRate < r)
    (hrank : Tensor.asymptoticRank (symSix F T) ≤ 68719476736)
    (hcount : DwzLevelTwoCountingStageAt r T) :
    omega F < (2374631 / 1000000 : ℝ) :=
  omega_lt_2374631_of_dwzLevelTwoAssembledStage hambient
    (dwzLevelTwoAssembledStage_of_countingStageAt hambient hgap hrank hcount)

/-! ## The committed statements, recovered -/

/-- The committed `dwzLevelTwoAssembledStage_of_countingStage`, as the instance at the true global
rate. -/
theorem dwzLevelTwoAssembledStage_of_countingStageAt_true
    {T : Tensor3 F V} {ambient : ℝ} (hambient : 0 < ambient)
    (hrank : Tensor.asymptoticRank (symSix F T) ≤ 68719476736)
    (hcount : DwzLevelTwoCountingStage T) :
    DwzLevelTwoAssembledStage T (dwz63RateData ambient hambient) :=
  dwzLevelTwoAssembledStage_of_countingStageAt hambient
    (dwz63_globalRate_lt_trueGlobalRate ambient hambient) hrank
    ((dwzLevelTwoCountingStageAt_trueGlobalRate T).mpr hcount)

/-- The committed `omega_lt_2374631_of_countingStage`, as the instance at the true global rate. -/
theorem omega_lt_2374631_of_countingStageAt_true
    {T : Tensor3 F V} {ambient : ℝ} (hambient : 0 < ambient)
    (hrank : Tensor.asymptoticRank (symSix F T) ≤ 68719476736)
    (hcount : DwzLevelTwoCountingStage T) :
    omega F < (2374631 / 1000000 : ℝ) :=
  omega_lt_2374631_of_countingStageAt hambient
    (dwz63_globalRate_lt_trueGlobalRate ambient hambient) hrank
    ((dwzLevelTwoCountingStageAt_trueGlobalRate T).mpr hcount)

end Reduction

/-! ## At the level-two source -/

/-- **`omega < 2.374631` at `[duan2023faster]`'s level-two source, from a residual at rate `r`.**
The rank budget is discharged; the only numeric input is `hgap`. -/
theorem omega_lt_2374631_of_dwz63CountingStageAt {F : Type u} [Field F] {r : ℝ}
    (hgap : (dwz63RateData 1 one_pos).globalRate < r)
    (hcount : DwzLevelTwoCountingStageAt r (dwz63Source F)) :
    omega F < (2374631 / 1000000 : ℝ) :=
  omega_lt_2374631_of_countingStageAt (T := dwz63Source F) (ambient := 1) one_pos hgap
    (dwz63_asymptoticRank_symSix_le F) hcount

end AlgebraicComplexity.Examples
