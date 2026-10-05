/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoInstanceData
import AlgebraicComplexity.MatrixMultiplication.RestrictedSplittingValue

/-!
# Exponent bookkeeping between the stage length, the `10 ^ 8` mass, and `6 n`

Layer 4 (`AlgebraicComplexity/Examples/`).  `MatrixMultiplication/RestrictedSplittingValue.lean`
proves that an `alpha`-typical leaf word of scale `t` carries the weight `base ^ t`, where
`base = ∏_s value s ^ alpha s` is the one-period product, and that the word length is then forced:
`(∑ alpha) * t = m + 1`.  At section 6.3 the distribution `dwz63Alpha` has mass exactly `10 ^ 8`,
so the leaf length is `10 ^ 8 * t`.

The endpoint asks for `exp dwz63LogVal ^ (6 n) <= leafValue` at stage length `n`.  Since
`exp dwz63LogVal` is the *per-symbol* rate, the two exponents must be reconciled, and this module
does exactly that.

## The two facts that pin the indices

* `dwz63_one_le_exp_logVal` --- `1 <= exp dwz63LogVal`, from the committed
  `dwz63_valRate_le_exp` and `dwz63ValRate = 21.5356...`.  This is what lets a *longer* leaf word
  only help.
* `dwz63_leafValue_of_base` --- if the values lane supplies one period,
  `exp dwz63LogVal ^ (10 ^ 8) <= base`, then any leaf of length `m + 1 = 10 ^ 8 * t` with
  `6 n <= m + 1` realizes `exp dwz63LogVal ^ (6 n) <= base ^ t`.

The consistent choice is `m + 1 = 6 n`, because the retained constituent of `sym_6(T)^{tensor n}`
is a product of exactly `6 n` component tensors and the leaf cannot be longer than it.  That forces
`10 ^ 8 | 6 n`, i.e. `n` a multiple of `5 * 10 ^ 7`.

## Consequence: the stage family must be cofinal, not total

`Examples/DuanWuZhouLevelTwoStageFamily.lean`'s `dwzLevelTwoCountingStage_of_stageFamily` asks for
a stage at *every* length `m + 1`, which the divisibility above makes impossible to supply.
`DwzLevelTwoCountingStage` only ever needs a cofinal set of lengths, so
`dwzLevelTwoCountingStage_of_cofinalStageFamily` below takes an index map and a cofinality
hypothesis instead.  It supersedes the total form for every client whose lengths are constrained;
the total form remains correct and is the special case `index = (· + 1)`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v

/-! ## The value rate exceeds one -/

/-- `1 <= alphabar_val`.  The committed enclosure `dwz63_valRate_le_exp` bounds
`exp dwz63LogVal` below by the rational `dwz63ValRate = 21.535632886771`, which is above one. -/
theorem dwz63_one_le_exp_logVal : (1 : ℝ) ≤ Real.exp dwz63LogVal :=
  le_trans (by norm_num [dwz63ValRate]) dwz63_valRate_le_exp

/-! ## Reconciling the leaf length with the stage length -/

/-- **The exponent bookkeeping.**

`base` is the one-period product `∏_s value s ^ dwz63Alpha s` supplied by the values lane, and the
leaf word is `dwz63Alpha`-typical at scale `t`, so it has length `10 ^ 8 * t` and weight
`base ^ t`.  Provided that length is at least `6 n`, the endpoint's value inequality holds.

The hypothesis `hbase` is the *only* numerical fact owed by the values lane: one period of the
fifteen-component product dominates `exp dwz63LogVal ^ (10 ^ 8)`.  Everything else here is
monotonicity of `x ^ k` in both arguments. -/
theorem dwz63_leafValue_of_base
    {base : ℝ} (n m t : ℕ)
    (hbase : Real.exp dwz63LogVal ^ (100000000 : ℕ) ≤ base)
    (hlen : 100000000 * t = m + 1)
    (hle : 6 * n ≤ m + 1) :
    Real.exp dwz63LogVal ^ (6 * n) ≤ base ^ t := by
  have hone := dwz63_one_le_exp_logVal
  have hstep : Real.exp dwz63LogVal ^ (6 * n) ≤ Real.exp dwz63LogVal ^ (m + 1) :=
    pow_le_pow_right₀ hone hle
  refine hstep.trans ?_
  have hrewrite : Real.exp dwz63LogVal ^ (m + 1) =
      (Real.exp dwz63LogVal ^ (100000000 : ℕ)) ^ t := by
    rw [← pow_mul, hlen]
  rw [hrewrite]
  exact pow_le_pow_left₀ (by positivity) hbase t

/-! ## The cofinal stage family -/

/-- **The count-side residual from a *cofinal* family of repaired stages.**

`DwzLevelTwoCountingStage` asks only for arbitrarily large lengths, never for all of them, and the
`10 ^ 8` divisibility of section 6.3's leaf makes the total form of
`dwzLevelTwoCountingStage_of_stageFamily` unusable.  Here the lengths are `index i`, and the only
requirement is that they are unbounded. -/
theorem dwzLevelTwoCountingStage_of_cofinalStageFamily
    {F : Type u} [Field F] {V : Leg → Type v}
    [∀ c, AddCommMonoid (V c)] [∀ c, Module F (V c)] {T : Tensor3 F V}
    {W : ℕ → Leg → Type v}
    [∀ i c, AddCommMonoid (W i c)] [∀ i c, Module F (W i c)]
    {β : ℕ → Type v} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (index : ℕ → ℕ) (leaf : ∀ i, Tensor3 F (W i)) (leafValue loss : ℕ → ℝ)
    (hloss : Growth.Subexponential loss)
    (hcofinal : ∀ cutoff : ℕ, ∃ i : ℕ, cutoff ≤ index i ∧ 0 < index i)
    (hstage : ∀ i : ℕ, Restricts (Tensor.power (symSix F T) (index i))
      (Tensor.indexedDirectSum (V := fun _ : β i ↦ W i) fun _ ↦ leaf i))
    (hleaf : ∀ i : ℕ, HasTauWeight F (leaf i) dwz63Tau (leafValue i))
    (hleafValue : ∀ i : ℕ, 0 < leafValue i)
    (hcards : ∀ i : ℕ, 0 < Fintype.card (β i))
    (hcount : ∀ i : ℕ,
      dwz63TrueCopyRate ^ (6 * index i) ≤ loss (index i) * (Fintype.card (β i) : ℝ))
    (hvalue : ∀ i : ℕ, Real.exp dwz63LogVal ^ (6 * index i) ≤ leafValue i) :
    DwzLevelTwoCountingStage T := by
  refine ⟨loss, hloss, fun cutoff ↦ ?_⟩
  obtain ⟨i, hi, hpos⟩ := hcofinal cutoff
  exact ⟨index i, hi, hpos,
    exists_value_of_repairedStage_true (index i) (hstage i) (hleaf i) (hleafValue i)
      (hcards i) (hcount i) (hvalue i)⟩

/-- **`omega < 2.374631` from a cofinal stage family at the concrete engine leaf.**  This is the
form the lanes should target: the lengths are `index i`, the leaf is `dwz63EngineLeaf`, and the
value obligation is the bookkeeping-reconciled one. -/
theorem omega_lt_2374631_of_dwz63CofinalEngineData
    {F : Type u} [Field F] (index m k : ℕ → ℕ) (leafValue loss : ℕ → ℝ)
    {β : ℕ → Type u} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (hloss : Growth.Subexponential loss)
    (hcofinal : ∀ cutoff : ℕ, ∃ i : ℕ, cutoff ≤ index i ∧ 0 < index i)
    (hstage : ∀ i : ℕ, Restricts (Tensor.power (symSix F (dwz63Source F)) (index i))
      (Tensor.indexedDirectSum (V := fun _ : β i ↦ _) fun _ ↦ dwz63EngineLeaf F (m i) (k i)))
    (hleaf : ∀ i : ℕ,
      HasTauWeight F (dwz63EngineLeaf F (m i) (k i)) dwz63Tau (leafValue i))
    (hleafValue : ∀ i : ℕ, 0 < leafValue i)
    (hcards : ∀ i : ℕ, 0 < Fintype.card (β i))
    (hcount : ∀ i : ℕ,
      dwz63TrueCopyRate ^ (6 * index i) ≤ loss (index i) * (Fintype.card (β i) : ℝ))
    (hvalue : ∀ i : ℕ, Real.exp dwz63LogVal ^ (6 * index i) ≤ leafValue i) :
    omega F < (2374631 / 1000000 : ℝ) :=
  omega_lt_2374631_of_dwz63CountingStage
    (dwzLevelTwoCountingStage_of_cofinalStageFamily index
      (fun i ↦ dwz63EngineLeaf F (m i) (k i)) leafValue loss hloss hcofinal hstage
      hleaf hleafValue hcards hcount hvalue)

end AlgebraicComplexity.Examples
