/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainLegFibreGrowth
import AlgebraicComplexity.Analysis.Subexponential

set_option autoImplicit false

/-!
# `hupper` and `hlower` in the binder shape `dwz63_hcount_of_rate` consumes

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoCountComparison.lean`'s
`dwz63_hcount_of_rate` takes its two inputs as **unconditional** `∀ N` statements over abstract
families `matchCard, fibreCard : ℕ → ℕ` and abstract per-index rates.  The section 6.3 counts,
by
contrast, exist only at the word lengths `n + 1 = 10 ^ 8 · t` forced by
`proportionalCounts dwz63PlainAlpha t`.  This module reconciles the two, and the reconciliation is
a change of index: the free index `N` of `dwz63_hcount_of_rate` counts *groups* of `blocks` blocks,
the word length is `dwz63PlainCountDepth blocks N + 1 = 10 ^ 8 · blocks · (N + 1)`, and the rates
are the per-group rates `ᾱ ^ (10 ^ 8 · blocks)`.

Two design points, both forced:

* **The index cannot be the word length.**  `hlower` is a *lower* bound with a base above one, so
  it fails at every length where the fibre is empty — that is, at every `N` off the lattice.  Only
  a lattice index gives an unconditional `∀ N`.
* **The group size stays free.**  Different inputs of
  `dwz63_cofinal_competitorBound_le_degree` live on different lattices — the compatibility brick
  has content only where `matchable` is nonempty, i.e. at the split profile's own mass — so the
  two
  must be lined up on a common refinement.  Leaving `blocks` a parameter is what makes that
  possible without restating anything: take `blocks` to be the ratio of the two masses.

Indexing by `N + 1` groups rather than by `N` is what makes the two statements *unconditional*:
`t = 0` is not a legal block count (`n + 1 = 0` has no solution in `ℕ`), and the leading group's
worth of rate is absorbed into the subexponential slacks — `dwz63PlainCountSu` multiplies by one
group of `(ᾱ_α / ᾱ_Z) ^ (10 ^ 8 · blocks)`, `dwz63PlainCountSl` divides by one group of
`(ᾱ_α / ᾱ_X) ^ (10 ^ 8 · blocks)`.  Both are fixed positive constants, so both slacks stay
subexponential (`dwz63_subexponential_comp_mul` plus `Growth.Subexponential.const_mul`), which is
all `dwz63_cofinal_competitorBound_le_degree` asks of them.

## The two families are parametrised, not chosen

`hupper` is uniform in the large `Z`-block `K` and `hlower` is uniform in the `X`-leg target word,
so neither statement can name a single witness.  Both are therefore stated over an arbitrary
*family* of witnesses of the correct type — `Kword` of the `Z` marginal type, `xword` in
`dwz63PlainLegTargets .X` — which is how a client supplies them: the retained triple at length `n`
supplies its own `Z`-block word and its own `X`-block word.

## `hashK`

`dwz63_hcount_of_rate`'s `hashK` is a free positive real, and `dwz63_hlower` is proved for every
`0 < hashK ≤ 1`.  The case `hashK = 1` is the one that composes; see the module docstring of
`Examples/DuanWuZhouLevelTwoPlainLegFibreGrowth.lean` for why the hash-loss multiplier
`K = 1 + 10⁻¹⁰` cannot be carried on this side, and why its absence is harmless against the
branch-1-binds margin.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.2 (`global_value.tex`), §6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

open scoped BigOperators

universe u

/-! ## The group-indexed word length -/

/-- **The word depth of the `m`-th plain group family**: `dwz63PlainCountDepth blocks m + 1` is the
`blocks · (m + 1)`-block word length `10 ^ 8 · blocks · (m + 1)`. -/
def dwz63PlainCountDepth (blocks m : ℕ) : ℕ := 100000000 * (blocks * (m + 1)) - 1

theorem dwz63PlainCountDepth_succ {blocks : ℕ} (hb : 0 < blocks) (m : ℕ) :
    dwz63PlainCountDepth blocks m + 1 = 100000000 * (blocks * (m + 1)) := by
  have h1 : 0 < 100000000 * (blocks * (m + 1)) :=
    Nat.mul_pos (by norm_num) (Nat.mul_pos hb (Nat.succ_pos m))
  show 100000000 * (blocks * (m + 1)) - 1 + 1 = 100000000 * (blocks * (m + 1))
  omega

theorem dwz63_plainCountDepth_length {blocks : ℕ} (hb : 0 < blocks) (m : ℕ) :
    WordType.profileMass dwz63PlainAlpha * (blocks * (m + 1)) =
      dwz63PlainCountDepth blocks m + 1 := by
  rw [profileMass_dwz63PlainAlpha, dwz63PlainCountDepth_succ hb]

/-! ## The per-group rates -/

/-- `ᾱ_α ^ (10 ^ 8 · blocks)`, the per-group joint rate. -/
noncomputable def dwz63PlainBlockRateAlpha (blocks : ℕ) : ℝ :=
  dwz63PlainRateAlpha ^ (100000000 * blocks)

/-- `ᾱ_X ^ (10 ^ 8 · blocks)`, the per-group `X` marginal rate. -/
noncomputable def dwz63PlainBlockRateX (blocks : ℕ) : ℝ :=
  Real.exp dwz63EntropyX ^ (100000000 * blocks)

/-- `ᾱ_Z ^ (10 ^ 8 · blocks)`, the per-group `Z` marginal rate. -/
noncomputable def dwz63PlainBlockRateZ (blocks : ℕ) : ℝ :=
  Real.exp dwz63EntropyZ ^ (100000000 * blocks)

theorem dwz63_plainXBase_pos : (0 : ℝ) < dwz63PlainRateAlpha / Real.exp dwz63EntropyX :=
  div_pos dwz63PlainRateAlpha_pos (Real.exp_pos _)

theorem dwz63_plainZBase_pos : (0 : ℝ) < dwz63PlainRateAlpha / Real.exp dwz63EntropyZ :=
  div_pos dwz63PlainRateAlpha_pos (Real.exp_pos _)

theorem dwz63PlainBlockRateAlpha_pos (blocks : ℕ) :
    (0 : ℝ) < dwz63PlainBlockRateAlpha blocks := by
  show (0 : ℝ) < dwz63PlainRateAlpha ^ (100000000 * blocks)
  exact pow_pos dwz63PlainRateAlpha_pos _

theorem dwz63PlainBlockRateX_pos (blocks : ℕ) : (0 : ℝ) < dwz63PlainBlockRateX blocks := by
  show (0 : ℝ) < Real.exp dwz63EntropyX ^ (100000000 * blocks)
  exact pow_pos (Real.exp_pos _) _

theorem dwz63PlainBlockRateZ_pos (blocks : ℕ) : (0 : ℝ) < dwz63PlainBlockRateZ blocks := by
  show (0 : ℝ) < Real.exp dwz63EntropyZ ^ (100000000 * blocks)
  exact pow_pos (Real.exp_pos _) _

/-- The per-group `X` ratio is one group of the per-position ratio. -/
theorem dwz63_plainBlockRatio_X (blocks : ℕ) :
    dwz63PlainBlockRateAlpha blocks / dwz63PlainBlockRateX blocks =
      (dwz63PlainRateAlpha / Real.exp dwz63EntropyX) ^ (100000000 * blocks) := by
  show dwz63PlainRateAlpha ^ (100000000 * blocks) /
    Real.exp dwz63EntropyX ^ (100000000 * blocks) = _
  rw [div_pow]

/-- The per-group `Z` ratio is one group of the per-position ratio. -/
theorem dwz63_plainBlockRatio_Z (blocks : ℕ) :
    dwz63PlainBlockRateAlpha blocks / dwz63PlainBlockRateZ blocks =
      (dwz63PlainRateAlpha / Real.exp dwz63EntropyZ) ^ (100000000 * blocks) := by
  show dwz63PlainRateAlpha ^ (100000000 * blocks) /
    Real.exp dwz63EntropyZ ^ (100000000 * blocks) = _
  rw [div_pow]

/-! ## The two explicit subexponential slacks -/

/-- **`su`**: one group of the `Z` ratio times the rescaled structural-zero loss of the `Z`
marginal. -/
noncomputable def dwz63PlainCountSu (blocks m : ℕ) : ℝ :=
  (dwz63PlainRateAlpha / Real.exp dwz63EntropyZ) ^ (100000000 * blocks) *
    WordType.structuralZeroMultinomialLoss dwz63AlphaZ (blocks * (m + 1))

/-- **`sl`**: the rescaled structural-zero loss of the joint profile, divided by one group of the
`X` ratio. -/
noncomputable def dwz63PlainCountSl (blocks m : ℕ) : ℝ :=
  ((dwz63PlainRateAlpha / Real.exp dwz63EntropyX) ^ (100000000 * blocks))⁻¹ *
    WordType.structuralZeroMultinomialLoss dwz63PlainAlpha (blocks * (m + 1))

/-- **Rescaling the index preserves subexponential growth.**

The comparison base is rescaled by its `c`-th root, `exp (log δ / c)`, which is again above one;
the shift by one group costs one further factor of `δ`. -/
theorem dwz63_subexponential_comp_mul {a : ℕ → ℝ} (ha : Growth.Subexponential a) {c : ℕ}
    (hc : 0 < c) : Growth.Subexponential (fun m ↦ a (c * (m + 1))) := by
  refine ⟨fun m ↦ ha.1 _, ?_⟩
  intro δ hδ
  have hδ0 : (0 : ℝ) < δ := zero_lt_one.trans hδ
  have hlog : 0 < Real.log δ := Real.log_pos hδ
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hx : 0 < Real.log δ / (c : ℝ) := div_pos hlog hcpos
  have hε1 : 1 < Real.exp (Real.log δ / (c : ℝ)) := by
    have hadd := Real.add_one_le_exp (Real.log δ / (c : ℝ))
    linarith
  have hεc : Real.exp (Real.log δ / (c : ℝ)) ^ c = δ := by
    rw [← dwz63_exp_natCast_mul c (Real.log δ / (c : ℝ))]
    rw [mul_div_cancel₀ _ (ne_of_gt hcpos), Real.exp_log hδ0]
  obtain ⟨C, hC, hbound⟩ := ha.2 _ hε1
  refine ⟨C * δ, mul_pos hC hδ0, fun m ↦ ?_⟩
  calc a (c * (m + 1)) ≤ C * Real.exp (Real.log δ / (c : ℝ)) ^ (c * (m + 1)) :=
        hbound (c * (m + 1))
    _ = C * δ ^ (m + 1) := by rw [pow_mul, hεc]
    _ = C * δ * δ ^ m := by rw [pow_succ]; ring

theorem dwz63_subexponential_plainCountSu (blocks : ℕ) (hb : 0 < blocks) :
    Growth.Subexponential (dwz63PlainCountSu blocks) := by
  have hloss := dwz63_subexponential_comp_mul
    (WordType.structuralZeroMultinomialLoss_subexponential dwz63AlphaZ) hb
  have hconst : (0 : ℝ) ≤
      (dwz63PlainRateAlpha / Real.exp dwz63EntropyZ) ^ (100000000 * blocks) :=
    (pow_pos dwz63_plainZBase_pos _).le
  exact hloss.const_mul hconst

theorem dwz63_subexponential_plainCountSl (blocks : ℕ) (hb : 0 < blocks) :
    Growth.Subexponential (dwz63PlainCountSl blocks) := by
  have hloss := dwz63_subexponential_comp_mul
    (WordType.structuralZeroMultinomialLoss_subexponential dwz63PlainAlpha) hb
  have hconst : (0 : ℝ) ≤
      (((dwz63PlainRateAlpha / Real.exp dwz63EntropyX) ^ (100000000 * blocks))⁻¹) :=
    (inv_pos.mpr (pow_pos dwz63_plainXBase_pos _)).le
  exact hloss.const_mul hconst

theorem dwz63_plainCountSu_nonneg (blocks : ℕ) (hb : 0 < blocks) (m : ℕ) :
    0 ≤ dwz63PlainCountSu blocks m :=
  (dwz63_subexponential_plainCountSu blocks hb).nonneg m

theorem dwz63_plainCountSl_nonneg (blocks : ℕ) (hb : 0 < blocks) (m : ℕ) :
    0 ≤ dwz63PlainCountSl blocks m :=
  (dwz63_subexponential_plainCountSl blocks hb).nonneg m

/-! ## `hupper` -/

/-- **`hupper`, in the exact binder shape of `dwz63_hcount_of_rate`.**

`matchCard N` is `|matchable α K|` at the `(N + 1)`-group word length, i.e. the typed word-map
fibre of the `Z` read over the supplied large `Z`-block word `Kword N`.  `matchable αType K` is by
definition `WordType.typedWordMapFiber S.zIndex αType K`, so the left side below **is** that
cardinality once `S.zIndex` is the plain `Z` read. -/
theorem dwz63_hupper (blocks : ℕ) (hb : 0 < blocks)
    (Kword : ∀ m : ℕ, Fin (dwz63PlainCountDepth blocks m + 1) → Fin 5)
    (hKword : ∀ m : ℕ, WordType.multiplicity (Kword m) =
      WordType.proportionalCounts dwz63AlphaZ (blocks * (m + 1))) :
    ∀ N : ℕ,
      ((WordType.typedWordMapFiber (dwz63PlainLegRead .Z)
          (WordType.proportionalCounts dwz63PlainAlpha (blocks * (N + 1)))
            (Kword N)).card : ℝ) ≤
        dwz63PlainCountSu blocks N *
          (dwz63PlainBlockRateAlpha blocks / dwz63PlainBlockRateZ blocks) ^ N := by
  intro m
  have hcore := dwz63_card_typedWordMapFiber_Z_le (t := blocks * (m + 1))
    (Nat.mul_pos hb (Nat.succ_pos m)) (dwz63_plainCountDepth_length hb m) (Kword m) (hKword m)
  refine hcore.trans_eq ?_
  simp only [dwz63PlainCountSu, dwz63_plainBlockRatio_Z, dwz63PlainCountDepth_succ hb]
  rw [show 100000000 * (blocks * (m + 1)) = 100000000 * blocks * m + 100000000 * blocks from by
      ring, pow_add, pow_mul]
  ring

/-! ## `hlower` -/

/-- The arithmetic step behind `hlower`: peel one group off the exponent and pay for it with the
reciprocal of one group of the base. -/
theorem dwz63_pow_le_of_mul_le {b lossValue fibreValue : ℝ} {m : ℕ} (hb : 0 < b)
    (h : b ^ m * b ≤ lossValue * fibreValue) :
    b ^ m ≤ b⁻¹ * lossValue * fibreValue := by
  have hne : b ≠ 0 := ne_of_gt hb
  calc b ^ m = b⁻¹ * (b ^ m * b) := by
        rw [mul_comm (b ^ m) b, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    _ ≤ b⁻¹ * (lossValue * fibreValue) :=
        mul_le_mul_of_nonneg_left h (inv_pos.mpr hb).le
    _ = b⁻¹ * lossValue * fibreValue := by ring

/-- **`hlower`, in the exact binder shape of `dwz63_hcount_of_rate`.**

`fibreCard N` is the `X`-leg fibre of the marginal-typical ambient at the `(N + 1)`-group word
length, over the supplied `X`-leg target word `xword N`.  Proved for every `0 < hashK ≤ 1`; the
composing instance is `hashK = 1`. -/
theorem dwz63_hlower (K : Type u) [CommRing K] (blocks : ℕ) (hb : 0 < blocks)
    (xword : ∀ m : ℕ, PositiveWord (Fin 5) (dwz63PlainCountDepth blocks m))
    (hxword : ∀ m : ℕ, xword m ∈
      dwz63PlainLegTargets .X (dwz63PlainCountDepth blocks m) (blocks * (m + 1)))
    {hashK : ℝ} (hashK0 : 0 < hashK) (hashK1 : hashK ≤ 1) :
    ∀ N : ℕ,
      (hashK * dwz63PlainBlockRateAlpha blocks / dwz63PlainBlockRateX blocks) ^ N ≤
        dwz63PlainCountSl blocks N *
          ((PartitionHashEncoding.sourceWordLegFiber (dwz63PlainCountDepth blocks N)
            (dwz63PlainMarginalWords K (dwz63PlainCountDepth blocks N) (blocks * (N + 1))) .X
              (xword N)).card : ℝ) := by
  intro m
  have hposB : (0 : ℝ) <
      (dwz63PlainRateAlpha / Real.exp dwz63EntropyX) ^ (100000000 * blocks) :=
    pow_pos dwz63_plainXBase_pos _
  have hcore := dwz63_plainXBase_pow_le_loss_mul_card_sourceWordLegFiber K
    (t := blocks * (m + 1)) (Nat.mul_pos hb (Nat.succ_pos m))
    (dwz63_plainCountDepth_length hb m) (hxword m)
  rw [dwz63PlainCountDepth_succ hb,
    show 100000000 * (blocks * (m + 1)) = 100000000 * blocks * m + 100000000 * blocks from by
      ring,
    pow_add, pow_mul] at hcore
  have hleft :
      (hashK * dwz63PlainBlockRateAlpha blocks / dwz63PlainBlockRateX blocks) ^ m ≤
        ((dwz63PlainRateAlpha / Real.exp dwz63EntropyX) ^ (100000000 * blocks)) ^ m := by
    refine pow_le_pow_left₀ ?_ ?_ m
    · exact div_nonneg (mul_nonneg hashK0.le (dwz63PlainBlockRateAlpha_pos blocks).le)
        (dwz63PlainBlockRateX_pos blocks).le
    · rw [mul_div_assoc, dwz63_plainBlockRatio_X]
      calc hashK * (dwz63PlainRateAlpha / Real.exp dwz63EntropyX) ^ (100000000 * blocks)
          ≤ 1 * (dwz63PlainRateAlpha / Real.exp dwz63EntropyX) ^ (100000000 * blocks) :=
            mul_le_mul_of_nonneg_right hashK1 hposB.le
        _ = (dwz63PlainRateAlpha / Real.exp dwz63EntropyX) ^ (100000000 * blocks) := one_mul _
  refine hleft.trans ?_
  show _ ≤ dwz63PlainCountSl blocks m * _
  rw [dwz63PlainCountSl]
  exact dwz63_pow_le_of_mul_le hposB hcore

end AlgebraicComplexity.Examples
