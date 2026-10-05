/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoEntropyAlphaLower
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainLegFibreGrowth
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainFiberCount

set_option autoImplicit false

/-!
# The sharp degree is eventually at least eleven

Layer 4 (`AlgebraicComplexity/Examples/`).  `[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:132-133, 137`: the modulus `M_0` is built from
`N_triple/N_X`, and the tree's transcription of that ratio is
`dwz63PlainSharpDegree = ⌊N_triple/N_X⌋ + 1`.  This module shows it eventually exceeds the
constant
`11` that the modulus branch of `Examples/DuanWuZhouLevelTwoPlainModulusBranch.lean` carries.

The argument is the paper's own `N_α = 2^{n H(α) + o(n)}` against `N_X = 2^{n H(α_X) + o(n)}`
(`:132-133`) in finite form: the committed
`dwz63_plainXBase_pow_le_loss_mul_card_sourceWordLegFiber`
(`Examples/DuanWuZhouLevelTwoPlainLegFibreGrowth.lean:131`) gives
`(ᾱ_α/ᾱ_X)^{n+1} ≤ loss(α,t) · #fibre`, the base exceeds one by `dwz63_one_lt_plainXBase`,
and the
multinomial loss is subexponential.  An exponential eventually beats a subexponential by any
constant factor, so the fibre — and hence the sharp degree, which dominates it — is eventually
at
least `11`.

**The leg-target binder is guarded by `0 < t`.**  `dwz63PlainLegTargets Leg.X n 0` is empty for
every `n` (a word of length `n + 1` cannot have the all-zero type), so an unguarded
`∀ t, xword t ∈ dwz63PlainLegTargets …` would be unsatisfiable and the theorem uninstantiable.
The proof only ever reads the witness past its own cutoff, which is at least `1`.

**Disclosed shape.**  The conclusion is *cofinal*: `∃ cutoff, ∀ t ≥ cutoff, …`.  That is
what the
growth argument gives; the paper's own statements at `:132-133` are likewise asymptotic
(`2^{o(n)}`).  A client needing the universal form must thread this cutoff.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:132-133, 137`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u

/-- **The sharp degree is eventually at least eleven** (`global_value.tex:132-133, 137`).

Proof sketch: pick `δ` strictly between `1` and `b := (ᾱ_α/ᾱ_X)^{10^8}`, take the
subexponential
constant `C` for `δ`, and let `r := b/δ > 1`.  Past the point where `r^t` exceeds `11·C`, the
committed fibre bound `b^t ≤ loss(α,t) · #fibre` gives `11 · loss ≤ b^t ≤ loss · #fibre`,
so
`11 ≤ #fibre`; and `card_sourceWordLegFiber_le_sharpDegree` bounds the fibre by the sharp
degree. -/
theorem dwz63_cofinal_eleven_le_plainSharpDegree (K : Type u) [CommRing K]
    (len : ℕ → ℕ) (hlen : ∀ t : ℕ, 0 < t → len t + 1 = 100000000 * t)
    (xword : ∀ t : ℕ, 0 < t → PositiveWord (Fin 5) (len t))
    (hxword : ∀ (t : ℕ) (ht : 0 < t), xword t ht ∈ dwz63PlainLegTargets Leg.X (len t) t) :
    ∃ cutoff : ℕ, ∀ t : ℕ, cutoff ≤ t → 11 ≤ dwz63PlainSharpDegree K (len t) t := by
  classical
  obtain ⟨hlossNonneg, hlossBound⟩ :=
    WordType.structuralZeroMultinomialLoss_subexponential dwz63PlainAlpha
  have h1 : (1 : ℝ) < dwz63PlainRateAlpha / Real.exp dwz63EntropyX := dwz63_one_lt_plainXBase
  set b : ℝ := (dwz63PlainRateAlpha / Real.exp dwz63EntropyX) ^ (100000000 : ℕ) with hbdef
  have hb1 : (1 : ℝ) < b := by
    rw [hbdef]
    exact one_lt_pow₀ h1 (by norm_num)
  set d : ℝ := (1 + b) / 2 with hddef
  have hd1 : (1 : ℝ) < d := by rw [hddef]; linarith
  have hdb : d < b := by rw [hddef]; linarith
  have hdpos : (0 : ℝ) < d := by linarith
  obtain ⟨C, hC, hCle⟩ := hlossBound d hd1
  set r : ℝ := b / d with hrdef
  have hr1 : (1 : ℝ) < r := (one_lt_div hdpos).mpr hdb
  have hrd : r * d = b := by
    rw [hrdef]
    field_simp
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt hr1).eventually_ge_atTop (11 * C))
  refine ⟨max t₀ 1, fun t ht ↦ ?_⟩
  have htpos : 0 < t := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right t₀ 1) ht)
  have hpow : 11 * C ≤ r ^ t := ht₀ t (le_trans (le_max_left t₀ 1) ht)
  have hmass : WordType.profileMass dwz63PlainAlpha * t = len t + 1 := by
    rw [profileMass_dwz63PlainAlpha, hlen t htpos]
  have hbound := dwz63_plainXBase_pow_le_loss_mul_card_sourceWordLegFiber K htpos hmass
    (hxword t htpos)
  have hbt : (dwz63PlainRateAlpha / Real.exp dwz63EntropyX) ^ (len t + 1) = b ^ t := by
    rw [hbdef, ← pow_mul, ← hlen t htpos]
  rw [hbt] at hbound
  set L : ℝ := WordType.structuralZeroMultinomialLoss dwz63PlainAlpha t with hLdef
  have hLpos : 0 < L := WordType.structuralZeroMultinomialLoss_pos dwz63PlainAlpha t
  have hdt : (0 : ℝ) < d ^ t := pow_pos hdpos t
  have hkey : 11 * L ≤ b ^ t := by
    have h₁ : 11 * L ≤ 11 * (C * d ^ t) := by
      have := hCle t
      rw [← hLdef] at this
      nlinarith [hdt]
    have h₂ : 11 * (C * d ^ t) ≤ r ^ t * d ^ t := by nlinarith [hdt]
    have h₃ : r ^ t * d ^ t = b ^ t := by rw [← mul_pow, hrd]
    linarith
  have hfib : (11 : ℝ) ≤
      ((PartitionHashEncoding.sourceWordLegFiber (len t)
        (dwz63PlainMarginalWords K (len t) t) Leg.X (xword t htpos)).card : ℝ) := by
    have hmul : 11 * L ≤ L * ((PartitionHashEncoding.sourceWordLegFiber (len t)
        (dwz63PlainMarginalWords K (len t) t) Leg.X (xword t htpos)).card : ℝ) :=
      le_trans hkey hbound
    nlinarith [hLpos]
  have hnat : 11 ≤ (PartitionHashEncoding.sourceWordLegFiber (len t)
      (dwz63PlainMarginalWords K (len t) t) Leg.X (xword t htpos)).card := by
    exact_mod_cast hfib
  exact le_trans hnat
    (card_sourceWordLegFiber_le_sharpDegree K Leg.X (hlen t htpos) (hxword t htpos))

end AlgebraicComplexity.Examples
