/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainMarkedBranch

set_option autoImplicit false

/-!
# `hbranch` at a field large enough for **both** branches of `M₀`

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoSeedInputs.lean` needs
`256 · V ≤ 3 · |R|`, i.e. `|R| ≥ 86 · V` with `V = N_α · p_comp / N_Z`, while
`Examples/DuanWuZhouLevelTwoSharpDegree.lean`'s `dwz63SharpHashModulus degree` is sized only for
the leg-fibre branch `8 · degree ≤ |R|`.  This module sizes the field for both.

## Why the two branches cannot be merged by an inequality

`[DuanWuZhou2022]`'s `M₀ = 8 · max(N_triple/N_X, N_α p_comp/N_Z)` has two branches, and at the
section 6.3 optimum they are **balanced**: with the committed rates
(`Examples/DuanWuZhouLevelTwoGlobalArithmetic.lean`)

`H_e(α_X) = 1.08917435…`,  `H_e(α_Z) = 1.07961152…`,  `log ᾱ_p = −0.00956294…`,
`log K = 1.0000…·10⁻¹⁰`,

the branch-1-binds margin is

`H_e(α_X) − H_e(α_Z) + log ᾱ_p − log K = −1.1215 · 10⁻⁷`  per symbol,

so the per-symbol ratio of branch 2 to branch 1 is `r = 0.99999989`.  Even ignoring every `2^{o(n)}`
factor, `86 · r^n ≤ 8` needs `n ≥ 2.1 · 10⁷`; and the `o(n)` terms are exactly the ones
`Analysis/CompatibilityRate.lean` records as a non-goal (`p_comp = ᾱ_p^{n+o(n)}`), so they are not
available to be beaten.  **Route (i) — deriving `86 V ≤ 8 · degree` past a cutoff from the rate
comparison — does not close.**  What follows is route (ii).

## The joint field, with no new field machinery

`dwz63SharpHashModulus` is already a function of its degree argument, so the joint field is the
*same* construction at a larger argument:

`dwz63JointHashDegree K n t Vb = max (dwz63PlainSharpDegree K n t) (11 · Vb)`.

Every committed fact — `dwz63SharpHashModulus_char_floor`, `_requirement`, `_le`, `_fact_prime`,
`_neZero`, and the field `dwz63SharpHashField` — applies verbatim at that argument.  The two
requirements are `dwz63_jointHashModulus_degree` (`8 · d ≤ |R|`, the leg-fibre branch) and
`dwz63_jointHashModulus_competitor` (`86 · Vb ≤ |R|`, hence
`dwz63_jointHashModulus_seedSelection`'s `256 · Vb ≤ 3 · |R|`, which is exactly the `hmodulus`
binder of `dwz63_exists_seed_aggregateHoleFraction`).

## `hbranch` re-proved, without touching image 54

`Examples/DuanWuZhouLevelTwoPlainMarkedBranch.lean` is **not edited**: its proof is generalized by
new theorems here, each carrying the degree `D` and the count constant `c` of
`N_X · D ≤ c · N_α'` as parameters.  At `D = dwz63PlainSharpDegree K n t` and `c = 2` the loss
constant `125008 + 64 c` is the committed `125136`, so `dwz63_hashBranch_atDegree` is
`dwz63_plainHashBranch` with the degree freed; at `D = dwz63JointHashDegree K n t Vb` and `c = 22`
it is the joint statement.

## The constant factor, explicitly

`N_X · D ≤ c · N_α'` at the joint degree needs `11 · Vb ≤ 11 · d`, i.e. the branch-1-binds
inequality `Vb ≤ d` — carried here as the hypothesis `hVdeg`, since it is a *rate* fact whose
finite form belongs to the count lane.  Under it `D ≤ 11 d`, so `c = 22` and:

* the field grows by at most `86/8 = 10.75` over image 54's;
* the loss constant grows from `125136` to `126416`, a factor `1.0102`;
* the retained count `E[N_ret] = N_α/M` falls by at most the same `10.75`.

Both are constants; the subexponential `loss` of the endpoint absorbs them, and
`dwz63_subexponential_comp_of_le_self` is the committed lemma that re-derives subexponentiality of
the enlarged Behrend factor from `D ≤ 11 · d` (that bookkeeping is the count lane's).

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.2 (`global_value.tex`), §2.9 (`hashing.tex`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity
open scoped BigOperators

universe u v

/-! ## The cancellation, with the degree freed -/

set_option maxRecDepth 8000 in
/-- **`N_X · retentionLoss D ≤ (125008 + 64 c) · Behrend D · N_α'`.**

`dwz63_plainLegCount_mul_retentionLoss_le` with the degree and the count constant as parameters.
At `D = dwz63PlainSharpDegree K n t`, `c = 2` the constant is the committed `125136`. -/
theorem dwz63_legCount_mul_retentionLoss_le_atDegree (K : Type u) [CommRing K] {n t : ℕ}
    (hn : n + 1 = 100000000 * t) (D c : ℕ)
    (hD : dwz63PlainLegCount .X n t * D ≤ c * (dwz63PlainMarginalWords K n t).card) :
    ((dwz63PlainLegCount .X n t : ℕ) : ℝ) * dwz63SharpRetentionLoss D ≤
      ((125008 + 64 * (c : ℝ)) * dwz63SharpBehrendLoss D) *
        (((dwz63PlainMarginalWords K n t).card : ℕ) : ℝ) := by
  have hB : (0 : ℝ) < dwz63SharpBehrendLoss D := dwz63SharpBehrendLoss_pos _
  have hXnn : (0 : ℝ) ≤ ((dwz63PlainLegCount .X n t : ℕ) : ℝ) := Nat.cast_nonneg _
  have hX : ((dwz63PlainLegCount .X n t : ℕ) : ℝ) ≤
      (((dwz63PlainMarginalWords K n t).card : ℕ) : ℝ) := by
    exact_mod_cast dwz63PlainLegCount_le_card_dwz63PlainMarginalWords K .X hn
  have hXd : ((dwz63PlainLegCount .X n t : ℕ) : ℝ) * (D : ℝ) ≤
      (c : ℝ) * (((dwz63PlainMarginalWords K n t).card : ℕ) : ℝ) := by
    exact_mod_cast hD
  unfold dwz63SharpRetentionLoss dwz63SharpModulusLoss
  nlinarith [hB, hX, hXd, hXnn]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The branch power against the marginal count, at a free degree.** -/
theorem dwz63_branch_pow_mul_retentionLoss_le_atDegree (K : Type u) [CommRing K] {n t : ℕ}
    (hn : n + 1 = 100000000 * t) (D c : ℕ)
    (hD : dwz63PlainLegCount .X n t * D ≤ c * (dwz63PlainMarginalWords K n t).card) :
    dwz63HashingBranch ^ (n + 1) * dwz63SharpRetentionLoss D ≤
      ((125008 + 64 * (c : ℝ)) * dwz63SharpBehrendLoss D *
          WordType.structuralZeroMultinomialLoss dwz63AlphaX t) *
        (((dwz63PlainMarginalWords K n t).card : ℕ) : ℝ) := by
  have hretPos : (0 : ℝ) < dwz63SharpRetentionLoss D :=
    mul_pos (dwz63SharpModulusLoss_pos _) (dwz63SharpBehrendLoss_pos _)
  have hstir : (0 : ℝ) ≤ WordType.structuralZeroMultinomialLoss dwz63AlphaX t :=
    (WordType.structuralZeroMultinomialLoss_pos dwz63AlphaX t).le
  have hpow := dwz63_plainHashingBranch_pow_le K hn
  have hcanc := dwz63_legCount_mul_retentionLoss_le_atDegree K hn D c hD
  calc dwz63HashingBranch ^ (n + 1) * dwz63SharpRetentionLoss D
      ≤ (WordType.structuralZeroMultinomialLoss dwz63AlphaX t *
            ((dwz63PlainLegCount .X n t : ℕ) : ℝ)) * dwz63SharpRetentionLoss D :=
        mul_le_mul_of_nonneg_right hpow hretPos.le
    _ = WordType.structuralZeroMultinomialLoss dwz63AlphaX t *
          (((dwz63PlainLegCount .X n t : ℕ) : ℝ) * dwz63SharpRetentionLoss D) := by ring
    _ ≤ WordType.structuralZeroMultinomialLoss dwz63AlphaX t *
          (((125008 + 64 * (c : ℝ)) * dwz63SharpBehrendLoss D) *
            (((dwz63PlainMarginalWords K n t).card : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hcanc hstir
    _ = ((125008 + 64 * (c : ℝ)) * dwz63SharpBehrendLoss D *
          WordType.structuralZeroMultinomialLoss dwz63AlphaX t) *
        (((dwz63PlainMarginalWords K n t).card : ℕ) : ℝ) := by ring

/-! ## `hbranch` at a free degree -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`hbranch`, at any degree the count side can certify.**

`dwz63_plainHashBranch` with the degree and the count constant freed; the committed statement is
the case `D = dwz63PlainSharpDegree K n t`, `c = 2`. -/
theorem dwz63_hashBranch_atDegree {R : Type v} [Field R] [Fintype R] (K : Type u) [CommRing K]
    {n t : ℕ} (hn : n + 1 = 100000000 * t) (D c : ℕ)
    (hD : dwz63PlainLegCount .X n t * D ≤ c * (dwz63PlainMarginalWords K n t).card)
    (hcard : Fintype.card R = dwz63SharpHashModulus D)
    (B : Finset R)
    (hB : ((dwz63SharpHashModulus D / 2 : ℕ) : ℝ) *
        Real.exp (-4 * Real.sqrt (Real.log ((dwz63SharpHashModulus D / 2 : ℕ) : ℝ))) ≤
      (B.card : ℝ)) :
    dwz63HashingBranch ^ (n + 1) *
        (4 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ))) ≤
      ((125008 + 64 * (c : ℝ)) * dwz63SharpBehrendLoss D *
          WordType.structuralZeroMultinomialLoss dwz63AlphaX t) *
        (3 * ((dwz63PlainMarginalWords K n t).card : ℝ) * (B.card : ℝ)) := by
  have hMfloor : 15625 ≤ dwz63SharpHashModulus D := dwz63SharpHashModulus_char_floor _
  have hMposNat : 0 < dwz63SharpHashModulus D := by omega
  have hMpos : (0 : ℝ) < (dwz63SharpHashModulus D : ℝ) := by exact_mod_cast hMposNat
  have hUM : (dwz63SharpHashModulus D : ℝ) ≤ 2 * (15625 + 8 * ((D : ℕ) : ℝ) + 1) := by
    have hnat := dwz63SharpHashModulus_le D
    have hcast : ((dwz63SharpHashModulus D : ℕ) : ℝ) ≤ ((2 * (15625 + 8 * D + 1) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at hcast
    linarith
  have hhalf : (dwz63SharpHashModulus D : ℝ) / 3 ≤ ((dwz63SharpHashModulus D / 2 : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    have hnat : dwz63SharpHashModulus D ≤ dwz63SharpHashModulus D / 2 * 3 := by omega
    exact_mod_cast hnat
  have hBehPos : (0 : ℝ) < dwz63SharpBehrendLoss D := dwz63SharpBehrendLoss_pos _
  have hinv : Real.exp (-4 * Real.sqrt (Real.log ((dwz63SharpHashModulus D / 2 : ℕ) : ℝ))) =
      (dwz63SharpBehrendLoss D)⁻¹ := by
    unfold dwz63SharpBehrendLoss
    rw [← Real.exp_neg]
    ring_nf
  have hBc : (dwz63SharpHashModulus D : ℝ) / 3 * (dwz63SharpBehrendLoss D)⁻¹ ≤ (B.card : ℝ) := by
    refine le_trans ?_ hB
    rw [← hinv]
    exact mul_le_mul_of_nonneg_right hhalf (Real.exp_nonneg _)
  have hlossNonneg : (0 : ℝ) ≤ (125008 + 64 * (c : ℝ)) * dwz63SharpBehrendLoss D *
      WordType.structuralZeroMultinomialLoss dwz63AlphaX t := by
    have hc : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
    have hstir : (0 : ℝ) ≤ WordType.structuralZeroMultinomialLoss dwz63AlphaX t :=
      (WordType.structuralZeroMultinomialLoss_pos dwz63AlphaX t).le
    positivity
  have hstep : dwz63HashingBranch ^ (n + 1) *
      (4 * (2 * (15625 + 8 * ((D : ℕ) : ℝ) + 1)) * dwz63SharpBehrendLoss D) ≤
      ((125008 + 64 * (c : ℝ)) * dwz63SharpBehrendLoss D *
          WordType.structuralZeroMultinomialLoss dwz63AlphaX t) *
        (((dwz63PlainMarginalWords K n t).card : ℕ) : ℝ) := by
    have h := dwz63_branch_pow_mul_retentionLoss_le_atDegree K hn D c hD
    unfold dwz63SharpRetentionLoss dwz63SharpModulusLoss at h
    exact h
  rw [hcard]
  exact dwz63_plainHashBranch_arith (pow_nonneg dwz63HashingBranch_pos.le _) hUM hMpos hBehPos
    hlossNonneg (Nat.cast_nonneg _) hBc hstep

/-! ## The joint degree, and the two requirements -/

/-- **The joint hashing degree**: large enough for the leg-fibre branch and for the competitor
branch of `[DuanWuZhou2022]`'s `M₀`. -/
noncomputable def dwz63JointHashDegree (K : Type u) [CommRing K] (n t Vb : ℕ) : ℕ :=
  max (dwz63PlainSharpDegree K n t) (11 * Vb)

/-- **The leg-fibre branch survives.** -/
theorem dwz63_jointHashModulus_degree (K : Type u) [CommRing K] (n t Vb : ℕ) :
    8 * dwz63PlainSharpDegree K n t ≤
      dwz63SharpHashModulus (dwz63JointHashDegree K n t Vb) := by
  have hreq := dwz63SharpHashModulus_requirement (dwz63JointHashDegree K n t Vb)
  have hle : dwz63PlainSharpDegree K n t ≤ dwz63JointHashDegree K n t Vb :=
    Nat.le_max_left _ _
  omega

/-- **The competitor branch: `86 · V ≤ |R|`.** -/
theorem dwz63_jointHashModulus_competitor (K : Type u) [CommRing K] (n t Vb : ℕ) :
    86 * Vb ≤ dwz63SharpHashModulus (dwz63JointHashDegree K n t Vb) := by
  have hreq := dwz63SharpHashModulus_requirement (dwz63JointHashDegree K n t Vb)
  have hle : 11 * Vb ≤ dwz63JointHashDegree K n t Vb := Nat.le_max_right _ _
  omega

/-- **`hmodulus` of `dwz63_exists_seed_aggregateHoleFraction`, at the joint field.** -/
theorem dwz63_jointHashModulus_seedSelection (K : Type u) [CommRing K] (n t Vb : ℕ) :
    256 * Vb ≤ 3 * dwz63SharpHashModulus (dwz63JointHashDegree K n t Vb) := by
  have h := dwz63_jointHashModulus_competitor K n t Vb
  omega

/-- **The joint degree is at most `11 d` when branch 1 binds.** -/
theorem dwz63JointHashDegree_le (K : Type u) [CommRing K] (n t Vb : ℕ)
    (hVdeg : Vb ≤ dwz63PlainSharpDegree K n t) :
    dwz63JointHashDegree K n t Vb ≤ 11 * dwz63PlainSharpDegree K n t := by
  unfold dwz63JointHashDegree
  omega

/-- **The count input at the joint degree**, with `c = 22`. -/
theorem dwz63_legCount_mul_jointHashDegree_le (K : Type u) [CommRing K] {n t : ℕ}
    (hn : n + 1 = 100000000 * t) (Vb : ℕ) (hVdeg : Vb ≤ dwz63PlainSharpDegree K n t) :
    dwz63PlainLegCount .X n t * dwz63JointHashDegree K n t Vb ≤
      22 * (dwz63PlainMarginalWords K n t).card := by
  have hsharp := dwz63PlainLegCount_mul_plainSharpDegree_le K hn
  have hle := dwz63JointHashDegree_le K n t Vb hVdeg
  calc dwz63PlainLegCount .X n t * dwz63JointHashDegree K n t Vb
      ≤ dwz63PlainLegCount .X n t * (11 * dwz63PlainSharpDegree K n t) :=
        Nat.mul_le_mul_left _ hle
    _ = 11 * (dwz63PlainLegCount .X n t * dwz63PlainSharpDegree K n t) := by ring
    _ ≤ 11 * (2 * (dwz63PlainMarginalWords K n t).card) := Nat.mul_le_mul_left _ hsharp
    _ = 22 * (dwz63PlainMarginalWords K n t).card := by ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`hbranch` at the joint field.**

The loss constant is `125008 + 64 · 22 = 126416`, against the committed `125136`: a factor
`1.0102`.  The field is at most `86/8 = 10.75` times image 54's. -/
theorem dwz63_jointHashBranch {R : Type v} [Field R] [Fintype R] (K : Type u) [CommRing K]
    {n t : ℕ} (hn : n + 1 = 100000000 * t) (Vb : ℕ)
    (hVdeg : Vb ≤ dwz63PlainSharpDegree K n t)
    (hcard : Fintype.card R = dwz63SharpHashModulus (dwz63JointHashDegree K n t Vb))
    (B : Finset R)
    (hB : ((dwz63SharpHashModulus (dwz63JointHashDegree K n t Vb) / 2 : ℕ) : ℝ) *
        Real.exp (-4 * Real.sqrt (Real.log
          ((dwz63SharpHashModulus (dwz63JointHashDegree K n t Vb) / 2 : ℕ) : ℝ))) ≤
      (B.card : ℝ)) :
    dwz63HashingBranch ^ (n + 1) *
        (4 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ))) ≤
      (126416 * dwz63SharpBehrendLoss (dwz63JointHashDegree K n t Vb) *
          WordType.structuralZeroMultinomialLoss dwz63AlphaX t) *
        (3 * ((dwz63PlainMarginalWords K n t).card : ℝ) * (B.card : ℝ)) := by
  have h := dwz63_hashBranch_atDegree K hn (dwz63JointHashDegree K n t Vb) 22
    (dwz63_legCount_mul_jointHashDegree_le K hn Vb hVdeg) hcard B hB
  norm_num at h
  exact h

end AlgebraicComplexity.Examples
