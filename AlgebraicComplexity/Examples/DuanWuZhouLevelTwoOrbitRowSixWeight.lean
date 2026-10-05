/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricMarginalCutImp
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainBatchedEndpointMargin
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSixOrientationValues
import AlgebraicComplexity.MatrixMultiplication.SymSixUniformLeaf

set_option autoImplicit false

/-!
# The `(1,1,2)` orbit row's `sym₃` weight, in the assembly's own binder shape

Layer 4 (`AlgebraicComplexity/Examples/`).  This is the last step of the `(1,1,2)` orbit row:
given a `tau`-weight for the committed symmetric ambient power at the published value, it produces
image 104's `hcut` premise at `eps = 10^(-22)` and then the assembly's `R3` binder at
`eps = dwz63LeafMargin`, for the orbit row `o = 0`.

## The paper

`[duan2023faster]` arXiv:2210.10173, `global_value.tex:341-348` fixes the value being carried:
with `α̃_{1,1,2}(0) = α̃_{1,1,2}(2) = b` and `α̃_{1,1,2}(1) = 1-2b`,
`V^{(3)}_τ(T_{1,1,2}, α̃_{1,1,2}) ≥ (4 / ((1-2b)^{1-2b} b^{2b}))^{1/3} q^{(2-2b)τ}` --- the
number whose logarithm is the committed `dwz112LogValue`, equal to `dwz63LogVal112 =
dwz63OrbitLogVal 0` by `dwz63LogVal112_eq_dwz112LogValue`.  `global_value.tex:270-320` is where that
per-component value enters the global bound: `α_val = ∏ V^{(6)}(T_{i,j,k},
α̃_{i,j,k})^{α(i,j,k)}`, each component contributing at its own `α(i,j,k)` --- for this row
`α(1,1,2) = 0.20088623`, i.e. the committed `dwz63Alpha 6 = 20088623`.  That exponent is exactly
why the assembly asks for the row's weight at index length `2·10⁸ · (dwz63Alpha 6 · s)`.

## The period reconciliation

The `112` chain's own period is `dwz112Mass = (2(L+G))^3 = 8·10^21`, so it reaches index lengths
`n + 1 = dwz112Mass · k`.  The assembly asks for `m + 1 = 2·10^8 · (dwz63Alpha 6 · s)`.  The two
agree exactly at `j = dwz63Alpha 6 · s = 4·10^13 · k`, since `2·10^8 · 4·10^13 = 8·10^21`;
and the assembly's own lattice hypothesis `40000000000000 ∣ s` (image 135,
`DuanWuZhouLevelTwoAssemblyMarkedSeededLoss.lean:59`) is precisely what makes `k` a natural number.

## What is assumed here

The `tau`-weight of the *ambient* power is a hypothesis, not a result of this module.  See the
board entry accompanying this file: the committed `exists_eventually_dwz112LeafHasTauWeight`
carries a weight for the **uncut** power, which is downstream of the ambient weight rather than
upstream of it, so it cannot supply this premise.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex:270-320` (the global value bound) and
`global_value.tex:341-348` (the `b`-split value of `T_{1,1,2}`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- The `(1,1,2)` row's share of the global distribution, `α(1,1,2) = 0.20088623`.  The literal is
read from the parameter table of `global_value.tex:374` (the `(1,1,2)` column of the level-two
result table); `global_value.tex:270-320` is where that share enters the global bound. -/
theorem dwz63_orbitRowSix_alpha : dwz63Alpha (dwz63OrbitRow 0) = 20088623 := by
  decide

/-- **The period reconciliation.**  On the assembly's own lattice `4·10^13 ∣ s`, the orbit row's
index parameter `j = α(1,1,2) · s` is a multiple of the `112` chain's period `4·10^13`. -/
theorem dwz63_orbitRowSix_period (s : ℕ) (hs : 40000000000000 ∣ s) :
    dwz63Alpha (dwz63OrbitRow 0) * s =
      40000000000000 * (20088623 * (s / 40000000000000)) := by
  obtain ⟨c, rfl⟩ := hs
  rw [dwz63_orbitRowSix_alpha]
  rw [Nat.mul_div_cancel_left _ (by norm_num)]
  ring

/-! ## The orbit row's `sym₃` weight from the ambient weight -/

/-- **The `(1,1,2)` orbit region's `sym₃` weight at `eps = 10^(-22)`**, from a `tau`-weight for
the committed symmetric ambient power at the published value.

This is image 104's `hcut` premise for `o = 0`, at the `112` chain's own period: index length
`n + 1 = dwz112Mass · k`, i.e. `n` the leaf's proportional depth.  The value is
`global_value.tex:341-348`'s `V^{(3)}_τ(T_{1,1,2}, α̃_{1,1,2})`, backed off by the round
`10^(-22)` nats of `dwz112_exp_le_leafTerm`.

Proof sketch: the weight travels from the ambient to `sym₃` of the typed cut (image 146's marginal
inclusion inside image 144's endpoint), then to `sym₃` of the leaf's orbit region (image 127 under
`Restricts.symThree_congr`); `HasTauWeight.mono` then inserts the exponential form, the two index
lengths agreeing because `2·10^8 · 4·10^13 = 8·10^21 = dwz112Mass`. -/
theorem dwz63_symThree_orbitRowSix_weight_of_ambient
    (K : Type u) [CommRing K] (hq : 0 < dwz63Q) (p : ℕ) [Fact p.Prime] (hp : 27 ≤ p)
    {M : ℕ} (t₀ : Fin M) (k : ℕ) {value : ℝ}
    (hvalue : HasTauWeight K
      (cw112SymmetricAmbientPartitionedPower K dwz63Q dwz112L dwz112G k p hq
        dwz112L_pos dwz112G_pos hp).realize dwz63Tau value)
    (hlower : Real.exp (dwz112LogValue - 1 / 10 ^ 22) ^ (3 * (dwz112Mass * k)) ≤ value) :
    HasTauWeight K
      (symThree K (dwz63OrbitRegion K dwz63Q 0 t₀
        ((cw112SymmetricPartitionRationalTypedLeaf K dwz63Q dwz112L dwz112G hq
          dwz112L_pos dwz112G_pos).proportionalDepth k)
        (40000000000000 * k)).realize) dwz63Tau
      (Real.exp ((200000000 : ℝ) * ((40000000000000 * k : ℕ) : ℝ)
        * (dwz63OrbitLogVal 0 - 1 / 10 ^ 22)) ^ 3) := by
  have hchain : HasTauWeight K
      (symThree K (dwz63OrbitRegion K dwz63Q 0 t₀
        ((cw112SymmetricPartitionRationalTypedLeaf K dwz63Q dwz112L dwz112G hq
          dwz112L_pos dwz112G_pos).proportionalDepth k) (40000000000000 * k)).realize)
      dwz63Tau value :=
    HasTauWeight.of_restricts
      (Tensor.Restricts.symThree_congr
        (dwz63_orbitRegion_restricts_typedCut K dwz63Q t₀ _ (40000000000000 * k)))
      (HasTauWeight.of_restricts
        (cw112_symThree_typedCut_restricts_symmetricAmbient K dwz63Q dwz112L dwz112G k p hq
          dwz112L_pos dwz112G_pos hp t₀ (40000000000000 * k)
          (fun c v hv ↦ cw112SymmetricKeepMarginal_symThreeKeep K dwz63Q k
            (40000000000000 * k) hq rfl t₀ c v hv))
        hvalue)
  refine hchain.mono (le_trans ?_ hlower)
  have hlog : dwz63OrbitLogVal 0 = dwz112LogValue := dwz63LogVal112_eq_dwz112LogValue
  rw [hlog, dwz112Mass_eq, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  apply le_of_eq
  congr 1
  push_cast
  ring

/-- **The index-length identification.**  On the assembly's lattice, the assembly's index length
`m + 1 = 2·10^8 · (α(1,1,2) · s)` is exactly the `112` chain's `dwz112Mass · k` at
`k = α(1,1,2) · s / 4·10^13`, so `m` is the leaf's proportional depth. -/
theorem dwz63_orbitRowSix_depth
    (K : Type u) [CommRing K] (hq : 0 < dwz63Q) (s : ℕ) (hs : 40000000000000 ∣ s)
    (hspos : 0 < 20088623 * (s / 40000000000000)) (m : ℕ)
    (hm : m + 1 = 200000000 * (dwz63Alpha (dwz63OrbitRow 0) * s)) :
    (cw112SymmetricPartitionRationalTypedLeaf K dwz63Q dwz112L dwz112G hq
      dwz112L_pos dwz112G_pos).proportionalDepth (20088623 * (s / 40000000000000)) = m := by
  have hmass : (cw112SymmetricPartitionRationalTypedLeaf K dwz63Q dwz112L dwz112G hq
      dwz112L_pos dwz112G_pos).profile.mass = dwz112Mass :=
    cw112SymmetricLeaf_profile_mass K dwz63Q dwz112L dwz112G hq dwz112L_pos dwz112G_pos
  have h := RationalTypedLeaf.proportionalDepth_add_one
    (cw112SymmetricPartitionRationalTypedLeaf K dwz63Q dwz112L dwz112G hq
      dwz112L_pos dwz112G_pos) hspos
  rw [hmass] at h
  rw [dwz63_orbitRowSix_period s hs] at hm
  have harith : dwz112Mass * (20088623 * (s / 40000000000000)) =
      200000000 * (40000000000000 * (20088623 * (s / 40000000000000))) := by
    norm_num [dwz112Mass, dwz112L, dwz112G]
    ring
  rw [harith, ← hm] at h
  exact Nat.succ_injective h

/-! ## The assembly's `R3` binder, for `o = 0` -/

/-- **The `R3` premise of the marked/seeded assembly, for the orbit row `o = 0`.**

The conclusion is image 135's `R3` binder
(`DuanWuZhouLevelTwoAssemblyMarkedSeededLoss.lean:67-72`) specialised to `o = 0`, at
`eps = dwz63LeafMargin`.  `hs` is that theorem's own `112` lattice condition (`:59`), and it is
what makes the chain's repetition count `k = α(1,1,2) · s / 4·10^13` a natural number --- the
period reconciliation `j = dwz63Alpha 6 · s ∈ 4·10^13 · ℕ`.

`hdepth` is `dwz63_orbitRowSix_depth`, kept as a binder so that the caller performs the
substitution of the index length in its own context.

Proof sketch: rewrite `j` by `dwz63_orbitRowSix_period`, apply the weight theorem at that `k`, and
drop from `eps = 10^(-22)` to `eps = dwz63LeafMargin = 10^(-7)` by `HasTauWeight.mono`, the larger
deficit giving the smaller value. -/
theorem dwz63_orbitRowSix_R3_of_ambient
    (K : Type u) [CommRing K] (hq : 0 < dwz63Q) (p : ℕ) [Fact p.Prime] (hp : 27 ≤ p)
    (s : ℕ) (hs : 40000000000000 ∣ s) {value : ℝ}
    (hvalue : HasTauWeight K
      (cw112SymmetricAmbientPartitionedPower K dwz63Q dwz112L dwz112G
        (20088623 * (s / 40000000000000)) p hq dwz112L_pos dwz112G_pos hp).realize
      dwz63Tau value)
    (hlower : Real.exp (dwz112LogValue - 1 / 10 ^ 22) ^
      (3 * (dwz112Mass * (20088623 * (s / 40000000000000)))) ≤ value)
    (m : ℕ)
    (hdepth : (cw112SymmetricPartitionRationalTypedLeaf K dwz63Q dwz112L dwz112G hq
      dwz112L_pos dwz112G_pos).proportionalDepth (20088623 * (s / 40000000000000)) = m) :
    HasTauWeight K (symThree K (dwz63OrbitRegion K dwz63Q 0 (dwz63OrbitRow 0) m
      (dwz63Alpha (dwz63OrbitRow 0) * s)).realize) dwz63Tau
      (Real.exp ((200000000 : ℝ) * ((dwz63Alpha (dwz63OrbitRow 0) * s : ℕ) : ℝ)
        * (dwz63OrbitLogVal 0 - dwz63LeafMargin)) ^ 3) := by
  subst hdepth
  rw [dwz63_orbitRowSix_period s hs]
  refine (dwz63_symThree_orbitRowSix_weight_of_ambient K hq p hp (dwz63OrbitRow 0)
    (20088623 * (s / 40000000000000)) hvalue hlower).mono ?_
  have hmargin : (1 : ℝ) / 10 ^ 22 ≤ dwz63LeafMargin := by
    unfold dwz63LeafMargin
    norm_num
  have hnn : (0 : ℝ) ≤ (200000000 : ℝ) *
      ((40000000000000 * (20088623 * (s / 40000000000000)) : ℕ) : ℝ) := by positivity
  refine pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_le_exp.mpr ?_) 3
  exact mul_le_mul_of_nonneg_left (by linarith) hnn

end AlgebraicComplexity.Examples
