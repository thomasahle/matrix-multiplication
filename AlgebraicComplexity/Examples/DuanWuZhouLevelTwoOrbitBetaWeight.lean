/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricSideMarginal
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitBetaAmbientWeight

set_option autoImplicit false

/-!
# The rotated orbit rows' `sym₃` weight, in the assembly's own binder shape

Layer 4 (`AlgebraicComplexity/Examples/`).  This is the last step of the `(1,2,1)` and `(2,1,1)`
orbit rows: given a `tau`-weight for the committed symmetric ambient power at the free-`beta`
value, it produces the assembly's `R3` binder at `eps = dwz63LeafMargin`, for `o ≠ 0`.

## The paper

`[duan2023faster]` arXiv:2210.10173, `global_value.tex:347`: *"For all other components, we use the
symmetric Z-marginal split distributions ... So the values of all other components (including
`(2,2,0)`, `(1,2,1)`, `(2,1,1)`) do not change"*.  The value carried is `V^{(3)}_τ` of the
symmetrization, `second_power.tex:142-158` (`lem:non-rot-values`) read through `:235`
(`note:T112`), whose logarithm is the committed `dwz121LogValue`, equal to
`dwz63LogVal121 = dwz63OrbitLogVal 1 = dwz63OrbitLogVal 2` by `dwz63LogVal121_eq_dwz121LogValue`.
`global_value.tex:270-320` is where each component enters the global bound at its own
`α(i,j,k)` --- for these two rows `α(1,2,1) = α(2,1,1) = 0.20734458`, the committed
`dwz63Alpha 7 = dwz63Alpha 10 = 20734458`, which is why the assembly asks for the rows' weight at
index length `2·10⁸ · (dwz63Alpha 7 · s)`.

## The period reconciliation

The free-`beta` chain's period is `dwz121Mass = (2(L+G))^3 = 1.25·10^29`, so it reaches index
lengths `n + 1 = dwz121Mass · k`.  The assembly asks for `m + 1 = 2·10^8 · (dwz63Alpha 7 · s)`.
The two agree exactly at `j = dwz63Alpha 7 · s = 6.25·10^20 · k`, since
`2·10^8 · 6.25·10^20 = 1.25·10^29`; and the assembly's own lattice condition
`312500000000000000000 ∣ s` is what makes `k` a natural number, because
`dwz63Alpha 7 = 2 · 10367229` supplies the missing factor `2`:
`6.25·10^20 · (10367229 · c) = 20734458 · (3.125·10^20 · c)`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex:270-320` (the global value bound) and
`global_value.tex:341-348` (`:347`, the symmetric split of the two rotated rows).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## The two rotated rows' share of the global distribution -/

/-- The `(1,2,1)` and `(2,1,1)` rows' share, `α = 0.20734458`.  The literal is read from the
parameter table of `global_value.tex:374`. -/
theorem dwz63_orbitRowsSevenTen_alpha (o : Fin 3) (ho : o ≠ 0) :
    dwz63Alpha (dwz63OrbitRow o) = 20734458 := by
  fin_cases o
  · exact absurd rfl ho
  · rfl
  · rfl

/-- **The period reconciliation.**  On the assembly's own `121` lattice, the orbit rows' index
parameter `j = α(1,2,1) · s` is `6.25·10^20 · k` at `k = 10367229 · (s / 3.125·10^20)`. -/
theorem dwz63_orbitRowsSevenTen_period (o : Fin 3) (ho : o ≠ 0) (s : ℕ)
    (hs : 312500000000000000000 ∣ s) :
    dwz63Alpha (dwz63OrbitRow o) * s =
      625000000000000000000 * (10367229 * (s / 312500000000000000000)) := by
  obtain ⟨c, rfl⟩ := hs
  rw [dwz63_orbitRowsSevenTen_alpha o ho,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 312500000000000000000)]
  ring

/-! ## `sym₃` of the rotated typed cut meets the committed symmetric ambient power -/

/-- **`sym₃` of the rotated row's typed cut restricts onto the committed symmetric ambient
power.**  Image 140 with the constrained leg free: the proof is the same normal form, since
`isomorphic_symThreePartition_positivePower_select` is generic in the cut predicate. -/
theorem cw112_symThree_legTypedCut_restricts_symmetricAmbient
    (K : Type u) [CommRing K] (q L G k p : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    [Fact p.Prime] (hp : 27 ≤ p) (c₀ : Leg) {M : ℕ} (t₀ : Fin M) (j : ℕ)
    (himp : ∀ c w, cw112SymmetricKeepMarginal K q L G k hq hL hG c w →
      PartitionedTensor.symThreeKeep
        ((SegmentedSplitRestriction.ofLeg (A := CW112Block) c₀
          (cw112LegPushedProfile c₀ t₀ j)).Keeps
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)
            (fun _ ↦ t₀)) c
        ((PartitionedTensor.symThreeWordEquiv
          ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)
          c).symm w)) :
    Restricts
      (symThree K (cw112LegTypedCut K q c₀ t₀
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)
        j).realize)
      (cw112SymmetricAmbientPartitionedPower K q L G k p hq hL hG hp).realize :=
  (PartitionedTensor.isomorphic_symThreePartition_positivePower_select
      (cw112PartitionedTensor K q) _ _).restricts.trans
    (Restricts.select_of_imp _ _ _ himp)

/-! ## The rotated row's `sym₃` weight from the ambient weight -/

/-- **The rotated orbit region's `sym₃` weight at `eps = 10^(-29)`**, from a `tau`-weight for the
committed symmetric ambient power at the free-`beta` value.

Proof sketch: the weight travels from the ambient to `sym₃` of the rotated typed cut (the
`himp` above, discharged by `cw112SymmetricKeepMarginal_symThreeKeepSide`), then to `sym₃` of the
rotated region under `Restricts.symThree_congr`; `HasTauWeight.mono` then inserts the exponential
form, the two index lengths agreeing because `2·10^8 · 6.25·10^20 = 1.25·10^29 = dwz121Mass`. -/
theorem dwz63_symThree_sideRegion_weight_of_ambient
    (K : Type u) [CommRing K] (hq : 0 < dwz63Q) (p : ℕ) [Fact p.Prime] (hp : 27 ≤ p)
    (c₀ : Leg) (hc₀ : cwSquare112 c₀ = 1) {M : ℕ} (t₀ : Fin M) (k : ℕ) {value : ℝ}
    (hvalue : HasTauWeight K
      (cw112SymmetricAmbientPartitionedPower K dwz63Q dwz121L dwz121G k p hq
        dwz121L_pos dwz121G_pos hp).realize dwz63Tau value)
    (hlower : Real.exp (dwz121LogValue - 1 / 10 ^ 29) ^ (3 * (dwz121Mass * k)) ≤ value) :
    HasTauWeight K
      (symThree K (dwz63SideOrbitRegion K dwz63Q c₀ t₀
        ((cw112SymmetricPartitionRationalTypedLeaf K dwz63Q dwz121L dwz121G hq
          dwz121L_pos dwz121G_pos).proportionalDepth k)
        (625000000000000000000 * k)).realize) dwz63Tau
      (Real.exp ((200000000 : ℝ) * ((625000000000000000000 * k : ℕ) : ℝ)
        * (dwz63LogVal121 - 1 / 10 ^ 29)) ^ 3) := by
  have hchain : HasTauWeight K
      (symThree K (dwz63SideOrbitRegion K dwz63Q c₀ t₀
        ((cw112SymmetricPartitionRationalTypedLeaf K dwz63Q dwz121L dwz121G hq
          dwz121L_pos dwz121G_pos).proportionalDepth k)
        (625000000000000000000 * k)).realize) dwz63Tau value :=
    HasTauWeight.of_restricts
      (Tensor.Restricts.symThree_congr
        (dwz63_sideOrbitRegion_restricts_legTypedCut K dwz63Q c₀ hc₀ t₀ _
          (625000000000000000000 * k)))
      (HasTauWeight.of_restricts
        (cw112_symThree_legTypedCut_restricts_symmetricAmbient K dwz63Q dwz121L dwz121G k p hq
          dwz121L_pos dwz121G_pos hp c₀ t₀ (625000000000000000000 * k)
          (fun c w hw ↦ cw112SymmetricKeepMarginal_symThreeKeepSide K dwz63Q k
            (625000000000000000000 * k) hq rfl c₀ hc₀ t₀ c w hw))
        hvalue)
  refine hchain.mono (le_trans ?_ hlower)
  have hlog : dwz63LogVal121 = dwz121LogValue := dwz63LogVal121_eq_dwz121LogValue
  rw [hlog, dwz121Mass_eq, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  apply le_of_eq
  congr 1
  push_cast
  ring

/-! ## The index-length identification -/

/-- **The index-length identification.**  On the assembly's `121` lattice, the assembly's index
length `m + 1 = 2·10^8 · (α(1,2,1) · s)` is exactly the free-`beta` chain's `dwz121Mass · k` at
`k = 10367229 · (s / 3.125·10^20)`, so `m` is the leaf's proportional depth. -/
theorem dwz63_sideRegion_depth
    (K : Type u) [CommRing K] (hq : 0 < dwz63Q) (o : Fin 3) (ho : o ≠ 0) (s : ℕ)
    (hs : 312500000000000000000 ∣ s)
    (hspos : 0 < 10367229 * (s / 312500000000000000000)) (m : ℕ)
    (hm : m + 1 = 200000000 * (dwz63Alpha (dwz63OrbitRow o) * s)) :
    (cw112SymmetricPartitionRationalTypedLeaf K dwz63Q dwz121L dwz121G hq
      dwz121L_pos dwz121G_pos).proportionalDepth
        (10367229 * (s / 312500000000000000000)) = m := by
  have hmass : (cw112SymmetricPartitionRationalTypedLeaf K dwz63Q dwz121L dwz121G hq
      dwz121L_pos dwz121G_pos).profile.mass = dwz121Mass :=
    cw112SymmetricLeaf_profile_mass K dwz63Q dwz121L dwz121G hq dwz121L_pos dwz121G_pos
  have h := RationalTypedLeaf.proportionalDepth_add_one
    (cw112SymmetricPartitionRationalTypedLeaf K dwz63Q dwz121L dwz121G hq
      dwz121L_pos dwz121G_pos) hspos
  rw [hmass] at h
  rw [dwz63_orbitRowsSevenTen_period o ho s hs] at hm
  have harith : dwz121Mass * (10367229 * (s / 312500000000000000000)) =
      200000000 * (625000000000000000000 * (10367229 * (s / 312500000000000000000))) := by
    norm_num [dwz121Mass, dwz121L, dwz121G]
    ring
  rw [harith, ← hm] at h
  exact Nat.succ_injective h

/-! ## The assembly's `R3` binder, for `o ≠ 0` -/

/-- **The `R3` premise of the marked/seeded assembly, for the orbit rows `o ≠ 0`.**

The conclusion is image 135's `R3` binder specialised to `o ≠ 0`, at `eps = dwz63LeafMargin`.
`hs` is that theorem's own `121` lattice condition, and it is what makes the chain's repetition
count `k = 10367229 · (s / 3.125·10^20)` a natural number.

Proof sketch: `o ≠ 0` leaves the two rotated rows; each is carried onto its rotated `(1,1,2)`
region by `dwz63_isomorphic_symThree_orbitRegion_one` / `_two`, the rotated region takes the
free-`beta` ambient weight, and the deficit drops from `10^(-29)` to
`dwz63LeafMargin = 10^(-7)`. -/
theorem dwz63_orbitRowsSevenTen_R3_of_ambient
    (K : Type u) [CommRing K] (hq : 0 < dwz63Q) (p : ℕ) [Fact p.Prime] (hp : 27 ≤ p)
    (o : Fin 3) (ho : o ≠ 0) (s : ℕ) (hs : 312500000000000000000 ∣ s) {value : ℝ}
    (hvalue : HasTauWeight K
      (cw112SymmetricAmbientPartitionedPower K dwz63Q dwz121L dwz121G
        (10367229 * (s / 312500000000000000000)) p hq dwz121L_pos dwz121G_pos hp).realize
      dwz63Tau value)
    (hlower : Real.exp (dwz121LogValue - 1 / 10 ^ 29) ^
      (3 * (dwz121Mass * (10367229 * (s / 312500000000000000000)))) ≤ value)
    (m : ℕ)
    (hdepth : (cw112SymmetricPartitionRationalTypedLeaf K dwz63Q dwz121L dwz121G hq
      dwz121L_pos dwz121G_pos).proportionalDepth
        (10367229 * (s / 312500000000000000000)) = m) :
    HasTauWeight K (symThree K (dwz63OrbitRegion K dwz63Q o (dwz63OrbitRow o) m
      (dwz63Alpha (dwz63OrbitRow o) * s)).realize) dwz63Tau
      (Real.exp ((200000000 : ℝ) * ((dwz63Alpha (dwz63OrbitRow o) * s : ℕ) : ℝ)
        * (dwz63OrbitLogVal o - dwz63LeafMargin)) ^ 3) := by
  have hmargin : (1 : ℝ) / 10 ^ 29 ≤ dwz63LeafMargin := by
    unfold dwz63LeafMargin
    norm_num
  have hstep : ∀ c₀ : Leg, cwSquare112 c₀ = 1 →
      ∀ (o' : Fin 3) (t₀ : Fin 15),
        Isomorphic (symThree K (dwz63OrbitRegion K dwz63Q o' t₀ m
            (625000000000000000000 * (10367229 * (s / 312500000000000000000)))).realize)
          (symThree K (dwz63SideOrbitRegion K dwz63Q c₀ t₀ m
            (625000000000000000000 * (10367229 * (s / 312500000000000000000)))).realize) →
        HasTauWeight K (symThree K (dwz63OrbitRegion K dwz63Q o' t₀ m
          (625000000000000000000 * (10367229 * (s / 312500000000000000000)))).realize) dwz63Tau
          (Real.exp ((200000000 : ℝ)
            * ((625000000000000000000 * (10367229 * (s / 312500000000000000000)) : ℕ) : ℝ)
            * (dwz63LogVal121 - dwz63LeafMargin)) ^ 3) := by
    intro c₀ hc₀ o' t₀ hiso
    subst hdepth
    refine HasTauWeight.of_restricts hiso.restricts ?_
    refine (dwz63_symThree_sideRegion_weight_of_ambient K hq p hp c₀ hc₀ t₀ _
      hvalue hlower).mono ?_
    have hnn : (0 : ℝ) ≤ (200000000 : ℝ)
        * ((625000000000000000000 * (10367229 * (s / 312500000000000000000)) : ℕ) : ℝ) := by
      positivity
    refine pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_le_exp.mpr ?_) 3
    exact mul_le_mul_of_nonneg_left (by linarith) hnn
  have ho' : o = 1 ∨ o = 2 := by
    fin_cases o
    · exact absurd rfl ho
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases ho' with rfl | rfl
  · rw [dwz63_orbitRowsSevenTen_period 1 (by decide) s hs]
    exact hstep Leg.X (by decide) 1 (dwz63OrbitRow 1)
      (dwz63_isomorphic_symThree_orbitRegion_one K dwz63Q (dwz63OrbitRow 1) m _)
  · rw [dwz63_orbitRowsSevenTen_period 2 (by decide) s hs]
    exact hstep Leg.Y (by decide) 2 (dwz63OrbitRow 2)
      (dwz63_isomorphic_symThree_orbitRegion_two K dwz63Q (dwz63OrbitRow 2) m _)

end AlgebraicComplexity.Examples
