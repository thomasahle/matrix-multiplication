/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainRate
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainSharpDegree

set_option autoImplicit false

/-!
# `hbranch` at the plain partition, proved

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoPlainIntegration.lean`
states its one open count-side input as the hypothesis

`dwz63HashingBranch ^ (n+1) * (4 M²) ≤ lossHash * (3 · #marked · #B)`,

`[DuanWuZhou2022]` §6.3's step (4) arithmetic, and records that it is provable from what is already
green.  This module proves it, at `marked = dwz63PlainMarginalWords K n t`, `M` the Bertrand
modulus `dwz63SharpHashModulus` of the plain sharp degree, and `B` the Behrend set of
`exists_threeAPFree_zmod_half_behrend`.

## The cancellation, in three moves

* **The branch, against `N_X`.**  `dwz63HashLossMultiplier = 1 + 10⁻¹⁰ > 1`, so
  `dwz63HashingBranch ≤ exp dwz63EntropyX`, and `PlainRate`'s **lossy**
  `dwz63_exp_entropyX_pow_le_loss_mul_dwz63PlainLegCount` gives
  `exp(H_X) ^ (n+1) ≤ Stirling(t) · N_X` with no use of `K`.  (The loss-free
  `dwz63_hashingBranch_pow_le_dwz63XTypicalCount` of the six-orientation lane is *not* usable
  here: it spends `K` on the Stirling loss, and on the plain route `K` is already claimed by the
  joint-versus-marginal Gibbs gap.)
* **`N_X` against the retention loss.**  At the sharp degree `d = ⌊N_α'/N_X⌋ + 1` one has
  `N_X · d ≤ 2 N_α'` and `N_X ≤ N_α'`, so
  `N_X · dwz63SharpRetentionLoss d ≤ 125136 · Behrend(d) · N_α'` --- the whole rate-carrying step,
  and the reason the loss is only `Behrend · Stirling`.  `N_X ≤ N_α'` is read off the fibre
  identity `card_dwz63PlainMarginalWords_eq`: a marginal-typical word lies in its own leg fibre, so
  that fibre is nonempty.
* **Behrend, and the modulus.**  `#B ≥ (M/2) · exp(-4 √(log (M/2))) ≥ (M/3) / Behrend(d)` and
  `M ≤ 2 (15625 + 8 d + 1)` (Bertrand), so `4 M² ≤ 4 M · 2(15625 + 8d + 1)` and the surviving
  `M` cancels against the `M` inside `#B`.  `4 · 2(15625 + 8d + 1) · Behrend` is exactly
  `dwz63SharpRetentionLoss d`, which is why the second move is stated against it.

## The loss, and why it is subexponential

`dwz63PlainMarkedLossHash K N = (125136 · Behrend(degree N)) · Stirling(N / 10⁸)` with
`degree N = dwz63PlainSharpDegree K (N-1) (N/10⁸)`.  The Behrend half is
`subexponential_dwz63PlainLossHash` at the plain radix (`degree N ≤ 15 ^ (N+1) + 1`, because a
count of fifteen-letter block words never exceeds `15 ^ (N)`); the Stirling half is the committed
`WordType.structuralZeroMultinomialLoss_subexponential` reindexed along `N ↦ N / 10⁸`, which is
pointwise below the identity.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

/-! ## Subexponentiality survives a pointwise-smaller reindexing -/

/-- **Reindexing a subexponential loss by a pointwise-smaller index keeps it subexponential.**
Used to read the Stirling loss, which is stated at the repetition count `t`, as a loss at the word
length `N = 10⁸ t`. -/
theorem dwz63_subexponential_comp_of_le_self {a : ℕ → ℝ} (ha : Growth.Subexponential a)
    (f : ℕ → ℕ) (hf : ∀ N : ℕ, f N ≤ N) :
    Growth.Subexponential (fun N ↦ a (f N)) := by
  refine ⟨fun N ↦ ha.nonneg (f N), fun δ hδ ↦ ?_⟩
  obtain ⟨C, hC, hbound⟩ := ha.2 δ hδ
  refine ⟨C, hC, fun N ↦ (hbound (f N)).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hδ.le (hf N)) hC.le

/-! ## The marginal-typical ambient is nonempty -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The marginal-typical ambient is nonempty.**  A jointly typical block word --- one whose
fifteen-cell multiplicity is the repeated profile --- has every leg marginal right, because
`WordType.multiplicity_comp_eq_mappedType` pushes its type forward and
`mappedType_dwz63PlainLegRead_proportionalCounts` identifies the pushforward. -/
theorem dwz63PlainMarginalWords_nonempty (K : Type u) [CommRing K] {n t : ℕ}
    (hn : n + 1 = 100000000 * t) : (dwz63PlainMarginalWords K n t).Nonempty := by
  classical
  have hmem : WordType.proportionalCounts dwz63PlainAlpha t ∈
      WordType.types ((cwSquarePartitionedTensor K dwz63Q).support) (n + 1) :=
    proportionalCounts_dwz63PlainAlpha_mem_types hn
  obtain ⟨word, hwordMem⟩ := WordType.typeClass_nonempty _ hmem
  have hword : WordType.multiplicity word = WordType.proportionalCounts dwz63PlainAlpha t :=
    WordType.mem_typeClass.mp hwordMem
  refine ⟨(positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n).symm word, ?_⟩
  rw [mem_dwz63PlainMarginalWords]
  intro c
  have hqw : (positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n)
      ((positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n).symm word) = word :=
    Equiv.apply_symm_apply _ _
  -- ELABORATION RISK: rewrite with the *concrete* equation `hqw` rather than with
  -- `Equiv.apply_symm_apply`.  The higher-order pattern `?e (?e.symm ?x)` forces a `whnf` of the
  -- `PositiveWord` block family and fails with a `(↑i).1` type mismatch.
  rw [hqw]
  -- ELABORATION RISK: the two ascriptions `↥cwSquareSupport` and
  -- `↥(cwSquarePartitionedTensor K dwz63Q).support` are `rfl`-equal but not syntactically equal, so
  -- their `Fintype`/`DecidableEq` instances differ as terms.  `rw` therefore cannot move `hword`
  -- into place; `Eq.trans`/`congrArg`, which only need defeq, can.
  refine Eq.trans (WordType.multiplicity_comp_eq_mappedType (dwz63PlainLegRead c) word) ?_
  refine Eq.trans (congrArg (WordType.mappedType (dwz63PlainLegRead c)) hword) ?_
  exact mappedType_dwz63PlainLegRead_proportionalCounts c t

/-! ## `N_X ≤ N_α'`, and the sharp-degree product -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`N_c ≤ N_α'`.**  A marginal-typical word lies in the leg fibre over its own leg word, so the
fibre identity `#ambient = N_c · #fibre` has `#fibre ≥ 1`. -/
theorem dwz63PlainLegCount_le_card_dwz63PlainMarginalWords (K : Type u) [CommRing K] (c : Leg)
    {n t : ℕ} (hn : n + 1 = 100000000 * t) :
    dwz63PlainLegCount c n t ≤ (dwz63PlainMarginalWords K n t).card := by
  classical
  obtain ⟨q, hq⟩ := dwz63PlainMarginalWords_nonempty K hn
  have hx : PartitionHashEncoding.supportWordAddress n q c ∈ dwz63PlainLegTargets c n t :=
    mem_dwz63PlainLegTargets.mpr ((mem_dwz63PlainMarginalWords_iff_keep K n t q).mp hq c)
  have hcount := card_dwz63PlainMarginalWords_eq K c n t hx
  have hmem : q ∈ PartitionHashEncoding.sourceWordLegFiber n (dwz63PlainMarginalWords K n t) c
      (PartitionHashEncoding.supportWordAddress n q c) := by
    rw [PartitionHashEncoding.sourceWordLegFiber, Finset.mem_filter]
    exact ⟨hq, rfl⟩
  have hfpos : 0 < (PartitionHashEncoding.sourceWordLegFiber n (dwz63PlainMarginalWords K n t) c
      (PartitionHashEncoding.supportWordAddress n q c)).card :=
    Finset.card_pos.mpr ⟨q, hmem⟩
  calc dwz63PlainLegCount c n t
      ≤ dwz63PlainLegCount c n t *
          (PartitionHashEncoding.sourceWordLegFiber n (dwz63PlainMarginalWords K n t) c
            (PartitionHashEncoding.supportWordAddress n q c)).card :=
        Nat.le_mul_of_pos_right _ hfpos
    _ = (dwz63PlainMarginalWords K n t).card := hcount.symm

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`N_X · d ≤ 2 N_α'` at the plain sharp degree.** -/
theorem dwz63PlainLegCount_mul_plainSharpDegree_le (K : Type u) [CommRing K] {n t : ℕ}
    (hn : n + 1 = 100000000 * t) :
    dwz63PlainLegCount .X n t * dwz63PlainSharpDegree K n t ≤
      2 * (dwz63PlainMarginalWords K n t).card := by
  have hXJ := dwz63PlainLegCount_le_card_dwz63PlainMarginalWords K .X hn
  have hdiv : (dwz63PlainMarginalWords K n t).card / dwz63PlainLegCount .X n t *
      dwz63PlainLegCount .X n t ≤ (dwz63PlainMarginalWords K n t).card :=
    Nat.div_mul_le_self _ _
  unfold dwz63PlainSharpDegree dwz63SharpDegree
  calc dwz63PlainLegCount .X n t *
        ((dwz63PlainMarginalWords K n t).card / dwz63PlainLegCount .X n t + 1)
      = (dwz63PlainMarginalWords K n t).card / dwz63PlainLegCount .X n t *
          dwz63PlainLegCount .X n t + dwz63PlainLegCount .X n t := by ring
    _ ≤ (dwz63PlainMarginalWords K n t).card + (dwz63PlainMarginalWords K n t).card :=
        Nat.add_le_add hdiv hXJ
    _ = 2 * (dwz63PlainMarginalWords K n t).card := by ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The cancellation.**  `N_X` times the retention loss at the plain sharp degree is at most a
Behrend-only multiple of the marginal-typical count. -/
theorem dwz63_plainLegCount_mul_retentionLoss_le (K : Type u) [CommRing K] {n t : ℕ}
    (hn : n + 1 = 100000000 * t) :
    ((dwz63PlainLegCount .X n t : ℕ) : ℝ) *
        dwz63SharpRetentionLoss (dwz63PlainSharpDegree K n t) ≤
      (125136 * dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t)) *
        (((dwz63PlainMarginalWords K n t).card : ℕ) : ℝ) := by
  have hB : (0 : ℝ) < dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t) :=
    dwz63SharpBehrendLoss_pos _
  have hXnn : (0 : ℝ) ≤ ((dwz63PlainLegCount .X n t : ℕ) : ℝ) := Nat.cast_nonneg _
  have hX : ((dwz63PlainLegCount .X n t : ℕ) : ℝ) ≤
      (((dwz63PlainMarginalWords K n t).card : ℕ) : ℝ) := by
    exact_mod_cast dwz63PlainLegCount_le_card_dwz63PlainMarginalWords K .X hn
  have hXd : ((dwz63PlainLegCount .X n t : ℕ) : ℝ) *
      ((dwz63PlainSharpDegree K n t : ℕ) : ℝ) ≤
      2 * (((dwz63PlainMarginalWords K n t).card : ℕ) : ℝ) := by
    exact_mod_cast dwz63PlainLegCount_mul_plainSharpDegree_le K hn
  unfold dwz63SharpRetentionLoss dwz63SharpModulusLoss
  nlinarith [hB, hX, hXd, hXnn]

/-! ## The plain degree sequence is at most geometric -/

set_option maxRecDepth 8000 in
/-- **A count of fifteen-letter block words never exceeds `15 ^ (n+1)`.** -/
theorem card_dwz63PlainMarginalWords_le (K : Type u) [CommRing K] (n t : ℕ) :
    (dwz63PlainMarginalWords K n t).card ≤ 15 ^ (n + 1) := by
  classical
  calc (dwz63PlainMarginalWords K n t).card
      ≤ Fintype.card (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n) :=
        Finset.card_le_univ _
    _ = Fintype.card (Fin (n + 1) → ((cwSquarePartitionedTensor K dwz63Q).support)) :=
        Fintype.card_congr (positiveWordEquiv _ n)
    _ = 15 ^ (n + 1) := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
          cwSquarePartitionedTensor_support, card_cwSquareSupport]

/-- **The plain sharp degree is at most `15 ^ (n+1) + 1`.** -/
theorem dwz63PlainSharpDegree_le (K : Type u) [CommRing K] (n t : ℕ) :
    dwz63PlainSharpDegree K n t ≤ 15 ^ (n + 1) + 1 := by
  have hcard := card_dwz63PlainMarginalWords_le K n t
  have hdiv := Nat.div_le_self (dwz63PlainMarginalWords K n t).card
    (dwz63PlainLegCount .X n t)
  unfold dwz63PlainSharpDegree dwz63SharpDegree
  omega

/-! ## The loss -/

/-- **The plain degree sequence, as a function of the word length.**  At `N = n + 1 = 10⁸ t` this
is `dwz63PlainSharpDegree K n t`. -/
noncomputable def dwz63PlainMarkedDegree (K : Type u) [CommRing K] (N : ℕ) : ℕ :=
  dwz63PlainSharpDegree K (N - 1) (N / 100000000)

theorem dwz63PlainMarkedDegree_le (K : Type u) [CommRing K] (N : ℕ) :
    dwz63PlainMarkedDegree K N ≤ 15 ^ (N + 1) + 1 := by
  have hmono : (15 : ℕ) ^ (N - 1 + 1) ≤ 15 ^ (N + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h := dwz63PlainSharpDegree_le K (N - 1) (N / 100000000)
  unfold dwz63PlainMarkedDegree
  omega

/-- **The plain marked-count loss**: Behrend at the plain sharp degree, times the method-of-types
Stirling loss of the `X` marginal.  Both factors are subexponential; nothing else is spent. -/
noncomputable def dwz63PlainMarkedLossHash (K : Type u) [CommRing K] (N : ℕ) : ℝ :=
  (125136 * dwz63SharpBehrendLoss (dwz63PlainMarkedDegree K N)) *
    WordType.structuralZeroMultinomialLoss dwz63AlphaX (N / 100000000)

theorem dwz63PlainMarkedLossHash_pos (K : Type u) [CommRing K] (N : ℕ) :
    0 < dwz63PlainMarkedLossHash K N := by
  unfold dwz63PlainMarkedLossHash
  exact mul_pos (mul_pos (by norm_num) (dwz63SharpBehrendLoss_pos _))
    (WordType.structuralZeroMultinomialLoss_pos dwz63AlphaX (N / 100000000))

theorem dwz63PlainMarkedLossHash_nonneg (K : Type u) [CommRing K] (N : ℕ) :
    0 ≤ dwz63PlainMarkedLossHash K N := (dwz63PlainMarkedLossHash_pos K N).le

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The plain marked-count loss is subexponential.** -/
theorem subexponential_dwz63PlainMarkedLossHash (K : Type u) [CommRing K] :
    Growth.Subexponential (dwz63PlainMarkedLossHash K) := by
  have hbehrend : Growth.Subexponential
      (fun N ↦ 125136 * dwz63SharpBehrendLoss (dwz63PlainMarkedDegree K N)) :=
    subexponential_dwz63PlainLossHash (dwz63PlainMarkedDegree K) (dwz63PlainMarkedDegree_le K)
  have hstirling : Growth.Subexponential
      (fun N ↦ WordType.structuralZeroMultinomialLoss dwz63AlphaX (N / 100000000)) :=
    dwz63_subexponential_comp_of_le_self
      (WordType.structuralZeroMultinomialLoss_subexponential dwz63AlphaX)
      (fun N ↦ N / 100000000) (fun N ↦ Nat.div_le_self _ _)
  exact hbehrend.mul hstirling

/-! ## The branch, against the retention loss -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The hashing branch is below the full `X` marginal rate.**  `dwz63HashLossMultiplier > 1`. -/
theorem dwz63HashingBranch_le_exp_entropyX :
    dwz63HashingBranch ≤ Real.exp dwz63EntropyX := by
  unfold dwz63HashingBranch
  exact div_le_self (Real.exp_pos _).le (by norm_num [dwz63HashLossMultiplier])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The branch power, against the marginal count, with the Stirling loss named.** -/
theorem dwz63_plainHashingBranch_pow_le (K : Type u) [CommRing K] {n t : ℕ}
    (hn : n + 1 = 100000000 * t) :
    dwz63HashingBranch ^ (n + 1) ≤
      WordType.structuralZeroMultinomialLoss dwz63AlphaX t *
        ((dwz63PlainLegCount .X n t : ℕ) : ℝ) :=
  (pow_le_pow_left₀ dwz63HashingBranch_pos.le dwz63HashingBranch_le_exp_entropyX (n + 1)).trans
    (dwz63_exp_entropyX_pow_le_loss_mul_dwz63PlainLegCount hn)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`hbranch` in the retention-loss form.**

`dwz63HashingBranch ^ (n+1) · dwz63SharpRetentionLoss d ≤ lossHash (n+1) · N_α'`, the shape from
which the `4 M²` / Behrend form follows by cancelling one power of the modulus. -/
theorem dwz63_plainBranch_pow_mul_retentionLoss_le (K : Type u) [CommRing K] {n t : ℕ}
    (hn : n + 1 = 100000000 * t) :
    dwz63HashingBranch ^ (n + 1) * dwz63SharpRetentionLoss (dwz63PlainSharpDegree K n t) ≤
      dwz63PlainMarkedLossHash K (n + 1) *
        (((dwz63PlainMarginalWords K n t).card : ℕ) : ℝ) := by
  have ht : (n + 1) / 100000000 = t := by omega
  have hn1 : (n + 1) - 1 = n := by omega
  have hlossEq : dwz63PlainMarkedLossHash K (n + 1) =
      (125136 * dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t)) *
        WordType.structuralZeroMultinomialLoss dwz63AlphaX t := by
    unfold dwz63PlainMarkedLossHash dwz63PlainMarkedDegree
    rw [ht, hn1]
  have hretPos : (0 : ℝ) < dwz63SharpRetentionLoss (dwz63PlainSharpDegree K n t) :=
    mul_pos (dwz63SharpModulusLoss_pos _) (dwz63SharpBehrendLoss_pos _)
  have hstir : (0 : ℝ) ≤ WordType.structuralZeroMultinomialLoss dwz63AlphaX t :=
    (WordType.structuralZeroMultinomialLoss_pos dwz63AlphaX t).le
  rw [hlossEq]
  calc dwz63HashingBranch ^ (n + 1) * dwz63SharpRetentionLoss (dwz63PlainSharpDegree K n t)
      ≤ (WordType.structuralZeroMultinomialLoss dwz63AlphaX t *
            ((dwz63PlainLegCount .X n t : ℕ) : ℝ)) *
          dwz63SharpRetentionLoss (dwz63PlainSharpDegree K n t) :=
        mul_le_mul_of_nonneg_right (dwz63_plainHashingBranch_pow_le K hn) hretPos.le
    _ = WordType.structuralZeroMultinomialLoss dwz63AlphaX t *
          (((dwz63PlainLegCount .X n t : ℕ) : ℝ) *
            dwz63SharpRetentionLoss (dwz63PlainSharpDegree K n t)) := by ring
    _ ≤ WordType.structuralZeroMultinomialLoss dwz63AlphaX t *
          ((125136 * dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t)) *
            (((dwz63PlainMarginalWords K n t).card : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (dwz63_plainLegCount_mul_retentionLoss_le K hn) hstir
    _ = (125136 * dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t)) *
          WordType.structuralZeroMultinomialLoss dwz63AlphaX t *
          (((dwz63PlainMarginalWords K n t).card : ℕ) : ℝ) := by ring

/-! ## Cancelling the modulus against Behrend -/

/-- **The arithmetic of the modulus cancellation**, stated over the reals alone.

`A` is the branch power, `Mr` the modulus, `U ≥ Mr` its Bertrand ceiling, `Beh` the Behrend factor
and `Bc ≥ (Mr/3)/Beh` the size of the progression-free set. -/
theorem dwz63_plainHashBranch_arith {A U Mr Beh N Bc loss : ℝ}
    (hA : 0 ≤ A) (hUM : Mr ≤ U) (hMpos : 0 < Mr) (hBeh : 0 < Beh)
    (hloss : 0 ≤ loss) (hN : 0 ≤ N)
    (hBc : Mr / 3 * Beh⁻¹ ≤ Bc)
    (hstep : A * (4 * U * Beh) ≤ loss * N) :
    A * (4 * (Mr * Mr)) ≤ loss * (3 * N * Bc) := by
  have hBehne : Beh ≠ 0 := ne_of_gt hBeh
  have h5 : A * (4 * (Mr * Mr)) ≤ A * (4 * (U * Mr)) := by
    refine mul_le_mul_of_nonneg_left ?_ hA
    have : Mr * Mr ≤ U * Mr := mul_le_mul_of_nonneg_right hUM hMpos.le
    linarith
  have h4 : A * (4 * U * Beh) * Mr * Beh⁻¹ = A * (4 * (U * Mr)) := by
    field_simp
  have h3 : A * (4 * U * Beh) * Mr * Beh⁻¹ ≤ loss * N * Mr * Beh⁻¹ := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right hstep hMpos.le
  have h2 : loss * N * Mr * Beh⁻¹ = loss * (3 * N * (Mr / 3 * Beh⁻¹)) := by
    field_simp
  have h1 : loss * (3 * N * (Mr / 3 * Beh⁻¹)) ≤ loss * (3 * N * Bc) := by
    refine mul_le_mul_of_nonneg_left ?_ hloss
    exact mul_le_mul_of_nonneg_left hBc (by positivity)
  calc A * (4 * (Mr * Mr))
      ≤ A * (4 * (U * Mr)) := h5
    _ = A * (4 * U * Beh) * Mr * Beh⁻¹ := h4.symm
    _ ≤ loss * N * Mr * Beh⁻¹ := h3
    _ = loss * (3 * N * (Mr / 3 * Beh⁻¹)) := h2
    _ ≤ loss * (3 * N * Bc) := h1

/-! ## `hbranch`, at the Bertrand field and the Behrend set -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`hbranch`, for any field whose cardinality is the Bertrand modulus at the plain sharp
degree, against any set with Behrend's lower bound.**

This is the exact shape `dwz63_exists_seed_plainCopyCount_at_sharpDegree` consumes, at
`marked = dwz63PlainMarginalWords K n t` and `lossHash = dwz63PlainMarkedLossHash K (n+1)`. -/
theorem dwz63_plainHashBranch {R : Type v} [Field R] [Fintype R] (K : Type u) [CommRing K]
    {n t : ℕ} (hn : n + 1 = 100000000 * t)
    (hcard : Fintype.card R = dwz63SharpHashModulus (dwz63PlainSharpDegree K n t))
    (B : Finset R)
    (hB : ((dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) / 2 : ℕ) : ℝ) *
        Real.exp (-4 * Real.sqrt (Real.log
          ((dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) / 2 : ℕ) : ℝ))) ≤
      (B.card : ℝ)) :
    dwz63HashingBranch ^ (n + 1) *
        (4 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ))) ≤
      dwz63PlainMarkedLossHash K (n + 1) *
        (3 * ((dwz63PlainMarginalWords K n t).card : ℝ) * (B.card : ℝ)) := by
  have hMfloor : 15625 ≤ dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) :=
    dwz63SharpHashModulus_char_floor _
  have hMposNat : 0 < dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) := by omega
  have hMpos : (0 : ℝ) < (dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) : ℝ) := by
    exact_mod_cast hMposNat
  have hUM : (dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) : ℝ) ≤
      2 * (15625 + 8 * ((dwz63PlainSharpDegree K n t : ℕ) : ℝ) + 1) := by
    have hnat := dwz63SharpHashModulus_le (dwz63PlainSharpDegree K n t)
    have hcast : ((dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) : ℕ) : ℝ) ≤
        ((2 * (15625 + 8 * dwz63PlainSharpDegree K n t + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hcast
    linarith
  have hhalf : (dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) : ℝ) / 3 ≤
      ((dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) / 2 : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    have hnat : dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) ≤
        dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) / 2 * 3 := by omega
    exact_mod_cast hnat
  have hBehPos : (0 : ℝ) < dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t) :=
    dwz63SharpBehrendLoss_pos _
  have hinv : Real.exp (-4 * Real.sqrt (Real.log
        ((dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) / 2 : ℕ) : ℝ))) =
      (dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t))⁻¹ := by
    unfold dwz63SharpBehrendLoss
    rw [← Real.exp_neg]
    ring_nf
  have hBc : (dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) : ℝ) / 3 *
      (dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t))⁻¹ ≤ (B.card : ℝ) := by
    refine le_trans ?_ hB
    rw [← hinv]
    exact mul_le_mul_of_nonneg_right hhalf (Real.exp_nonneg _)
  have hstep : dwz63HashingBranch ^ (n + 1) *
      (4 * (2 * (15625 + 8 * ((dwz63PlainSharpDegree K n t : ℕ) : ℝ) + 1)) *
        dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t)) ≤
      dwz63PlainMarkedLossHash K (n + 1) *
        (((dwz63PlainMarginalWords K n t).card : ℕ) : ℝ) := by
    have h := dwz63_plainBranch_pow_mul_retentionLoss_le K hn
    unfold dwz63SharpRetentionLoss dwz63SharpModulusLoss at h
    calc dwz63HashingBranch ^ (n + 1) *
          (4 * (2 * (15625 + 8 * ((dwz63PlainSharpDegree K n t : ℕ) : ℝ) + 1)) *
            dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t))
        = dwz63HashingBranch ^ (n + 1) *
            (4 * (2 * (15625 + 8 * ((dwz63PlainSharpDegree K n t : ℕ) : ℝ) + 1)) *
              dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t)) := rfl
      _ ≤ dwz63PlainMarkedLossHash K (n + 1) *
            (((dwz63PlainMarginalWords K n t).card : ℕ) : ℝ) := h
  rw [hcard]
  exact dwz63_plainHashBranch_arith (pow_nonneg dwz63HashingBranch_pos.le _) hUM hMpos hBehPos
    (dwz63PlainMarkedLossHash_nonneg K (n + 1)) (Nat.cast_nonneg _) hBc hstep

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`hbranch`, with the progression-free set produced.**

The Behrend set of `exists_threeAPFree_zmod_half_behrend` inside the Bertrand field at the plain
sharp degree.  This is deliverable (A): the last count-side input of
`Examples/DuanWuZhouLevelTwoPlainIntegration.lean`, discharged. -/
theorem exists_behrend_dwz63_plainHashBranch (K : Type u) [CommRing K] {n t : ℕ}
    (hn : n + 1 = 100000000 * t) :
    ∃ B : Finset (dwz63SharpHashField (dwz63PlainSharpDegree K n t)),
      ThreeAPFree (B : Set (dwz63SharpHashField (dwz63PlainSharpDegree K n t))) ∧
        dwz63HashingBranch ^ (n + 1) *
            (4 * ((Fintype.card (dwz63SharpHashField (dwz63PlainSharpDegree K n t)) : ℝ) *
              (Fintype.card (dwz63SharpHashField (dwz63PlainSharpDegree K n t)) : ℝ))) ≤
          dwz63PlainMarkedLossHash K (n + 1) *
            (3 * ((dwz63PlainMarginalWords K n t).card : ℝ) * (B.card : ℝ)) := by
  obtain ⟨B, hfree, hcard⟩ :=
    exists_threeAPFree_zmod_half_behrend (dwz63SharpHashModulus (dwz63PlainSharpDegree K n t))
  exact ⟨B, hfree, dwz63_plainHashBranch K hn (card_dwz63SharpHashField _) B hcard⟩

end AlgebraicComplexity.Examples
