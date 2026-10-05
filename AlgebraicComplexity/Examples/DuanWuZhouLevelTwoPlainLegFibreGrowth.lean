/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainPushedBases
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainFiberCount

set_option autoImplicit false

/-!
# `hlower`: the `X`-leg fibre of the marginal-typical ambient grows at the pushed rate

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoCountComparison.lean`
reports that the tree already carries the *shape* of `hlower` —
`Combinatorics/PushedProfileFiberGrowth.lean`'s
`pushedTypeFiberEntropyBase_pow_le_loss_mul_card_typedFiber` and its `_of_length_eq` variant in
`Analysis/ConditionalLegFiberGrowth.lean` — and that what is missing is the **instantiation** at
`dwz63PlainMarginalWords`' `X`-leg fibre.  This module is that instantiation.

## The identification

`PartitionHashEncoding.sourceWordLegFiber n (dwz63PlainMarginalWords K n t) c x` is a set of
recursive words over the *supported square addresses*, cut by the leg-transposition
`supportWordAddress`;
`WordType.typedWordMapFiber (dwz63PlainLegRead c) α_t (positiveWordEquiv _ n x)`
is a set of function-representation words over the same alphabet, cut by the letterwise leg read.
`dwz63_card_typedWordMapFiber_le_card_sourceWordLegFiber` transports the second into the first
along `positiveWordEquiv`.  Two facts do all of the work, both committed:

* `PartitionHashEncoding.positiveWordEquiv_supportWordAddress` — transposing a support word to one
  leg *is* reading that leg letterwise, so the two cuts are the same condition; and
* `WordType.multiplicity_comp_eq_mappedType` together with
  `mappedType_dwz63PlainLegRead_proportionalCounts` — a **joint**-typical word is *marginally*
  typical on all three legs, so the typed fibre lands inside the marginal-typical ambient.

The inclusion is one-directional and that is exactly right: the ambient is marginal-typical, hence
strictly larger than the joint type class, so the fibre over it is at least the joint typed fibre.
No surjectivity, and no reverse inclusion, is claimed or needed.

## The rate, and where `K` is *not*

`pushedTypeFiberEntropyBase (dwz63PlainLegRead .X) dwz63PlainAlpha` evaluates, by
`Examples/DuanWuZhouLevelTwoPlainPushedBases.lean`, to `ᾱ_α / ᾱ_X` per position, so the bound
proved here is

`(ᾱ_α / ᾱ_X) ^ (n + 1) ≤ structuralZeroMultinomialLoss dwz63PlainAlpha t · |fibre|`.

The hash-loss multiplier `K = 1 + 10⁻¹⁰` does **not** appear, and cannot be inserted from
anything
committed: `dwz63_gibbsDeficit_le_log_hashLossMultiplier` bounds the marginal-typical ambient
*above* by `K ^ n` times the joint typical count, and a factor `K ^ n` on the left of `hlower`
would need the opposite inequality — an exhibited non-`α` member of `D_α` of entropy at least
`H(α) + log K`.  The estimate is therefore stated at `K = 1`, which is the conservative direction:
`dwz63_hcount_of_rate`'s ratio `r = ᾱ_p ᾱ_X / (ᾱ_Z · hashK)` is *largest* at `hashK = 1`, and
the
branch-1-binds margin `−1.1215 · 10⁻⁷` per symbol recorded in
`Examples/DuanWuZhouLevelTwoJointHashBranch.lean` exceeds `log K ≈ 10⁻¹⁰` by three orders of
magnitude, so dropping `K` does not endanger `r < 1`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.2 (`global_value.tex`), §2.9 (`hashing.tex`), §6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

open scoped BigOperators

universe u

/-! ## The typed fibre sits inside the marginal-typical leg fibre -/

-- ELABORATION RISK: `dwz63PlainAlpha` has domain `↥cwSquareSupport` while
-- `dwz63PlainMarginalWords` is indexed by `↥((cwSquarePartitionedTensor K dwz63Q).support)`.  The
-- two are *definitionally* equal — `cwSquarePartitionedTensor_support` is proved by `rfl` — so
-- the
-- transport below needs no rewriting.  Fallback if unification stalls: insert
-- `rw [show (cwSquarePartitionedTensor K dwz63Q).support = cwSquareSupport from rfl]` before the
-- `refine`, or state the map as `fun w ↦ (positiveWordEquiv cwSquareSupport n).symm w` and close
-- the type mismatch with `cwSquarePartitionedTensor_support`.
/-- **Every joint-typical lift of a leg word lies in the marginal-typical leg fibre.**

`positiveWordEquiv` carries the typed word-map fibre of the letterwise leg read into the
source-word leg fibre of the marginal-typical ambient, injectively. -/
theorem dwz63_card_typedWordMapFiber_le_card_sourceWordLegFiber (K : Type u) [CommRing K]
    (c : Leg) (n t : ℕ) (x : PositiveWord (Fin 5) n) :
    (WordType.typedWordMapFiber (dwz63PlainLegRead c)
        (WordType.proportionalCounts dwz63PlainAlpha t)
        (positiveWordEquiv (Fin 5) n x)).card ≤
      (PartitionHashEncoding.sourceWordLegFiber n (dwz63PlainMarginalWords K n t) c x).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun w ↦ (positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n).symm w) ?_ ?_
  · intro w hw
    rw [Finset.mem_coe, WordType.mem_typedWordMapFiber] at hw
    obtain ⟨htype, hleg⟩ := hw
    have hsymm : (positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n)
        ((positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n).symm w) = w :=
      Equiv.apply_symm_apply _ _
    have hread : ∀ c' : Leg,
        (fun j ↦ (((positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n)
            ((positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n).symm w)
              j).val c')) = dwz63PlainLegRead c' ∘ w := by
      intro c'
      funext j
      exact congrArg
        (fun v : Fin (n + 1) → ((cwSquarePartitionedTensor K dwz63Q).support) ↦ (v j).val c')
        hsymm
    have haddr := PartitionHashEncoding.positiveWordEquiv_supportWordAddress
      (A := fun _ : Leg ↦ Fin 5) (support := (cwSquarePartitionedTensor K dwz63Q).support) n
      ((positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n).symm w) c
    have hmem : (positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n).symm w ∈
        PartitionHashEncoding.sourceWordLegFiber n (dwz63PlainMarginalWords K n t) c x := by
      simp only [PartitionHashEncoding.sourceWordLegFiber, Finset.mem_filter]
      refine ⟨mem_dwz63PlainMarginalWords.mpr ?_, ?_⟩
      · intro c'
        refine (congrArg WordType.multiplicity (hread c')).trans ?_
        rw [WordType.multiplicity_comp_eq_mappedType, htype,
          mappedType_dwz63PlainLegRead_proportionalCounts]
      · apply (positiveWordEquiv (Fin 5) n).injective
        exact haddr.trans ((hread c).trans hleg)
    exact hmem
  · intro a _ b _ hab
    exact (positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n).symm.injective hab

/-! ## `hlower`, at one fixed word length -/

/-- **`hlower` at one word length.**

`(ᾱ_α / ᾱ_X) ^ (n + 1) ≤ loss(α) · |fibre|`, the committed pushed-fibre lower bound
instantiated
at the plain profile and transported to the marginal-typical `X`-leg fibre. -/
theorem dwz63_plainXBase_pow_le_loss_mul_card_sourceWordLegFiber (K : Type u) [CommRing K]
    {n t : ℕ} (ht : 0 < t)
    (hlen : WordType.profileMass dwz63PlainAlpha * t = n + 1)
    {x : PositiveWord (Fin 5) n} (hx : x ∈ dwz63PlainLegTargets .X n t) :
    (dwz63PlainRateAlpha / Real.exp dwz63EntropyX) ^ (n + 1) ≤
      WordType.structuralZeroMultinomialLoss dwz63PlainAlpha t *
        ((PartitionHashEncoding.sourceWordLegFiber n
          (dwz63PlainMarginalWords K n t) .X x).card : ℝ) := by
  have htarget : positiveWordEquiv (Fin 5) n x ∈ WordType.typeClass (n + 1)
      (WordType.proportionalCounts
        (WordType.mappedType (dwz63PlainLegRead .X) dwz63PlainAlpha) t) := by
    rw [WordType.mem_typeClass, mappedType_dwz63PlainLegRead]
    exact mem_dwz63PlainLegTargets.mp hx
  have hbound := WordType.pushedTypeFiberEntropyBase_pow_le_loss_mul_card_typedFiber_of_length_eq
    (dwz63PlainLegRead .X) dwz63PlainAlpha dwz63_plainAlpha_profileMass_pos t ht hlen
    (positiveWordEquiv (Fin 5) n x) htarget
  rw [dwz63_pushedTypeFiberEntropyBase_X_pow hlen] at hbound
  simp only [WordType.pushedTypeFiberLoss] at hbound
  refine hbound.trans (mul_le_mul_of_nonneg_left ?_
    (WordType.structuralZeroMultinomialLoss_pos dwz63PlainAlpha t).le)
  exact_mod_cast dwz63_card_typedWordMapFiber_le_card_sourceWordLegFiber K .X n t x

end AlgebraicComplexity.Examples
