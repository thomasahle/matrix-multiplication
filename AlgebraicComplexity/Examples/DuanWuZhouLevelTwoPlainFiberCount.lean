/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainMarginalSelect
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainCount
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSharpDegree

set_option autoImplicit false

/-!
# The leg fiber over the plain marginal-typical ambient

Layer 4 (`AlgebraicComplexity/Examples/`).  `exists_seed_dwz63PlainJointRetained` takes its fibre
hypothesis over `legalTargets n (dwz63PlainMarginalWords K n t)` --- the marginal-typical ambient,
which is the one a legwise `select` actually reaches.  This module counts that fibre exactly:

`#(dwz63PlainMarginalWords K n t) = dwz63PlainLegCount c n t * #(sourceWordLegFiber …)`,

so the fibre is `N_α' / N_c` division-free, and `card_sourceWordLegFiber_le_sharpDegree` is the
rounded form `hXfiber` consumes.

## The double count, and why surjectivity is not needed

The fibre map is `q ↦ supportWordAddress n q c`, and `mem_dwz63PlainMarginalWords_iff_keep` says it
lands in `dwz63PlainLegTargets c n t` --- the leg words the marginal cut keeps.
`Finset.card_eq_sum_card_fiberwise` then writes the ambient as a sum of fibres over that target
set, and every target in it carries **one and the same multiplicity**, so
`PartitionHashEncoding.card_sourceWordLegFiber_eq_of_multiplicity_eq` collapses the sum to a
constant.  No target need actually be hit: empty fibres are harmless, since they are equinumerous
with the rest and the identity is proved at a *fixed* `x`.  So no surjectivity, no completion
construction, and no existence argument enters.

The reindexing stability that lemma requires is immediate here: every condition of
`Dwz63PlainMarginalTypical` is a multiplicity, and `WordType.multiplicity_reindex` says
multiplicities do not see a permutation of the positions.

Nothing about the fifteen-cell *joint* profile is used --- the count is stated purely in terms of
the ambient's own cardinality --- so the joint-versus-marginal entropy gap is confined to the one
place it belongs, the rate.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

open scoped BigOperators

universe u

/-! ## The leg words the marginal cut keeps -/

/-- **The leg-`c` words kept by the plain marginal cut.** -/
noncomputable def dwz63PlainLegTargets (c : Leg) (n t : ℕ) :
    Finset (PositiveWord (Fin 5) n) := by
  classical
  exact Finset.univ.filter (dwz63PlainMarginalKeep n t c)

@[simp] theorem mem_dwz63PlainLegTargets {c : Leg} {n t : ℕ} {target : PositiveWord (Fin 5) n} :
    target ∈ dwz63PlainLegTargets c n t ↔ dwz63PlainMarginalKeep n t c target := by
  classical
  simp [dwz63PlainLegTargets]

/-- They are `N_c` in number: the leg-typed words, transported through `positiveWordEquiv`. -/
theorem card_dwz63PlainLegTargets (c : Leg) (n t : ℕ) :
    (dwz63PlainLegTargets c n t).card = dwz63PlainLegCount c n t := by
  classical
  rw [dwz63PlainLegCount]
  refine Finset.card_equiv (positiveWordEquiv (Fin 5) n) fun target ↦ ?_
  rw [mem_dwz63PlainLegTargets, WordType.mem_typeClass]
  exact Iff.rfl

/-! ## Reindexing stability of the ambient -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The marginal-typical family does not see a permutation of the positions.**  Every one of its
conditions is a multiplicity. -/
theorem dwz63PlainMarginalWords_stable (K : Type u) [CommRing K] (n t : ℕ)
    (e : Equiv.Perm (Fin (n + 1)))
    (q : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n) :
    q ∈ dwz63PlainMarginalWords K n t ↔
      PartitionHashEncoding.positiveWordReindex n e q ∈ dwz63PlainMarginalWords K n t := by
  have hleg : ∀ c : Leg,
      (fun j ↦ ((positiveWordEquiv _ n
          (PartitionHashEncoding.positiveWordReindex n e q) j).val c)) =
        (fun j ↦ ((positiveWordEquiv _ n q j).val c)) ∘ e.symm := by
    intro c
    funext j
    simp only [PartitionHashEncoding.positiveWordEquiv_positiveWordReindex, Function.comp_apply]
  simp only [mem_dwz63PlainMarginalWords, Dwz63PlainMarginalTypical]
  constructor
  · intro h c
    rw [hleg c, WordType.multiplicity_reindex]
    exact h c
  · intro h c
    have hc := h c
    rw [hleg c, WordType.multiplicity_reindex] at hc
    exact hc

/-! ## The double count -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The exact fibre identity over the marginal-typical ambient.**

`#ambient = N_c · #fibre`, for any kept leg word `x`.  Both halves are committed: the fibrewise
decomposition is `Finset.card_eq_sum_card_fiberwise`, and the equinumerosity of fibres over targets
of equal multiplicity is `PartitionHashEncoding.card_sourceWordLegFiber_eq_of_multiplicity_eq`. -/
theorem card_dwz63PlainMarginalWords_eq (K : Type u) [CommRing K] (c : Leg) (n t : ℕ)
    {x : PositiveWord (Fin 5) n} (hx : x ∈ dwz63PlainLegTargets c n t) :
    (dwz63PlainMarginalWords K n t).card =
      dwz63PlainLegCount c n t *
        (PartitionHashEncoding.sourceWordLegFiber n (dwz63PlainMarginalWords K n t) c x).card := by
  classical
  have hmaps : ∀ q ∈ dwz63PlainMarginalWords K n t,
      PartitionHashEncoding.supportWordAddress n q c ∈ dwz63PlainLegTargets c n t := by
    intro q hq
    rw [mem_dwz63PlainLegTargets]
    exact (mem_dwz63PlainMarginalWords_iff_keep K n t q).mp hq c
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hconst : ∀ target ∈ dwz63PlainLegTargets c n t,
      ((dwz63PlainMarginalWords K n t).filter fun q ↦
          PartitionHashEncoding.supportWordAddress n q c = target).card =
        (PartitionHashEncoding.sourceWordLegFiber n
          (dwz63PlainMarginalWords K n t) c x).card := by
    intro target htarget
    refine PartitionHashEncoding.card_sourceWordLegFiber_eq_of_multiplicity_eq n
      (dwz63PlainMarginalWords K n t) c
      (fun e word ↦ dwz63PlainMarginalWords_stable K n t e word) target x ?_
    rw [mem_dwz63PlainLegTargets] at htarget
    rw [mem_dwz63PlainLegTargets] at hx
    exact htarget.trans hx.symm
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, card_dwz63PlainLegTargets, smul_eq_mul]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The rounded form, in the shape `hXfiber` consumes.** -/
theorem card_sourceWordLegFiber_le_sharpDegree (K : Type u) [CommRing K] (c : Leg) {n t : ℕ}
    (hn : n + 1 = 100000000 * t) {x : PositiveWord (Fin 5) n}
    (hx : x ∈ dwz63PlainLegTargets c n t) :
    (PartitionHashEncoding.sourceWordLegFiber n (dwz63PlainMarginalWords K n t) c x).card ≤
      dwz63SharpDegree (dwz63PlainMarginalWords K n t).card (dwz63PlainLegCount c n t) := by
  have hpos : 0 < dwz63PlainLegCount c n t := dwz63PlainLegCount_pos c hn
  have hcount := card_dwz63PlainMarginalWords_eq K c n t hx
  have hdiv : (dwz63PlainMarginalWords K n t).card / dwz63PlainLegCount c n t =
      (PartitionHashEncoding.sourceWordLegFiber n (dwz63PlainMarginalWords K n t) c x).card := by
    refine Nat.div_eq_of_eq_mul_left hpos ?_
    rw [hcount]
    ring
  unfold dwz63SharpDegree
  rw [hdiv]
  exact Nat.le_succ _

end AlgebraicComplexity.Examples
