/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.LocalizedCoarsenedSelection
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainMarginalAmbient

/-!
# Expanding a coarse square letter into its fine power

Layer 4 (`AlgebraicComplexity/Examples/`).  `[DuanWuZhou2022]`'s Additional Zeroing-Out Step 2 and
the Hole Lemma act on **small** (level-one) `Z`-blocks inside a retained **coarse** (level-two)
triple, so the count lane owes a bridge from a retained coarse-word constituent down to the fine
family it contains.

**That bridge is already committed at `HEAD`, in full generality.**
`Tensor/LocalizedCoarsenedSelection.lean` proves

* `coarsen_constituent_to_fineFiber` (`:627`) --- one coarse constituent restricts to the
  realization of its whole fine fiber, no representative chosen and no fiber cardinality
  discarded;
* `coarsen_constituent_to_fineFiberSelect` (`:652`) --- the same with an arbitrary legwise fine
  selection;
* `coarsenedPositivePower_constituent_to_fineFiberSelect` (`:680`) --- the word-level,
  quotient-first form, described in its own docstring as "the semantic interface used after
  hashing has isolated constituents";
* `indexedDirectSum_coarsenedPositivePower_constituent_to_fineFiberSelect` (`:699`) --- the
  indexed form, which is exactly the `⊕_retained` shape the batched Hole Lemma consumes.

The direction is the forward one this lane's paper note predicted: the coarse constituent
**restricts to** the fine family.  So this module contains no new mathematics; it instantiates
those four at the level-two square, where
`cwSquarePartitionedTensor K q = ((cwPartitionedTensor K q).positivePower 1).coarsen
cwSquareDegreeMap` (`Examples/CoppersmithWinogradSquare.lean:204-207`) and the fine alphabet is
`CWBlock` (`Examples/CoppersmithWinogradPartitionDataCore.lean:143-144`).

## The `keep` predicate is word-level, so nothing is left open

An earlier reading of this module flagged a residual step, on the grounds that the committed
bridges select fine labels one at a time.  **They do not.**  `keep` is
`∀ c, PositiveWord (A c) n → Prop` --- a predicate on the *whole* fine word per leg, exactly as
instantiated below --- and `segmentedRestrictedSplittingPower` is by definition the `select` of
the segmented `Keeps` predicate.  So the Hole Lemma's `hleaf` is
`dwz63_coarseWord_restricts_fineFiberSelect` instantiated at that predicate, with no gap between
them.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6 and `hole_lemma.tex`.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## One coarse letter -/

/-- **A coarse square constituent restricts to its fine fiber.**  The level-two square is the
degree-sum coarsening of the level-one partition's square, so this is
`coarsen_constituent_to_fineFiber` read at `cwSquareDegreeMap`. -/
theorem cwSquareConstituent_restricts_fineFiber (K : Type u) [CommRing K] (q : ℕ)
    (target : CWSquareAddress) (htarget : target ∈ (cwSquarePartitionedTensor K q).support) :
    Restricts ((cwSquarePartitionedTensor K q).constituent target)
      ((((cwPartitionedTensor K q).positivePower 1).coarseningFiber
        cwSquareDegreeMap target).realize) :=
  Tensor.Restricts.coarsen_constituent_to_fineFiber
    ((cwPartitionedTensor K q).positivePower 1) cwSquareDegreeMap target htarget

/-- **The same, under a legwise fine selection.**  This is the shape a split restriction would use
if the restriction were letterwise; see the module docstring for why the Hole Lemma's is not. -/
theorem cwSquareConstituent_restricts_fineFiberSelect (K : Type u) [CommRing K] (q : ℕ)
    (target : CWSquareAddress) (htarget : target ∈ (cwSquarePartitionedTensor K q).support)
    (keep : ∀ _c : Leg, PositiveWord CWBlock 1 → Prop) [∀ c a, Decidable (keep c a)] :
    Restricts ((cwSquarePartitionedTensor K q).constituent target)
      (((((cwPartitionedTensor K q).positivePower 1).coarseningFiber
        cwSquareDegreeMap target).select keep).realize) :=
  Tensor.Restricts.coarsen_constituent_to_fineFiberSelect
    ((cwPartitionedTensor K q).positivePower 1) cwSquareDegreeMap target htarget keep

/-! ## A whole coarse word -/

/-- **A retained coarse-word constituent restricts to its fine fiber.**

This is `dwz63_coarseWord_restricts_finePower` in the shape this lane stated, obtained from the
committed quotient-first bridge.  `target` ranges over the addresses the plain hash retains. -/
theorem dwz63_coarseWord_restricts_fineFiberSelect (K : Type u) [CommRing K] (n : ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (htarget : target ∈
      (((cwPartitionedTensor K dwz63Q).positivePower 1).coarsenedPositivePower
        cwSquareDegreeMap n).support)
    (keep : ∀ _c : Leg, PositiveWord (PositiveWord CWBlock 1) n → Prop)
    [∀ c w, Decidable (keep c w)] :
    Restricts
      ((((cwPartitionedTensor K dwz63Q).positivePower 1).coarsenedPositivePower
        cwSquareDegreeMap n).constituent target)
      (((((((cwPartitionedTensor K dwz63Q).positivePower 1).positivePower n).coarseningFiber
        (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) target).select keep).realize)) :=
  Tensor.Restricts.coarsenedPositivePower_constituent_to_fineFiberSelect
    ((cwPartitionedTensor K dwz63Q).positivePower 1) cwSquareDegreeMap n target htarget keep

/-- **The indexed form: every retained copy expands, with the outer index untouched.**

This is the `⊕_retained` shape `restricts_indexedDirectSum_segmentedHoleRepair_batched` consumes
on its left-hand side. -/
theorem dwz63_indexedDirectSum_coarseWord_restricts_fineFiberSelect
    {I : Type*} [Fintype I] (K : Type u) [CommRing K] (n : ℕ)
    (target : I → BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (htarget : ∀ i, target i ∈
      (((cwPartitionedTensor K dwz63Q).positivePower 1).coarsenedPositivePower
        cwSquareDegreeMap n).support)
    (keep : ∀ _c : Leg, PositiveWord (PositiveWord CWBlock 1) n → Prop)
    [∀ c w, Decidable (keep c w)] :
    Restricts
      (Tensor.indexedDirectSum (fun i ↦
        (((cwPartitionedTensor K dwz63Q).positivePower 1).coarsenedPositivePower
          cwSquareDegreeMap n).constituent (target i)))
      (Tensor.indexedDirectSum (fun i ↦
        ((((((cwPartitionedTensor K dwz63Q).positivePower 1).positivePower n).coarseningFiber
          (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) (target i)).select keep).realize))) :=
  Tensor.Restricts.indexedDirectSum_coarsenedPositivePower_constituent_to_fineFiberSelect
    ((cwPartitionedTensor K dwz63Q).positivePower 1) cwSquareDegreeMap n target htarget keep

end AlgebraicComplexity.Examples
