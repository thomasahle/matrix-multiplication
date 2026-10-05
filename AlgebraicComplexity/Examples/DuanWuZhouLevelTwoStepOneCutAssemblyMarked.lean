/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutStageUnconditional
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAggregateBatching
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAssembly
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarkedWitness

set_option autoImplicit false

/-!
# The section 6.3 stage over `𝒯^{(1)}`, at the marked family and one reference frame

Layer 4 (`AlgebraicComplexity/Examples/`).  `[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:98-121`, instantiated at section 6.3 (`:332-378`).

Each retained triple's broken copy is read in **its own frame**: the paper's copies are indexed by
the retained triples and compared against one standard-form `𝒯^*` (`:99`, `:102`), so a
relabelling of positions is needed per triple before `cor:hole_lemma`
(`hole_lemma.tex:159-168`) can treat them as copies of one tensor.

`dwz63FrameOf` fixes that relabelling **as a function of the address alone**.  That is the point of
this module: the frame must be available *before* a seed is chosen, because the hole-side
compatibility relation --- which the seed selection of image 129 fixes up front --- reads its small
block in the owner's frame.  A frame chosen inside the assembly, as
`dwz63_referenceLeafAssembly_stage_marked` (`Examples/DuanWuZhouLevelTwoAssemblyMarked.lean`) does,
cannot be referred to by that relation.  Taking the frame as a binder here, and instantiating it at
`dwz63FrameOf`, keeps the two consistent.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:98-121`, with `hole_lemma.tex:159-168`, at the section
6.3 instance (`global_value.tex:332-378`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v

noncomputable section

/-! ## The canonical reference frame -/

/-- **The frame of one large triple**: a position relabelling carrying the reference word onto the
address `g`, chosen once and for all as a function of `g`.

`global_value.tex:98-102` compares every broken copy with one standard-form `𝒯^*`; this is the
relabelling that makes the comparison, and making it depend on the address alone (not on the seed,
nor on the retained family) is what lets the compatibility relation of Additional Zeroing-Out Step 2
be fixed before a seed is selected. -/
def dwz63FrameOf (K : Type u) [CommRing K] (n : ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (g : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) : Equiv.Perm (Fin (n + 1)) := by
  classical
  exact if h : ∃ σ : Equiv.Perm (Fin (n + 1)),
      positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n
          (positiveWordPositionEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n σ wRef) = g
    then h.choose else 1

/-- **The canonical frame is a frame**, wherever one exists.

Proof sketch: the `dite` takes its positive branch and `Exists.choose_spec` is the equation. -/
theorem dwz63_frameOf_spec (K : Type u) [CommRing K] (n : ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (g : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)
    (h : ∃ σ : Equiv.Perm (Fin (n + 1)),
      positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n
          (positiveWordPositionEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n σ wRef) =
        g) :
    positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n
        (positiveWordPositionEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n
          (dwz63FrameOf K n wRef g) wRef) = g := by
  classical
  rw [dwz63FrameOf, dif_pos h]
  exact h.choose_spec

/-- **The owner's reading of a small block**: transport it into the owner's own canonical frame.

This is the `read` the hole side's compatibility relation uses; because `dwz63FrameOf` depends only
on the modelled address, so does this, and both are available before a seed is chosen. -/
def dwz63CanonicalRead {R : Type v} [Field R] (K : Type u) [CommRing K] (n : ℕ)
    (hinj : Function.Injective (cwSquareFieldValue (R := R)))
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (x : ProgressionHash.LegalTriple R (Fin (n + 1))
      (cwSquarePartitionHashEncoding hinj).target)
    (z : SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) :
    Fin (n + 1) → PositiveWord CWBlock 1 :=
  positiveWordEquiv (PositiveWord CWBlock 1) n
    (positiveWordPositionEquiv (PositiveWord CWBlock 1) n
      (dwz63FrameOf K n wRef ((cwSquarePartitionHashEncoding hinj).modeledAddress n x)) z.1)

/-! ## The stage at the marked family, with the frame as a binder -/

section Stage

variable {R : Type v} [Field R] [NeZero (2 : R)]

/-- **The section 6.3 stage over `𝒯^{(1)}`, at `markedWords := dwz63MarkedWords`, in a given
frame.**

The R1 re-issue of `dwz63_referenceLeafAssembly_stage_marked`
(`Examples/DuanWuZhouLevelTwoAssemblyMarked.lean`), differing in exactly two ways: the hole family
is image 145's `dwz63CutReferenceHoles` over the Step-1 cut, and the reference frame is a **binder**
rather than chosen internally (see the module docstring).

Proof sketch: `dwz63_aggregate_hbatch` and `dwz63_aggregate_hbudget` turn the aggregate hole
fraction into the batching data `cor:hole_lemma` needs (`hole_lemma.tex:161-165`), and
`dwz63_plainCutSymSixStage` runs the four degeneration steps. -/
theorem dwz63_cutReferenceLeafAssembly_stage_marked
    (K : Type u) [CommRing K]
    (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t s : ℕ)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (a₀ : dwz63PlainJointRetainedSupport K hinj n t
      (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)) B seed)
    (perm : dwz63PlainJointRetainedSupport K hinj n t
      (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)) B seed →
      Equiv.Perm (Fin (n + 1)))
    (hperm : ∀ a, positiveSupportWordBlockAddress
        ((cwSquarePartitionedTensor K dwz63Q).support) n
        (positiveWordPositionEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n
          (perm a) wRef) = (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (hpos : 0 < Fintype.card
      (SegmentedAvailableWord (dwz63Seg K n wRef) (dwz63JoinedAlphaTilde s)))
    (haggregate : Dwz63AggregateHoleFraction (dwz63Seg K n wRef) (dwz63JoinedAlphaTilde s)
      (dwz63PlainJointRetainedSupport K hinj n t
        (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)) B seed)
      (fun a ↦ dwz63CutReferenceHoles K _ a₀ s (dwz63JoinedAlphaTilde s) wRef perm a))
    {batches : ℕ} (hbatches : 0 < batches)
    (hfit : 2 * (batches * dwz63GoodBatchSize n) ≤
      (dwz63PlainJointRetainedSupport K hinj n t
        (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)) B seed).card) :
    Restricts
      (Tensor.power (symSix K (cwSquarePartitionedTensor K dwz63Q).realize) (n + 1))
      (Tensor.indexedDirectSum
        (fun _ : dwz63SymSixIndex (Fin batches) ↦
          symSix K (dwz63ReferenceLeaf K n (dwz63JoinedAlphaTilde s) wRef).realize)) :=
  dwz63_plainCutSymSixStage K hinj n t s
    (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t))
    (dwz63_marked_subset_marginal K n t) B hB seed a₀ rfl wRef perm hperm
    (dwz63GoodBatch (dwz63GoodCopies
      (fun a ↦ dwz63CutReferenceHoles K _ a₀ s (dwz63JoinedAlphaTilde s) wRef perm a))
      (dwz63GoodBatchSize n) hbatches)
    (dwz63_aggregate_hbatch (dwz63Seg K n wRef) (dwz63JoinedAlphaTilde s) _ _ hpos
      haggregate hbatches hfit)
    (dwz63_aggregate_hbudget (dwz63Seg K n wRef) (dwz63JoinedAlphaTilde s) _ _ hpos
      haggregate hbatches hfit)

end Stage

end

end AlgebraicComplexity.Examples
