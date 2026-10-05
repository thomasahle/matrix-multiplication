/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainMarginalAmbient
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSegmentationData
import AlgebraicComplexity.Combinatorics.MappedTypeIdentities

set_option autoImplicit false

/-!
# The marked family as a single joint type, and the reference-frame witness

Layer 4 (`AlgebraicComplexity/Examples/`).  The localized stage of `[duan2023faster]` §6.3 carries
every retained copy onto one reference leaf by a position permutation, so it needs each retained
address to be the block address of a word of the **same letter type** as the reference word.  That
holds exactly when the marked family is a single joint fifteen-cell type --- the paper's `N_alpha`,
as `card_markedXYIsolatedTargets_le_card_marked` already records ("bounded above by the marked
count `N_alpha`, never by the ambient count `N_triple`").

This module supplies the three facts for that choice:

* `dwz63_marked_subset_marginal` --- the joint type class is marginal-typical, so it is a legal
  `markedWords` for the hash (`hmarked`).  The joint type determines the three marginals, by the
  committed `mappedType_dwz63{X,Y,Z}Index_proportionalCounts`.
* `dwz63_referenceWord_mem_markedWords` --- the reference word of
  `Examples/DuanWuZhouLevelTwoReferenceWord.lean` lies in that class.  Its cell profile determines
  its letter profile because `dwz63CellEquiv` is a bijection.
* `dwz63_hwitness_of_markedWords` --- every retained address has a same-type preimage word, which
  is the hypothesis `exists_perm_positiveSupportWordBlockAddress`
  (`MatrixMultiplication/PositiveWordTypeTransport.lean`) turns into the reference frame.

## What this does not do

The endpoint chain currently hard-codes `markedWords := dwz63PlainMarginalWords` (inside
`omega_lt_2374631_of_plainBatchedStageAndLeaf_margin`'s own proof, and in its `hbatchCard` binder),
and `exists_behrend_dwz63_plainHashBranch` proves the branch bound at
`#(dwz63PlainMarginalWords)`.  So these facts cannot yet be threaded into the assembly telescope:
that needs the endpoint re-parameterised by `markedWords` and the branch bound re-calibrated at
`#(dwz63MarkedWords)`.  Both belong to the count side.  Nothing here assumes either.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v

/-! ## The joint type class is marginal-typical -/

/-- **`hmarked` at the joint type class.**  A word of the exact fifteen-cell type
`proportionalCounts dwz63Alpha t` has, on each leg, the corresponding marginal type, so it is
marginal-typical. -/
theorem dwz63_marked_subset_marginal (K : Type u) [CommRing K] (n t : ℕ) :
    dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t) ⊆
      dwz63PlainMarginalWords K n t := by
  classical
  intro q hq
  have hqt := mem_positiveTypeClass.1 hq
  refine mem_dwz63PlainMarginalWords.2 fun c ↦ ?_
  have hleg : (fun j ↦ ((positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support)
        n q j).val c))
      = (fun x : CWSquareSupport ↦ x.val c) ∘
        (positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n q) := rfl
  have hcomp : ∀ τ : Fin 15,
      ((fun x : CWSquareSupport ↦ x.val c) ∘ (dwz63CellEquiv : Fin 15 → CWSquareSupport)) τ
        = dwz63LegIndex c τ := by
    intro τ
    cases c <;> rfl
  calc WordType.multiplicity
        (fun j ↦ ((positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n q j).val c))
      = WordType.mappedType (fun x : CWSquareSupport ↦ x.val c)
          (WordType.multiplicity
            (positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n q)) := by
        rw [hleg]
        exact WordType.multiplicity_comp_eq_mappedType _ _
    _ = WordType.mappedType (fun x : CWSquareSupport ↦ x.val c)
          (WordType.mappedType (dwz63CellEquiv : Fin 15 → CWSquareSupport)
            (WordType.proportionalCounts dwz63Alpha t)) :=
        congrArg (WordType.mappedType (fun x : CWSquareSupport ↦ x.val c)) hqt
    _ = WordType.mappedType (dwz63LegIndex c) (WordType.proportionalCounts dwz63Alpha t) :=
        (WordType.mappedType_comp _ _ _).trans (WordType.mappedType_congr hcomp _)
    _ = WordType.proportionalCounts (dwz63AlphaMarginal c) t := by
        cases c
        · exact mappedType_dwz63XIndex_proportionalCounts t
        · exact mappedType_dwz63YIndex_proportionalCounts t
        · exact mappedType_dwz63ZIndex_proportionalCounts t

/-! ## The reference word lies in the marked family -/

/-- **The cell profile determines the letter profile.**  `dwz63CellEquiv` is a bijection, so a word
whose fifteen cells carry `profile` has letter type `mappedType dwz63CellEquiv profile`, which is
membership in `dwz63MarkedWords n profile`. -/
theorem dwz63_referenceWord_mem_markedWords (K : Type u) [CommRing K] (n : ℕ)
    (profile : Fin 15 → ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hprofile : WordType.multiplicity (dwz63Seg K n wRef) = profile) :
    wRef ∈ dwz63MarkedWords n profile := by
  classical
  refine mem_positiveTypeClass.2 ?_
  have hsymm : ∀ x : CWSquareSupport,
      dwz63CellIndex x.val = (dwz63CellEquiv.symm x : Fin 15) := by
    intro x
    have hx : dwz63Cell (dwz63CellEquiv.symm x) = x.val := by
      rw [← dwz63CellEquiv_coe, Equiv.apply_symm_apply]
    rw [← hx, dwz63CellIndex_dwz63Cell]
  have hpush : WordType.mappedType (fun x : CWSquareSupport ↦ dwz63CellIndex x.val)
      (WordType.multiplicity
        (positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n wRef)) = profile := by
    rw [← hprofile]
    exact (WordType.multiplicity_comp_eq_mappedType _ _).symm
  have hround : ∀ x : CWSquareSupport,
      ((dwz63CellEquiv : Fin 15 → CWSquareSupport) ∘
        (fun y : CWSquareSupport ↦ dwz63CellIndex y.val)) x = id x := by
    intro x
    show dwz63CellEquiv (dwz63CellIndex x.val) = x
    rw [hsymm x]
    exact dwz63CellEquiv.apply_symm_apply x
  have key : WordType.mappedType (dwz63CellEquiv : Fin 15 → CWSquareSupport) profile
      = WordType.multiplicity
        (positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n wRef) :=
    (congrArg (WordType.mappedType (dwz63CellEquiv : Fin 15 → CWSquareSupport)) hpush.symm).trans
      ((WordType.mappedType_comp _ _ _).trans
        ((WordType.mappedType_congr hround _).trans (WordType.mappedType_id _)))
  exact key.symm

/-! ## The witness -/

/-- **`hwitness` at the joint type class.**

Every retained address is the block address of a marked word: marked isolation never leaves the
marked family (`markedXYIsolatedTargets_subset_marked`), and a modeled legal target unpacks to its
source word (`exists_sourceWord_of_mem_modeledAddresses_legalTargets`).  Since the marked family is
one letter-multiplicity class, that word has the reference word's type. -/
theorem dwz63_hwitness_of_markedWords {R : Type v} [Field R] (K : Type u) [CommRing K]
    (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ) (profile : Fin 15 → ℕ)
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hwRef : wRef ∈ dwz63MarkedWords n profile)
    (a : (dwz63PlainJointRetainedSupport K hinj n t (dwz63MarkedWords n profile) B seed)) :
    ∃ w : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n,
      WordType.multiplicity
          (positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n wRef) =
        WordType.multiplicity
          (positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n w) ∧
      positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n w =
        (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) := by
  classical
  have hmem : (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) ∈
      (cwSquarePartitionHashEncoding hinj).modeledAddresses n
        ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63MarkedWords n profile)) := by
    have hsub := ProgressionHash.LegalTriple.markedXYIsolatedTargets_subset_marked
      ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63PlainMarginalWords K n t))
      ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63MarkedWords n profile)) B seed
    exact Finset.image_subset_image hsub a.2
  obtain ⟨q, hq, haddress⟩ :=
    (cwSquarePartitionHashEncoding hinj).exists_sourceWord_of_mem_modeledAddresses_legalTargets
      n (dwz63MarkedWords n profile) hmem
  refine ⟨q, ?_, haddress⟩
  exact (mem_positiveTypeClass.1 hwRef).trans (mem_positiveTypeClass.1 hq).symm

end AlgebraicComplexity.Examples
