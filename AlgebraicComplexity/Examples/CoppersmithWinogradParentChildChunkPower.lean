/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveChunkSplit
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTargetRelabeling
import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorRegionalDivision
import AlgebraicComplexity.Tensor.PartitionedPowerExternalInterchange
import AlgebraicComplexity.Tensor.PartitionedReindexStructureRelabeling

set_option autoImplicit false

/-!
# A power of parent chunks is a power of labelled child chunks

A positive power of the depth-`depth + 1` Coppersmith--Winograd chunk partition carries the same
partitioned tensor as the twice-as-long positive power of the depth-`depth` chunk partition.  This
module exhibits that identification as an exact legwise partition reindex and computes its label
equivalence: it is exactly the doubled labelled-child alphabet of
`cwRecursiveLabelledChildrenEquiv`, read through the complete-split encoding.

## What this closes

`CWRecursiveChildOccurrenceRelabelingLift` asks, for a permutation `tau` of the `2 (n + 1)`
labelled child occurrences, for a structure relabeling of
`(cwChunkPartitionedTensor K q (depth + 1)).positivePower n` acting on every leg by
`cwRecursiveChildOccurrencePartEquiv depth n tau`.  The committed
`positivePowerPositionRelabeling` only realizes permutations of *outer* chunk positions, so it
cannot see a permutation that breaks and remakes the left/right parent pairing.  The two facts
proved here supply exactly the missing geometry:

* `cwParentChunkPower_reindexEquiv` and `cwChildChunkPower_reindexEquiv` present both powers as
  reindexes of one common external square, so their composite label equivalence
  `cwParentChildChunkWordEquiv` is an exact partition reindex in both directions;
* `cwRecursiveChildOccurrencePartEquiv_eq_conj` proves that every decoded child-occurrence
  permutation is the `cwParentChildChunkWordEquiv`-conjugate of an ordinary *position* permutation
  of the doubled child word.

Composing these with `exists_positivePowerPositionRelabeling` on the child power and the transport
of structure relabelings across a partition reindex discharges the lift, in
`cwRecursiveChildOccurrenceRelabelingLift_holds`, for **every** permutation of
`Fin ((n + 1) + (n + 1))` -- not only for members of the doubled tagged-cell stabilizer, which is
strictly stronger than the hypothesis its client names.

## Why the reduction is available at all

The label-level half of the identification is already committed:
`cwRecursiveChunkJoin_eq_standard` states that splitting a native parent chunk into its two
complete-split children is exactly inverse to positive-word concatenation.  Everything below is the
propagation of that single identity through one middle-four interchange and one word
concatenation; no arithmetic on flattened base positions occurs.

No hole estimate, survivor count, tensor degeneration, entropy bound, or certificate-specific
number occurs here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

/-! ## The doubled child word -/

/-- The `2 (n + 1)` labelled child positions counted as one concatenation of two blocks of
`n + 1`. -/
theorem cwDoubledChildLength (n : ℕ) : n + n + 1 + 1 = (n + 1) + (n + 1) := by omega

/-- Join a pair of child-chunk words into the parent-chunk word of the same length, position by
position. -/
noncomputable def cwParentChildChunkWordJoin (depth n : ℕ) :
    PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n ×
        PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n ≃
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n :=
  (positiveWordProdEquiv (PositiveWord CWBlock (2 ^ depth - 1))
      (PositiveWord CWBlock (2 ^ depth - 1)) n).trans
    (positiveWordCongrEquiv (cwStandardChunkJoin depth) n)

/-- Reading a joined parent word at one sample joins the two child chunks at that sample. -/
theorem positiveWordEquiv_cwParentChildChunkWordJoin (depth n : ℕ)
    (u v : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) (i : Fin (n + 1)) :
    positiveWordEquiv (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n
        (cwParentChildChunkWordJoin depth n (u, v)) i =
      cwStandardChunkJoin depth
        (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n u i,
          positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n v i) := by
  have hstep : cwParentChildChunkWordJoin depth n (u, v) =
      positiveWordCongrEquiv (cwStandardChunkJoin depth) n
        (positiveWordProdEquiv (PositiveWord CWBlock (2 ^ depth - 1))
          (PositiveWord CWBlock (2 ^ depth - 1)) n (u, v)) := rfl
  rw [hstep,
    congrFun (positiveWordEquiv_positiveWordCongrEquiv (cwStandardChunkJoin depth) n _) i,
    congrFun (positiveWordEquiv_positiveWordProdEquiv
      (PositiveWord CWBlock (2 ^ depth - 1)) (PositiveWord CWBlock (2 ^ depth - 1)) n u v) i]

/-- The left labelled child of a joined parent word is the encoded left source chunk. -/
theorem cwRecursiveLabelledChildren_join_left (depth n : ℕ)
    (u v : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) (i : Fin (n + 1)) :
    cwRecursiveLabelledChildrenEquiv depth n
        (cwParentChildChunkWordJoin depth n (u, v)) (Fin.castAdd (n + 1) i) =
      cwChunkSplitWord depth
        (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n u i) := by
  rw [cwRecursiveLabelledChildrenEquiv_apply, positiveWordLabelledChildren_left,
    positiveWordEquiv_cwParentChildChunkWordJoin, leftChildHalf_eq_splitWordSuccEquiv,
    cwStandardChunkJoin_encoded, splitWordSuccEquiv_concatSplitWords]

/-- The right labelled child of a joined parent word is the encoded right source chunk. -/
theorem cwRecursiveLabelledChildren_join_right (depth n : ℕ)
    (u v : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) (i : Fin (n + 1)) :
    cwRecursiveLabelledChildrenEquiv depth n
        (cwParentChildChunkWordJoin depth n (u, v)) (Fin.natAdd (n + 1) i) =
      cwChunkSplitWord depth
        (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n v i) := by
  rw [cwRecursiveLabelledChildrenEquiv_apply, positiveWordLabelledChildren_right,
    positiveWordEquiv_cwParentChildChunkWordJoin, rightChildHalf_eq_splitWordSuccEquiv,
    cwStandardChunkJoin_encoded, splitWordSuccEquiv_concatSplitWords]

/-- A word of `n + 1` parent chunks is a word of `2 (n + 1)` labelled child chunks, all left
occurrences first. -/
noncomputable def cwParentChildChunkWordEquiv (depth n : ℕ) :
    PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n ≃
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) (n + n + 1) :=
  (cwParentChildChunkWordJoin depth n).symm.trans
    (positiveWordAppendEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n n)

/-- The decoded child word reads, at every doubled position, as the labelled child occurrence at
that position. -/
theorem positiveWordEquiv_cwParentChildChunkWordEquiv (depth n : ℕ)
    (w : PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    (k : Fin (n + n + 1 + 1)) :
    positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) (n + n + 1)
        (cwParentChildChunkWordEquiv depth n w) k =
      (cwChunkSplitWordEquiv depth).symm
        (cwRecursiveLabelledChildrenEquiv depth n w
          (Fin.cast (cwDoubledChildLength n) k)) := by
  rcases hp : (cwParentChildChunkWordJoin depth n).symm w with ⟨u, v⟩
  have hw : cwParentChildChunkWordJoin depth n (u, v) = w := by
    rw [← hp]
    exact (cwParentChildChunkWordJoin depth n).apply_symm_apply w
  have hword : cwParentChildChunkWordEquiv depth n w = positiveWordAppend u n v := by
    have hunfold : cwParentChildChunkWordEquiv depth n w =
        positiveWordAppendEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n n
          ((cwParentChildChunkWordJoin depth n).symm w) := rfl
    rw [hunfold, hp, positiveWordAppendEquiv_apply]
  rw [hword, ← hw, congrFun (positiveWordEquiv_append u v) k, Function.comp_apply]
  generalize hj : Fin.cast (cwDoubledChildLength n) k = j
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
  · rw [Fin.append_left, cwRecursiveLabelledChildren_join_left]
    exact ((cwChunkSplitWordEquiv depth).symm_apply_apply _).symm
  · rw [Fin.append_right, cwRecursiveLabelledChildren_join_right]
    exact ((cwChunkSplitWordEquiv depth).symm_apply_apply _).symm

/-! ## The conjugation identity -/

/-- A permutation of labelled child occurrences, read on the concatenated child word. -/
def cwDoubledPositionPerm (n : ℕ) (tau : Equiv.Perm (Fin ((n + 1) + (n + 1)))) :
    Equiv.Perm (Fin (n + n + 1 + 1)) :=
  (finCongr (cwDoubledChildLength n)).trans
    (tau.trans (finCongr (cwDoubledChildLength n)).symm)

/-- **The seam.**  Every decoded child-occurrence permutation of parent-chunk words is the
`cwParentChildChunkWordEquiv`-conjugate of an ordinary position permutation of the doubled child
word.

This is what makes the missing lift reachable: position permutations of a positive partitioned
power are realized by genuine structure relabelings, and conjugating a relabeling across an exact
partition reindex is again a relabeling. -/
theorem cwRecursiveChildOccurrencePartEquiv_eq_conj (depth n : ℕ)
    (tau : Equiv.Perm (Fin ((n + 1) + (n + 1)))) :
    cwRecursiveChildOccurrencePartEquiv depth n tau =
      (cwParentChildChunkWordEquiv depth n).trans
        ((positiveWordPositionEquiv (PositiveWord CWBlock (2 ^ depth - 1)) (n + n + 1)
            (cwDoubledPositionPerm n tau)).trans
          (cwParentChildChunkWordEquiv depth n).symm) := by
  have key : ∀ w : PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n,
      cwParentChildChunkWordEquiv depth n
          (cwRecursiveChildOccurrencePartEquiv depth n tau w) =
        positiveWordPositionEquiv (PositiveWord CWBlock (2 ^ depth - 1)) (n + n + 1)
          (cwDoubledPositionPerm n tau) (cwParentChildChunkWordEquiv depth n w) := by
    intro w
    apply (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) (n + n + 1)).injective
    funext k
    rw [positiveWordEquiv_position_apply, Function.comp_apply,
      positiveWordEquiv_cwParentChildChunkWordEquiv,
      positiveWordEquiv_cwParentChildChunkWordEquiv,
      cwRecursiveLabelledChildrenEquiv_childOccurrencePartEquiv_apply, Function.comp_apply]
    congr 1
  apply Equiv.ext
  intro w
  rw [Equiv.trans_apply, Equiv.trans_apply, ← key w, Equiv.symm_apply_apply]

/-! ## The two partition reindexes -/

variable (K : Type u) [CommRing K] (q : ℕ)

/-- The depth-`depth + 1` chunk partition is the external square of the depth-`depth` chunk
partition, reindexed by native consecutive-word joining. -/
theorem cwChunkPartitionedTensor_succ_reindexEquiv (depth : ℕ) :
    ((cwChunkPartitionedTensor K q depth).external
        (cwChunkPartitionedTensor K q depth)).ReindexEquiv
      (cwChunkPartitionedTensor K q (depth + 1))
      (fun _ ↦ cwStandardChunkJoin depth) := by
  have happend :
      (((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).external
          ((cwPartitionedTensor K q).positivePower (2 ^ depth - 1))).ReindexEquiv
        ((cwPartitionedTensor K q).positivePower
          ((2 ^ depth - 1) + (2 ^ depth - 1) + 1))
        (fun _ ↦ positiveWordAppendEquiv CWBlock (2 ^ depth - 1) (2 ^ depth - 1)) :=
    ⟨_, PartitionedTensor.appendPositiveWordPartitions_positivePowers
      (cwPartitionedTensor K q) (2 ^ depth - 1) (2 ^ depth - 1)⟩
  have hcast := PartitionedTensor.reindexEquiv_positivePower_cast
    (cwPartitionedTensor K q) (cwChunkParameter_succ depth).symm
  exact PartitionedTensor.ReindexEquiv.congr_equiv (by funext c; rfl)
    (happend.trans hcast)

/-- A positive power of parent chunks is an exact legwise reindex of the external square of the
corresponding power of child chunks. -/
theorem cwParentChunkPower_reindexEquiv (depth n : ℕ) :
    (((cwChunkPartitionedTensor K q depth).positivePower n).external
        ((cwChunkPartitionedTensor K q depth).positivePower n)).ReindexEquiv
      ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n)
      (fun _ ↦ cwParentChildChunkWordJoin depth n) := by
  exact PartitionedTensor.ReindexEquiv.congr_equiv (by funext c; rfl)
    ((PartitionedTensor.reindexEquiv_positivePower_external
        (cwChunkPartitionedTensor K q depth) (cwChunkPartitionedTensor K q depth) n).trans
      ((cwChunkPartitionedTensor_succ_reindexEquiv K q depth).positivePower n))

/-- The twice-as-long positive power of child chunks is an exact legwise reindex of the same
external square, by word concatenation. -/
theorem cwChildChunkPower_reindexEquiv (depth n : ℕ) :
    (((cwChunkPartitionedTensor K q depth).positivePower n).external
        ((cwChunkPartitionedTensor K q depth).positivePower n)).ReindexEquiv
      ((cwChunkPartitionedTensor K q depth).positivePower (n + n + 1))
      (fun _ ↦ positiveWordAppendEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n n) :=
  ⟨_, PartitionedTensor.appendPositiveWordPartitions_positivePowers
    (cwChunkPartitionedTensor K q depth) n n⟩

/-! ## Discharging the recursive child-occurrence lift -/

/-- Every permutation of the `2 (n + 1)` labelled child occurrences is realized by a genuine
structure relabeling of the nested parent-chunk positive power, acting on each leg by the decoded
child-occurrence permutation.

Proof sketch: both the parent power and the twice-as-long child power are exact legwise reindexes
of one common external square, so a position relabeling of the child power transports backward to
the square and forward to the parent power.  The resulting `partEquiv` is the
`cwParentChildChunkWordEquiv`-conjugate of that position permutation, which
`cwRecursiveChildOccurrencePartEquiv_eq_conj` identifies with the decoded permutation. -/
theorem exists_cwRecursiveChildOccurrenceRelabeling
    (K : Type) [CommRing K] (q : ℕ) (depth n : ℕ)
    (tau : Equiv.Perm (Fin ((n + 1) + (n + 1)))) :
    ∃ r : ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n).StructureRelabeling,
      ∀ physicalLeg,
        r.partEquiv physicalLeg = cwRecursiveChildOccurrencePartEquiv depth n tau := by
  obtain ⟨childBlocks, hchild⟩ := cwChildChunkPower_reindexEquiv K q depth n
  obtain ⟨parentBlocks, hparent⟩ := cwParentChunkPower_reindexEquiv K q depth n
  refine ⟨PartitionedTensor.StructureRelabeling.toReindex _ parentBlocks hparent
    (PartitionedTensor.StructureRelabeling.ofReindex _ childBlocks hchild
      (PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling
        (cwChunkPartitionedTensor K q depth) (n + n + 1)
        (cwDoubledPositionPerm n tau))), ?_⟩
  intro physicalLeg
  rw [cwRecursiveChildOccurrencePartEquiv_eq_conj]
  simp only [PartitionedTensor.StructureRelabeling.toReindex_partEquiv,
    PartitionedTensor.StructureRelabeling.ofReindex_partEquiv,
    PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling_partEquiv]
  apply Equiv.ext
  intro word
  rfl

/-- **The honest geometric premise of the recursive target relabeling package is discharged.**

The doubled tagged-cell stabilizer hypothesis is not used: the relabeling exists for every
permutation of labelled child occurrences. -/
theorem cwRecursiveChildOccurrenceRelabelingLift_holds
    (K : Type) [CommRing K] (q : ℕ) {Part : Type} [Fintype Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (orientation : Orientation) (reference : CWRecursiveCoarseAddress depth n) :
    CWRecursiveChildOccurrenceRelabelingLift K q depth n partAt orientation reference :=
  fun tau ↦ exists_cwRecursiveChildOccurrenceRelabeling K q depth n tau.1

end AlgebraicComplexity.Examples
