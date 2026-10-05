/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradNestedTotalWeightCoarsening
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateInput

set_option autoImplicit false

/-!
# Actual-support encoding for the nested total-weight quotient

The Total-Weight construction hashes a level-four CW row only after retaining the ordered pair of
depth-one total weights inside each depth-two child.  This module proves the first finite semantic
fact needed by that hash: every coordinate of the **actual** coarsened source is a legal
depth-one total-weight triple.  It then encodes the actual supported addresses injectively as the
legal triples consumed by the generic hashing API.

The local legality equation transcribes the tight total-weight equation
`eq:total-weight-tight` of *Total-Weight Hashing and Rectangular Volume in the
Coppersmith--Winograd Method*, `better_bound/paper.tex:1290-1300`, at the forced level-two
granularity of Remark `rem:granularity-forced`, `better_bound/paper.tex:1784-1801`.  The nested
blocks themselves follow Definition `def:split-hatI` of [alman2025more],
`papers/sources/2404.16349/prelim.tex:225-232,249-269`.

This is the support-side input to the recursive quotient-count requirement
`hyp:quotient-count`, `better_bound/paper.tex:1729-1761`; it does not itself prove the
competitor-count or whole-fibre clauses of that hypothesis.

This file deliberately does **not** define the ambient competitor family or a partition model.
The paper's `rem:quotient-count-nonexamples`, `better_bound/paper.tex:1763-1768`, forbids
replacing the actual intrinsic family by all locally legal quotient words.  Those objects must be
added only after the certificate's refined intrinsic nested family has been reconstructed.

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
- *Total-Weight Hashing and Rectangular Volume in the Coppersmith--Winograd Method*.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u v

/-! ## The local four-symbol legality equation -/

/-- Three fine-legal depth-two words give a legal total-weight triple on each of their two
ordered depth-one halves.

In human terms, each chosen half contains two CW positions.  The three leg digits sum to two at
each position, so the three half-weights sum to `2 + 2 = 4 = coarseTotal 1`.

Proof sketch: split on the left/right half.  Expand each half-weight as a two-position sum,
exchange the position and leg sums, and apply the supplied fine-legality equation at each parent
position. -/
theorem cwDepthTwoTotalWeightPayload_sum_eq_coarseTotal
    (x y z : SplitWord 2)
    (hlegal : ∀ position,
      (x position : ℕ) + (y position : ℕ) + (z position : ℕ) = 2)
    (side : Fin 2) :
    (cwDepthTwoTotalWeightPayload x side : ℕ) +
        (cwDepthTwoTotalWeightPayload y side : ℕ) +
      (cwDepthTwoTotalWeightPayload z side : ℕ) = coarseTotal 1 := by
  fin_cases side
  · change
      splitWordWeight (leftChildHalf x) +
          splitWordWeight (leftChildHalf y) +
        splitWordWeight (leftChildHalf z) = coarseTotal 1
    unfold splitWordWeight
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    calc
      (∑ position : Fin (2 ^ 1),
          ((leftChildHalf x position : ℕ) +
            (leftChildHalf y position : ℕ) +
              (leftChildHalf z position : ℕ))) =
          ∑ _position : Fin (2 ^ 1), 2 := by
            apply Finset.sum_congr rfl
            intro position _
            simpa only [leftChildHalf_apply] using
              hlegal (leftChildPosition 1 position)
      _ = coarseTotal 1 := by simp [coarseTotal]
  · change
      splitWordWeight (rightChildHalf x) +
          splitWordWeight (rightChildHalf y) +
        splitWordWeight (rightChildHalf z) = coarseTotal 1
    unfold splitWordWeight
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    calc
      (∑ position : Fin (2 ^ 1),
          ((rightChildHalf x position : ℕ) +
            (rightChildHalf y position : ℕ) +
              (rightChildHalf z position : ℕ))) =
          ∑ _position : Fin (2 ^ 1), 2 := by
            apply Finset.sum_congr rfl
            intro position _
            simpa only [rightChildHalf_apply] using
              hlegal (rightChildPosition 1 position)
      _ = coarseTotal 1 := by simp [coarseTotal]

/-! ## Legality of the actual selected source -/

/-- The actual depth-three alpha-selected row after the four-symbol level-two total-weight
coarsening.

The definition retains the physical leg order.  Region orientation is applied only when the
supported address is encoded as a legal triple below. -/
noncomputable def cwRecursiveApproximateNestedTotalWeightTerm
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (2 + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal 2) (n + 1)) :=
  (cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).coarsen
    (cwLevelFourNestedTotalWeightCoarsening n)

/-- Every coordinate in the actual nested total-weight support satisfies the tight depth-one
equation `x + y + z = 4`.

Proof sketch: unpack coarsened-support membership to an actual fine address.  The approximate
interface selector is a restriction of the positive CW power, hence its three depth-two child
words are coordinatewise fine-legal.  Apply the preceding two-half lemma at the requested child
occurrence and side. -/
theorem cwRecursiveApproximateNestedTotalWeightTerm_coarse_sum
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (2 + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal 2) (n + 1))
    (address : CWLevelFourNestedTotalWeightAddress n)
    (haddress : address ∈
      (cwRecursiveApproximateNestedTotalWeightTerm
        K q term hmultiplicity epsilon sigma alpha).support)
    (index : CWLevelFourNestedTotalWeightIndex n) :
    (address .X index : ℕ) + (address .Y index : ℕ) +
        (address .Z index : ℕ) = coarseTotal 1 := by
  classical
  change address ∈
    ((cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).coarsen
      (cwLevelFourNestedTotalWeightCoarsening n)).support at haddress
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at haddress
  obtain ⟨fine, hfine, rfl⟩ := haddress
  have hparent : fine ∈
      (cwSelectedApproximateInterfaceTerm K q
        (cwRecursiveSemanticParentTerm term hmultiplicity)
        (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
        epsilon).support :=
    (mem_cwRecursiveApproximateAlphaMarginalSelectedTerm_support
      K q term hmultiplicity epsilon sigma alpha fine).mp hfine |>.1
  let partAt : Fin (n + 1) → PUnit.{1} := fun _ ↦ PUnit.unit
  let model := cwRecursiveChildCompatibilityModel 2 n partAt
  have hfineLegal : model.IsFineLegal fine :=
    cwRecursiveChildCompatibilityModel_isFineLegal_of_mem_approximateSelected_support
      K q partAt term hmultiplicity epsilon fine hparent
  obtain ⟨occurrence, side⟩ := index
  exact cwDepthTwoTotalWeightPayload_sum_eq_coarseTotal
    (positiveWordLabelledChildren (cwChunkSplitWord (2 + 1))
      (fine .X) occurrence)
    (positiveWordLabelledChildren (cwChunkSplitWord (2 + 1))
      (fine .Y) occurrence)
    (positiveWordLabelledChildren (cwChunkSplitWord (2 + 1))
      (fine .Z) occurrence)
    (fun position ↦ hfineLegal occurrence position) side

/-! ## Injective legal-triple encoding of the actual support -/

namespace CWCoarseFieldEncoding

variable {R : Type v} [Field R]

/-- Encode one actually supported nested address as a legal affine-hashing triple in logical leg
order.

No inverse or ambient family is hidden in this definition: `source` is literally a member of the
actual coarsened support. -/
def cwLevelFourNestedTotalWeightOrientedLegalTriple
    (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (2 + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal 2) (n + 1))
    (source : {address : CWLevelFourNestedTotalWeightAddress n //
      address ∈ (cwRecursiveApproximateNestedTotalWeightTerm
        K q term hmultiplicity epsilon sigma alpha).support}) :
    ProgressionHash.LegalTriple R
      (CWLevelFourNestedTotalWeightIndex n) encoding.target where
  xIndex index := encoding.encode (source.1 (sigma .X) index)
  yIndex index := encoding.encode (source.1 (sigma .Y) index)
  zIndex index := encoding.encode (source.1 (sigma .Z) index)
  legal index := by
    apply encoding.legal_of_val_sum
    have hsum := cwRecursiveApproximateNestedTotalWeightTerm_coarse_sum
      K q term hmultiplicity epsilon sigma alpha source.1 source.2 index
    have hperm :
        (∑ c : Leg, (source.1 (sigma c) index : ℕ)) =
          ∑ c : Leg, (source.1 c index : ℕ) :=
      Equiv.sum_comp sigma (fun c : Leg ↦ (source.1 c index : ℕ))
    calc
      (source.1 (sigma .X) index : ℕ) +
          (source.1 (sigma .Y) index : ℕ) +
          (source.1 (sigma .Z) index : ℕ) =
        ∑ c : Leg, (source.1 (sigma c) index : ℕ) := by
          simp [Tensor.sum_leg]
      _ = ∑ c : Leg, (source.1 c index : ℕ) := hperm
      _ = coarseTotal 1 := by simpa [Tensor.sum_leg] using hsum

/-- The oriented legal-triple encoding loses no actually supported nested address.

Proof sketch: compare the three logical hashing words, cancel the injective field encoding
coordinatewise, and use surjectivity of the orientation permutation to recover every physical
leg. -/
theorem cwLevelFourNestedTotalWeightOrientedLegalTriple_injective
    (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (2 + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal 2) (n + 1)) :
    Function.Injective
      (encoding.cwLevelFourNestedTotalWeightOrientedLegalTriple
        K q term hmultiplicity epsilon sigma alpha) := by
  intro left right h
  apply Subtype.ext
  funext physicalLeg index
  generalize hlogical : sigma.symm physicalLeg = logicalLeg
  have hphysical : sigma logicalLeg = physicalLeg := by
    rw [← hlogical]
    exact sigma.apply_symm_apply physicalLeg
  apply encoding.encode_injective
  cases logicalLeg with
  | X =>
      rw [← hphysical]
      simpa [cwLevelFourNestedTotalWeightOrientedLegalTriple] using
        congrFun (congrArg ProgressionHash.LegalTriple.xIndex h) index
  | Y =>
      rw [← hphysical]
      simpa [cwLevelFourNestedTotalWeightOrientedLegalTriple] using
        congrFun (congrArg ProgressionHash.LegalTriple.yIndex h) index
  | Z =>
      rw [← hphysical]
      simpa [cwLevelFourNestedTotalWeightOrientedLegalTriple] using
        congrFun (congrArg ProgressionHash.LegalTriple.zIndex h) index

/-- The finite legal-target family represented by the actual nested coarsened support.

This is a present family, not the larger intrinsic ambient competitor family required by the
paper's quotient-count hypothesis. -/
noncomputable def cwLevelFourNestedTotalWeightPresentTargets
    (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (2 + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal 2) (n + 1)) :
    Finset (ProgressionHash.LegalTriple R
      (CWLevelFourNestedTotalWeightIndex n) encoding.target) := by
  classical
  exact Finset.univ.image
    (encoding.cwLevelFourNestedTotalWeightOrientedLegalTriple
      K q term hmultiplicity epsilon sigma alpha)

/-- Encoding the actual nested support preserves its cardinality exactly. -/
@[simp] theorem card_cwLevelFourNestedTotalWeightPresentTargets
    (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (2 + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal 2) (n + 1)) :
    (encoding.cwLevelFourNestedTotalWeightPresentTargets
      K q term hmultiplicity epsilon sigma alpha).card =
      (cwRecursiveApproximateNestedTotalWeightTerm
        K q term hmultiplicity epsilon sigma alpha).support.card := by
  classical
  unfold cwLevelFourNestedTotalWeightPresentTargets
  rw [Finset.card_image_of_injOn
    (encoding.cwLevelFourNestedTotalWeightOrientedLegalTriple_injective
      K q term hmultiplicity epsilon sigma alpha).injOn]
  simp

end CWCoarseFieldEncoding

end AlgebraicComplexity.Examples
