/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveExactTargetSegmented

set_option autoImplicit false

/-!
# A two-cell satisfiability client for recursive exact targets

This file is a permanent small-model regression for the exact-target interface used in the proof
of Claim 6.18 of [alman2025more],
`papers/sources/2404.16349/constituent.tex:376-440`.  At recursion depth zero and with two parent
samples, it constructs an honest target over two Boolean part cells.  Every occurrence has the
legal nonzero coarse address `(2,0,0)`, the labelled `X` child is the one-letter word `2`, and the
`Y` and `Z` profiles are its complemented one-letter profile.

The example first proves membership using the original exact-target definition.  It then applies
both directions of `mem_cwRecursiveExactTargetFiberParts_iff_segmentMultiplicity`: the forward
direction produces the segmented equations, and the reverse direction reconstructs membership.
The public conclusion also exhibits two distinct occupied cells, two distinct canonical segments,
and positive entries in both cells, ruling out an all-zero or false-iff-false witness.

This is only a satisfiability test for the finite data-carrying hypotheses.  It asserts no tensor
restriction, counting estimate, asymptotic rate, or matrix-multiplication endpoint.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

private abbrev tinyOrientation : Orientation := Equiv.refl Leg

/-- The two parent samples receive genuinely different part tags. -/
private def tinyPartAt : Fin 2 → Bool :=
  Fin.cases false (fun _ : Fin 1 ↦ true)

/-- Every labelled occurrence lies in the legal nonzero coarse constituent `(2,0,0)`. -/
private def tinyReference : CWRecursiveCoarseAddress 0 1 :=
  fun logicalLeg _occurrence ↦
    match logicalLeg with
    | .X => 2
    | .Y => 0
    | .Z => 0

/-- The unique depth-zero split position carries digit two. -/
private def highWord : SplitWord 0 := fun _position ↦ 2

/-- The complementary depth-zero split word. -/
private def zeroWord : SplitWord 0 := fun _position ↦ 0

/-- Four labelled children: left and right children of each of the two parent samples. -/
private def exactChildren : Fin 4 → SplitWord 0 := fun _occurrence ↦ highWord

/-- The native parent represented by the explicit four-child word. -/
private noncomputable def tinyParent : PositiveWord (PositiveWord CWBlock 1) 1 :=
  (cwRecursiveLabelledChildrenEquiv 0 1).symm exactChildren

/-- The finite tagged source cells attached to the four labelled children. -/
private def tinyFiniteSource : Fin 4 → CWOrientedCoarseCell Bool 0 :=
  cwRecursiveOrientedFiniteCellSequence 0 1 tinyPartAt tinyOrientation tinyReference

/-- The same four source cells after forgetting the finite digit bounds. -/
private def tinyCoarseSource : Fin 4 → CoarseIndex Bool :=
  cwRecursiveOrientedCoarseIndexSequence 0 1 tinyPartAt tinyOrientation tinyReference

/-- The exact empirical `X` profile of the explicit source and child word. -/
private noncomputable def xProfile (cell : CoarseIndex Bool) (word : SplitWord 0) : ℕ :=
  cellMultiplicity tinyCoarseSource exactChildren cell word

/-- The first sample's left-child occurrence. -/
private def falseOccurrence : Fin 4 := Fin.castAdd 2 (0 : Fin 2)

/-- The second sample's left-child occurrence. -/
private def trueOccurrence : Fin 4 := Fin.castAdd 2 (1 : Fin 2)

private theorem tinyParent_children :
    cwRecursiveLabelledChildrenEquiv 0 1 tinyParent = exactChildren := by
  exact (cwRecursiveLabelledChildrenEquiv 0 1).apply_symm_apply exactChildren

private theorem tinyParent_labelledChildren :
    positiveWordLabelledChildren (cwChunkSplitWord 1) tinyParent = exactChildren := by
  rw [← cwRecursiveLabelledChildrenEquiv_apply 0 1 tinyParent]
  exact tinyParent_children

private theorem splitWordWeight_highWord : splitWordWeight highWord = 2 := by
  simp [splitWordWeight, highWord]

private theorem splitWordWeight_zeroWord : splitWordWeight zeroWord = 0 := by
  simp [splitWordWeight, zeroWord]

private theorem complement_highWord : complementSplitWord highWord = zeroWord := by
  funext position
  have hposition : position = 0 := Fin.eq_zero position
  subst position
  rfl

private theorem word_eq_zero_of_complement_eq_high {word : SplitWord 0}
    (hword : complementSplitWord word = highWord) : word = zeroWord := by
  calc
    word = complementSplitWord (complementSplitWord word) :=
      (complementSplitWord_complementSplitWord word).symm
    _ = complementSplitWord highWord := congrArg complementSplitWord hword
    _ = zeroWord := complement_highWord

private theorem exists_occurrence_of_xProfile_pos
    {cell : CoarseIndex Bool} {word : SplitWord 0} (hpositive : 0 < xProfile cell word) :
    ∃ occurrence : Fin 4,
      tinyCoarseSource occurrence = cell ∧ exactChildren occurrence = word := by
  classical
  unfold xProfile cellMultiplicity at hpositive
  rw [Finset.card_pos] at hpositive
  rcases hpositive with ⟨occurrence, hoccurrence⟩
  refine ⟨occurrence, ?_⟩
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hoccurrence

private theorem xProfile_pos_data
    {cell : CoarseIndex Bool} {word : SplitWord 0} (hpositive : 0 < xProfile cell word) :
    cell.x = 2 ∧ cell.y = 0 ∧ cell.z = 0 ∧ word = highWord := by
  rcases exists_occurrence_of_xProfile_pos hpositive with ⟨occurrence, rfl, rfl⟩
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem xProfile_eq_zero_of_x_eq_zero
    (cell : CoarseIndex Bool) (word : SplitWord 0) (hx : cell.x = 0) :
    xProfile cell word = 0 := by
  by_contra hnonzero
  have hpositive : 0 < xProfile cell word := Nat.pos_of_ne_zero hnonzero
  have htwo : cell.x = 2 := (xProfile_pos_data hpositive).1
  omega

/-- Exact targets for the three legs.  The pooled profiles are unused and identically zero. -/
private noncomputable def tinyTargets : CompatibilityTargets Bool 0 where
  xExact := xProfile
  yExact := fun cell word ↦ xProfile cell (complementSplitWord word)
  zExact := fun cell word ↦ xProfile cell (complementSplitWord word)
  yPooled := fun _part _total _word ↦ 0
  zPooled := fun _part _total _word ↦ 0
  yBoundary := by
    intro _cell _hz _word
    rfl
  zBoundaryOfX := by
    intro _cell _hy _word
    rfl
  zBoundaryOfY := by
    intro cell hx word
    rw [xProfile_eq_zero_of_x_eq_zero cell (complementSplitWord word) hx]
    rw [xProfile_eq_zero_of_x_eq_zero cell
      (complementSplitWord (complementSplitWord word)) hx]

private theorem tinyTargets_weightSupported : tinyTargets.IsWeightSupported := by
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro cell word hpositive
    change 0 < xProfile cell word at hpositive
    rcases xProfile_pos_data hpositive with ⟨hx, _hy, _hz, hword⟩
    simp [hword, hx, splitWordWeight_highWord]
  · intro cell word hpositive
    change 0 < xProfile cell (complementSplitWord word) at hpositive
    rcases xProfile_pos_data hpositive with ⟨_hx, hy, _hz, hword⟩
    have hzero : word = zeroWord := word_eq_zero_of_complement_eq_high hword
    simp [hzero, hy, splitWordWeight_zeroWord]
  · intro _part _total _word hpositive
    change 0 < (0 : ℕ) at hpositive
    omega
  · intro cell word hpositive
    change 0 < xProfile cell (complementSplitWord word) at hpositive
    rcases xProfile_pos_data hpositive with ⟨_hx, _hy, hz, hword⟩
    have hzero : word = zeroWord := word_eq_zero_of_complement_eq_high hword
    simp [hzero, hz, splitWordWeight_zeroWord]
  · intro _part _total _word hpositive
    change 0 < (0 : ℕ) at hpositive
    omega

private theorem coarseTotal_of_xProfile_pos
    {cell : CoarseIndex Bool} {word : SplitWord 0} (hpositive : 0 < xProfile cell word) :
    cell.x + cell.y + cell.z = coarseTotal 0 := by
  rcases xProfile_pos_data hpositive with ⟨hx, hy, hz, _hword⟩
  simp [hx, hy, hz, coarseTotal]

private theorem tinyTargets_coarseTotalSupported :
    CWRecursiveTargetCoarseTotalSupported tinyTargets := by
  intro logicalLeg cell word hpositive
  cases logicalLeg with
  | X =>
      change 0 < xProfile cell word at hpositive
      exact coarseTotal_of_xProfile_pos hpositive
  | Y =>
      change 0 < xProfile cell (complementSplitWord word) at hpositive
      exact coarseTotal_of_xProfile_pos hpositive
  | Z =>
      change 0 < xProfile cell (complementSplitWord word) at hpositive
      exact coarseTotal_of_xProfile_pos hpositive

private theorem tinyReference_literal (occurrence : Fin 4) :
    (tinyReference .X occurrence : ℕ) = 2 ∧
      (tinyReference .Y occurrence : ℕ) = 0 ∧
      (tinyReference .Z occurrence : ℕ) = 0 :=
  ⟨rfl, rfl, rfl⟩

private theorem tinyParent_coarseWord :
    cwRecursiveLabelledChildWord 0 1 tinyParent = tinyReference .X := by
  funext occurrence
  apply Fin.ext
  have hweight := val_cwRecursiveLabelledChildWord_eq_splitWordWeight
    0 1 tinyParent occurrence
  rw [tinyParent_labelledChildren] at hweight
  simpa [exactChildren, tinyReference, splitWordWeight_highWord, coarseTotal] using hweight

private theorem tinyParent_mem_oldFiber :
    tinyParent ∈ cwRecursiveExactTargetFiberParts
      tinyPartAt tinyOrientation tinyTargets tinyReference .X := by
  apply (mem_cwRecursiveExactTargetFiberParts_iff
    tinyPartAt tinyOrientation tinyTargets tinyReference .X tinyParent).2
  refine ⟨tinyParent_coarseWord, ?_⟩
  intro cell word
  change cellMultiplicity tinyCoarseSource
      (positiveWordLabelledChildren (cwChunkSplitWord 1) tinyParent) cell word =
    xProfile cell word
  rw [tinyParent_labelledChildren]
  rfl

private theorem tinyFiniteCells_ne :
    tinyFiniteSource falseOccurrence ≠ tinyFiniteSource trueOccurrence := by
  intro heq
  have hpart := congrArg Prod.fst heq
  change tinyPartAt (0 : Fin 2) = tinyPartAt (1 : Fin 2) at hpart
  have hzero : tinyPartAt (0 : Fin 2) = false := rfl
  have hone : tinyPartAt (1 : Fin 2) = true := by
    rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) by rfl]
    rfl
  have hfalseTrue : false = true := hzero.symm.trans (hpart.trans hone)
  cases hfalseTrue

private theorem tinySegments_ne :
    cwRecursiveExactTargetSegmentation
        0 1 tinyPartAt tinyOrientation tinyReference falseOccurrence ≠
      cwRecursiveExactTargetSegmentation
        0 1 tinyPartAt tinyOrientation tinyReference trueOccurrence := by
  intro heq
  apply tinyFiniteCells_ne
  apply (Fintype.equivFin (CWOrientedCoarseCell Bool 0)).injective
  simpa [cwRecursiveExactTargetSegmentation, WordType.finiteCellSegmentation,
    tinyFiniteSource, Function.comp_apply] using heq

private theorem tinyTarget_positive (occurrence : Fin 4) :
    0 < tinyTargets.exactProfile .X
      (tinyCoarseSource occurrence)
      (cwRecursiveLabelledChildrenEquiv 0 1 tinyParent occurrence) := by
  have hpositive := cellMultiplicity_pos_of_apply_eq
    tinyCoarseSource exactChildren occurrence
    (tinyCoarseSource occurrence) (exactChildren occurrence) rfl rfl
  change 0 < xProfile (tinyCoarseSource occurrence)
    (cwRecursiveLabelledChildrenEquiv 0 1 tinyParent occurrence)
  rw [tinyParent_children]
  exact hpositive

/-- **The recursive exact-target and segmented hypotheses have a nonzero two-cell model.**

The witnesses use two Boolean parts and two parent samples at depth zero.  The displayed reference
condition says every source cell has coarse address `(2,0,0)`.  The last existential exhibits two
different occupied cells whose canonical segment labels are also different and whose prescribed
`X` multiplicities are both positive.

Proof sketch: construct a parent from the inverse labelled-child equivalence applied to four
all-`2` child words.  Use their empirical cell multiplicities as the exact `X` table and complement
the words for `Y` and `Z`.  Direct finite support proves the original target membership.  The
forward direction of the public segmented iff gives every segment equation; its reverse direction
then reconstructs the displayed membership. -/
theorem cwRecursiveExactTargetSegmented_twoCell_nonvacuous :
    ∃ (partAt : Fin 2 → Bool)
      (targets : CompatibilityTargets Bool 0)
      (reference : CWRecursiveCoarseAddress 0 1)
      (parent : PositiveWord (PositiveWord CWBlock 1) 1),
      targets.IsWeightSupported ∧
        CWRecursiveTargetCoarseTotalSupported targets ∧
        (∀ occurrence : Fin 4,
          (reference .X occurrence : ℕ) = 2 ∧
            (reference .Y occurrence : ℕ) = 0 ∧
            (reference .Z occurrence : ℕ) = 0) ∧
        parent ∈ cwRecursiveExactTargetFiberParts
          partAt (Equiv.refl Leg) targets reference .X ∧
        (∀ segment : Fin (Fintype.card (CWOrientedCoarseCell Bool 0)),
          segmentMultiplicity
              (cwRecursiveExactTargetSegmentation
                0 1 partAt (Equiv.refl Leg) reference)
              (cwRecursiveLabelledChildrenEquiv 0 1 parent) segment =
            fun word ↦ targets.exactProfile .X
              (cwOrientedCoarseCellToIndex
                ((Fintype.equivFin (CWOrientedCoarseCell Bool 0)).symm segment)) word) ∧
        ∃ left right : Fin 4,
          cwRecursiveOrientedFiniteCellSequence
              0 1 partAt (Equiv.refl Leg) reference left ≠
            cwRecursiveOrientedFiniteCellSequence
              0 1 partAt (Equiv.refl Leg) reference right ∧
          cwRecursiveExactTargetSegmentation
              0 1 partAt (Equiv.refl Leg) reference left ≠
            cwRecursiveExactTargetSegmentation
              0 1 partAt (Equiv.refl Leg) reference right ∧
          0 < targets.exactProfile .X
            (cwRecursiveOrientedCoarseIndexSequence
              0 1 partAt (Equiv.refl Leg) reference left)
            (cwRecursiveLabelledChildrenEquiv 0 1 parent left) ∧
          0 < targets.exactProfile .X
            (cwRecursiveOrientedCoarseIndexSequence
              0 1 partAt (Equiv.refl Leg) reference right)
            (cwRecursiveLabelledChildrenEquiv 0 1 parent right) := by
  have hsegmented :=
    (mem_cwRecursiveExactTargetFiberParts_iff_segmentMultiplicity
      tinyPartAt tinyOrientation tinyTargets tinyTargets_weightSupported
      tinyTargets_coarseTotalSupported tinyReference .X tinyParent).mp
      tinyParent_mem_oldFiber
  have hmembership :=
    (mem_cwRecursiveExactTargetFiberParts_iff_segmentMultiplicity
      tinyPartAt tinyOrientation tinyTargets tinyTargets_weightSupported
      tinyTargets_coarseTotalSupported tinyReference .X tinyParent).mpr
      hsegmented
  refine ⟨tinyPartAt, tinyTargets, tinyReference, tinyParent,
    tinyTargets_weightSupported, tinyTargets_coarseTotalSupported,
    tinyReference_literal, hmembership, hsegmented, ?_⟩
  exact ⟨falseOccurrence, trueOccurrence, tinyFiniteCells_ne, tinySegments_ne,
    tinyTarget_positive falseOccurrence, tinyTarget_positive trueOccurrence⟩

end AlgebraicComplexity.Examples
