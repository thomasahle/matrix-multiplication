/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.PushedProfileTypeCounting
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveOccurrenceConcentrationModel
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveRelaxedCoarseFamily
import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceTermScaling
import MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
import MatrixMultiplication.SimplifiedLevelFourOccurrenceProfileCore

set_option autoImplicit false

/-!
# Exact source words for level-four occurrence concentration

The relaxed recursive quotient family is indexed by words of child shapes, whereas the exact
level-four occurrence law is indexed by valid certificate slots.  The child-shape word forgets
which slot supplied a shape, so passing from the former to the latter is a genuine finite lifting
step rather than a choice of an arbitrary representative.

This module performs that lift by the exact pushed-type fiber identity.  Every marked relaxed
address has a valid-slot word of the prescribed proportional type.  Its first half is exactly the
word of left occurrence cells and its second half is exactly the same word transported by the
canonical complement permutation.  Self-complementary slots remain two labelled occurrences.

No parent complete-split law, compatibility count, cleanup, repair, tensor restriction, generated
certificate datum, or asymptotic estimate is used.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourValidity
open MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

/-- Repeat the exact recursively assembled parent term by a common positive-block factor. -/
def levelFourOccurrenceParentTerm
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (k : ℕ) : ExactInterfaceTermParameters 3 :=
  (levelFourRecursiveParentTerm top betaThree root region parent sigma hvalid).scale k

@[simp] theorem levelFourOccurrenceParentTerm_multiplicity
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (k : ℕ) :
    (levelFourOccurrenceParentTerm top betaThree root region parent sigma hvalid k).multiplicity =
      levelFourParentSamples top root region parent * k := by
  rw [levelFourOccurrenceParentTerm, ExactInterfaceTermParameters.scale_multiplicity,
    levelFourRecursiveParentTerm_multiplicity]

/-- With identity address orientation, the scaled term exposes the certificate's chosen logical
orientation directly. -/
@[simp] theorem cwRecursiveLogicalParent_levelFourOccurrenceParentTerm_refl
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (k : ℕ) :
    cwRecursiveLogicalParent
        (levelFourOccurrenceParentTerm top betaThree root region parent sigma hvalid k)
        (Equiv.refl Leg) =
      (positiveLevelFourShape parent).orientedLeg sigma := by
  rfl

/-- The certificate slot's child shape, transported once to the exact child-shape type expected
by the scaled interface term.  Keeping this transport named prevents dependent-type reductions
from leaking into the finite lifting proof. -/
def levelFourOccurrenceTermChildShape
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (k : ℕ) (slot : LevelFourValidSlot parent) :
    RecursiveChildShape
      (cwRecursiveLogicalParent
        (levelFourOccurrenceParentTerm top betaThree root region parent sigma hvalid k)
        (Equiv.refl Leg)) (coarseTotal 2) := by
  exact RecursiveChildShape.ofCoordinates
    (fun c ↦ (levelFourChildShape parent sigma slot).get c)
    (fun c ↦ by
      rw [cwRecursiveLogicalParent_levelFourOccurrenceParentTerm_refl]
      exact (levelFourChildShape parent sigma slot).get_le_parent c)
    (by
      simpa [coarseTotal] using (levelFourChildShape parent sigma slot).total_eq)

@[simp] theorem levelFourOccurrenceTermChildShape_get
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (k : ℕ) (slot : LevelFourValidSlot parent) (c : Leg) :
    (levelFourOccurrenceTermChildShape
      top betaThree root region parent sigma hvalid k slot).get c =
      (levelFourChildShape parent sigma slot).get c := by
  simp [levelFourOccurrenceTermChildShape]

/-- The typed transport respects the canonical slot-complement permutation exactly. -/
theorem levelFourOccurrenceTermChildShape_complement
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (k : ℕ) (slot : LevelFourValidSlot parent) :
    levelFourOccurrenceTermChildShape top betaThree root region parent sigma hvalid k
        (levelFourComplementSlotPerm parent slot) =
      RecursiveChildShape.complement
        (cwRecursiveLogicalParent_total
          (levelFourOccurrenceParentTerm top betaThree root region parent sigma hvalid k)
          (Equiv.refl Leg))
        (levelFourOccurrenceTermChildShape
          top betaThree root region parent sigma hvalid k slot) := by
  apply RecursiveChildShape.ext
  intro c
  simp only [levelFourOccurrenceTermChildShape_get,
    RecursiveChildShape.complement_get, levelFourComplementSlotPerm_apply]
  rw [levelFourChildShape_complement]
  simp only [RecursiveChildShape.complement_get]
  rw [cwRecursiveLogicalParent_levelFourOccurrenceParentTerm_refl]

/-- Exact pushed split type on child shapes induced by the proportional valid-slot profile. -/
noncomputable def levelFourOccurrenceSplitType
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (k n : ℕ)
    (hsamples :
      WordType.profileMass (levelFourOccurrenceSourceProfile top root region parent) * k = n + 1) :
    ExactRecursiveSplitType
      (cwRecursiveLogicalParent
        (levelFourOccurrenceParentTerm top betaThree root region parent sigma hvalid k)
        (Equiv.refl Leg)) (coarseTotal 2) (n + 1) :=
  ExactRecursiveSplitType.ofMappedCounts
    (levelFourOccurrenceTermChildShape
      top betaThree root region parent sigma hvalid k)
    (WordType.proportionalCounts
      (levelFourOccurrenceSourceProfile top root region parent) k)
    (by
      simpa only [WordType.profileMass, WordType.proportionalCounts, Finset.sum_mul]
        using hsamples)

@[simp] theorem levelFourOccurrenceSplitType_count
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (k n : ℕ)
    (hsamples :
      WordType.profileMass (levelFourOccurrenceSourceProfile top root region parent) * k = n + 1)
    (child : RecursiveChildShape
      (cwRecursiveLogicalParent
        (levelFourOccurrenceParentTerm top betaThree root region parent sigma hvalid k)
        (Equiv.refl Leg)) (coarseTotal 2)) :
    (levelFourOccurrenceSplitType top betaThree root region parent sigma hvalid k n
      hsamples).count child =
      WordType.mappedType
        (levelFourOccurrenceTermChildShape
          top betaThree root region parent sigma hvalid k)
        (WordType.proportionalCounts
          (levelFourOccurrenceSourceProfile top root region parent) k) child :=
  rfl

/-- A marked relaxed quotient address has an exact valid-slot lift, and its doubled address is
literally the left occurrence-cell word followed by its complement-transported copy. -/
theorem exists_levelFourOccurrenceStateWord_of_markedReference
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (k n : ℕ)
    (hsamples :
      WordType.profileMass (levelFourOccurrenceSourceProfile top root region parent) * k = n + 1)
    (reference : CWRecursiveCoarseAddress 2 n)
    (hreference : reference ∈
      cwRecursiveRelaxedMarkedCoarseSupport
        (levelFourOccurrenceParentTerm top betaThree root region parent sigma hvalid k)
        (Equiv.refl Leg)
        (levelFourOccurrenceSplitType top betaThree root region parent sigma hvalid k n
          hsamples)) :
    ∃ state : Fin (n + 1) → LevelFourValidSlot parent,
      WordType.multiplicity state =
          WordType.proportionalCounts
            (levelFourOccurrenceSourceProfile top root region parent) k ∧
        cwRecursiveOrientedFiniteCellSequence 2 n (fun _ ↦ PUnit.unit)
            (Equiv.refl Leg) reference =
          Fin.append
            (cwRecursiveOccurrenceStateCell 2
              (levelFourOccurrenceCoarseIndex parent sigma)
              (levelFourOccurrenceCoarseIndex_total parent sigma) ∘ state)
            (cwRecursiveOccurrenceStateCell 2
              (levelFourOccurrenceCoarseIndex parent sigma)
              (levelFourOccurrenceCoarseIndex_total parent sigma) ∘
                levelFourComplementSlotPerm parent ∘ state) := by
  classical
  unfold cwRecursiveRelaxedMarkedCoarseSupport at hreference
  obtain ⟨word, hword, href⟩ := Finset.mem_image.mp hreference
  subst reference
  have htarget :
      word ∈ WordType.typeClass (n + 1)
        (WordType.mappedType
          (levelFourOccurrenceTermChildShape
            top betaThree root region parent sigma hvalid k)
          (WordType.proportionalCounts
            (levelFourOccurrenceSourceProfile top root region parent) k)) := by
    rw [WordType.mem_typeClass]
    rw [MoreAsymmetryCompatibility.ExactRecursiveSplitType.mem_markedWords] at hword
    exact hword.trans (by
      funext child
      exact levelFourOccurrenceSplitType_count
        top betaThree root region parent sigma hvalid k n hsamples child)
  have hsourceType :
      WordType.proportionalCounts
          (levelFourOccurrenceSourceProfile top root region parent) k ∈
        WordType.types (LevelFourValidSlot parent) (n + 1) := by
    rw [WordType.mem_types]
    simpa only [WordType.profileMass, WordType.proportionalCounts, Finset.sum_mul]
      using hsamples
  have hfiber :
      (WordType.typedWordMapFiber
        (levelFourOccurrenceTermChildShape
          top betaThree root region parent sigma hvalid k)
        (WordType.proportionalCounts
          (levelFourOccurrenceSourceProfile top root region parent) k) word).Nonempty := by
    rw [← Finset.card_pos]
    have hfactor := WordType.card_targetType_mul_card_typedWordMapFiber
      (levelFourOccurrenceTermChildShape
        top betaThree root region parent sigma hvalid k)
      (WordType.proportionalCounts
        (levelFourOccurrenceSourceProfile top root region parent) k) word htarget
    have hpositive :
        0 < (WordType.typeClass (n + 1)
          (WordType.proportionalCounts
            (levelFourOccurrenceSourceProfile top root region parent) k)).card :=
      Finset.card_pos.mpr (WordType.typeClass_nonempty _ hsourceType)
    rw [← hfactor] at hpositive
    exact Nat.pos_of_mul_pos_left hpositive
  obtain ⟨state, hstate⟩ := hfiber
  have hstate' := WordType.mem_typedWordMapFiber.mp hstate
  refine ⟨state, hstate'.1, ?_⟩
  funext occurrence
  refine Fin.addCases ?_ ?_ occurrence <;> intro sample
  · simp only [Fin.append_left, Function.comp_apply,
      cwRecursiveOrientedFiniteCellSequence,
      cwRecursiveCoarseAddressOfLeftShapeWord_left,
      labelledChildParts_left]
    apply Prod.ext
    · rfl
    · funext c
      apply Fin.ext
      simp only [ExactRecursiveSplitType.coordinate_val,
        cwRecursiveOccurrenceStateCell, cwRecursiveOccurrenceFiniteCell,
        levelFourOccurrenceCoarseIndex, levelFourOccurrenceChildShape_left,
        recursiveChildShapeCoarseIndex_get]
      have hshape := congrFun hstate'.2 sample
      simpa only [Function.comp_apply, levelFourOccurrenceTermChildShape_get] using
        congrArg (fun child ↦ child.get c) hshape.symm
  · simp only [Fin.append_right, Function.comp_apply,
      cwRecursiveOrientedFiniteCellSequence,
      cwRecursiveCoarseAddressOfLeftShapeWord_right,
      labelledChildParts_right]
    apply Prod.ext
    · rfl
    · funext c
      apply Fin.ext
      simp only [ExactRecursiveSplitType.coordinate_val,
        RecursiveChildShape.complementPerm_apply,
        cwRecursiveOccurrenceStateCell, cwRecursiveOccurrenceFiniteCell,
        levelFourOccurrenceCoarseIndex, levelFourOccurrenceChildShape_left,
        recursiveChildShapeCoarseIndex_get]
      have hshape := congrFun hstate'.2 sample
      rw [← levelFourOccurrenceTermChildShape_get
        top betaThree root region parent sigma hvalid k
          (levelFourComplementSlotPerm parent (state sample)) c,
        levelFourOccurrenceTermChildShape_complement]
      exact congrArg
        (fun child ↦
          (RecursiveChildShape.complement
            (cwRecursiveLogicalParent_total
              (levelFourOccurrenceParentTerm
                top betaThree root region parent sigma hvalid k)
              (Equiv.refl Leg)) child).get c)
        hshape.symm

end AlgebraicComplexity.Examples
