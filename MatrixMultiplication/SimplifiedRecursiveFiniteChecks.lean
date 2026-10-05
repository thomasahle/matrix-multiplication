/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles

/-!
# Bounded checkers for the simplified recursive certificate

The exact recursive-profile modules deliberately state their certificate obligations as ordinary
mathematical propositions.  This file supplies a small executable boundary for four of those
obligations:

* normalization of every labelled level-two child row used by a level-three node;
* equality of the reconstructed and semantic level-three parent rows;
* normalization of every labelled level-three child row used by a level-four parent; and
* equality of the reconstructed and semantic level-four parent rows.

Each checker enumerates only an explicitly finite type.  The accompanying soundness theorem turns
the Boolean result into the semantic proposition; generated modules therefore need contain only a
small equality proved by kernel reduction.  No optimizer output, certificate hash, selected node
list, or numerical floor is baked into this reusable adapter.

Boundary compatibility has a separate specialized checker in
`SimplifiedExponentLevelFourValidity.lean`; unlike the four predicates here, its semantic statement
quantifies over unbounded natural-valued coarse indices and needs a support argument in its
soundness proof.
-/

open scoped BigOperators

namespace MatrixMultiplication.SimplifiedRecursiveFiniteChecks

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.MoreAsymmetryCompatibility
open AlgebraicComplexity.Tensor
open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedRecursiveChildProfiles
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveParentTerms
open MatrixMultiplication.SimplifiedRecursiveSplitTypes
open MatrixMultiplication.SimplifiedVolumeReconstruction

/-- Executable universal quantification over the three tensor legs. -/
private def allLegs (predicate : Leg → Bool) : Bool :=
  predicate .X && predicate .Y && predicate .Z

/-- A successful three-leg check proves the predicate at any leg.

Proof sketch: split the requested leg into the three constructors and project the corresponding
Boolean conjunction. -/
private theorem allLegs_sound (predicate : Leg → Bool) (hcheck : allLegs predicate = true)
    (c : Leg) : predicate c = true := by
  cases c <;> simp_all [allLegs]

/-- A depth-two split word assembled from its four digits. -/
private def splitWordDepthTwoOfDigits (a b c d : SplitDigit) : SplitWord 2 :=
  ![a, b, c, d]

/-- Executable universal quantification over the 81 depth-two split words. -/
private def allDepthTwoWords (predicate : SplitWord 2 → Bool) : Bool :=
  (List.ofFn (fun a : SplitDigit ↦ a)).all fun a ↦
  (List.ofFn (fun b : SplitDigit ↦ b)).all fun b ↦
  (List.ofFn (fun c : SplitDigit ↦ c)).all fun c ↦
  (List.ofFn (fun d : SplitDigit ↦ d)).all fun d ↦
    predicate (splitWordDepthTwoOfDigits a b c d)

/-- A successful depth-two word check proves the predicate at every word.

Proof sketch: read the four digits from the requested word, project the four nested `List.all`
checks, and use function extensionality to identify the reconstructed word. -/
private theorem allDepthTwoWords_sound (predicate : SplitWord 2 → Bool)
    (hcheck : allDepthTwoWords predicate = true) (word : SplitWord 2) :
    predicate word = true := by
  let a : SplitDigit := word ⟨0, by decide⟩
  let b : SplitDigit := word ⟨1, by decide⟩
  let c : SplitDigit := word ⟨2, by decide⟩
  let d : SplitDigit := word ⟨3, by decide⟩
  have ha := (List.all_eq_true.mp hcheck) a (List.mem_ofFn.mpr ⟨a, rfl⟩)
  have hb := (List.all_eq_true.mp ha) b (List.mem_ofFn.mpr ⟨b, rfl⟩)
  have hc := (List.all_eq_true.mp hb) c (List.mem_ofFn.mpr ⟨c, rfl⟩)
  have hd := (List.all_eq_true.mp hc) d (List.mem_ofFn.mpr ⟨d, rfl⟩)
  have hword : splitWordDepthTwoOfDigits a b c d = word := by
    funext position
    fin_cases position <;> rfl
  simpa [allDepthTwoWords, hword] using hd

/-- A depth-three split word assembled from its eight digits. -/
private def splitWordDepthThreeOfDigits
    (a b c d e f g h : SplitDigit) : SplitWord 3 :=
  ![a, b, c, d, e, f, g, h]

/-- Executable universal quantification over the 6,561 depth-three split words. -/
private def allDepthThreeWords (predicate : SplitWord 3 → Bool) : Bool :=
  (List.ofFn (fun a : SplitDigit ↦ a)).all fun a ↦
  (List.ofFn (fun b : SplitDigit ↦ b)).all fun b ↦
  (List.ofFn (fun c : SplitDigit ↦ c)).all fun c ↦
  (List.ofFn (fun d : SplitDigit ↦ d)).all fun d ↦
  (List.ofFn (fun e : SplitDigit ↦ e)).all fun e ↦
  (List.ofFn (fun f : SplitDigit ↦ f)).all fun f ↦
  (List.ofFn (fun g : SplitDigit ↦ g)).all fun g ↦
  (List.ofFn (fun h : SplitDigit ↦ h)).all fun h ↦
    predicate (splitWordDepthThreeOfDigits a b c d e f g h)

/-- A successful depth-three word check proves the predicate at every word.

Proof sketch: project the eight nested checks at the requested word's digits, then identify the
reconstructed eight-coordinate function by extensionality. -/
private theorem allDepthThreeWords_sound (predicate : SplitWord 3 → Bool)
    (hcheck : allDepthThreeWords predicate = true) (word : SplitWord 3) :
    predicate word = true := by
  let a : SplitDigit := word ⟨0, by decide⟩
  let b : SplitDigit := word ⟨1, by decide⟩
  let c : SplitDigit := word ⟨2, by decide⟩
  let d : SplitDigit := word ⟨3, by decide⟩
  let e : SplitDigit := word ⟨4, by decide⟩
  let f : SplitDigit := word ⟨5, by decide⟩
  let g : SplitDigit := word ⟨6, by decide⟩
  let h : SplitDigit := word ⟨7, by decide⟩
  have ha := (List.all_eq_true.mp hcheck) a (List.mem_ofFn.mpr ⟨a, rfl⟩)
  have hb := (List.all_eq_true.mp ha) b (List.mem_ofFn.mpr ⟨b, rfl⟩)
  have hc := (List.all_eq_true.mp hb) c (List.mem_ofFn.mpr ⟨c, rfl⟩)
  have hd := (List.all_eq_true.mp hc) d (List.mem_ofFn.mpr ⟨d, rfl⟩)
  have he := (List.all_eq_true.mp hd) e (List.mem_ofFn.mpr ⟨e, rfl⟩)
  have hf := (List.all_eq_true.mp he) f (List.mem_ofFn.mpr ⟨f, rfl⟩)
  have hg := (List.all_eq_true.mp hf) g (List.mem_ofFn.mpr ⟨g, rfl⟩)
  have hh := (List.all_eq_true.mp hg) h (List.mem_ofFn.mpr ⟨h, rfl⟩)
  have hword : splitWordDepthThreeOfDigits a b c d e f g h = word := by
    funext position
    fin_cases position <;> rfl
  simpa [allDepthThreeWords, hword] using hh

/-! ## Level three -/

/-- Executable child-normalization check for one quotient, level-three node, and region. -/
def levelThreeChildRowsValidCheckFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation) : Bool :=
  (List.ofFn (fun slot : Fin PositiveLevelThreeData.splitSlotCount ↦ slot)).all fun slot ↦
    if hslot : PositiveLevelThreeData.splitSlotValid node slot then
      allLegs fun c ↦
        decide
          ((∑ word,
              levelThreeLeftChildWordCountFor supportSlot data node region sigma
                ⟨slot, hslot⟩ c word =
              levelTwoChildDenominator) ∧
            (∑ word,
              levelThreeRightChildWordCountFor supportSlot data node region sigma
                ⟨slot, hslot⟩ c word =
              levelTwoChildDenominator))
    else true

/-- Sorted-pair specialization of the level-three child-normalization checker. -/
def levelThreeChildRowsValidCheck
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation) : Bool :=
  levelThreeChildRowsValidCheckFor sortedPairSupportSlot data node region sigma

/-- Passing the quotient-parametric child checker proves normalization of every labelled row.

Proof sketch: select the requested genuine slot from the ten padded positions, project the
requested leg from the three-way Boolean conjunction, and decode the checked conjunction.
-/
theorem levelThreeChildRowsValidFor_of_check
    (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hcheck : levelThreeChildRowsValidCheckFor supportSlot data node region sigma = true) :
    LevelThreeChildRowsValidFor supportSlot data node region sigma := by
  intro slot c
  have hslot := (List.all_eq_true.mp hcheck) slot.1
    (List.mem_ofFn.mpr ⟨slot.1, rfl⟩)
  rw [dif_pos slot.2] at hslot
  exact of_decide_eq_true (allLegs_sound _ hslot c)

/-- Passing the level-three child checker proves exact normalization of every labelled child row.

Proof sketch: select the requested genuine slot from the ten padded positions, project the
requested leg from the three-way Boolean conjunction, and decode the checked conjunction with
`of_decide_eq_true`. -/
theorem levelThreeChildRowsValid_of_check
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hcheck : levelThreeChildRowsValidCheck data node region sigma = true) :
    LevelThreeChildRowsValid data node region sigma :=
  levelThreeChildRowsValidFor_of_check sortedPairSupportSlot data node region sigma hcheck

/-- Executable row-agreement check for one quotient, level-three node, and region. -/
def levelThreeEvaluatorRowsAgreeCheckFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation) : Bool :=
  allLegs fun c ↦ allDepthTwoWords fun word ↦
    decide (levelThreeParentWordCountFor supportSlot data node region sigma c word =
      levelThreeSemanticParentWordCountFor supportSlot data node region sigma c word)

/-- Sorted-pair specialization of the level-three evaluator-row checker. -/
def levelThreeEvaluatorRowsAgreeCheck
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation) : Bool :=
  levelThreeEvaluatorRowsAgreeCheckFor sortedPairSupportSlot data node region sigma

/-- Passing the quotient-parametric row checker identifies serialization with convolution.

Proof sketch: enumerate the finite leg and depth-two word types, then decode the checked natural
number equality. -/
theorem levelThreeEvaluatorRowsAgreeFor_of_check
    (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hcheck : levelThreeEvaluatorRowsAgreeCheckFor supportSlot data node region sigma = true) :
    LevelThreeEvaluatorRowsAgreeFor supportSlot data node region sigma := by
  intro c word
  exact of_decide_eq_true
    (allDepthTwoWords_sound _ (allLegs_sound _ hcheck c) word)

/-- Passing the level-three row checker identifies every evaluator row with its recursive semantic
convolution.

Proof sketch: enumerate the finite leg and depth-two word types, then decode the checked natural
number equality. -/
theorem levelThreeEvaluatorRowsAgree_of_check
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hcheck : levelThreeEvaluatorRowsAgreeCheck data node region sigma = true) :
    LevelThreeEvaluatorRowsAgree data node region sigma :=
  levelThreeEvaluatorRowsAgreeFor_of_check sortedPairSupportSlot data node region sigma hcheck

/-! ## Level four -/

/-- Executable child-normalization check for the nonzero support of one level-four parent row. -/
def levelFourChildRowsValidCheck
    (top : TopBranchRows) (betaThree : BetaThreeRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation) : Bool :=
  (List.ofFn (fun slot : Fin levelFourPairSlotCount ↦ slot)).all fun slot ↦
    if hslot : levelFourPairSlotValid parent slot then
      if _hactive : levelFourSlotNumerator top root region parent ⟨slot, hslot⟩ ≠ 0 then
        allLegs fun c ↦
          decide
            ((∑ word,
                levelFourLeftChildWordCount betaThree region parent sigma ⟨slot, hslot⟩ c word =
                  levelFourChildSamples) ∧
              (∑ word,
                levelFourRightChildWordCount betaThree region parent sigma ⟨slot, hslot⟩ c word =
                  levelFourChildSamples))
      else true
    else true

/-- Passing the level-four child checker proves exact normalization of every consumed child row.

Proof sketch: specialize the nested finite check at the requested parent-local slot, use its
nonzero numerator to enter the active branch, select the tensor leg, and decode the conjunction. -/
theorem levelFourChildRowsValid_of_check
    (top : TopBranchRows) (betaThree : BetaThreeRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (hcheck : levelFourChildRowsValidCheck top betaThree root region parent sigma = true) :
    LevelFourChildRowsValid top betaThree root region parent sigma := by
  intro slot c hactive
  have hslot := (List.all_eq_true.mp hcheck) slot.1
    (List.mem_ofFn.mpr ⟨slot.1, rfl⟩)
  rw [dif_pos slot.2, dif_pos hactive] at hslot
  exact of_decide_eq_true (allLegs_sound _ hslot c)

/-- Executable row-agreement check for one level-four parent, root, and incoming region. -/
def levelFourEvaluatorRowsAgreeCheck
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation) : Bool :=
  allLegs fun c ↦ allDepthThreeWords fun word ↦
    decide (levelFourEvaluatorParentWordCount top betaThree root region parent sigma c word =
      levelFourSemanticParentWordCount top betaThree root region parent sigma c word)

/-- Passing the level-four row checker identifies every evaluator row with its recursive semantic
convolution.

Proof sketch: specialize the finite check at one leg and one depth-three word and decode the
checked equality. -/
theorem levelFourEvaluatorRowsAgree_of_check
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hcheck : levelFourEvaluatorRowsAgreeCheck top betaThree root region parent sigma = true) :
    LevelFourEvaluatorRowsAgree top betaThree root region parent sigma := by
  intro c word
  exact of_decide_eq_true
    (allDepthThreeWords_sound _ (allLegs_sound _ hcheck c) word)

end MatrixMultiplication.SimplifiedRecursiveFiniteChecks
