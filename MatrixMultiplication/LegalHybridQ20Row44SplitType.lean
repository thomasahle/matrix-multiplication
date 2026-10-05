/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.LegalHybridQ20Row44SlotProfile
import AlgebraicComplexity.MatrixMultiplication.RecursiveSplitCertificateGeometry

set_option autoImplicit false

/-!
# Exact ordered recursive split type for q20 row 44

The slot profile proved in `LegalHybridQ20Row44SlotProfile` is instantiated through the existing
`levelFourExactSplitType` constructor, not a second recursive distribution framework. This is
the finite ordered alpha input of Total-Weight `cor:recursive-common-input-box`,
`better_bound/paper.tex:1085-1124`, using the ordered-left-child definition in [alman2025more],
`papers/sources/2404.16349/constituent.tex:41-47`.

The same physical data can be read in any logical orientation. A nonempty abstract child-shape
type class demonstrates that the data conditions are satisfiable. This supplies neither a
supported fine CW word nor the parent beta-profile correspondence. The raw mass 1696 is not the
expanded occurrence mass: subsequent child products multiply it by their own exact denominator.
-/

open scoped BigOperators

namespace MatrixMultiplication.LegalHybridQ20Row44SplitType

open AlgebraicComplexity AlgebraicComplexity.Tensor
open AlgebraicComplexity.LevelFourReconstruction AlgebraicComplexity.MoreAsymmetryCompatibility
open MatrixMultiplication.LegalHybridQ20Row44SlotProfile

/-- Identify the sixteen small addresses with all genuine parent-six slots. -/
def row44SlotEquiv : Fin 16 ≃ LevelFourValidSlot ⟨6, by decide⟩ where
  toFun i := ⟨⟨i.val, by have := i.isLt; change i.val < 30; omega⟩, by
    change i.val < row44Pairs.length
    rw [row44Pairs_length]
    exact i.isLt⟩
  invFun slot := ⟨slot.val.val, by
    have h : slot.val.val < row44Pairs.length := slot.property
    rwa [row44Pairs_length] at h⟩
  left_inv i := by rfl
  right_inv slot := by rfl

/-- The exact numerator at a small slot address. -/
def row44Numerator (i : Fin 16) : ℕ :=
  row44SlotNumerators.get ⟨i.val, by rw [row44SlotNumerators_length]; exact i.isLt⟩

/-- Reading the numerator vector by finite indices recovers the original list. -/
theorem row44Numerator_ofFn : List.ofFn row44Numerator = row44SlotNumerators := by
  rfl

/-- Slot lookup preserves the proved exact total mass. -/
theorem row44Numerator_sum : ∑ i, row44Numerator i = 1696 := by
  rw [← List.sum_ofFn, row44Numerator_ofFn, row44SlotNumerators_sum]

/-- The same numerator function on the actual parent-local slot type. -/
def row44SlotCount (slot : LevelFourValidSlot ⟨6, by decide⟩) : ℕ :=
  row44Numerator (row44SlotEquiv.symm slot)

/-- Reindexing to valid certificate slots does not change the numerator mass. -/
theorem row44SlotCount_sum : ∑ slot, row44SlotCount slot = 1696 := by
  rw [← Equiv.sum_comp row44SlotEquiv]
  simpa [row44SlotCount] using row44Numerator_sum

/-- The actual q20 slot law as an exact ordered recursive split type, in any orientation. -/
noncomputable def row44ExactSplitType (sigma : Orientation) :
    ExactRecursiveSplitType ((positiveLevelFourShape ⟨6, by decide⟩).orientedLeg sigma)
      8 1696 :=
  levelFourExactSplitType ⟨6, by decide⟩ sigma 1696 row44SlotCount row44SlotCount_sum

/-- The instantiated ordered child-shape type has exactly 1696 samples. -/
theorem row44ExactSplitType_total (sigma : Orientation) :
    ∑ child, (row44ExactSplitType sigma).count child = 1696 :=
  (row44ExactSplitType sigma).total

/-- The concrete profile is realized by an abstract child-shape word; no tensor witness is
inferred from this combinatorial nonemptiness statement. -/
theorem row44ExactSplitType_nonempty (sigma : Orientation) :
    (WordType.typeClass 1696 (row44ExactSplitType sigma).count).Nonempty :=
  (row44ExactSplitType sigma).typeClass_nonempty

end MatrixMultiplication.LegalHybridQ20Row44SplitType
