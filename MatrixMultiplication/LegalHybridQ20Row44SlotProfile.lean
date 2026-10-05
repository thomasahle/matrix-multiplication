/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.LevelFourPairGeometry
import MatrixMultiplication.Generated.LegalHybridQ20Row44Top

set_option autoImplicit false

/-!
# The literal ordered split profile of q20 row 44

This is the finite data input to Total-Weight's common-input-box construction,
`better_bound/paper.tex`, `cor:recursive-common-input-box`, lines 1085–1124. The ordered
left-child law is the object defined in [alman2025more],
`papers/sources/2404.16349/constituent.tex:41-47`. All numerators here are our own q20 data.

The sixteen parent-local slots correspond to nonconsecutive flat addresses. We identify them
with the committed pair geometry, then prove that zipping them with the displayed slot counts
and removing zero counts gives exactly the entries already reconstructed from the q20 top law.
The numerator sum is 1696. This is not a statement about a dense reconstructed beta cache,
supported fine words, or tensor extraction. The split-type adapter is in a separate module so
these small address computations do not import the tensor/entropy machinery.
-/

namespace MatrixMultiplication.LegalHybridQ20Row44SlotProfile

open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.Generated.LegalHybridQ20Row44Top

/-- The physical shape of parent six in the certificate geometry is `(1,7,8)`. -/
theorem row44_parentShape : positiveLevelFourShape ⟨6, by decide⟩ = ⟨1, 7, 8⟩ := by
  decide

/-- The actual ordered child pairs of parent six, in the certificate's slot order. -/
def row44Pairs : List (Shape × Shape) :=
  levelFourPairsForParent (positiveLevelFourShape ⟨6, by decide⟩)

/-- Explicit geometry of all sixteen slots, including the eight slots of zero mass. -/
theorem row44Pairs_eq : row44Pairs =
    [(⟨0, 0, 8⟩, ⟨1, 7, 0⟩), (⟨0, 1, 7⟩, ⟨1, 6, 1⟩),
     (⟨0, 2, 6⟩, ⟨1, 5, 2⟩), (⟨0, 3, 5⟩, ⟨1, 4, 3⟩),
     (⟨0, 4, 4⟩, ⟨1, 3, 4⟩), (⟨0, 5, 3⟩, ⟨1, 2, 5⟩),
     (⟨0, 6, 2⟩, ⟨1, 1, 6⟩), (⟨0, 7, 1⟩, ⟨1, 0, 7⟩),
     (⟨1, 0, 7⟩, ⟨0, 7, 1⟩), (⟨1, 1, 6⟩, ⟨0, 6, 2⟩),
     (⟨1, 2, 5⟩, ⟨0, 5, 3⟩), (⟨1, 3, 4⟩, ⟨0, 4, 4⟩),
     (⟨1, 4, 3⟩, ⟨0, 3, 5⟩), (⟨1, 5, 2⟩, ⟨0, 2, 6⟩),
     (⟨1, 6, 1⟩, ⟨0, 1, 7⟩), (⟨1, 7, 0⟩, ⟨0, 0, 8⟩)] := by
  rw [row44Pairs, row44_parentShape]
  decide

/-- Parent six has exactly sixteen genuine slots, not thirty padded slots. -/
theorem row44Pairs_length : row44Pairs.length = 16 := by
  rw [row44Pairs_eq]
  rfl

/-- Slotwise numerators, with structural zero entries retained. -/
def row44SlotNumerators : List ℕ :=
  [0, 0, 7, 175, 596, 71, 0, 0, 0, 0, 69, 596, 173, 9, 0, 0]

/-- There is one numerator for every genuine parent-local slot. -/
theorem row44SlotNumerators_length : row44SlotNumerators.length = 16 := rfl

/-- The exact unscaled ordered-split mass is 1696. -/
theorem row44SlotNumerators_sum : row44SlotNumerators.sum = 1696 := rfl

/-- Encoding the actual ordered pairs gives precisely the selected nonconsecutive q20 atoms.

Proof sketch: evaluate the small parent list once, establish each flat lookup separately, and
assemble the map symbolically. No sparse mass table is evaluated by this theorem. -/
theorem row44Pairs_atoms :
    row44Pairs.map (fun pair ↦ 288 + (1 * 6 + 1) * 1785 + levelFourPairs.idxOf pair) =
      row44Atoms := by
  have h0 : levelFourPairs.idxOf (⟨0, 0, 8⟩, ⟨1, 7, 0⟩) = 6 := by decide
  have h1 : levelFourPairs.idxOf (⟨0, 1, 7⟩, ⟨1, 6, 1⟩) = 34 := by decide
  have h2 : levelFourPairs.idxOf (⟨0, 2, 6⟩, ⟨1, 5, 2⟩) = 69 := by decide
  have h3 : levelFourPairs.idxOf (⟨0, 3, 5⟩, ⟨1, 4, 3⟩) = 104 := by decide
  have h4 : levelFourPairs.idxOf (⟨0, 4, 4⟩, ⟨1, 3, 4⟩) = 139 := by decide
  have h5 : levelFourPairs.idxOf (⟨0, 5, 3⟩, ⟨1, 2, 5⟩) = 174 := by decide
  -- This exact address calculation was independently reproduced in the row44 R4 consumer:
  -- reference build machine, 2026-09-05, 2.35 s / 1690160 KiB for the whole consumer.
  -- Later flat-list lookups need recursion depth 8192; heartbeats and memory are unchanged.
  have h6 : levelFourPairs.idxOf (⟨0, 6, 2⟩, ⟨1, 1, 6⟩) = 209 := by
    set_option maxRecDepth 8192 in decide
  have h7 : levelFourPairs.idxOf (⟨0, 7, 1⟩, ⟨1, 0, 7⟩) = 244 := by
    set_option maxRecDepth 8192 in decide
  have h8 : levelFourPairs.idxOf (⟨1, 0, 7⟩, ⟨0, 7, 1⟩) = 314 := by
    set_option maxRecDepth 8192 in decide
  have h9 : levelFourPairs.idxOf (⟨1, 1, 6⟩, ⟨0, 6, 2⟩) = 350 := by
    set_option maxRecDepth 8192 in decide
  have h10 : levelFourPairs.idxOf (⟨1, 2, 5⟩, ⟨0, 5, 3⟩) = 394 := by
    set_option maxRecDepth 8192 in decide
  have h11 : levelFourPairs.idxOf (⟨1, 3, 4⟩, ⟨0, 4, 4⟩) = 438 := by
    set_option maxRecDepth 8192 in decide
  have h12 : levelFourPairs.idxOf (⟨1, 4, 3⟩, ⟨0, 3, 5⟩) = 482 := by
    set_option maxRecDepth 8192 in decide
  have h13 : levelFourPairs.idxOf (⟨1, 5, 2⟩, ⟨0, 2, 6⟩) = 526 := by
    set_option maxRecDepth 8192 in decide
  have h14 : levelFourPairs.idxOf (⟨1, 6, 1⟩, ⟨0, 1, 7⟩) = 570 := by
    set_option maxRecDepth 8192 in decide
  have h15 : levelFourPairs.idxOf (⟨1, 7, 0⟩, ⟨0, 0, 8⟩) = 614 := by
    set_option maxRecDepth 8192 in decide
  rw [row44Pairs_eq]
  simp only [List.map_cons, List.map_nil, h0, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10, h11, h12, h13, h14, h15]
  rfl

/-- Sparse encoding of the slot numerators through the actual pair geometry. -/
def row44SlotEntries : List (ℕ × ℕ) :=
  ((row44Pairs.map
    (fun pair ↦ 288 + (1 * 6 + 1) * 1785 + levelFourPairs.idxOf pair)).zip
      row44SlotNumerators).filter (fun entry ↦ decide (0 < entry.2))

/-- The geometric slot profile reproduces the actual selected q20 top entries exactly.

Proof sketch: use the proved sparse-table reconstruction and address map, then check only the
sixteen small slot/count pairs. No dense top array or lower-level cache is reduced. -/
theorem row44TopEntries_eq_slotEntries : row44TopEntries = row44SlotEntries := by
  rw [row44TopEntries_eq, row44SlotEntries, row44Pairs_atoms]
  decide

end MatrixMultiplication.LegalHybridQ20Row44SlotProfile
