/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.LevelFourPairGeometry

set_option autoImplicit false

/-!
# Lightweight level-four top-row definitions

This definition-only module contains the exact top-row lookup geometry used by the recursive
Coppersmith--Winograd recurrence [coppersmith1990matrix].  It preserves the established
qualified declarations while separating them from primary-table reconstruction and generated
certificate data.  The full recurrence owner re-exports these names and supplies the later
reconstruction and entropy layers.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

open AlgebraicComplexity.LevelFourReconstruction

/-- Bit width of each exact depth-three child profile. -/
def childBits : ℕ := 48

/-- Number of regional copies in the repeated-orientation construction. -/
def regionCount : ℕ := 6

/-- Width of a small constant-time leaf chunk in the positive top cache. -/
def topBranchChunkSize : ℕ := 64

/-- Row-and-leaf-chunked dense exact cache of the positive part of the sparse top distribution.

The two boundaries keep generated literals shallow enough for the elaborator, while all three
lookups remain constant-time array operations. -/
abbrev TopBranchRows := Array (Array (Array ℕ))

/-- Total lookup in a dense positive top cache. -/
def topNumeratorFrom (top : TopBranchRows) (root region pair : ℕ) : ℕ :=
  let row := top[root * regionCount + region]?.getD #[]
  (row[pair / topBranchChunkSize]?.getD #[])[pair % topBranchChunkSize]?.getD 0

/-- Positive parent occupying a proof-free certificate index. -/
def parentShapeAt (parent : ℕ) : Shape :=
  positiveLevelFourShapes[parent]?.getD default

/-- Ordered child pair at one proof-free parent-local slot. -/
def pairAt (parent slot : ℕ) : Shape × Shape :=
  (levelFourPairsForParent (parentShapeAt parent))[slot]?.getD default

/-- Global flat pair index of one parent-local ordered split. -/
def pairIndexAt (parent slot : ℕ) : ℕ :=
  levelFourPairs.idxOf (pairAt parent slot)

/-- Exact ordered top-split numerator at denominator `2^20`. -/
def topSplitNumerator (top : TopBranchRows)
    (root region parent slot : ℕ) : ℕ :=
  topNumeratorFrom top root region (pairIndexAt parent slot)

end MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
