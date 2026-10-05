/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradInterfaceCore

/-!
# Canonical all-zero CW words

This definition-only module names the all-zero native chunk word and its positive outer word.  It
also proves that the native split encoding is zero.  It intentionally does not import the generic
compatibility-zeroing theory used to establish shared-fiber properties of selected interfaces.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

/-- The native chunk word whose every base-CW block is the zero block. -/
def cwZeroChunkWord (depth : ℕ) : PositiveWord CWBlock (2 ^ depth - 1) :=
  positiveWordConst .zero (2 ^ depth - 1)

@[simp] theorem cwChunkSplitWord_zeroChunkWord (depth : ℕ) :
    cwChunkSplitWord depth (cwZeroChunkWord depth) = 0 := by
  funext position
  simp [cwChunkSplitWord, cwZeroChunkWord]

/-- The common outer block label on a zero coordinate: every selected chunk is the all-zero
native chunk word. -/
def cwZeroInterfaceLegWord (depth n : ℕ) :
    PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n :=
  positiveWordConst (cwZeroChunkWord depth) n

end AlgebraicComplexity.Examples
