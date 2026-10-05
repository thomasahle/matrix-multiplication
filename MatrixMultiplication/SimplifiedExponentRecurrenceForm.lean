/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SignedDyadicLogFormDefs
import MatrixMultiplication.SimplifiedExponentRecurrenceInput

/-!
# Lightweight exact forms for the level-two exponent recurrence

The generated level-two checker only needs to turn an exact three-integer `EdgeInput` into a
signed dyadic logarithm form.  It does not need sparse-table reconstruction or the real-valued
proof that the form denotes entropy.  This module provides that narrow exact boundary.

`SimplifiedExponentRecurrence.lean` imports these definitions and proves their semantic evaluation
laws.  Generated normalization certificates may instead import this file directly, keeping their
proof terms and import closure independent of the much larger recurrence implementation.
-/

namespace MatrixMultiplication.SimplifiedExponentRecurrence

open MatrixMultiplication.SignedDyadicLogForm

/-- Number of dyadic bits used by the top distribution. -/
def topBits : Nat := 20

/-- Number of dyadic bits used by each local distribution. -/
def localBits : Nat := 12

/-- Common denominator exponent of a level-two occurrence mass. -/
def levelTwoOccurrenceBits : Nat := topBits + localBits + localBits

/-- Common denominator exponent after weighting a local entropy term. -/
def levelTwoFormBits : Nat := levelTwoOccurrenceBits + localBits

/-- One occurrence-weighted entropy summand in the common exact signed-log representation. -/
def weightedEntropyTermForm (occurrence numerator : Nat) : Form :=
  if numerator = 0 then Form.zero
  else
    { constantNumerator := occurrence * numerator * localBits
      terms := [⟨numerator, -(occurrence * numerator : Int)⟩] }

/-- The three-symbol entropy form with numerator profile `(mu, 2^12 - 2*mu, mu)`. -/
def positiveEdgeEntropyForm (occurrence numerator : Nat) : Form :=
  Form.sum [
    weightedEntropyTermForm occurrence numerator,
    weightedEntropyTermForm occurrence (2 ^ localBits - 2 * numerator),
    weightedEntropyTermForm occurrence numerator]

namespace Chunked

/-- Exact signed-log form contributed by one level-two input to one coordinate branch. -/
def inputForm (input : EdgeInput) (coordinate : Fin 3) : Form :=
  if input.occurrenceNumerator = 0 then Form.zero
  else if coordinate.val = input.heavyCoordinate then
    positiveEdgeEntropyForm input.occurrenceNumerator input.muNumerator
  else
    { constantNumerator := input.occurrenceNumerator * 2 ^ localBits, terms := [] }

/-- Exact branch form obtained by summing the forms of a finite input list. -/
def inputBranchForm (inputs : List EdgeInput) (coordinate : Fin 3) : Form :=
  Form.sum (inputs.map fun input => inputForm input coordinate)

end Chunked

end MatrixMultiplication.SimplifiedExponentRecurrence
