/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk3
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk4
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk5
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk6
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk7
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk8
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk9
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk10
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk11
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk12
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk13
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk14
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk15
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk16
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk17
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInputData

/-!
# Compact sufficient statistic for the total-quotient level-two recurrence

The historical checker exposed 1,620 recurrence records to the nonlinear analytic layer.  Only
the pair `(muNumerator, heavyCoordinate)` affects the nonlinear part of a record's contribution,
so exact grouping reduces the 953 positive-mass records to the 67 records below.

Eighteen independent proof leaves group 90 exact integer records each.  This module then checks
only the merge of those already-small summaries.  It deliberately does not import the sparse
primary tables or real entropy; a separate provenance adapter connects these exact literals to the
established recurrence, and the semantic adapter proves that grouping preserves all three branch
rates.

The Python producer is untrusted.  Lean recomputes both the local groupings and this global merge
with proof-producing evaluation.
-/

namespace MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedData

open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000
set_option Elab.async false

/-- The final 67-key sufficient statistic consumed by all three branch forms.

Its order is the executable `groupInputs` order.  No theorem relies on that order semantically, but
keeping the literal canonical makes the certificate equality directly checkable. -/
def expectedInputs : List EdgeInput :=
  [
    ⟨1346169714, 170, 1⟩,
    ⟨210483917174, 68, 1⟩,
    ⟨9706726, 178, 1⟩,
    ⟨18816476, 173, 0⟩,
    ⟨30013594378, 82, 1⟩,
    ⟨4275034812, 66, 0⟩,
    ⟨9379736, 217, 0⟩,
    ⟨18549230342, 41, 1⟩,
    ⟨9722588, 171, 1⟩,
    ⟨5371022, 195, 0⟩,
    ⟨104626060314, 82, 0⟩,
    ⟨73146094, 172, 0⟩,
    ⟨15043933015, 67, 0⟩,
    ⟨305526922, 215, 0⟩,
    ⟨7464160323, 79, 0⟩,
    ⟨1385791451, 193, 0⟩,
    ⟨1322044954311, 78, 0⟩,
    ⟨15765724308, 63, 2⟩,
    ⟨1168883983, 213, 2⟩,
    ⟨794710769088, 67, 2⟩,
    ⟨594047946, 224, 2⟩,
    ⟨16372006930, 100, 2⟩,
    ⟨1594096099, 203, 2⟩,
    ⟨24421834, 194, 0⟩,
    ⟨268252975, 177, 1⟩,
    ⟨992937532, 171, 0⟩,
    ⟨497366223024, 70, 0⟩,
    ⟨47122399618, 66, 1⟩,
    ⟨285232051398, 80, 0⟩,
    ⟨194625427360, 72, 1⟩,
    ⟨8837937648808, 75, 0⟩,
    ⟨11306012, 216, 0⟩,
    ⟨169434800470, 57, 2⟩,
    ⟨150712723070, 64, 1⟩,
    ⟨84959713800, 68, 0⟩,
    ⟨38058857746, 96, 2⟩,
    ⟨63644644466, 40, 1⟩,
    ⟨745825682888, 77, 0⟩,
    ⟨21912099000, 62, 2⟩,
    ⟨516600824464, 81, 0⟩,
    ⟨195965715000, 58, 2⟩,
    ⟨1205170539564, 38, 1⟩,
    ⟨1383788325860, 78, 2⟩,
    ⟨5439353633640, 58, 1⟩,
    ⟨685429571112, 55, 2⟩,
    ⟨464470790620, 75, 1⟩,
    ⟨1621328058584, 49, 2⟩,
    ⟨755072147856, 87, 1⟩,
    ⟨406113886398, 77, 2⟩,
    ⟨196182820740, 45, 1⟩,
    ⟨353010, 174, 0⟩,
    ⟨214836, 218, 0⟩,
    ⟨1110781120912, 42, 2⟩,
    ⟨73850113000, 93, 2⟩,
    ⟨168120645488, 78, 1⟩,
    ⟨2557088312064, 62, 1⟩,
    ⟨2736871728660, 82, 2⟩,
    ⟨1476527164830, 76, 0⟩,
    ⟨41811749220, 67, 1⟩,
    ⟨2449593657494, 68, 2⟩,
    ⟨170682260220, 69, 0⟩,
    ⟨214325856750, 59, 2⟩,
    ⟨49580436588, 81, 1⟩,
    ⟨229101714864, 71, 2⟩,
    ⟨1411695099144, 57, 1⟩,
    ⟨1529092919550, 83, 2⟩,
    ⟨241995575094, 61, 1⟩
  ]

/-- The compact payload has exactly 67 positive-mass groups. -/
theorem expectedInputs_length : expectedInputs.length = 67 := by decide

/-- No sufficient-statistic key occurs twice in the compact payload. -/
theorem expectedInputs_keys_nodup : (expectedInputs.map EdgeInput.key).Nodup := by decide

/-- Every compact group has strictly positive occurrence mass. -/
theorem expectedInputs_occurrence_pos :
    ∀ input ∈ expectedInputs, 0 < input.occurrenceNumerator := by decide

/-- The eighteen consecutive 90-record input blocks, in certificate order. -/
abbrev expectedInputChunks : List (List EdgeInput) :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.expectedInputChunks

/-- The independently checked sufficient statistics of the eighteen input blocks. -/
def expectedGroupedChunks : List (List EdgeInput) :=
  [
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk0.expectedInputs,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk1.expectedInputs,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk2.expectedInputs,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk3.expectedInputs,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk4.expectedInputs,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk5.expectedInputs,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk6.expectedInputs,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk7.expectedInputs,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk8.expectedInputs,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk9.expectedInputs,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk10.expectedInputs,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk11.expectedInputs,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk12.expectedInputs,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk13.expectedInputs,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk14.expectedInputs,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk15.expectedInputs,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk16.expectedInputs,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk17.expectedInputs
  ]

/-- Every 90-record input block groups to its independently emitted local statistic.

Proof sketch: expand only the two short umbrellas.  Each of the eighteen remaining equalities is
the kernel-checked `inputs_grouped_eq` theorem from its own compilation unit. -/
theorem expectedInputChunks_grouped :
    expectedInputChunks.map groupInputs = expectedGroupedChunks := by
  unfold expectedInputChunks
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceInput.expectedInputChunks
    expectedGroupedChunks
  simp only [List.map_cons, List.map_nil]
  rw [MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk0.inputs_grouped_eq,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk1.inputs_grouped_eq,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk2.inputs_grouped_eq,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk3.inputs_grouped_eq,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk4.inputs_grouped_eq,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk5.inputs_grouped_eq,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk6.inputs_grouped_eq,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk7.inputs_grouped_eq,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk8.inputs_grouped_eq,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk9.inputs_grouped_eq,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk10.inputs_grouped_eq,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk11.inputs_grouped_eq,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk12.inputs_grouped_eq,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk13.inputs_grouped_eq,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk14.inputs_grouped_eq,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk15.inputs_grouped_eq,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk16.inputs_grouped_eq,
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk17.inputs_grouped_eq]

/-- Merging the eighteen local summaries gives the final 67-record sufficient statistic.

Proof sketch: this evaluates `groupInputs` over only the compact local summaries.  It never unfolds
the 1,620 source records or any sparse primary table. -/
theorem expectedGroupedChunks_merge :
    groupInputs expectedGroupedChunks.flatten = expectedInputs := by
  unfold expectedGroupedChunks expectedInputs
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk0.expectedInputs
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk1.expectedInputs
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk2.expectedInputs
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk3.expectedInputs
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk4.expectedInputs
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk5.expectedInputs
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk6.expectedInputs
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk7.expectedInputs
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk8.expectedInputs
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk9.expectedInputs
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk10.expectedInputs
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk11.expectedInputs
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk12.expectedInputs
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk13.expectedInputs
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk14.expectedInputs
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk15.expectedInputs
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk16.expectedInputs
    MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedChunk17.expectedInputs
  decide_cbv

/-- The compact payload carries exactly the total occurrence mass of all 1,620 input records.

Proof sketch: local and global grouping each preserve total mass.  The only certificate-dependent
steps are the already-proved local grouping equalities. -/
theorem expectedInputs_occurrenceTotal :
    occurrenceTotal expectedInputs = occurrenceTotal expectedInputChunks.flatten := by
  calc
    occurrenceTotal expectedInputs =
        occurrenceTotal (groupInputs expectedGroupedChunks.flatten) := by
      rw [expectedGroupedChunks_merge]
    _ = occurrenceTotal expectedGroupedChunks.flatten := occurrenceTotal_groupInputs _
    _ = occurrenceTotal ((expectedInputChunks.map groupInputs).flatten) := by
      rw [expectedInputChunks_grouped]
    _ = occurrenceTotal expectedInputChunks.flatten :=
      occurrenceTotal_flatten_map_groupInputs _

end MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedData
