/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.LegalHybridQ20PrimaryManifest
import MatrixMultiplication.Generated.LegalHybridQ20PrimaryTopData0
import MatrixMultiplication.Generated.LegalHybridQ20PrimaryTopData1

set_option autoImplicit false

/-!
# Canonical legal-hybrid q20 top-law aggregate

This generated TW-15 boundary aggregates only the two independently checked top chunks used by
the Total-Weight candidate in `better_bound/paper.tex:148-159`. The hand-written
`LegalHybridQ20PrimaryTables` wrapper reuses all six lower fields of the existing 90df primary
table.  No broad semantic, count, logarithmic, restriction, or endpoint packet is generated here.

The downstream ordered-child laws follow [alman2025more],
`papers/sources/2404.16349/constituent.tex:41-47`; the q20 numerators are this project's own data.
The proofs below assemble checked chunk totals and support bounds, not a tensor extraction.
-/

namespace MatrixMultiplication.Generated.LegalHybridQ20Primary

open MatrixMultiplication.Generated.SimplifiedVolume

/-- The two bounded sparse chunks of the canonical q20 top law. -/
def topChunks : Array SparseMassChunk := #[TopData0.data, TopData1.data]

/-- Half-open sparse-address ranges, retained as a tiny cross-chunk reduction boundary. -/
def topChunkRanges : Array (Nat × Nat) := #[(51, 14319), (14319, 64278)]

/-- The two chunk ranges are ordered and disjoint. -/
theorem topChunkRanges_pairwise :
    topChunkRanges.toList.Pairwise (fun earlier later => earlier.2 ≤ later.1) := by
  decide

/-- Ordered sparse support of the q20 top law, with the source-image chunk boundary forgotten. -/
def topSupportAtomIndices : List Nat :=
  TopData0.data.atomIndices.toList ++ TopData1.data.atomIndices.toList

/-- The q20 top support is globally strictly increasing. -/
theorem topSupportAtomIndices_strictlyIncreasing :
    StrictlyIncreasing topSupportAtomIndices := by
  apply LegalHybridQ20Primary.ArrayCore.strictlyIncreasing_append_of_cut
  · exact TopData0.data_isValid.2.1
  · exact TopData1.data_isValid.2.1
  · exact LegalHybridQ20Primary.ArrayCore.all_mono
      (fun _ h => h.2.1) TopData0.data_isValid.2.2.1
  · exact LegalHybridQ20Primary.ArrayCore.all_mono
      (fun _ h => h.1) TopData1.data_isValid.2.2.1

/-- Number of positive top-law coordinates stored by the source image. -/
def topValueCount : Nat := TopData0.data.valueCount + TopData1.data.valueCount

/-- The q20 source image has exactly 2,244 positive coordinates. -/
theorem topValueCount_eq : topValueCount = 2244 := by
  unfold topValueCount
  rw [TopData0.valueCount_eq, TopData1.valueCount_eq]

/-- The ordered sparse support contains exactly the 2,244 checked positive coordinates. -/
theorem topSupportAtomIndices_length : topSupportAtomIndices.length = 2244 := by
  unfold topSupportAtomIndices
  simp only [List.length_append, Array.length_toList]
  rw [TopData0.data_isValid.1, TopData1.data_isValid.1]
  change TopData0.data.valueCount + TopData1.data.valueCount = 2244
  rw [TopData0.valueCount_eq, TopData1.valueCount_eq]

/-- Exact numerator sum across the two q20 chunks. -/
def topNumeratorTotal : Nat := TopData0.data.total + TopData1.data.total

/-- The q20 top law is normalized at denominator `2^20`. -/
theorem topNumeratorTotal_eq : topNumeratorTotal = 2 ^ 20 := by
  unfold topNumeratorTotal
  rw [TopData0.total_eq, TopData1.total_eq]

/-- The provenance census agrees with the checked sparse source image. -/
theorem manifest_top_count : Manifest.activeTopValues = topValueCount := by
  rw [topValueCount_eq]
  rfl

end MatrixMultiplication.Generated.LegalHybridQ20Primary
