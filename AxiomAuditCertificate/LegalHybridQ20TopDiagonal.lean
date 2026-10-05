/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.LegalHybridQ20TopDiagonal
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Audit of the literal q20 diagonal top-support theorem

All three public declarations are asserted. The finite property specializes the regional
division of [alman2025more], `cl:dividing_into_region_zero_out`,
`papers/sources/2404.16349/constituent.tex:153-175`, to q20's diagonal top face checked at
`better_bound/legal_hybrid/check_directed.py:258-261`. No predecessor support theorem is used.

The concrete client below reads atom 12852 from q20's native block 0/1, transports membership
through the exact native concatenation, and applies the public theorem. Its decoded root and
incoming region are both one. This is an actual supported input, not an assumed support premise.
-/

open MatrixMultiplication.LegalHybridQ20TopDiagonal

#assert_axioms boundaryOrDiagonal
#assert_axioms topSupport_boundaryOrDiagonal
#assert_axioms topSupport_root_eq_region

section ActualAtomClient

open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.LevelFourReconstruction.PositiveLevelThreeData
open MatrixMultiplication.LevelFourRemainingReconstruction (zeroFourShapeCount)
open MatrixMultiplication.Generated.LegalHybridQ20Primary

local notation "topZeroAtomCount" => regionCount * zeroFourShapeCount
local notation "topPairCount" => levelFourPairCount

example :
    (12852 - topZeroAtomCount) / topPairCount / regionCount = 1 ∧
      ((12852 - topZeroAtomCount) / topPairCount) % regionCount = 1 := by
  have hnative : 12852 ∈ TopData0.DataBlock1.data.atomIndices.toList := by decide
  have hraw : 12852 ∈ TopData0.rawData.atomIndices.toList := by
    simp only [TopData0.rawData, ArrayCore.appendMassChunk, ArrayCore.concatArrays_toList,
      List.mem_append, hnative, or_true, true_or]
  have htop0 : 12852 ∈ TopData0.data.atomIndices.toList := by
    rw [TopData0.data_eq_rawData]
    exact hraw
  have htop : 12852 ∈ topSupportAtomIndices :=
    List.mem_append_left TopData1.data.atomIndices.toList htop0
  have hdiagonal := topSupport_root_eq_region htop (by decide)
  have hregion : ((12852 - topZeroAtomCount) / topPairCount) % regionCount = 1 := by decide
  exact ⟨hdiagonal.trans hregion, hregion⟩

end ActualAtomClient
