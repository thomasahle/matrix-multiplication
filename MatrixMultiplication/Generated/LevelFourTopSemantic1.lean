import MatrixMultiplication.Generated.LevelFourTopRawData
import MatrixMultiplication.Generated.LevelFourTopCheck1

/-!
# Generated semantic top-mass checks for root 1

This module transports the sealed literal checks to the joint top-mass interface.
-/

namespace MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top

open AlgebraicComplexity.LevelFourReconstruction.PositiveLevelThreeData

set_option maxRecDepth 100000
set_option Elab.async false

private abbrev r0 : Fin regionCount := ⟨0, by norm_num [regionCount]⟩
private abbrev r1 : Fin regionCount := ⟨1, by norm_num [regionCount]⟩
private abbrev r2 : Fin regionCount := ⟨2, by norm_num [regionCount]⟩
private abbrev r3 : Fin regionCount := ⟨3, by norm_num [regionCount]⟩
private abbrev r4 : Fin regionCount := ⟨4, by norm_num [regionCount]⟩
private abbrev r5 : Fin regionCount := ⟨5, by norm_num [regionCount]⟩

theorem zeroRowTotal_1 : certificate.zeroRowTotal r1 = 5900058 := by
  change (∑ shape : Fin zeroFourShapeCount, zeroNumerators1[shape.val]?.getD 0) = 5900058
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum zeroNumerators1 zeroFourShapeCount zeroNumerators1_exact.1, zeroNumerators1_exact.2]

theorem branchRowTotal_1_0 : certificate.branchRowTotal r1 r0 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators1_0[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators1_0 topPairCount branchNumerators1_0_exact.1, branchNumerators1_0_exact.2]

theorem branchRowTotal_1_1 : certificate.branchRowTotal r1 r1 = 4281758036 := by
  change (∑ pair : Fin topPairCount, branchNumerators1_1[pair.val]?.getD 0) = 4281758036
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators1_1 topPairCount branchNumerators1_1_exact.1, branchNumerators1_1_exact.2]

theorem branchRowTotal_1_2 : certificate.branchRowTotal r1 r2 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators1_2[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators1_2 topPairCount branchNumerators1_2_exact.1, branchNumerators1_2_exact.2]

theorem branchRowTotal_1_3 : certificate.branchRowTotal r1 r3 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators1_3[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators1_3 topPairCount branchNumerators1_3_exact.1, branchNumerators1_3_exact.2]

theorem branchRowTotal_1_4 : certificate.branchRowTotal r1 r4 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators1_4[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators1_4 topPairCount branchNumerators1_4_exact.1, branchNumerators1_4_exact.2]

theorem branchRowTotal_1_5 : certificate.branchRowTotal r1 r5 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators1_5[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators1_5 topPairCount branchNumerators1_5_exact.1, branchNumerators1_5_exact.2]

theorem branchRootTotal_1 :
    (∑ region : Fin regionCount, certificate.branchRowTotal r1 region) =
      4281758036 := by
  rw [sum_regions_six, branchRowTotal_1_0, branchRowTotal_1_1, branchRowTotal_1_2, branchRowTotal_1_3, branchRowTotal_1_4, branchRowTotal_1_5]

end MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top
