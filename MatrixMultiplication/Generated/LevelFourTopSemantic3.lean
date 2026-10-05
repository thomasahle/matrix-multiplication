import MatrixMultiplication.Generated.LevelFourTopRawData
import MatrixMultiplication.Generated.LevelFourTopCheck3

/-!
# Generated semantic top-mass checks for root 3

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

theorem zeroRowTotal_3 : certificate.zeroRowTotal r3 = 368 := by
  change (∑ shape : Fin zeroFourShapeCount, zeroNumerators3[shape.val]?.getD 0) = 368
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum zeroNumerators3 zeroFourShapeCount zeroNumerators3_exact.1, zeroNumerators3_exact.2]

theorem branchRowTotal_3_0 : certificate.branchRowTotal r3 r0 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators3_0[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators3_0 topPairCount branchNumerators3_0_exact.1, branchNumerators3_0_exact.2]

theorem branchRowTotal_3_1 : certificate.branchRowTotal r3 r1 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators3_1[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators3_1 topPairCount branchNumerators3_1_exact.1, branchNumerators3_1_exact.2]

theorem branchRowTotal_3_2 : certificate.branchRowTotal r3 r2 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators3_2[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators3_2 topPairCount branchNumerators3_2_exact.1, branchNumerators3_2_exact.2]

theorem branchRowTotal_3_3 : certificate.branchRowTotal r3 r3 = 94631 := by
  change (∑ pair : Fin topPairCount, branchNumerators3_3[pair.val]?.getD 0) = 94631
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators3_3 topPairCount branchNumerators3_3_exact.1, branchNumerators3_3_exact.2]

theorem branchRowTotal_3_4 : certificate.branchRowTotal r3 r4 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators3_4[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators3_4 topPairCount branchNumerators3_4_exact.1, branchNumerators3_4_exact.2]

theorem branchRowTotal_3_5 : certificate.branchRowTotal r3 r5 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators3_5[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators3_5 topPairCount branchNumerators3_5_exact.1, branchNumerators3_5_exact.2]

theorem branchRootTotal_3 :
    (∑ region : Fin regionCount, certificate.branchRowTotal r3 region) =
      94631 := by
  rw [sum_regions_six, branchRowTotal_3_0, branchRowTotal_3_1, branchRowTotal_3_2, branchRowTotal_3_3, branchRowTotal_3_4, branchRowTotal_3_5]

end MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top
