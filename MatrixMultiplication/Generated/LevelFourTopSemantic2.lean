import MatrixMultiplication.Generated.LevelFourTopRawData
import MatrixMultiplication.Generated.LevelFourTopCheck2

/-!
# Generated semantic top-mass checks for root 2

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

theorem zeroRowTotal_2 : certificate.zeroRowTotal r2 = 375 := by
  change (∑ shape : Fin zeroFourShapeCount, zeroNumerators2[shape.val]?.getD 0) = 375
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum zeroNumerators2 zeroFourShapeCount zeroNumerators2_exact.1, zeroNumerators2_exact.2]

theorem branchRowTotal_2_0 : certificate.branchRowTotal r2 r0 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators2_0[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators2_0 topPairCount branchNumerators2_0_exact.1, branchNumerators2_0_exact.2]

theorem branchRowTotal_2_1 : certificate.branchRowTotal r2 r1 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators2_1[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators2_1 topPairCount branchNumerators2_1_exact.1, branchNumerators2_1_exact.2]

theorem branchRowTotal_2_2 : certificate.branchRowTotal r2 r2 = 95321 := by
  change (∑ pair : Fin topPairCount, branchNumerators2_2[pair.val]?.getD 0) = 95321
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators2_2 topPairCount branchNumerators2_2_exact.1, branchNumerators2_2_exact.2]

theorem branchRowTotal_2_3 : certificate.branchRowTotal r2 r3 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators2_3[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators2_3 topPairCount branchNumerators2_3_exact.1, branchNumerators2_3_exact.2]

theorem branchRowTotal_2_4 : certificate.branchRowTotal r2 r4 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators2_4[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators2_4 topPairCount branchNumerators2_4_exact.1, branchNumerators2_4_exact.2]

theorem branchRowTotal_2_5 : certificate.branchRowTotal r2 r5 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators2_5[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators2_5 topPairCount branchNumerators2_5_exact.1, branchNumerators2_5_exact.2]

theorem branchRootTotal_2 :
    (∑ region : Fin regionCount, certificate.branchRowTotal r2 region) =
      95321 := by
  rw [sum_regions_six, branchRowTotal_2_0, branchRowTotal_2_1, branchRowTotal_2_2, branchRowTotal_2_3, branchRowTotal_2_4, branchRowTotal_2_5]

end MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top
