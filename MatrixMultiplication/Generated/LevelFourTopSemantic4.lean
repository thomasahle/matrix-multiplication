import MatrixMultiplication.Generated.LevelFourTopRawData
import MatrixMultiplication.Generated.LevelFourTopCheck4

/-!
# Generated semantic top-mass checks for root 4

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

theorem zeroRowTotal_4 : certificate.zeroRowTotal r4 = 2469 := by
  change (∑ shape : Fin zeroFourShapeCount, zeroNumerators4[shape.val]?.getD 0) = 2469
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum zeroNumerators4 zeroFourShapeCount zeroNumerators4_exact.1, zeroNumerators4_exact.2]

theorem branchRowTotal_4_0 : certificate.branchRowTotal r4 r0 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators4_0[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators4_0 topPairCount branchNumerators4_0_exact.1, branchNumerators4_0_exact.2]

theorem branchRowTotal_4_1 : certificate.branchRowTotal r4 r1 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators4_1[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators4_1 topPairCount branchNumerators4_1_exact.1, branchNumerators4_1_exact.2]

theorem branchRowTotal_4_2 : certificate.branchRowTotal r4 r2 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators4_2[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators4_2 topPairCount branchNumerators4_2_exact.1, branchNumerators4_2_exact.2]

theorem branchRowTotal_4_3 : certificate.branchRowTotal r4 r3 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators4_3[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators4_3 topPairCount branchNumerators4_3_exact.1, branchNumerators4_3_exact.2]

theorem branchRowTotal_4_4 : certificate.branchRowTotal r4 r4 = 3434892 := by
  change (∑ pair : Fin topPairCount, branchNumerators4_4[pair.val]?.getD 0) = 3434892
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators4_4 topPairCount branchNumerators4_4_exact.1, branchNumerators4_4_exact.2]

theorem branchRowTotal_4_5 : certificate.branchRowTotal r4 r5 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators4_5[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators4_5 topPairCount branchNumerators4_5_exact.1, branchNumerators4_5_exact.2]

theorem branchRootTotal_4 :
    (∑ region : Fin regionCount, certificate.branchRowTotal r4 region) =
      3434892 := by
  rw [sum_regions_six, branchRowTotal_4_0, branchRowTotal_4_1, branchRowTotal_4_2, branchRowTotal_4_3, branchRowTotal_4_4, branchRowTotal_4_5]

end MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top
