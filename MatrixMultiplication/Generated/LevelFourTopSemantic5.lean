import MatrixMultiplication.Generated.LevelFourTopRawData
import MatrixMultiplication.Generated.LevelFourTopCheck5

/-!
# Generated semantic top-mass checks for root 5

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

theorem zeroRowTotal_5 : certificate.zeroRowTotal r5 = 1051 := by
  change (∑ shape : Fin zeroFourShapeCount, zeroNumerators5[shape.val]?.getD 0) = 1051
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum zeroNumerators5 zeroFourShapeCount zeroNumerators5_exact.1, zeroNumerators5_exact.2]

theorem branchRowTotal_5_0 : certificate.branchRowTotal r5 r0 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators5_0[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators5_0 topPairCount branchNumerators5_0_exact.1, branchNumerators5_0_exact.2]

theorem branchRowTotal_5_1 : certificate.branchRowTotal r5 r1 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators5_1[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators5_1 topPairCount branchNumerators5_1_exact.1, branchNumerators5_1_exact.2]

theorem branchRowTotal_5_2 : certificate.branchRowTotal r5 r2 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators5_2[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators5_2 topPairCount branchNumerators5_2_exact.1, branchNumerators5_2_exact.2]

theorem branchRowTotal_5_3 : certificate.branchRowTotal r5 r3 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators5_3[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators5_3 topPairCount branchNumerators5_3_exact.1, branchNumerators5_3_exact.2]

theorem branchRowTotal_5_4 : certificate.branchRowTotal r5 r4 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators5_4[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators5_4 topPairCount branchNumerators5_4_exact.1, branchNumerators5_4_exact.2]

theorem branchRowTotal_5_5 : certificate.branchRowTotal r5 r5 = 1401124 := by
  change (∑ pair : Fin topPairCount, branchNumerators5_5[pair.val]?.getD 0) = 1401124
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators5_5 topPairCount branchNumerators5_5_exact.1, branchNumerators5_5_exact.2]

theorem branchRootTotal_5 :
    (∑ region : Fin regionCount, certificate.branchRowTotal r5 region) =
      1401124 := by
  rw [sum_regions_six, branchRowTotal_5_0, branchRowTotal_5_1, branchRowTotal_5_2, branchRowTotal_5_3, branchRowTotal_5_4, branchRowTotal_5_5]

end MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top
