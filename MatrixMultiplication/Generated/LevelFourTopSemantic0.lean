import MatrixMultiplication.Generated.LevelFourTopRawData
import MatrixMultiplication.Generated.LevelFourTopCheck0

/-!
# Generated semantic top-mass checks for root 0

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

theorem zeroRowTotal_0 : certificate.zeroRowTotal r0 = 1686 := by
  change (∑ shape : Fin zeroFourShapeCount, zeroNumerators0[shape.val]?.getD 0) = 1686
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum zeroNumerators0 zeroFourShapeCount zeroNumerators0_exact.1, zeroNumerators0_exact.2]

theorem branchRowTotal_0_0 : certificate.branchRowTotal r0 r0 = 2277285 := by
  change (∑ pair : Fin topPairCount, branchNumerators0_0[pair.val]?.getD 0) = 2277285
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators0_0 topPairCount branchNumerators0_0_exact.1, branchNumerators0_0_exact.2]

theorem branchRowTotal_0_1 : certificate.branchRowTotal r0 r1 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators0_1[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators0_1 topPairCount branchNumerators0_1_exact.1, branchNumerators0_1_exact.2]

theorem branchRowTotal_0_2 : certificate.branchRowTotal r0 r2 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators0_2[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators0_2 topPairCount branchNumerators0_2_exact.1, branchNumerators0_2_exact.2]

theorem branchRowTotal_0_3 : certificate.branchRowTotal r0 r3 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators0_3[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators0_3 topPairCount branchNumerators0_3_exact.1, branchNumerators0_3_exact.2]

theorem branchRowTotal_0_4 : certificate.branchRowTotal r0 r4 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators0_4[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators0_4 topPairCount branchNumerators0_4_exact.1, branchNumerators0_4_exact.2]

theorem branchRowTotal_0_5 : certificate.branchRowTotal r0 r5 = 0 := by
  change (∑ pair : Fin topPairCount, branchNumerators0_5[pair.val]?.getD 0) = 0
  rw [AlgebraicComplexity.array_getElem?_getD_sum_eq_toList_sum branchNumerators0_5 topPairCount branchNumerators0_5_exact.1, branchNumerators0_5_exact.2]

theorem branchRootTotal_0 :
    (∑ region : Fin regionCount, certificate.branchRowTotal r0 region) =
      2277285 := by
  rw [sum_regions_six, branchRowTotal_0_0, branchRowTotal_0_1, branchRowTotal_0_2, branchRowTotal_0_3, branchRowTotal_0_4, branchRowTotal_0_5]

end MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top
