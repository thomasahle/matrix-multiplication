import MatrixMultiplication.Generated.LevelFourTopRaw2

/-!
# Generated exact top-mass checks for root 2

Source SHA-256: `7a255f50ab903cb7f3da56d93ceccfff3acf39061463115655d7f3f63e746481`.

The arrays are emitted from the archived `2^32`-denominator certificate.  Generated checking
modules use Lean's kernel with `decide`; no floating-point values are imported.
-/

namespace MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top

open AlgebraicComplexity.LevelFourReconstruction.PositiveLevelThreeData

set_option maxRecDepth 100000
set_option Elab.async false

theorem zeroNumerators2_exact :
    zeroNumerators2.size = zeroFourShapeCount ∧
      zeroNumerators2.toList.sum = 375 :=
  ⟨zeroNumerators2Checked.size_eq, zeroNumerators2Checked.sum_eq⟩

theorem branchNumerators2_0_exact :
    branchNumerators2_0.size = topPairCount ∧
      branchNumerators2_0.toList.sum = 0 :=
  ⟨branchNumerators2_0Checked.size_eq, branchNumerators2_0Checked.sum_eq⟩

theorem branchNumerators2_1_exact :
    branchNumerators2_1.size = topPairCount ∧
      branchNumerators2_1.toList.sum = 0 :=
  ⟨branchNumerators2_1Checked.size_eq, branchNumerators2_1Checked.sum_eq⟩

theorem branchNumerators2_2_exact :
    branchNumerators2_2.size = topPairCount ∧
      branchNumerators2_2.toList.sum = 95321 :=
  ⟨branchNumerators2_2Checked.size_eq, branchNumerators2_2Checked.sum_eq⟩

theorem branchNumerators2_3_exact :
    branchNumerators2_3.size = topPairCount ∧
      branchNumerators2_3.toList.sum = 0 :=
  ⟨branchNumerators2_3Checked.size_eq, branchNumerators2_3Checked.sum_eq⟩

theorem branchNumerators2_4_exact :
    branchNumerators2_4.size = topPairCount ∧
      branchNumerators2_4.toList.sum = 0 :=
  ⟨branchNumerators2_4Checked.size_eq, branchNumerators2_4Checked.sum_eq⟩

theorem branchNumerators2_5_exact :
    branchNumerators2_5.size = topPairCount ∧
      branchNumerators2_5.toList.sum = 0 :=
  ⟨branchNumerators2_5Checked.size_eq, branchNumerators2_5Checked.sum_eq⟩

end MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top
