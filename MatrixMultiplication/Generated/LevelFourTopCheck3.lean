import MatrixMultiplication.Generated.LevelFourTopRaw3

/-!
# Generated exact top-mass checks for root 3

Source SHA-256: `7a255f50ab903cb7f3da56d93ceccfff3acf39061463115655d7f3f63e746481`.

The arrays are emitted from the archived `2^32`-denominator certificate.  Generated checking
modules use Lean's kernel with `decide`; no floating-point values are imported.
-/

namespace MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top

open AlgebraicComplexity.LevelFourReconstruction.PositiveLevelThreeData

set_option maxRecDepth 100000
set_option Elab.async false

theorem zeroNumerators3_exact :
    zeroNumerators3.size = zeroFourShapeCount ∧
      zeroNumerators3.toList.sum = 368 :=
  ⟨zeroNumerators3Checked.size_eq, zeroNumerators3Checked.sum_eq⟩

theorem branchNumerators3_0_exact :
    branchNumerators3_0.size = topPairCount ∧
      branchNumerators3_0.toList.sum = 0 :=
  ⟨branchNumerators3_0Checked.size_eq, branchNumerators3_0Checked.sum_eq⟩

theorem branchNumerators3_1_exact :
    branchNumerators3_1.size = topPairCount ∧
      branchNumerators3_1.toList.sum = 0 :=
  ⟨branchNumerators3_1Checked.size_eq, branchNumerators3_1Checked.sum_eq⟩

theorem branchNumerators3_2_exact :
    branchNumerators3_2.size = topPairCount ∧
      branchNumerators3_2.toList.sum = 0 :=
  ⟨branchNumerators3_2Checked.size_eq, branchNumerators3_2Checked.sum_eq⟩

theorem branchNumerators3_3_exact :
    branchNumerators3_3.size = topPairCount ∧
      branchNumerators3_3.toList.sum = 94631 :=
  ⟨branchNumerators3_3Checked.size_eq, branchNumerators3_3Checked.sum_eq⟩

theorem branchNumerators3_4_exact :
    branchNumerators3_4.size = topPairCount ∧
      branchNumerators3_4.toList.sum = 0 :=
  ⟨branchNumerators3_4Checked.size_eq, branchNumerators3_4Checked.sum_eq⟩

theorem branchNumerators3_5_exact :
    branchNumerators3_5.size = topPairCount ∧
      branchNumerators3_5.toList.sum = 0 :=
  ⟨branchNumerators3_5Checked.size_eq, branchNumerators3_5Checked.sum_eq⟩

end MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top
