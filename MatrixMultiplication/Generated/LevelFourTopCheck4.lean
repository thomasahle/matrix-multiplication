import MatrixMultiplication.Generated.LevelFourTopRaw4

/-!
# Generated exact top-mass checks for root 4

Source SHA-256: `7a255f50ab903cb7f3da56d93ceccfff3acf39061463115655d7f3f63e746481`.

The arrays are emitted from the archived `2^32`-denominator certificate.  Generated checking
modules use Lean's kernel with `decide`; no floating-point values are imported.
-/

namespace MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top

open AlgebraicComplexity.LevelFourReconstruction.PositiveLevelThreeData

set_option maxRecDepth 100000
set_option Elab.async false

theorem zeroNumerators4_exact :
    zeroNumerators4.size = zeroFourShapeCount ∧
      zeroNumerators4.toList.sum = 2469 :=
  ⟨zeroNumerators4Checked.size_eq, zeroNumerators4Checked.sum_eq⟩

theorem branchNumerators4_0_exact :
    branchNumerators4_0.size = topPairCount ∧
      branchNumerators4_0.toList.sum = 0 :=
  ⟨branchNumerators4_0Checked.size_eq, branchNumerators4_0Checked.sum_eq⟩

theorem branchNumerators4_1_exact :
    branchNumerators4_1.size = topPairCount ∧
      branchNumerators4_1.toList.sum = 0 :=
  ⟨branchNumerators4_1Checked.size_eq, branchNumerators4_1Checked.sum_eq⟩

theorem branchNumerators4_2_exact :
    branchNumerators4_2.size = topPairCount ∧
      branchNumerators4_2.toList.sum = 0 :=
  ⟨branchNumerators4_2Checked.size_eq, branchNumerators4_2Checked.sum_eq⟩

theorem branchNumerators4_3_exact :
    branchNumerators4_3.size = topPairCount ∧
      branchNumerators4_3.toList.sum = 0 :=
  ⟨branchNumerators4_3Checked.size_eq, branchNumerators4_3Checked.sum_eq⟩

theorem branchNumerators4_4_exact :
    branchNumerators4_4.size = topPairCount ∧
      branchNumerators4_4.toList.sum = 3434892 :=
  ⟨branchNumerators4_4Checked.size_eq, branchNumerators4_4Checked.sum_eq⟩

theorem branchNumerators4_5_exact :
    branchNumerators4_5.size = topPairCount ∧
      branchNumerators4_5.toList.sum = 0 :=
  ⟨branchNumerators4_5Checked.size_eq, branchNumerators4_5Checked.sum_eq⟩

end MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top
