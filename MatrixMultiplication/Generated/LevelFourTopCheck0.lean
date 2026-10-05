import MatrixMultiplication.Generated.LevelFourTopRaw0

/-!
# Generated exact top-mass checks for root 0

Source SHA-256: `7a255f50ab903cb7f3da56d93ceccfff3acf39061463115655d7f3f63e746481`.

The arrays are emitted from the archived `2^32`-denominator certificate.  Generated checking
modules use Lean's kernel with `decide`; no floating-point values are imported.
-/

namespace MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top

open AlgebraicComplexity.LevelFourReconstruction.PositiveLevelThreeData

set_option maxRecDepth 100000
set_option Elab.async false

theorem zeroNumerators0_exact :
    zeroNumerators0.size = zeroFourShapeCount ∧
      zeroNumerators0.toList.sum = 1686 :=
  ⟨zeroNumerators0Checked.size_eq, zeroNumerators0Checked.sum_eq⟩

theorem branchNumerators0_0_exact :
    branchNumerators0_0.size = topPairCount ∧
      branchNumerators0_0.toList.sum = 2277285 :=
  ⟨branchNumerators0_0Checked.size_eq, branchNumerators0_0Checked.sum_eq⟩

theorem branchNumerators0_1_exact :
    branchNumerators0_1.size = topPairCount ∧
      branchNumerators0_1.toList.sum = 0 :=
  ⟨branchNumerators0_1Checked.size_eq, branchNumerators0_1Checked.sum_eq⟩

theorem branchNumerators0_2_exact :
    branchNumerators0_2.size = topPairCount ∧
      branchNumerators0_2.toList.sum = 0 :=
  ⟨branchNumerators0_2Checked.size_eq, branchNumerators0_2Checked.sum_eq⟩

theorem branchNumerators0_3_exact :
    branchNumerators0_3.size = topPairCount ∧
      branchNumerators0_3.toList.sum = 0 :=
  ⟨branchNumerators0_3Checked.size_eq, branchNumerators0_3Checked.sum_eq⟩

theorem branchNumerators0_4_exact :
    branchNumerators0_4.size = topPairCount ∧
      branchNumerators0_4.toList.sum = 0 :=
  ⟨branchNumerators0_4Checked.size_eq, branchNumerators0_4Checked.sum_eq⟩

theorem branchNumerators0_5_exact :
    branchNumerators0_5.size = topPairCount ∧
      branchNumerators0_5.toList.sum = 0 :=
  ⟨branchNumerators0_5Checked.size_eq, branchNumerators0_5Checked.sum_eq⟩

end MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top
