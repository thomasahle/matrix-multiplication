import MatrixMultiplication.Generated.LevelFourTopRaw5

/-!
# Generated exact top-mass checks for root 5

Source SHA-256: `7a255f50ab903cb7f3da56d93ceccfff3acf39061463115655d7f3f63e746481`.

The arrays are emitted from the archived `2^32`-denominator certificate.  Generated checking
modules use Lean's kernel with `decide`; no floating-point values are imported.
-/

namespace MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top

open AlgebraicComplexity.LevelFourReconstruction.PositiveLevelThreeData

set_option maxRecDepth 100000
set_option Elab.async false

theorem zeroNumerators5_exact :
    zeroNumerators5.size = zeroFourShapeCount ∧
      zeroNumerators5.toList.sum = 1051 :=
  ⟨zeroNumerators5Checked.size_eq, zeroNumerators5Checked.sum_eq⟩

theorem branchNumerators5_0_exact :
    branchNumerators5_0.size = topPairCount ∧
      branchNumerators5_0.toList.sum = 0 :=
  ⟨branchNumerators5_0Checked.size_eq, branchNumerators5_0Checked.sum_eq⟩

theorem branchNumerators5_1_exact :
    branchNumerators5_1.size = topPairCount ∧
      branchNumerators5_1.toList.sum = 0 :=
  ⟨branchNumerators5_1Checked.size_eq, branchNumerators5_1Checked.sum_eq⟩

theorem branchNumerators5_2_exact :
    branchNumerators5_2.size = topPairCount ∧
      branchNumerators5_2.toList.sum = 0 :=
  ⟨branchNumerators5_2Checked.size_eq, branchNumerators5_2Checked.sum_eq⟩

theorem branchNumerators5_3_exact :
    branchNumerators5_3.size = topPairCount ∧
      branchNumerators5_3.toList.sum = 0 :=
  ⟨branchNumerators5_3Checked.size_eq, branchNumerators5_3Checked.sum_eq⟩

theorem branchNumerators5_4_exact :
    branchNumerators5_4.size = topPairCount ∧
      branchNumerators5_4.toList.sum = 0 :=
  ⟨branchNumerators5_4Checked.size_eq, branchNumerators5_4Checked.sum_eq⟩

theorem branchNumerators5_5_exact :
    branchNumerators5_5.size = topPairCount ∧
      branchNumerators5_5.toList.sum = 1401124 :=
  ⟨branchNumerators5_5Checked.size_eq, branchNumerators5_5Checked.sum_eq⟩

end MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top
