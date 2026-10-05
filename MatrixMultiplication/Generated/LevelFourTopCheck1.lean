import MatrixMultiplication.Generated.LevelFourTopRaw1

/-!
# Generated exact top-mass checks for root 1

Source SHA-256: `7a255f50ab903cb7f3da56d93ceccfff3acf39061463115655d7f3f63e746481`.

The arrays are emitted from the archived `2^32`-denominator certificate.  Generated checking
modules use Lean's kernel with `decide`; no floating-point values are imported.
-/

namespace MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top

open AlgebraicComplexity.LevelFourReconstruction.PositiveLevelThreeData

set_option maxRecDepth 100000
set_option Elab.async false

theorem zeroNumerators1_exact :
    zeroNumerators1.size = zeroFourShapeCount ∧
      zeroNumerators1.toList.sum = 5900058 :=
  ⟨zeroNumerators1Checked.size_eq, zeroNumerators1Checked.sum_eq⟩

theorem branchNumerators1_0_exact :
    branchNumerators1_0.size = topPairCount ∧
      branchNumerators1_0.toList.sum = 0 :=
  ⟨branchNumerators1_0Checked.size_eq, branchNumerators1_0Checked.sum_eq⟩

theorem branchNumerators1_1_exact :
    branchNumerators1_1.size = topPairCount ∧
      branchNumerators1_1.toList.sum = 4281758036 :=
  ⟨branchNumerators1_1Checked.size_eq, branchNumerators1_1Checked.sum_eq⟩

theorem branchNumerators1_2_exact :
    branchNumerators1_2.size = topPairCount ∧
      branchNumerators1_2.toList.sum = 0 :=
  ⟨branchNumerators1_2Checked.size_eq, branchNumerators1_2Checked.sum_eq⟩

theorem branchNumerators1_3_exact :
    branchNumerators1_3.size = topPairCount ∧
      branchNumerators1_3.toList.sum = 0 :=
  ⟨branchNumerators1_3Checked.size_eq, branchNumerators1_3Checked.sum_eq⟩

theorem branchNumerators1_4_exact :
    branchNumerators1_4.size = topPairCount ∧
      branchNumerators1_4.toList.sum = 0 :=
  ⟨branchNumerators1_4Checked.size_eq, branchNumerators1_4Checked.sum_eq⟩

theorem branchNumerators1_5_exact :
    branchNumerators1_5.size = topPairCount ∧
      branchNumerators1_5.toList.sum = 0 :=
  ⟨branchNumerators1_5Checked.size_eq, branchNumerators1_5Checked.sum_eq⟩

end MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top
