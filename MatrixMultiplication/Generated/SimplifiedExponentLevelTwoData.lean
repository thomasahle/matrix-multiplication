import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoBranchData0
import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoBranchData1
import MatrixMultiplication.Generated.SimplifiedExponentLevelTwoBranchData2

/-! Directed numerical floors for the exact level-two branch forms.

Certificate SHA-256 `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwo

open MatrixMultiplication.SignedDyadicLogForm

noncomputable def commonFloor : ℝ := 177249 / 100000

theorem commonFloor_le_branch0 :
    commonFloor ≤ Form.eval Branch0.bits Branch0.expectedForm := by
  apply le_trans (b := Branch0.branchFloor)
  · norm_num [commonFloor, Branch0.branchFloor, Branch0.constantNumerator,
      Branch0.bits, Branch0.ceiling]
  · exact Branch0.branchFloor_le_expectedForm_eval

theorem commonFloor_le_branch1 :
    commonFloor ≤ Form.eval Branch1.bits Branch1.expectedForm := by
  apply le_trans (b := Branch1.branchFloor)
  · norm_num [commonFloor, Branch1.branchFloor, Branch1.constantNumerator,
      Branch1.bits, Branch1.ceiling]
  · exact Branch1.branchFloor_le_expectedForm_eval

theorem commonFloor_le_branch2 :
    commonFloor ≤ Form.eval Branch2.bits Branch2.expectedForm := by
  apply le_trans (b := Branch2.branchFloor)
  · norm_num [commonFloor, Branch2.branchFloor, Branch2.constantNumerator,
      Branch2.bits, Branch2.ceiling]
  · exact Branch2.branchFloor_le_expectedForm_eval

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwo
