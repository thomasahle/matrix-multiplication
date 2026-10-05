import MatrixMultiplication.Generated.SimplifiedVolumeManifest
import MatrixMultiplication.Generated.SimplifiedVolumePrimaryData
import MatrixMultiplication.Generated.SimplifiedVolumeDualData

/-! # Complete simplified volume generated-data boundary -/

namespace MatrixMultiplication.Generated.SimplifiedVolume

theorem manifest_primary_count : Manifest.activePrimaryValues = primaryValueCount := by
  rw [primaryValueCount_eq]
  decide

theorem manifest_dual_count : Manifest.activeDualValues = dualValueCount := by
  rw [dualValueCount_eq]
  decide

theorem supplied_value_count : primaryValueCount + dualValueCount = 44109 := by
  rw [primaryValueCount_eq, dualValueCount_eq]

end MatrixMultiplication.Generated.SimplifiedVolume
