import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3


/-! Generated exact scalar-volume recurrence check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.ZeroThree1

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedForm : LogLinearForm :=
  { constantNumerator := 16828300341018624
    terms := [
      ⟨5, (3698521295290368 : ℤ)⟩,
      ⟨31, (-4512332906496 : ℤ)⟩,
      ⟨39, (-23023910387712 : ℤ)⟩,
      ⟨40, (-23614267064320 : ℤ)⟩,
      ⟨41, (-38085756715008 : ℤ)⟩,
      ⟨42, (-13004892536832 : ℤ)⟩,
      ⟨51, (-31583310446592 : ℤ)⟩,
      ⟨53, (-31288903860224 : ℤ)⟩,
      ⟨606, (-22306382413824 : ℤ)⟩,
      ⟨607, (-22343191625728 : ℤ)⟩,
      ⟨611, (-43955769049088 : ℤ)⟩,
      ⟨764, (-27481348243456 : ℤ)⟩,
      ⟨773, (-28453520801792 : ℤ)⟩,
      ⟨890, (-275579865661440 : ℤ)⟩,
      ⟨891, (-275889505959936 : ℤ)⟩,
      ⟨892, (-526598155534336 : ℤ)⟩,
      ⟨1024, (-14637248544768 : ℤ)⟩
    ] }

opaque cached_normalizes :
    LogLinearForm.normalize (zeroThreeRangeFormWithMass3 generatedPrimaryTables Mass3.expectedNumerators 90 90) =
      expectedForm := by
  unfold generatedPrimaryTables zero3Chunks
  rw [Zero3Data0.data_eq_rawData]
  decide +kernel

opaque recurrence_normalizes :
    LogLinearForm.normalize (zeroThreeRangeForm generatedPrimaryTables 90 90) =
      expectedForm := by
  rw [zeroThreeRangeForm_eq_withMass3, Mass3.recurrence_eq]
  exact cached_normalizes


theorem recurrence_eval_eq :
    (zeroThreeRangeForm generatedPrimaryTables 90 90).eval commonBits =
      expectedForm.eval commonBits :=
  LogLinearForm.eval_eq_of_normalize_eq recurrence_normalizes commonBits

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.ZeroThree1
