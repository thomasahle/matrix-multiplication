import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3


/-! Generated exact scalar-volume recurrence check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge13

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedForm : LogLinearForm :=
  { constantNumerator := 2230301425434624
    terms := [
      ⟨5, (213091779190688 : ℤ)⟩,
      ⟨138, (-95571072 : ℤ)⟩,
      ⟨139, (-61470804 : ℤ)⟩,
      ⟨140, (-61913040 : ℤ)⟩,
      ⟨147, (-275819040 : ℤ)⟩,
      ⟨169, (-121031040 : ℤ)⟩,
      ⟨170, (-31894714560 : ℤ)⟩,
      ⟨189, (-2920809780 : ℤ)⟩,
      ⟨190, (-2936263800 : ℤ)⟩,
      ⟨191, (-24550253760 : ℤ)⟩,
      ⟨2043, (-38526959376000 : ℤ)⟩,
      ⟨2046, (-38583533472000 : ℤ)⟩,
      ⟨2048, (-5744549142528 : ℤ)⟩,
      ⟨2050, (-38658965600000 : ℤ)⟩,
      ⟨2053, (-38715539696000 : ℤ)⟩,
      ⟨3714, (-238690163520 : ℤ)⟩,
      ⟨3717, (-57442592340 : ℤ)⟩,
      ⟨3756, (-352342787904 : ℤ)⟩,
      ⟨3758, (-1345664640 : ℤ)⟩,
      ⟨3802, (-3566884320 : ℤ)⟩,
      ⟨3817, (-1688014812 : ℤ)⟩,
      ⟨3820, (-1322759040 : ℤ)⟩,
      ⟨4096, (-24909588119552 : ℤ)⟩
    ] }

opaque cached_normalizes :
    LogLinearForm.normalize (edgeRangeFormWithMass3 generatedPrimaryTables Mass3.expectedNumerators 7020 540) =
      expectedForm := by
  unfold generatedPrimaryTables pos3AChunks pos3AlphaChunks edgeZero2Chunks muChunks
  rw [Pos3AData0.data_eq_rawData,
    Pos3AlphaData0.data_eq_rawData,
    Pos3AlphaData1.data_eq_rawData,
    EdgeZero2Data0.data_eq_rawData,
    EdgeZero2Data1.data_eq_rawData,
    EdgeZero2Data2.data_eq_rawData,
    MuData0.data_eq_rawData]
  decide +kernel

opaque recurrence_normalizes :
    LogLinearForm.normalize (edgeRangeForm generatedPrimaryTables 7020 540) =
      expectedForm := by
  rw [edgeRangeForm_eq_withMass3, Mass3.recurrence_eq]
  exact cached_normalizes


theorem recurrence_eval_eq :
    (edgeRangeForm generatedPrimaryTables 7020 540).eval commonBits =
      expectedForm.eval commonBits :=
  LogLinearForm.eval_eq_of_normalize_eq recurrence_normalizes commonBits

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge13
