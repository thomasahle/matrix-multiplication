import MatrixMultiplication.SimplifiedVolumeReconstruction


/-! Generated exact scalar-volume recurrence check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.ZeroFour0

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedForm : LogLinearForm :=
  { constantNumerator := 0
    terms := [] }

opaque recurrence_normalizes :
    LogLinearForm.normalize (zeroFourRangeForm generatedPrimaryTables 0 48) =
      expectedForm := by
  unfold generatedPrimaryTables topChunks zero4Chunks
  rw [TopData0.data_eq_rawData,
    TopData1.data_eq_rawData,
    Zero4Data0.data_eq_rawData,
    Zero4Data1.data_eq_rawData,
    Zero4Data2.data_eq_rawData,
    Zero4Data3.data_eq_rawData,
    Zero4Data4.data_eq_rawData,
    Zero4Data5.data_eq_rawData,
    Zero4Data6.data_eq_rawData,
    Zero4Data7.data_eq_rawData,
    Zero4Data8.data_eq_rawData,
    Zero4Data9.data_eq_rawData,
    Zero4Data10.data_eq_rawData,
    Zero4Data11.data_eq_rawData,
    Zero4Data12.data_eq_rawData,
    Zero4Data13.data_eq_rawData]
  decide +kernel


theorem recurrence_eval_eq :
    (zeroFourRangeForm generatedPrimaryTables 0 48).eval commonBits =
      expectedForm.eval commonBits :=
  LogLinearForm.eval_eq_of_normalize_eq recurrence_normalizes commonBits

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.ZeroFour0
