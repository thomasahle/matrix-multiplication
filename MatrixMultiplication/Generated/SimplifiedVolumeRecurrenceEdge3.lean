import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3


/-! Generated exact scalar-volume recurrence check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge3

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedForm : LogLinearForm :=
  { constantNumerator := 2298010013073408
    terms := [
      ⟨5, (198425198536552 : ℤ)⟩,
      ⟨134, (-62313216 : ℤ)⟩,
      ⟨140, (-232548960 : ℤ)⟩,
      ⟨142, (-69632256 : ℤ)⟩,
      ⟨159, (-14897870064 : ℤ)⟩,
      ⟨160, (-14991567360 : ℤ)⟩,
      ⟨161, (-7205046240 : ℤ)⟩,
      ⟨167, (-14518258560 : ℤ)⟩,
      ⟨168, (-1940484672 : ℤ)⟩,
      ⟨169, (-1952035176 : ℤ)⟩,
      ⟨240, (-177736320 : ℤ)⟩,
      ⟨2009, (-4065072662028 : ℤ)⟩,
      ⟨2024, (-2882499840 : ℤ)⟩,
      ⟨2026, (-515799356208 : ℤ)⟩,
      ⟨2027, (-84630006720 : ℤ)⟩,
      ⟨2028, (-43929181296 : ℤ)⟩,
      ⟨2031, (-1585934784 : ℤ)⟩,
      ⟨2042, (-1346041476 : ℤ)⟩,
      ⟨2045, (-738555840 : ℤ)⟩,
      ⟨2046, (-1241840160 : ℤ)⟩,
      ⟨2048, (-177193448325120 : ℤ)⟩,
      ⟨2050, (-1244268000 : ℤ)⟩,
      ⟨2051, (-740722752 : ℤ)⟩,
      ⟨2054, (-1353951612 : ℤ)⟩,
      ⟨2065, (-1612484160 : ℤ)⟩,
      ⟨2068, (-44795634576 : ℤ)⟩,
      ⟨2069, (-86383563840 : ℤ)⟩,
      ⟨2070, (-527001316560 : ℤ)⟩,
      ⟨2072, (-2950859520 : ℤ)⟩,
      ⟨2087, (-4222900271604 : ℤ)⟩,
      ⟨3616, (-1338946944 : ℤ)⟩,
      ⟨3759, (-43418344536 : ℤ)⟩,
      ⟨3762, (-163526014080 : ℤ)⟩,
      ⟨3774, (-84446722080 : ℤ)⟩,
      ⟨3777, (-353894686992 : ℤ)⟩,
      ⟨3812, (-934641408 : ℤ)⟩,
      ⟨3816, (-3169310112 : ℤ)⟩,
      ⟨3828, (-890055936 : ℤ)⟩,
      ⟨4096, (-3993510731776 : ℤ)⟩
    ] }

opaque cached_normalizes :
    LogLinearForm.normalize (edgeRangeFormWithMass3 generatedPrimaryTables Mass3.expectedNumerators 1620 540) =
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
    LogLinearForm.normalize (edgeRangeForm generatedPrimaryTables 1620 540) =
      expectedForm := by
  rw [edgeRangeForm_eq_withMass3, Mass3.recurrence_eq]
  exact cached_normalizes


theorem recurrence_eval_eq :
    (edgeRangeForm generatedPrimaryTables 1620 540).eval commonBits =
      expectedForm.eval commonBits :=
  LogLinearForm.eval_eq_of_normalize_eq recurrence_normalizes commonBits

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge3
