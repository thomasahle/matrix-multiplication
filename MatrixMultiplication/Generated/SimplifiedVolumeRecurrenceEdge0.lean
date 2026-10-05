import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3


/-! Generated exact scalar-volume recurrence check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge0

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedForm : LogLinearForm :=
  { constantNumerator := 25779674011779072
    terms := [
      ⟨5, (4410808287055552 : ℤ)⟩,
      ⟨134, (-29522880 : ℤ)⟩,
      ⟨135, (-4173318720 : ℤ)⟩,
      ⟨136, (-4204232192 : ℤ)⟩,
      ⟨140, (-212674560 : ℤ)⟩,
      ⟨141, (-4163364246 : ℤ)⟩,
      ⟨142, (-4229970692 : ℤ)⟩,
      ⟨143, (-4255453631 : ℤ)⟩,
      ⟨144, (-4285212048 : ℤ)⟩,
      ⟨161, (-19659334608214 : ℤ)⟩,
      ⟨162, (-19798159199148 : ℤ)⟩,
      ⟨170, (-598610403900 : ℤ)⟩,
      ⟨171, (-608129924850 : ℤ)⟩,
      ⟨233, (-6948390860 : ℤ)⟩,
      ⟨234, (-6978212280 : ℤ)⟩,
      ⟨240, (-35196480 : ℤ)⟩,
      ⟨241, (-35343132 : ℤ)⟩,
      ⟨2045, (-41678047203100 : ℤ)⟩,
      ⟨2048, (-1514525821194240 : ℤ)⟩,
      ⟨2051, (-41800329982180 : ℤ)⟩,
      ⟨3615, (-530146980 : ℤ)⟩,
      ⟨3629, (-108221933180 : ℤ)⟩,
      ⟨3754, (-65840805360 : ℤ)⟩,
      ⟨3755, (-13222247450850 : ℤ)⟩,
      ⟨3772, (-194617999680 : ℤ)⟩,
      ⟨3773, (-460712232775102 : ℤ)⟩,
      ⟨3809, (-113349810353 : ℤ)⟩,
      ⟨3812, (-497694720 : ℤ)⟩,
      ⟨3813, (-112587999078 : ℤ)⟩,
      ⟨3816, (-2898450432 : ℤ)⟩,
      ⟨3825, (-118244030400 : ℤ)⟩,
      ⟨3828, (-421692480 : ℤ)⟩,
      ⟨4096, (-34946493452288 : ℤ)⟩
    ] }

opaque cached_normalizes :
    LogLinearForm.normalize (edgeRangeFormWithMass3 generatedPrimaryTables Mass3.expectedNumerators 0 540) =
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
    LogLinearForm.normalize (edgeRangeForm generatedPrimaryTables 0 540) =
      expectedForm := by
  rw [edgeRangeForm_eq_withMass3, Mass3.recurrence_eq]
  exact cached_normalizes


theorem recurrence_eval_eq :
    (edgeRangeForm generatedPrimaryTables 0 540).eval commonBits =
      expectedForm.eval commonBits :=
  LogLinearForm.eval_eq_of_normalize_eq recurrence_normalizes commonBits

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge0
