import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3


/-! Generated exact scalar-volume recurrence check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge12

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedForm : LogLinearForm :=
  { constantNumerator := 48829393075863552
    terms := [
      ⟨5, (8758174704898524 : ℤ)⟩,
      ⟨138, (-310675536 : ℤ)⟩,
      ⟨140, (-138763800 : ℤ)⟩,
      ⟨141, (-34844879082 : ℤ)⟩,
      ⟨142, (-8737989312 : ℤ)⟩,
      ⟨143, (-17819324666 : ℤ)⟩,
      ⟨144, (-9528015456 : ℤ)⟩,
      ⟨147, (-262525536 : ℤ)⟩,
      ⟨150, (-18666741600 : ℤ)⟩,
      ⟨161, (-2462442452176 : ℤ)⟩,
      ⟨162, (-41834293189344 : ℤ)⟩,
      ⟨163, (-5934414024 : ℤ)⟩,
      ⟨164, (-14469806592 : ℤ)⟩,
      ⟨166, (-1824262317312 : ℤ)⟩,
      ⟨167, (-5117073720 : ℤ)⟩,
      ⟨168, (-7983343872 : ℤ)⟩,
      ⟨169, (-78329472 : ℤ)⟩,
      ⟨170, (-32140299960 : ℤ)⟩,
      ⟨172, (-129437568 : ℤ)⟩,
      ⟨176, (-94283904 : ℤ)⟩,
      ⟨179, (-79271940 : ℤ)⟩,
      ⟨186, (-5100616620 : ℤ)⟩,
      ⟨187, (-53083791354 : ℤ)⟩,
      ⟨192, (-43829889080832 : ℤ)⟩,
      ⟨2037, (-232367113411020 : ℤ)⟩,
      ⟨2042, (-451051132411152 : ℤ)⟩,
      ⟨2044, (-248286421586112 : ℤ)⟩,
      ⟨2045, (-426045836885200 : ℤ)⟩,
      ⟨2047, (-137422659336 : ℤ)⟩,
      ⟨2048, (-248681775230976 : ℤ)⟩,
      ⟨2049, (-137556926712 : ℤ)⟩,
      ⟨2051, (-427295849120560 : ℤ)⟩,
      ⟨2052, (-249258188402496 : ℤ)⟩,
      ⟨2054, (-453701775696624 : ℤ)⟩,
      ⟨2059, (-234876723865140 : ℤ)⟩,
      ⟨3712, (-423688927781376 : ℤ)⟩,
      ⟨3722, (-477249489792 : ℤ)⟩,
      ⟨3723, (-102094600410 : ℤ)⟩,
      ⟨3738, (-827705340 : ℤ)⟩,
      ⟨3744, (-1002837888 : ℤ)⟩,
      ⟨3752, (-1411772544 : ℤ)⟩,
      ⟨3756, (-355055784264 : ℤ)⟩,
      ⟨3758, (-870893952 : ℤ)⟩,
      ⟨3760, (-89337419520 : ℤ)⟩,
      ⟨3762, (-57636021960 : ℤ)⟩,
      ⟨3764, (-20682299284224 : ℤ)⟩,
      ⟨3768, (-166226314752 : ℤ)⟩,
      ⟨3770, (-68628039480 : ℤ)⟩,
      ⟨3772, (-458188053925056 : ℤ)⟩,
      ⟨3773, (-57706803553168 : ℤ)⟩,
      ⟨3796, (-236196503712 : ℤ)⟩,
      ⟨3802, (-3394973088 : ℤ)⟩,
      ⟨3809, (-252029242166 : ℤ)⟩,
      ⟨3810, (-111335606640 : ℤ)⟩,
      ⟨3812, (-113873146608 : ℤ)⟩,
      ⟨3813, (-6827435784 : ℤ)⟩,
      ⟨3814, (-466743909976 : ℤ)⟩,
      ⟨3815, (-2225159790 : ℤ)⟩,
      ⟨3816, (-778280832 : ℤ)⟩,
      ⟨3820, (-4299929520 : ℤ)⟩,
      ⟨4096, (-44326757224448 : ℤ)⟩
    ] }

opaque cached_normalizes :
    LogLinearForm.normalize (edgeRangeFormWithMass3 generatedPrimaryTables Mass3.expectedNumerators 6480 540) =
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
    LogLinearForm.normalize (edgeRangeForm generatedPrimaryTables 6480 540) =
      expectedForm := by
  rw [edgeRangeForm_eq_withMass3, Mass3.recurrence_eq]
  exact cached_normalizes


theorem recurrence_eval_eq :
    (edgeRangeForm generatedPrimaryTables 6480 540).eval commonBits =
      expectedForm.eval commonBits :=
  LogLinearForm.eval_eq_of_normalize_eq recurrence_normalizes commonBits

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge12
