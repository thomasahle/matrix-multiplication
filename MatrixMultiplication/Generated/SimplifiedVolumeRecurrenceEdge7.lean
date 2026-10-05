import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3


/-! Generated exact scalar-volume recurrence check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge7

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedForm : LogLinearForm :=
  { constantNumerator := 78402461524328448
    terms := [
      ⟨5, (23225377420441788 : ℤ)⟩,
      ⟨138, (-788063904 : ℤ)⟩,
      ⟨139, (-88061516788 : ℤ)⟩,
      ⟨140, (-110250000 : ℤ)⟩,
      ⟨141, (-1017066276 : ℤ)⟩,
      ⟨142, (-2063112888 : ℤ)⟩,
      ⟨145, (-46443110820 : ℤ)⟩,
      ⟨146, (-139209614168 : ℤ)⟩,
      ⟨147, (-83788236 : ℤ)⟩,
      ⟨163, (-23655269376 : ℤ)⟩,
      ⟨164, (-2201658672 : ℤ)⟩,
      ⟨165, (-95596338420 : ℤ)⟩,
      ⟨166, (-202480945752368 : ℤ)⟩,
      ⟨167, (-203386134842320 : ℤ)⟩,
      ⟨168, (-844730208 : ℤ)⟩,
      ⟨170, (-21369081600 : ℤ)⟩,
      ⟨171, (-6883372440 : ℤ)⟩,
      ⟨172, (-450633120 : ℤ)⟩,
      ⟨175, (-31313028238800 : ℤ)⟩,
      ⟨177, (-4000596480 : ℤ)⟩,
      ⟨185, (-93091260 : ℤ)⟩,
      ⟨186, (-93594456 : ℤ)⟩,
      ⟨2027, (-487307016 : ℤ)⟩,
      ⟨2028, (-427924224 : ℤ)⟩,
      ⟨2030, (-293818140 : ℤ)⟩,
      ⟨2035, (-127900238400 : ℤ)⟩,
      ⟨2036, (-24843357609728 : ℤ)⟩,
      ⟨2037, (-40998332340 : ℤ)⟩,
      ⟨2040, (-27386485920 : ℤ)⟩,
      ⟨2043, (-700544700 : ℤ)⟩,
      ⟨2046, (-411899017728 : ℤ)⟩,
      ⟨2047, (-26913472908 : ℤ)⟩,
      ⟨2048, (-1110884074668032 : ℤ)⟩,
      ⟨2049, (-26939768436 : ℤ)⟩,
      ⟨2050, (-412704294400 : ℤ)⟩,
      ⟨2053, (-703973700 : ℤ)⟩,
      ⟨2056, (-27601281888 : ℤ)⟩,
      ⟨2059, (-41441122380 : ℤ)⟩,
      ⟨2060, (-25136206618880 : ℤ)⟩,
      ⟨2061, (-129534344640 : ℤ)⟩,
      ⟨2066, (-299028708 : ℤ)⟩,
      ⟨2068, (-436364544 : ℤ)⟩,
      ⟨2069, (-497404152 : ℤ)⟩,
      ⟨3725, (-1874405100 : ℤ)⟩,
      ⟨3742, (-42288791040 : ℤ)⟩,
      ⟨3746, (-335138867950128 : ℤ)⟩,
      ⟨3752, (-4915044960 : ℤ)⟩,
      ⟨3754, (-75556082280 : ℤ)⟩,
      ⟨3756, (-236065501440 : ℤ)⟩,
      ⟨3760, (-9452933280 : ℤ)⟩,
      ⟨3763, (-4582886379710480 : ℤ)⟩,
      ⟨3764, (-3545097970416 : ℤ)⟩,
      ⟨3766, (-1065678201000 : ℤ)⟩,
      ⟨3767, (-50571025716 : ℤ)⟩,
      ⟨3770, (-273559403520 : ℤ)⟩,
      ⟨3802, (-1083547188 : ℤ)⟩,
      ⟨3804, (-1204333451184 : ℤ)⟩,
      ⟨3805, (-1218731287380 : ℤ)⟩,
      ⟨3812, (-27692205384 : ℤ)⟩,
      ⟨3814, (-12907788852 : ℤ)⟩,
      ⟨3815, (-1696149000 : ℤ)⟩,
      ⟨3817, (-1308849300 : ℤ)⟩,
      ⟨3818, (-1208765803528 : ℤ)⟩,
      ⟨3820, (-10907261280 : ℤ)⟩,
      ⟨4096, (-6766849654784 : ℤ)⟩
    ] }

opaque cached_normalizes :
    LogLinearForm.normalize (edgeRangeFormWithMass3 generatedPrimaryTables Mass3.expectedNumerators 3780 540) =
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
    LogLinearForm.normalize (edgeRangeForm generatedPrimaryTables 3780 540) =
      expectedForm := by
  rw [edgeRangeForm_eq_withMass3, Mass3.recurrence_eq]
  exact cached_normalizes


theorem recurrence_eval_eq :
    (edgeRangeForm generatedPrimaryTables 3780 540).eval commonBits =
      expectedForm.eval commonBits :=
  LogLinearForm.eval_eq_of_normalize_eq recurrence_normalizes commonBits

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge7
