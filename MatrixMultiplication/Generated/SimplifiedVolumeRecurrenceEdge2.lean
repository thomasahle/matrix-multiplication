import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3


/-! Generated exact scalar-volume recurrence check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge2

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedForm : LogLinearForm :=
  { constantNumerator := 106660027974107136
    terms := [
      ⟨5, (29021912314228586 : ℤ)⟩,
      ⟨134, (-661799736 : ℤ)⟩,
      ⟨136, (-7285998720 : ℤ)⟩,
      ⟨140, (-9792737080 : ℤ)⟩,
      ⟨141, (-8206245684 : ℤ)⟩,
      ⟨142, (-9413284512 : ℤ)⟩,
      ⟨157, (-31283304081672 : ℤ)⟩,
      ⟨158, (-2098030551408 : ℤ)⟩,
      ⟨160, (-7088209920 : ℤ)⟩,
      ⟨161, (-7132511232 : ℤ)⟩,
      ⟨163, (-163901064 : ℤ)⟩,
      ⟨164, (-9326285152944 : ℤ)⟩,
      ⟨165, (-467655547461300 : ℤ)⟩,
      ⟨166, (-69721274880 : ℤ)⟩,
      ⟨168, (-7981799616 : ℤ)⟩,
      ⟨170, (-274090320 : ℤ)⟩,
      ⟨171, (-275702616 : ℤ)⟩,
      ⟨231, (-132522489792 : ℤ)⟩,
      ⟨232, (-336469446416 : ℤ)⟩,
      ⟨233, (-79026966490 : ℤ)⟩,
      ⟨234, (-11985370488 : ℤ)⟩,
      ⟨240, (-365817600 : ℤ)⟩,
      ⟨2009, (-318158443148 : ℤ)⟩,
      ⟨2024, (-1642500288 : ℤ)⟩,
      ⟨2029, (-434599163388 : ℤ)⟩,
      ⟨2030, (-1527859200 : ℤ)⟩,
      ⟨2033, (-2116706742 : ℤ)⟩,
      ⟨2034, (-100752416352 : ℤ)⟩,
      ⟨2039, (-225219376200 : ℤ)⟩,
      ⟨2043, (-1704474900 : ℤ)⟩,
      ⟨2047, (-140891585154065 : ℤ)⟩,
      ⟨2048, (-2227458726801408 : ℤ)⟩,
      ⟨2049, (-141029241807855 : ℤ)⟩,
      ⟨2053, (-1712817900 : ℤ)⟩,
      ⟨2057, (-227207580600 : ℤ)⟩,
      ⟨2062, (-102139371936 : ℤ)⟩,
      ⟨2063, (-2147941962 : ℤ)⟩,
      ⟨2066, (-1554954240 : ℤ)⟩,
      ⟨2067, (-442738526724 : ℤ)⟩,
      ⟨2072, (-1681452864 : ℤ)⟩,
      ⟨2087, (-330511035764 : ℤ)⟩,
      ⟨3616, (-2755825920 : ℤ)⟩,
      ⟨3628, (-92912231048 : ℤ)⟩,
      ⟨3631, (-1231531825430 : ℤ)⟩,
      ⟨3632, (-975986274816 : ℤ)⟩,
      ⟨3633, (-2084217339456 : ℤ)⟩,
      ⟨3755, (-6054171480 : ℤ)⟩,
      ⟨3760, (-89320138560 : ℤ)⟩,
      ⟨3765, (-1581328915200 : ℤ)⟩,
      ⟨3766, (-5336150918687820 : ℤ)⟩,
      ⟨3768, (-107136649659312 : ℤ)⟩,
      ⟨3769, (-3789835032 : ℤ)⟩,
      ⟨3775, (-167237452800 : ℤ)⟩,
      ⟨3781, (-50206667815656 : ℤ)⟩,
      ⟨3782, (-351684472732320 : ℤ)⟩,
      ⟨3812, (-15420325272 : ℤ)⟩,
      ⟨3813, (-221917835412 : ℤ)⟩,
      ⟨3816, (-133461016776 : ℤ)⟩,
      ⟨3824, (-102432570240 : ℤ)⟩,
      ⟨3828, (-9452870856 : ℤ)⟩,
      ⟨4096, (-13812633706496 : ℤ)⟩
    ] }

opaque cached_normalizes :
    LogLinearForm.normalize (edgeRangeFormWithMass3 generatedPrimaryTables Mass3.expectedNumerators 1080 540) =
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
    LogLinearForm.normalize (edgeRangeForm generatedPrimaryTables 1080 540) =
      expectedForm := by
  rw [edgeRangeForm_eq_withMass3, Mass3.recurrence_eq]
  exact cached_normalizes


theorem recurrence_eval_eq :
    (edgeRangeForm generatedPrimaryTables 1080 540).eval commonBits =
      expectedForm.eval commonBits :=
  LogLinearForm.eval_eq_of_normalize_eq recurrence_normalizes commonBits

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge2
