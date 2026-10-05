import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3


/-! Generated exact scalar-volume recurrence check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge8

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedForm : LogLinearForm :=
  { constantNumerator := 182782065085022208
    terms := [
      ⟨5, (138709466488751004 : ℤ)⟩,
      ⟨134, (-48774928 : ℤ)⟩,
      ⟨138, (-469847496 : ℤ)⟩,
      ⟨139, (-19610120 : ℤ)⟩,
      ⟨140, (-318472000 : ℤ)⟩,
      ⟨141, (-357534264 : ℤ)⟩,
      ⟨142, (-260025288 : ℤ)⟩,
      ⟨147, (-136277232 : ℤ)⟩,
      ⟨161, (-36900169934880 : ℤ)⟩,
      ⟨162, (-13056843667392 : ℤ)⟩,
      ⟨163, (-34340179524 : ℤ)⟩,
      ⟨164, (-4258078288 : ℤ)⟩,
      ⟨165, (-413333667780 : ℤ)⟩,
      ⟨166, (-315399190871512 : ℤ)⟩,
      ⟨167, (-66738760780696 : ℤ)⟩,
      ⟨168, (-2952319478976 : ℤ)⟩,
      ⟨169, (-329639102208 : ℤ)⟩,
      ⟨170, (-9622567065600 : ℤ)⟩,
      ⟨171, (-28401566068440 : ℤ)⟩,
      ⟨172, (-18844280020320 : ℤ)⟩,
      ⟨176, (-77679360 : ℤ)⟩,
      ⟨180, (-485624160 : ℤ)⟩,
      ⟨181, (-995127864 : ℤ)⟩,
      ⟨187, (-45957884198688 : ℤ)⟩,
      ⟨188, (-590577584307648 : ℤ)⟩,
      ⟨191, (-8347051440 : ℤ)⟩,
      ⟨192, (-155332086144 : ℤ)⟩,
      ⟨193, (-21513901826946 : ℤ)⟩,
      ⟨231, (-4196357550000 : ℤ)⟩,
      ⟨232, (-4278531691008 : ℤ)⟩,
      ⟨237, (-2176304640 : ℤ)⟩,
      ⟨239, (-191963844 : ℤ)⟩,
      ⟨240, (-242470080 : ℤ)⟩,
      ⟨241, (-49910136 : ℤ)⟩,
      ⟨2030, (-31075245927600 : ℤ)⟩,
      ⟨2033, (-126948652 : ℤ)⟩,
      ⟨2035, (-31792404105000 : ℤ)⟩,
      ⟨2042, (-3709507410000 : ℤ)⟩,
      ⟨2043, (-64607832 : ℤ)⟩,
      ⟨2044, (-132591728981712 : ℤ)⟩,
      ⟨2046, (-68487912274320 : ℤ)⟩,
      ⟨2047, (-429811727133944 : ℤ)⟩,
      ⟨2048, (-522774170304512 : ℤ)⟩,
      ⟨2049, (-430231670199048 : ℤ)⟩,
      ⟨2050, (-68621808486000 : ℤ)⟩,
      ⟨2052, (-133110678997296 : ℤ)⟩,
      ⟨2053, (-64924072 : ℤ)⟩,
      ⟨2054, (-3731306670000 : ℤ)⟩,
      ⟨2061, (-32198596983000 : ℤ)⟩,
      ⟨2063, (-128821972 : ℤ)⟩,
      ⟨2066, (-31626334032720 : ℤ)⟩,
      ⟨3615, (-748652040 : ℤ)⟩,
      ⟨3617, (-2905159932 : ℤ)⟩,
      ⟨3622, (-16629905920 : ℤ)⟩,
      ⟨3632, (-501028850304 : ℤ)⟩,
      ⟨3633, (-65997259650000 : ℤ)⟩,
      ⟨3710, (-205623409219200 : ℤ)⟩,
      ⟨3711, (-2311191807102 : ℤ)⟩,
      ⟨3712, (-345636198400 : ℤ)⟩,
      ⟨3714, (-81154316880 : ℤ)⟩,
      ⟨3720, (-5386123147930560 : ℤ)⟩,
      ⟨3721, (-913896190116000 : ℤ)⟩,
      ⟨3722, (-296067651264 : ℤ)⟩,
      ⟨3734, (-8154159840 : ℤ)⟩,
      ⟨3735, (-4222133640 : ℤ)⟩,
      ⟨3736, (-2928067584 : ℤ)⟩,
      ⟨3744, (-826225920 : ℤ)⟩,
      ⟨3752, (-233029441120 : ℤ)⟩,
      ⟨3753, (-410711624554320 : ℤ)⟩,
      ⟨3754, (-97871510040 : ℤ)⟩,
      ⟨3755, (-212545525478400 : ℤ)⟩,
      ⟨3759, (-7332031865088 : ℤ)⟩,
      ⟨3761, (-58757362083000 : ℤ)⟩,
      ⟨3763, (-1445031493016144 : ℤ)⟩,
      ⟨3764, (-2851481269102208 : ℤ)⟩,
      ⟨3765, (-3204462658500 : ℤ)⟩,
      ⟨3766, (-3073387408000 : ℤ)⟩,
      ⟨3767, (-81960999744 : ℤ)⟩,
      ⟨3769, (-15853393940 : ℤ)⟩,
      ⟨3770, (-389195361880 : ℤ)⟩,
      ⟨3772, (-99194347012416 : ℤ)⟩,
      ⟨3773, (-105654211850880 : ℤ)⟩,
      ⟨3774, (-379647219846240 : ℤ)⟩,
      ⟨3802, (-1762333456 : ℤ)⟩,
      ⟨3812, (-804446360 : ℤ)⟩,
      ⟨3813, (-5372913552 : ℤ)⟩,
      ⟨3815, (-4297979000 : ℤ)⟩,
      ⟨3816, (-1921584960 : ℤ)⟩,
      ⟨3817, (-538502360 : ℤ)⟩,
      ⟨3820, (-6502961720 : ℤ)⟩,
      ⟨3828, (-696680688 : ℤ)⟩
    ] }

opaque cached_normalizes :
    LogLinearForm.normalize (edgeRangeFormWithMass3 generatedPrimaryTables Mass3.expectedNumerators 4320 540) =
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
    LogLinearForm.normalize (edgeRangeForm generatedPrimaryTables 4320 540) =
      expectedForm := by
  rw [edgeRangeForm_eq_withMass3, Mass3.recurrence_eq]
  exact cached_normalizes


theorem recurrence_eval_eq :
    (edgeRangeForm generatedPrimaryTables 4320 540).eval commonBits =
      expectedForm.eval commonBits :=
  LogLinearForm.eval_eq_of_normalize_eq recurrence_normalizes commonBits

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge8
