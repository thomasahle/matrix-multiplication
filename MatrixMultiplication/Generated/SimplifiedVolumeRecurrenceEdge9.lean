import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3


/-! Generated exact scalar-volume recurrence check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge9

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedForm : LogLinearForm :=
  { constantNumerator := 79222480820994048
    terms := [
      ⟨5, (23686076977959496 : ℤ)⟩,
      ⟨134, (-27368160 : ℤ)⟩,
      ⟨138, (-1260964512 : ℤ)⟩,
      ⟨140, (-962071040 : ℤ)⟩,
      ⟨141, (-28371456 : ℤ)⟩,
      ⟨142, (-40836360 : ℤ)⟩,
      ⟨145, (-46126032070 : ℤ)⟩,
      ⟨146, (-46444142636 : ℤ)⟩,
      ⟨147, (-1455358800 : ℤ)⟩,
      ⟨161, (-228956209860 : ℤ)⟩,
      ⟨162, (-652210838136 : ℤ)⟩,
      ⟨163, (-16688653288 : ℤ)⟩,
      ⟨164, (-16791037664 : ℤ)⟩,
      ⟨167, (-444872773984084 : ℤ)⟩,
      ⟨168, (-19847620128 : ℤ)⟩,
      ⟨169, (-5850429156 : ℤ)⟩,
      ⟨170, (-51222123360 : ℤ)⟩,
      ⟨171, (-22338072 : ℤ)⟩,
      ⟨175, (-237405000 : ℤ)⟩,
      ⟨176, (-370505344 : ℤ)⟩,
      ⟨179, (-480274763065 : ℤ)⟩,
      ⟨180, (-58287816540 : ℤ)⟩,
      ⟨183, (-1623283200 : ℤ)⟩,
      ⟨185, (-504175320 : ℤ)⟩,
      ⟨186, (-275589504 : ℤ)⟩,
      ⟨187, (-131947200 : ℤ)⟩,
      ⟨238, (-1442622720 : ℤ)⟩,
      ⟨240, (-10897920 : ℤ)⟩,
      ⟨241, (-10943328 : ℤ)⟩,
      ⟨2024, (-49797006336 : ℤ)⟩,
      ⟨2028, (-18448184664 : ℤ)⟩,
      ⟨2031, (-318992922 : ℤ)⟩,
      ⟨2032, (-284207712 : ℤ)⟩,
      ⟨2033, (-84105210 : ℤ)⟩,
      ⟨2035, (-4678559192010 : ℤ)⟩,
      ⟨2041, (-1835479464 : ℤ)⟩,
      ⟨2043, (-295062318 : ℤ)⟩,
      ⟨2044, (-45073511280 : ℤ)⟩,
      ⟨2046, (-15204317040 : ℤ)⟩,
      ⟨2047, (-16742281992 : ℤ)⟩,
      ⟨2048, (-1106888717914112 : ℤ)⟩,
      ⟨2049, (-16758639864 : ℤ)⟩,
      ⟨2050, (-15234042000 : ℤ)⟩,
      ⟨2052, (-45249924240 : ℤ)⟩,
      ⟨2053, (-296506578 : ℤ)⟩,
      ⟨2055, (-1848069720 : ℤ)⟩,
      ⟨2061, (-4738334395446 : ℤ)⟩,
      ⟨2063, (-85346310 : ℤ)⟩,
      ⟨2064, (-288683424 : ℤ)⟩,
      ⟨2065, (-324333030 : ℤ)⟩,
      ⟨2068, (-18812054184 : ℤ)⟩,
      ⟨2072, (-50977963008 : ℤ)⟩,
      ⟨3615, (-164149920 : ℤ)⟩,
      ⟨3620, (-10971206400 : ℤ)⟩,
      ⟨3723, (-2626948800 : ℤ)⟩,
      ⟨3724, (-1445031168 : ℤ)⟩,
      ⟨3726, (-5077181736 : ℤ)⟩,
      ⟨3730, (-16543296000 : ℤ)⟩,
      ⟨3737, (-1210119835611 : ℤ)⟩,
      ⟨3738, (-4409490641808 : ℤ)⟩,
      ⟨3744, (-1401274368 : ℤ)⟩,
      ⟨3745, (-5080467000 : ℤ)⟩,
      ⟨3755, (-490523160 : ℤ)⟩,
      ⟨3756, (-565608482928 : ℤ)⟩,
      ⟨3759, (-130128776316 : ℤ)⟩,
      ⟨3760, (-5627088160 : ℤ)⟩,
      ⟨3761, (-302871599940 : ℤ)⟩,
      ⟨3762, (-5010661026115272 : ℤ)⟩,
      ⟨3769, (-385886713144 : ℤ)⟩,
      ⟨3772, (-4910964015248 : ℤ)⟩,
      ⟨3773, (-5365539004980 : ℤ)⟩,
      ⟨3802, (-18820660400 : ℤ)⟩,
      ⟨3805, (-1210410703630 : ℤ)⟩,
      ⟨3812, (-363985008 : ℤ)⟩,
      ⟨3813, (-368381556 : ℤ)⟩,
      ⟨3815, (-399064260 : ℤ)⟩,
      ⟨3816, (-12912069456 : ℤ)⟩,
      ⟨3820, (-17452479840 : ℤ)⟩,
      ⟨3828, (-390915360 : ℤ)⟩,
      ⟨4096, (-9513772597248 : ℤ)⟩
    ] }

opaque cached_normalizes :
    LogLinearForm.normalize (edgeRangeFormWithMass3 generatedPrimaryTables Mass3.expectedNumerators 4860 540) =
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
    LogLinearForm.normalize (edgeRangeForm generatedPrimaryTables 4860 540) =
      expectedForm := by
  rw [edgeRangeForm_eq_withMass3, Mass3.recurrence_eq]
  exact cached_normalizes


theorem recurrence_eval_eq :
    (edgeRangeForm generatedPrimaryTables 4860 540).eval commonBits =
      expectedForm.eval commonBits :=
  LogLinearForm.eval_eq_of_normalize_eq recurrence_normalizes commonBits

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge9
