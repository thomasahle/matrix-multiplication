import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3


/-! Generated exact scalar-volume recurrence check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge10

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedForm : LogLinearForm :=
  { constantNumerator := 180333086940020736
    terms := [
      ⟨5, (65217020065790820 : ℤ)⟩,
      ⟨134, (-5943168 : ℤ)⟩,
      ⟨138, (-2050465824 : ℤ)⟩,
      ⟨139, (-17373888 : ℤ)⟩,
      ⟨140, (-421523760 : ℤ)⟩,
      ⟨141, (-26691340608 : ℤ)⟩,
      ⟨142, (-176338638800 : ℤ)⟩,
      ⟨147, (-37241568 : ℤ)⟩,
      ⟨158, (-576391637088 : ℤ)⟩,
      ⟨160, (-3515149653120 : ℤ)⟩,
      ⟨161, (-372421015723988 : ℤ)⟩,
      ⟨162, (-198328181296752 : ℤ)⟩,
      ⟨163, (-82270435800 : ℤ)⟩,
      ⟨164, (-344944427520 : ℤ)⟩,
      ⟨165, (-88031966408100 : ℤ)⟩,
      ⟨166, (-136620871946744 : ℤ)⟩,
      ⟨167, (-35286885462114 : ℤ)⟩,
      ⟨168, (-35498536525872 : ℤ)⟩,
      ⟨169, (-51123949344 : ℤ)⟩,
      ⟨170, (-298223520 : ℤ)⟩,
      ⟨171, (-299977776 : ℤ)⟩,
      ⟨172, (-326819952 : ℤ)⟩,
      ⟨176, (-73269504 : ℤ)⟩,
      ⟨179, (-279759816 : ℤ)⟩,
      ⟨186, (-149173999128 : ℤ)⟩,
      ⟨187, (-39575966784618 : ℤ)⟩,
      ⟨188, (-39724158484296 : ℤ)⟩,
      ⟨192, (-16811569152 : ℤ)⟩,
      ⟨193, (-8497197667560 : ℤ)⟩,
      ⟨232, (-336338263872 : ℤ)⟩,
      ⟨240, (-8104320 : ℤ)⟩,
      ⟨241, (-8138088 : ℤ)⟩,
      ⟨2039, (-12259197855972 : ℤ)⟩,
      ⟨2041, (-160520698334178 : ℤ)⟩,
      ⟨2042, (-81409806929880 : ℤ)⟩,
      ⟨2044, (-505304461958912 : ℤ)⟩,
      ⟨2045, (-12449929513140 : ℤ)⟩,
      ⟨2047, (-19035208572 : ℤ)⟩,
      ⟨2048, (-1551162843197440 : ℤ)⟩,
      ⟨2049, (-19053806724 : ℤ)⟩,
      ⟨2051, (-12486457423692 : ℤ)⟩,
      ⟨2052, (-507282170224896 : ℤ)⟩,
      ⟨2054, (-81888219115560 : ℤ)⟩,
      ⟨2055, (-161621771228190 : ℤ)⟩,
      ⟨2057, (-12367420299036 : ℤ)⟩,
      ⟨3615, (-122071320 : ℤ)⟩,
      ⟨3632, (-2632716755136 : ℤ)⟩,
      ⟨3710, (-81507532581720 : ℤ)⟩,
      ⟨3711, (-324936110016 : ℤ)⟩,
      ⟨3721, (-786242519787582 : ℤ)⟩,
      ⟨3723, (-1256403311856 : ℤ)⟩,
      ⟨3724, (-864973621512 : ℤ)⟩,
      ⟨3738, (-2921067576 : ℤ)⟩,
      ⟨3744, (-779321088 : ℤ)⟩,
      ⟨3752, (-3564617616 : ℤ)⟩,
      ⟨3755, (-6587231280 : ℤ)⟩,
      ⟨3758, (-568413614304 : ℤ)⟩,
      ⟨3760, (-3942946560 : ℤ)⟩,
      ⟨3761, (-794694468401262 : ℤ)⟩,
      ⟨3764, (-544820616142208 : ℤ)⟩,
      ⟨3765, (-2008729415312100 : ℤ)⟩,
      ⟨3768, (-3962654277120 : ℤ)⟩,
      ⟨3770, (-18081161280 : ℤ)⟩,
      ⟨3771, (-1867152093912 : ℤ)⟩,
      ⟨3772, (-1170873762240 : ℤ)⟩,
      ⟨3773, (-4614877316650832 : ℤ)⟩,
      ⟨3774, (-2015452337621904 : ℤ)⟩,
      ⟨3775, (-82935562128300 : ℤ)⟩,
      ⟨3780, (-6894811355040 : ℤ)⟩,
      ⟨3802, (-481606944 : ℤ)⟩,
      ⟨3812, (-2011519933880 : ℤ)⟩,
      ⟨3813, (-710969768460 : ℤ)⟩,
      ⟨3815, (-10837911420 : ℤ)⟩,
      ⟨3816, (-85905792 : ℤ)⟩,
      ⟨3817, (-477094464 : ℤ)⟩,
      ⟨3820, (-28379635680 : ℤ)⟩,
      ⟨3828, (-84889728 : ℤ)⟩,
      ⟨4096, (-18100800159744 : ℤ)⟩
    ] }

opaque cached_normalizes :
    LogLinearForm.normalize (edgeRangeFormWithMass3 generatedPrimaryTables Mass3.expectedNumerators 5400 540) =
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
    LogLinearForm.normalize (edgeRangeForm generatedPrimaryTables 5400 540) =
      expectedForm := by
  rw [edgeRangeForm_eq_withMass3, Mass3.recurrence_eq]
  exact cached_normalizes


theorem recurrence_eval_eq :
    (edgeRangeForm generatedPrimaryTables 5400 540).eval commonBits =
      expectedForm.eval commonBits :=
  LogLinearForm.eval_eq_of_normalize_eq recurrence_normalizes commonBits

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge10
