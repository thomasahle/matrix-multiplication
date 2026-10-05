import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3


/-! Generated exact scalar-volume recurrence check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge5

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedForm : LogLinearForm :=
  { constantNumerator := 93467647592595456
    terms := [
      ⟨5, (69241456139785194 : ℤ)⟩,
      ⟨134, (-482105736 : ℤ)⟩,
      ⟨138, (-262509120 : ℤ)⟩,
      ⟨139, (-34433080 : ℤ)⟩,
      ⟨140, (-870717960 : ℤ)⟩,
      ⟨141, (-86816238 : ℤ)⟩,
      ⟨142, (-514567104 : ℤ)⟩,
      ⟨147, (-85398180 : ℤ)⟩,
      ⟨162, (-84932673120 : ℤ)⟩,
      ⟨163, (-32590301137162 : ℤ)⟩,
      ⟨164, (-40268227080 : ℤ)⟩,
      ⟨165, (-9297969120 : ℤ)⟩,
      ⟨166, (-99823235472 : ℤ)⟩,
      ⟨167, (-71107743624 : ℤ)⟩,
      ⟨168, (-8603886144 : ℤ)⟩,
      ⟨169, (-494145129018216 : ℤ)⟩,
      ⟨170, (-2318115240 : ℤ)⟩,
      ⟨171, (-839770309764 : ℤ)⟩,
      ⟨172, (-450121936 : ℤ)⟩,
      ⟨173, (-421544256 : ℤ)⟩,
      ⟨175, (-306399100 : ℤ)⟩,
      ⟨176, (-184734106304 : ℤ)⟩,
      ⟨177, (-9425411424 : ℤ)⟩,
      ⟨179, (-29487744 : ℤ)⟩,
      ⟨181, (-855814336 : ℤ)⟩,
      ⟨185, (-1665266400 : ℤ)⟩,
      ⟨188, (-33163073664 : ℤ)⟩,
      ⟨193, (-19903846230192 : ℤ)⟩,
      ⟨194, (-19976691681984 : ℤ)⟩,
      ⟨231, (-236849172714 : ℤ)⟩,
      ⟨232, (-468627224688 : ℤ)⟩,
      ⟨233, (-24777995424 : ℤ)⟩,
      ⟨235, (-13718307360 : ℤ)⟩,
      ⟨239, (-166734048 : ℤ)⟩,
      ⟨240, (-167431680 : ℤ)⟩,
      ⟨2031, (-263607552 : ℤ)⟩,
      ⟨2033, (-470037732 : ℤ)⟩,
      ⟨2037, (-155504905920 : ℤ)⟩,
      ⟨2042, (-151287867528 : ℤ)⟩,
      ⟨2043, (-404125830 : ℤ)⟩,
      ⟨2046, (-197360668828620 : ℤ)⟩,
      ⟨2047, (-11201564742 : ℤ)⟩,
      ⟨2048, (-550112472080384 : ℤ)⟩,
      ⟨2049, (-11212509114 : ℤ)⟩,
      ⟨2050, (-197746515688500 : ℤ)⟩,
      ⟨2053, (-406103930 : ℤ)⟩,
      ⟨2054, (-152176924536 : ℤ)⟩,
      ⟨2059, (-157184389440 : ℤ)⟩,
      ⟨2063, (-476973852 : ℤ)⟩,
      ⟨2065, (-268020480 : ℤ)⟩,
      ⟨3617, (-2523334944 : ℤ)⟩,
      ⟨3626, (-105835281888 : ℤ)⟩,
      ⟨3630, (-193013140320 : ℤ)⟩,
      ⟨3632, (-1806236893440 : ℤ)⟩,
      ⟨3633, (-3724991534502 : ℤ)⟩,
      ⟨3709, (-381925512621024 : ℤ)⟩,
      ⟨3710, (-289564401840 : ℤ)⟩,
      ⟨3720, (-328102750080 : ℤ)⟩,
      ⟨3726, (-16769682720 : ℤ)⟩,
      ⟨3734, (-8827653952 : ℤ)⟩,
      ⟨3738, (-307891584 : ℤ)⟩,
      ⟨3743, (-199318163616 : ℤ)⟩,
      ⟨3744, (-1861935828480 : ℤ)⟩,
      ⟨3745, (-6556940740 : ℤ)⟩,
      ⟨3750, (-4568760000 : ℤ)⟩,
      ⟨3752, (-1510442640 : ℤ)⟩,
      ⟨3753, (-6799865544 : ℤ)⟩,
      ⟨3754, (-9214428818772 : ℤ)⟩,
      ⟨3756, (-25608355416 : ℤ)⟩,
      ⟨3758, (-5494075132693656 : ℤ)⟩,
      ⟨3760, (-18679695040 : ℤ)⟩,
      ⟨3761, (-155245053600 : ℤ)⟩,
      ⟨3763, (-1446938494536 : ℤ)⟩,
      ⟨3764, (-408069392640 : ℤ)⟩,
      ⟨3766, (-106109550624 : ℤ)⟩,
      ⟨3768, (-460647721440 : ℤ)⟩,
      ⟨3769, (-3892660890 : ℤ)⟩,
      ⟨3770, (-376808083181140 : ℤ)⟩,
      ⟨3771, (-155657829600 : ℤ)⟩,
      ⟨3772, (-910934529760 : ℤ)⟩,
      ⟨3802, (-1104366940 : ℤ)⟩,
      ⟨3812, (-6627078136 : ℤ)⟩,
      ⟨3813, (-559580628 : ℤ)⟩,
      ⟨3815, (-1789090030 : ℤ)⟩,
      ⟨3816, (-10499212656 : ℤ)⟩,
      ⟨3817, (-945547240 : ℤ)⟩,
      ⟨3820, (-3633278400 : ℤ)⟩,
      ⟨3828, (-6886196856 : ℤ)⟩,
      ⟨4096, (-56486707200 : ℤ)⟩
    ] }

opaque cached_normalizes :
    LogLinearForm.normalize (edgeRangeFormWithMass3 generatedPrimaryTables Mass3.expectedNumerators 2700 540) =
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
    LogLinearForm.normalize (edgeRangeForm generatedPrimaryTables 2700 540) =
      expectedForm := by
  rw [edgeRangeForm_eq_withMass3, Mass3.recurrence_eq]
  exact cached_normalizes


theorem recurrence_eval_eq :
    (edgeRangeForm generatedPrimaryTables 2700 540).eval commonBits =
      expectedForm.eval commonBits :=
  LogLinearForm.eval_eq_of_normalize_eq recurrence_normalizes commonBits

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge5
