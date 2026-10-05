import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3


/-! Generated exact scalar-volume recurrence check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge11

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedForm : LogLinearForm :=
  { constantNumerator := 84976145026301952
    terms := [
      ⟨5, (25039215345519714 : ℤ)⟩,
      ⟨134, (-15285648 : ℤ)⟩,
      ⟨138, (-1475194608 : ℤ)⟩,
      ⟨139, (-48134310 : ℤ)⟩,
      ⟨140, (-673674960 : ℤ)⟩,
      ⟨141, (-109787958 : ℤ)⟩,
      ⟨142, (-48741621126 : ℤ)⟩,
      ⟨143, (-49004932119 : ℤ)⟩,
      ⟨147, (-1522240272 : ℤ)⟩,
      ⟨151, (-51912854136 : ℤ)⟩,
      ⟨152, (-52256647872 : ℤ)⟩,
      ⟨160, (-32088598080 : ℤ)⟩,
      ⟨161, (-46555785007788 : ℤ)⟩,
      ⟨162, (-46879000216452 : ℤ)⟩,
      ⟨163, (-1946673792 : ℤ)⟩,
      ⟨164, (-4132800 : ℤ)⟩,
      ⟨165, (-165177714240 : ℤ)⟩,
      ⟨168, (-58160579904 : ℤ)⟩,
      ⟨169, (-417790936680 : ℤ)⟩,
      ⟨170, (-1345690080 : ℤ)⟩,
      ⟨171, (-304660440 : ℤ)⟩,
      ⟨172, (-59598000 : ℤ)⟩,
      ⟨176, (-361527936 : ℤ)⟩,
      ⟨179, (-137038104 : ℤ)⟩,
      ⟨186, (-413987419450872 : ℤ)⟩,
      ⟨189, (-310765492296 : ℤ)⟩,
      ⟨192, (-58363764480 : ℤ)⟩,
      ⟨193, (-58667742420 : ℤ)⟩,
      ⟨240, (-13809600 : ℤ)⟩,
      ⟨241, (-13867140 : ℤ)⟩,
      ⟨2008, (-7040158440 : ℤ)⟩,
      ⟨2010, (-8456604660 : ℤ)⟩,
      ⟨2030, (-66211147464000 : ℤ)⟩,
      ⟨2032, (-99852480 : ℤ)⟩,
      ⟨2033, (-293520474 : ℤ)⟩,
      ⟨2038, (-9370365312 : ℤ)⟩,
      ⟨2040, (-5128462080 : ℤ)⟩,
      ⟨2041, (-6546417696 : ℤ)⟩,
      ⟨2042, (-3229529184 : ℤ)⟩,
      ⟨2043, (-146544390 : ℤ)⟩,
      ⟨2046, (-385716790429344 : ℤ)⟩,
      ⟨2047, (-66779961377766 : ℤ)⟩,
      ⟨2048, (-272685845839872 : ℤ)⟩,
      ⟨2049, (-66845208042522 : ℤ)⟩,
      ⟨2050, (-386470879951200 : ℤ)⟩,
      ⟨2053, (-147261690 : ℤ)⟩,
      ⟨2054, (-3248507808 : ℤ)⟩,
      ⟨2055, (-6591322080 : ℤ)⟩,
      ⟨2056, (-5168685312 : ℤ)⟩,
      ⟨2058, (-9462321792 : ℤ)⟩,
      ⟨2063, (-297851814 : ℤ)⟩,
      ⟨2064, (-101424960 : ℤ)⟩,
      ⟨2066, (-67385335300800 : ℤ)⟩,
      ⟨2086, (-8776356876 : ℤ)⟩,
      ⟨2088, (-7320642840 : ℤ)⟩,
      ⟨3615, (-208007100 : ℤ)⟩,
      ⟨3711, (-1128062135340 : ℤ)⟩,
      ⟨3718, (-3056682805176 : ℤ)⟩,
      ⟨3724, (-4144325672137224 : ℤ)⟩,
      ⟨3738, (-1430861544 : ℤ)⟩,
      ⟨3744, (-3845342592 : ℤ)⟩,
      ⟨3752, (-650034000 : ℤ)⟩,
      ⟨3755, (-6690058200 : ℤ)⟩,
      ⟨3756, (-11519997552 : ℤ)⟩,
      ⟨3758, (-3998595577920 : ℤ)⟩,
      ⟨3759, (-1293438971160 : ℤ)⟩,
      ⟨3760, (-3953053440 : ℤ)⟩,
      ⟨3766, (-1885028096448 : ℤ)⟩,
      ⟨3769, (-94978800 : ℤ)⟩,
      ⟨3770, (-22464645840 : ℤ)⟩,
      ⟨3772, (-1164756219480 : ℤ)⟩,
      ⟨3773, (-1089487572552918 : ℤ)⟩,
      ⟨3774, (-390322938348 : ℤ)⟩,
      ⟨3775, (-757090360950 : ℤ)⟩,
      ⟨3793, (-1304009640648 : ℤ)⟩,
      ⟨3802, (-19685569776 : ℤ)⟩,
      ⟨3811, (-1305998575563 : ℤ)⟩,
      ⟨3812, (-241436832 : ℤ)⟩,
      ⟨3813, (-1648542924 : ℤ)⟩,
      ⟨3815, (-1321096350 : ℤ)⟩,
      ⟨3816, (-7859784672 : ℤ)⟩,
      ⟨3817, (-1321788930 : ℤ)⟩,
      ⟨3820, (-20417548560 : ℤ)⟩,
      ⟨3828, (-218333808 : ℤ)⟩,
      ⟨4096, (-10234856656896 : ℤ)⟩
    ] }

opaque cached_normalizes :
    LogLinearForm.normalize (edgeRangeFormWithMass3 generatedPrimaryTables Mass3.expectedNumerators 5940 540) =
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
    LogLinearForm.normalize (edgeRangeForm generatedPrimaryTables 5940 540) =
      expectedForm := by
  rw [edgeRangeForm_eq_withMass3, Mass3.recurrence_eq]
  exact cached_normalizes


theorem recurrence_eval_eq :
    (edgeRangeForm generatedPrimaryTables 5940 540).eval commonBits =
      expectedForm.eval commonBits :=
  LogLinearForm.eval_eq_of_normalize_eq recurrence_normalizes commonBits

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge11
