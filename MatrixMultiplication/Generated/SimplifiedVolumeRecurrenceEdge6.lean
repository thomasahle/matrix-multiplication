import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3


/-! Generated exact scalar-volume recurrence check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge6

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedForm : LogLinearForm :=
  { constantNumerator := 112421279103221760
    terms := [
      ⟨5, (42396750124284636 : ℤ)⟩,
      ⟨134, (-182334336 : ℤ)⟩,
      ⟨138, (-679511448 : ℤ)⟩,
      ⟨139, (-24432864 : ℤ)⟩,
      ⟨140, (-312705960 : ℤ)⟩,
      ⟨141, (-7690753914 : ℤ)⟩,
      ⟨142, (-4410163296 : ℤ)⟩,
      ⟨143, (-3759167412 : ℤ)⟩,
      ⟨147, (-144178776 : ℤ)⟩,
      ⟨148, (-8089146016 : ℤ)⟩,
      ⟨158, (-232531745910192 : ℤ)⟩,
      ⟨161, (-238563178898184 : ℤ)⟩,
      ⟨162, (-1813149869328 : ℤ)⟩,
      ⟨163, (-1849964262 : ℤ)⟩,
      ⟨164, (-9722363784 : ℤ)⟩,
      ⟨166, (-406856757120 : ℤ)⟩,
      ⟨167, (-67455843736 : ℤ)⟩,
      ⟨168, (-132829838400 : ℤ)⟩,
      ⟨169, (-1684545859620 : ℤ)⟩,
      ⟨170, (-7704984120 : ℤ)⟩,
      ⟨171, (-11180646216 : ℤ)⟩,
      ⟨172, (-3463732560 : ℤ)⟩,
      ⟨173, (-837973248 : ℤ)⟩,
      ⟨174, (-842817024 : ℤ)⟩,
      ⟨176, (-71381376 : ℤ)⟩,
      ⟨178, (-37123065579600 : ℤ)⟩,
      ⟨179, (-1722965932 : ℤ)⟩,
      ⟨180, (-143816539680 : ℤ)⟩,
      ⟨181, (-73110824648 : ℤ)⟩,
      ⟨185, (-83227800 : ℤ)⟩,
      ⟨186, (-83677680 : ℤ)⟩,
      ⟨232, (-309600028160 : ℤ)⟩,
      ⟨234, (-4694147640 : ℤ)⟩,
      ⟨235, (-4714208100 : ℤ)⟩,
      ⟨237, (-2295949824 : ℤ)⟩,
      ⟨240, (-97338240 : ℤ)⟩,
      ⟨2007, (-109454466492 : ℤ)⟩,
      ⟨2024, (-1118535264 : ℤ)⟩,
      ⟨2025, (-227838006900 : ℤ)⟩,
      ⟨2028, (-304201995552 : ℤ)⟩,
      ⟨2029, (-524699400 : ℤ)⟩,
      ⟨2031, (-271954962 : ℤ)⟩,
      ⟨2032, (-644603232 : ℤ)⟩,
      ⟨2038, (-107365630680 : ℤ)⟩,
      ⟨2041, (-11634189840 : ℤ)⟩,
      ⟨2043, (-1076705946 : ℤ)⟩,
      ⟨2046, (-56554083432 : ℤ)⟩,
      ⟨2047, (-57916335972 : ℤ)⟩,
      ⟨2048, (-2820978672132096 : ℤ)⟩,
      ⟨2049, (-57972922524 : ℤ)⟩,
      ⟨2050, (-56664648600 : ℤ)⟩,
      ⟨2053, (-1081976166 : ℤ)⟩,
      ⟨2055, (-11713993200 : ℤ)⟩,
      ⟨2058, (-108419267880 : ℤ)⟩,
      ⟨2064, (-654754464 : ℤ)⟩,
      ⟨2065, (-276507630 : ℤ)⟩,
      ⟨2067, (-534526200 : ℤ)⟩,
      ⟨2068, (-310202034912 : ℤ)⟩,
      ⟨2071, (-233013586316 : ℤ)⟩,
      ⟨2072, (-1145061792 : ℤ)⟩,
      ⟨2089, (-113926447684 : ℤ)⟩,
      ⟨3616, (-733281408 : ℤ)⟩,
      ⟨3622, (-17544156672 : ℤ)⟩,
      ⟨3627, (-72759288420 : ℤ)⟩,
      ⟨3632, (-2423420910080 : ℤ)⟩,
      ⟨3725, (-1675803000 : ℤ)⟩,
      ⟨3735, (-1508668121880 : ℤ)⟩,
      ⟨3736, (-722296063104 : ℤ)⟩,
      ⟨3737, (-31336389280 : ℤ)⟩,
      ⟨3738, (-2317687092 : ℤ)⟩,
      ⟨3740, (-390000745134000 : ℤ)⟩,
      ⟨3744, (-759238272 : ℤ)⟩,
      ⟨3749, (-18159316224 : ℤ)⟩,
      ⟨3752, (-145427520 : ℤ)⟩,
      ⟨3753, (-75286906380 : ℤ)⟩,
      ⟨3755, (-170189502180 : ℤ)⟩,
      ⟨3758, (-18729358995420 : ℤ)⟩,
      ⟨3760, (-727045992960 : ℤ)⟩,
      ⟨3761, (-1519170229288 : ℤ)⟩,
      ⟨3764, (-4612677210240 : ℤ)⟩,
      ⟨3768, (-106105493376 : ℤ)⟩,
      ⟨3769, (-11169212898 : ℤ)⟩,
      ⟨3770, (-15807670320 : ℤ)⟩,
      ⟨3773, (-42228484302312 : ℤ)⟩,
      ⟨3774, (-2774959159104000 : ℤ)⟩,
      ⟨3780, (-2781550631457360 : ℤ)⟩,
      ⟨3800, (-103847144800 : ℤ)⟩,
      ⟨3802, (-1864516008 : ℤ)⟩,
      ⟨3811, (-100183125924 : ℤ)⟩,
      ⟨3812, (-9007771248 : ℤ)⟩,
      ⟨3813, (-166231548 : ℤ)⟩,
      ⟨3814, (-103771922240 : ℤ)⟩,
      ⟨3815, (-322130970 : ℤ)⟩,
      ⟨3816, (-3765247200 : ℤ)⟩,
      ⟨3817, (-670936992 : ℤ)⟩,
      ⟨3820, (-9404832360 : ℤ)⟩,
      ⟨3828, (-2604387456 : ℤ)⟩,
      ⟨4096, (-12921777340416 : ℤ)⟩
    ] }

opaque cached_normalizes :
    LogLinearForm.normalize (edgeRangeFormWithMass3 generatedPrimaryTables Mass3.expectedNumerators 3240 540) =
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
    LogLinearForm.normalize (edgeRangeForm generatedPrimaryTables 3240 540) =
      expectedForm := by
  rw [edgeRangeForm_eq_withMass3, Mass3.recurrence_eq]
  exact cached_normalizes


theorem recurrence_eval_eq :
    (edgeRangeForm generatedPrimaryTables 3240 540).eval commonBits =
      expectedForm.eval commonBits :=
  LogLinearForm.eval_eq_of_normalize_eq recurrence_normalizes commonBits

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge6
