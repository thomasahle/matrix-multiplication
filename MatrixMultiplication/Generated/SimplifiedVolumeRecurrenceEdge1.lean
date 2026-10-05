import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3


/-! Generated exact scalar-volume recurrence check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge1

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedForm : LogLinearForm :=
  { constantNumerator := 83845324381519872
    terms := [
      ⟨5, (24857602292004240 : ℤ)⟩,
      ⟨134, (-580835328 : ℤ)⟩,
      ⟨140, (-1094971920 : ℤ)⟩,
      ⟨141, (-553690080 : ℤ)⟩,
      ⟨142, (-1092248664 : ℤ)⟩,
      ⟨144, (-97073702208 : ℤ)⟩,
      ⟨160, (-436047185710080 : ℤ)⟩,
      ⟨162, (-73738143936 : ℤ)⟩,
      ⟨163, (-225305772 : ℤ)⟩,
      ⟨164, (-226688016 : ℤ)⟩,
      ⟨170, (-11491901581560 : ℤ)⟩,
      ⟨171, (-33995818476 : ℤ)⟩,
      ⟨231, (-372603680064 : ℤ)⟩,
      ⟨232, (-374216683008 : ℤ)⟩,
      ⟨239, (-201785310 : ℤ)⟩,
      ⟨240, (-453817440 : ℤ)⟩,
      ⟨2012, (-10742462352 : ℤ)⟩,
      ⟨2032, (-116750592 : ℤ)⟩,
      ⟨2033, (-296362608 : ℤ)⟩,
      ⟨2041, (-61476732408 : ℤ)⟩,
      ⟨2043, (-15983524908 : ℤ)⟩,
      ⟨2046, (-29305561824 : ℤ)⟩,
      ⟨2047, (-87670868838 : ℤ)⟩,
      ⟨2048, (-1247238593519616 : ℤ)⟩,
      ⟨2049, (-87756526746 : ℤ)⟩,
      ⟨2050, (-29362855200 : ℤ)⟩,
      ⟨2053, (-16061760468 : ℤ)⟩,
      ⟨2055, (-61898424840 : ℤ)⟩,
      ⟨2063, (-300735888 : ℤ)⟩,
      ⟨2064, (-118589184 : ℤ)⟩,
      ⟨2084, (-11126884464 : ℤ)⟩,
      ⟨3616, (-1892281728 : ℤ)⟩,
      ⟨3617, (-3053796930 : ℤ)⟩,
      ⟨3633, (-5860039695552 : ℤ)⟩,
      ⟨3754, (-247928605392 : ℤ)⟩,
      ⟨3755, (-250527066300 : ℤ)⟩,
      ⟨3756, (-126826415873424 : ℤ)⟩,
      ⟨3769, (-5209677636 : ℤ)⟩,
      ⟨3772, (-858457651008 : ℤ)⟩,
      ⟨3776, (-5145356791378944 : ℤ)⟩,
      ⟨3808, (-1283530062528 : ℤ)⟩,
      ⟨3812, (-14660746152 : ℤ)⟩,
      ⟨3815, (-14981047200 : ℤ)⟩,
      ⟨3816, (-7430415984 : ℤ)⟩,
      ⟨3828, (-8296409088 : ℤ)⟩,
      ⟨4096, (-10225194196992 : ℤ)⟩
    ] }

opaque cached_normalizes :
    LogLinearForm.normalize (edgeRangeFormWithMass3 generatedPrimaryTables Mass3.expectedNumerators 540 540) =
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
    LogLinearForm.normalize (edgeRangeForm generatedPrimaryTables 540 540) =
      expectedForm := by
  rw [edgeRangeForm_eq_withMass3, Mass3.recurrence_eq]
  exact cached_normalizes


theorem recurrence_eval_eq :
    (edgeRangeForm generatedPrimaryTables 540 540).eval commonBits =
      expectedForm.eval commonBits :=
  LogLinearForm.eval_eq_of_normalize_eq recurrence_normalizes commonBits

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge1
