import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3


/-! Generated exact scalar-volume recurrence check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.ZeroThree0

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedForm : LogLinearForm :=
  { constantNumerator := 36879269263048704
    terms := [
      ⟨5, (8996931464331264 : ℤ)⟩,
      ⟨6, (-4632524881920 : ℤ)⟩,
      ⟨17, (-1711276032 : ℤ)⟩,
      ⟨18, (-1811939328 : ℤ)⟩,
      ⟨19, (-7650410496 : ℤ)⟩,
      ⟨25, (-939524096000 : ℤ)⟩,
      ⟨26, (-977105059840 : ℤ)⟩,
      ⟨31, (-2278010388480 : ℤ)⟩,
      ⟨37, (-23305700507648 : ℤ)⟩,
      ⟨38, (-47871168610304 : ℤ)⟩,
      ⟨39, (-24240929636352 : ℤ)⟩,
      ⟨40, (-24862491934720 : ℤ)⟩,
      ⟨53, (-32942801813504 : ℤ)⟩,
      ⟨119, (-183756820316160 : ℤ)⟩,
      ⟨122, (-49123688448 : ℤ)⟩,
      ⟨126, (-389132090081280 : ℤ)⟩,
      ⟨136, (-54760833024 : ℤ)⟩,
      ⟨137, (-55163486208 : ℤ)⟩,
      ⟨553, (-20782273003520 : ℤ)⟩,
      ⟨604, (-22192230236160 : ℤ)⟩,
      ⟨605, (-22228972339200 : ℤ)⟩,
      ⟨722, (-54266911784960 : ℤ)⟩,
      ⟨777, (-28548614062080 : ℤ)⟩,
      ⟨892, (-554433570144256 : ℤ)⟩,
      ⟨911, (-573824139526144 : ℤ)⟩,
      ⟨1021, (-10431888359424 : ℤ)⟩,
      ⟨1024, (-25632364822528 : ℤ)⟩,
      ⟨1033, (-3518165417984 : ℤ)⟩,
      ⟨2405, (-242095226880 : ℤ)⟩,
      ⟨2580, (-995992849612800 : ℤ)⟩,
      ⟨4096, (-18348100288512 : ℤ)⟩
    ] }

opaque cached_normalizes :
    LogLinearForm.normalize (zeroThreeRangeFormWithMass3 generatedPrimaryTables Mass3.expectedNumerators 0 90) =
      expectedForm := by
  unfold generatedPrimaryTables zero3Chunks
  rw [Zero3Data0.data_eq_rawData]
  decide +kernel

opaque recurrence_normalizes :
    LogLinearForm.normalize (zeroThreeRangeForm generatedPrimaryTables 0 90) =
      expectedForm := by
  rw [zeroThreeRangeForm_eq_withMass3, Mass3.recurrence_eq]
  exact cached_normalizes


theorem recurrence_eval_eq :
    (zeroThreeRangeForm generatedPrimaryTables 0 90).eval commonBits =
      expectedForm.eval commonBits :=
  LogLinearForm.eval_eq_of_normalize_eq recurrence_normalizes commonBits

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.ZeroThree0
