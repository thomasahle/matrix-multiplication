import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3


/-! Generated exact scalar-volume recurrence check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.ZeroThree2

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedForm : LogLinearForm :=
  { constantNumerator := 55284269278298112
    terms := [
      ⟨5, (13975074109390848 : ℤ)⟩,
      ⟨6, (-22656892010496 : ℤ)⟩,
      ⟨16, (-4831838208 : ℤ)⟩,
      ⟨17, (-8556380160 : ℤ)⟩,
      ⟨18, (-10871635968 : ℤ)⟩,
      ⟨20, (-8053063680 : ℤ)⟩,
      ⟨29, (-2267272970240 : ℤ)⟩,
      ⟨31, (-2250965516288 : ℤ)⟩,
      ⟨40, (-50691351511040 : ℤ)⟩,
      ⟨42, (-53750173532160 : ℤ)⟩,
      ⟨44, (-56035096133632 : ℤ)⟩,
      ⟨106, (-42681237504 : ℤ)⟩,
      ⟨116, (-46707769344 : ℤ)⟩,
      ⟨119, (-175499343036416 : ℤ)⟩,
      ⟨120, (-48318382080 : ℤ)⟩,
      ⟨121, (-189240621137920 : ℤ)⟩,
      ⟨127, (-143304922497024 : ℤ)⟩,
      ⟨128, (-633488348807168 : ℤ)⟩,
      ⟨133, (-40164655104 : ℤ)⟩,
      ⟨134, (-13488881664 : ℤ)⟩,
      ⟨135, (-95126814720 : ℤ)⟩,
      ⟨136, (-68451041280 : ℤ)⟩,
      ⟨145, (-58384711680 : ℤ)⟩,
      ⟨148, (-59592671232 : ℤ)⟩,
      ⟨643, (-25135457239040 : ℤ)⟩,
      ⟨654, (-23744055607296 : ℤ)⟩,
      ⟨666, (-48359452704768 : ℤ)⟩,
      ⟨673, (-26308184637440 : ℤ)⟩,
      ⟨674, (-26347275550720 : ℤ)⟩,
      ⟨896, (-573335184343040 : ℤ)⟩,
      ⟨900, (-570277704499200 : ℤ)⟩,
      ⟨1024, (-26594437496832 : ℤ)⟩,
      ⟨2395, (-241088593920 : ℤ)⟩,
      ⟨2423, (-243907166208 : ℤ)⟩,
      ⟨2451, (-246725738496 : ℤ)⟩,
      ⟨2555, (-998987163238400 : ℤ)⟩,
      ⟨2562, (-944599405166592 : ℤ)⟩,
      ⟨4096, (-9002251452416 : ℤ)⟩
    ] }

opaque cached_normalizes :
    LogLinearForm.normalize (zeroThreeRangeFormWithMass3 generatedPrimaryTables Mass3.expectedNumerators 180 90) =
      expectedForm := by
  unfold generatedPrimaryTables zero3Chunks
  rw [Zero3Data0.data_eq_rawData]
  decide +kernel

opaque recurrence_normalizes :
    LogLinearForm.normalize (zeroThreeRangeForm generatedPrimaryTables 180 90) =
      expectedForm := by
  rw [zeroThreeRangeForm_eq_withMass3, Mass3.recurrence_eq]
  exact cached_normalizes


theorem recurrence_eval_eq :
    (zeroThreeRangeForm generatedPrimaryTables 180 90).eval commonBits =
      expectedForm.eval commonBits :=
  LogLinearForm.eval_eq_of_normalize_eq recurrence_normalizes commonBits

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.ZeroThree2
