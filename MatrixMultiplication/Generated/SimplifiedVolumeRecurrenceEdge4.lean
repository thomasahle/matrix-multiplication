import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceMass3


/-! Generated exact scalar-volume recurrence check; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge4

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedForm : LogLinearForm :=
  { constantNumerator := 111582339431989248
    terms := [
      ⟨5, (41644804052235010 : ℤ)⟩,
      ⟨134, (-29490720 : ℤ)⟩,
      ⟨138, (-52724042916 : ℤ)⟩,
      ⟨139, (-822835520 : ℤ)⟩,
      ⟨140, (-1029364840 : ℤ)⟩,
      ⟨141, (-202042566 : ℤ)⟩,
      ⟨142, (-23212274382 : ℤ)⟩,
      ⟨143, (-71215023451 : ℤ)⟩,
      ⟨144, (-32445414144 : ℤ)⟩,
      ⟨145, (-40917177930 : ℤ)⟩,
      ⟨146, (-24573462356 : ℤ)⟩,
      ⟨147, (-1234174368 : ℤ)⟩,
      ⟨148, (-1221510304 : ℤ)⟩,
      ⟨162, (-26029733393088 : ℤ)⟩,
      ⟨163, (-25896872087136 : ℤ)⟩,
      ⟨166, (-184128257598616 : ℤ)⟩,
      ⟨167, (-91856211606416 : ℤ)⟩,
      ⟨168, (-799279488 : ℤ)⟩,
      ⟨169, (-92867509187596 : ℤ)⟩,
      ⟨170, (-93408778774520 : ℤ)⟩,
      ⟨171, (-2959401924 : ℤ)⟩,
      ⟨172, (-1363147472 : ℤ)⟩,
      ⟨174, (-11698057584 : ℤ)⟩,
      ⟨175, (-63171441200 : ℤ)⟩,
      ⟨176, (-67800620800 : ℤ)⟩,
      ⟨177, (-30642823038 : ℤ)⟩,
      ⟨178, (-30815946332 : ℤ)⟩,
      ⟨184, (-690110875456 : ℤ)⟩,
      ⟨185, (-4568760 : ℤ)⟩,
      ⟨186, (-4593456 : ℤ)⟩,
      ⟨232, (-193705199792 : ℤ)⟩,
      ⟨233, (-39079191982 : ℤ)⟩,
      ⟨2047, (-163737974280 : ℤ)⟩,
      ⟨2048, (-2951604162396160 : ℤ)⟩,
      ⟨2049, (-163897952760 : ℤ)⟩,
      ⟨3631, (-608998051874 : ℤ)⟩,
      ⟨3632, (-1211661263232 : ℤ)⟩,
      ⟨3725, (-91992600 : ℤ)⟩,
      ⟨3728, (-6991123216576 : ℤ)⟩,
      ⟨3741, (-647654242854 : ℤ)⟩,
      ⟨3744, (-45398126592 : ℤ)⟩,
      ⟨3745, (-1351868841680 : ℤ)⟩,
      ⟨3748, (-125989424784 : ℤ)⟩,
      ⟨3752, (-490311360 : ℤ)⟩,
      ⟨3753, (-28762676748 : ℤ)⟩,
      ⟨3754, (-17862523056 : ℤ)⟩,
      ⟨3755, (-473130000 : ℤ)⟩,
      ⟨3757, (-2064333537534892 : ℤ)⟩,
      ⟨3758, (-91338430512 : ℤ)⟩,
      ⟨3760, (-8944318080 : ℤ)⟩,
      ⟨3762, (-876706027956 : ℤ)⟩,
      ⟨3763, (-2068036087577236 : ℤ)⟩,
      ⟨3764, (-1053233561021328 : ℤ)⟩,
      ⟨3771, (-599123341353312 : ℤ)⟩,
      ⟨3772, (-3396404518272 : ℤ)⟩,
      ⟨3801, (-31371355848 : ℤ)⟩,
      ⟨3802, (-270504696 : ℤ)⟩,
      ⟨3805, (-640424823730 : ℤ)⟩,
      ⟨3807, (-433526114736 : ℤ)⟩,
      ⟨3808, (-212180480512 : ℤ)⟩,
      ⟨3810, (-641266380660 : ℤ)⟩,
      ⟨3811, (-615035891235 : ℤ)⟩,
      ⟨3812, (-3968932416 : ℤ)⟩,
      ⟨3815, (-5466612690 : ℤ)⟩,
      ⟨3817, (-22595418560 : ℤ)⟩,
      ⟨3820, (-729731318620 : ℤ)⟩,
      ⟨3828, (-421233120 : ℤ)⟩,
      ⟨4096, (-27560789417984 : ℤ)⟩
    ] }

opaque cached_normalizes :
    LogLinearForm.normalize (edgeRangeFormWithMass3 generatedPrimaryTables Mass3.expectedNumerators 2160 540) =
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
    LogLinearForm.normalize (edgeRangeForm generatedPrimaryTables 2160 540) =
      expectedForm := by
  rw [edgeRangeForm_eq_withMass3, Mass3.recurrence_eq]
  exact cached_normalizes


theorem recurrence_eval_eq :
    (edgeRangeForm generatedPrimaryTables 2160 540).eval commonBits =
      expectedForm.eval commonBits :=
  LogLinearForm.eval_eq_of_normalize_eq recurrence_normalizes commonBits

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.Edge4
