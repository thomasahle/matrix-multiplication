import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceEdge0
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceEdge1
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceEdge2
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceEdge3
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceEdge4
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceEdge5
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceEdge6
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceEdge7
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceEdge8
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceEdge9
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceEdge10
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceEdge11
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceEdge12
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceEdge13
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceZeroThree0
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceZeroThree1
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceZeroThree2
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceZeroFour0
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceZeroFour1
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceZeroFour2
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceZeroFour3
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceZeroFour4
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceZeroFour5

/-! # Checked semantic scalar-volume recurrence -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedChunkForms : List LogLinearForm :=
  [Edge0.expectedForm,
    Edge1.expectedForm,
    Edge2.expectedForm,
    Edge3.expectedForm,
    Edge4.expectedForm,
    Edge5.expectedForm,
    Edge6.expectedForm,
    Edge7.expectedForm,
    Edge8.expectedForm,
    Edge9.expectedForm,
    Edge10.expectedForm,
    Edge11.expectedForm,
    Edge12.expectedForm,
    Edge13.expectedForm,
    ZeroThree0.expectedForm,
    ZeroThree1.expectedForm,
    ZeroThree2.expectedForm,
    ZeroFour0.expectedForm,
    ZeroFour1.expectedForm,
    ZeroFour2.expectedForm,
    ZeroFour3.expectedForm,
    ZeroFour4.expectedForm,
    ZeroFour5.expectedForm]

opaque expected_chunks_normalize :
    LogLinearForm.normalize (LogLinearForm.sum expectedChunkForms) =
      LogLinearForm.normalize scalarExpectedForm := by
  decide

theorem reconstructedScalarCoordinateSum_eq_scalarCoordinateSum :
    reconstructedScalarCoordinateSum =
      MatrixMultiplication.Generated.SimplifiedVolumeScalar.scalarCoordinateSum := by
  unfold reconstructedScalarCoordinateSum scalarRecurrenceForm scalarRecurrenceFormFrom
  rw [LogLinearForm.eval_sum]
  have hchunks :
      (scalarRecurrenceChunks generatedPrimaryTables).map
          (LogLinearForm.eval commonBits) =
        expectedChunkForms.map (LogLinearForm.eval commonBits) := by
    simp only [scalarRecurrenceChunks, expectedChunkForms, List.map_cons, List.map_nil]
    rw [Edge0.recurrence_eval_eq, Edge1.recurrence_eval_eq, Edge2.recurrence_eval_eq, Edge3.recurrence_eval_eq, Edge4.recurrence_eval_eq, Edge5.recurrence_eval_eq, Edge6.recurrence_eval_eq, Edge7.recurrence_eval_eq, Edge8.recurrence_eval_eq, Edge9.recurrence_eval_eq, Edge10.recurrence_eval_eq, Edge11.recurrence_eval_eq, Edge12.recurrence_eval_eq, Edge13.recurrence_eval_eq, ZeroThree0.recurrence_eval_eq, ZeroThree1.recurrence_eval_eq, ZeroThree2.recurrence_eval_eq, ZeroFour0.recurrence_eval_eq, ZeroFour1.recurrence_eval_eq, ZeroFour2.recurrence_eval_eq, ZeroFour3.recurrence_eval_eq, ZeroFour4.recurrence_eval_eq, ZeroFour5.recurrence_eval_eq]
  rw [hchunks, ← LogLinearForm.eval_sum]
  exact (LogLinearForm.eval_eq_of_normalize_eq expected_chunks_normalize commonBits).trans
    scalarExpectedForm_eval

def reconstructedThreeCoordinateMean : ℝ :=
  reconstructedScalarCoordinateSum / 3

/-- Strongest directed rational lower supplied by the sealed scalar log chunks. -/
def reconstructedThreeCoordinateMeanLower : ℝ :=
  MatrixMultiplication.Generated.SimplifiedVolumeScalar.scalarCoordinateSumLower / 3

theorem reconstructedThreeCoordinateMeanLower_le_reconstructedThreeCoordinateMean :
    reconstructedThreeCoordinateMeanLower ≤ reconstructedThreeCoordinateMean := by
  have h :=
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.scalarCoordinateSumLower_le
  rw [← reconstructedScalarCoordinateSum_eq_scalarCoordinateSum] at h
  unfold reconstructedThreeCoordinateMeanLower reconstructedThreeCoordinateMean
  linarith

theorem volumeFloor_lt_reconstructedThreeCoordinateMean :
    (60167 / 10000 : ℝ) < reconstructedThreeCoordinateMean := by
  have h :=
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.three_mul_volumeFloor_lt_scalarCoordinateSum
  rw [← reconstructedScalarCoordinateSum_eq_scalarCoordinateSum] at h
  unfold reconstructedThreeCoordinateMean
  linarith

/-- Tight decimal floor used by the strongest current rigorously certified endpoint. -/
theorem certifiedVolumeFloor_lt_reconstructedThreeCoordinateMean :
    (6016717904289 / 1000000000000 : ℝ) < reconstructedThreeCoordinateMean := by
  apply lt_of_lt_of_le (b := reconstructedThreeCoordinateMeanLower) ?_
    reconstructedThreeCoordinateMeanLower_le_reconstructedThreeCoordinateMean
  norm_num [reconstructedThreeCoordinateMeanLower,
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.scalarCoordinateSumLower,
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.negativeCeilingSum,
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.bits,
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.constantNumerator,
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.Positive.floor,
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative0.ceiling,
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative1.ceiling,
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative2.ceiling,
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative3.ceiling,
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative4.ceiling,
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative5.ceiling,
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative6.ceiling,
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative7.ceiling,
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative8.ceiling,
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative9.ceiling,
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative10.ceiling,
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative11.ceiling,
    MatrixMultiplication.DyadicEntropy.mass]

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence
