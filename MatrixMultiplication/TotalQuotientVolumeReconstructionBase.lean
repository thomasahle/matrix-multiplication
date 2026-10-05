import MatrixMultiplication.TotalQuotientPrimaryTables
import MatrixMultiplication.Generated.TotalQuotientVolumeScalarData

/-!
# Exact recurrence boundary for the total-weight quotient volume certificate

This module binds the reusable level-four volume recurrence to the primary tables and compact
logarithmic scalar certificate generated from certificate SHA-256
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.

It intentionally contains no large kernel reductions.  The generated recurrence chunks import
this boundary, prove their exact integer normalizations independently, and are assembled by
`TotalQuotientVolumeReconstruction`.
-/

open scoped BigOperators

namespace MatrixMultiplication.TotalQuotientVolumeReconstruction

open MatrixMultiplication.SimplifiedVolumeReconstruction

noncomputable section

/-- Exact integer-log recurrence form for `M_X + M_Y + M_Z`. -/
def scalarRecurrenceForm : LogLinearForm :=
  scalarRecurrenceFormFrom primaryTables

/-- Real evaluation of the exact primary-table recurrence. -/
def reconstructedScalarCoordinateSum : ℝ :=
  scalarRecurrenceForm.eval commonBits

open MatrixMultiplication.Generated.TotalQuotientVolumeScalar

/-- Compact signed integer-log target independently exported from the same binary certificate. -/
def scalarExpectedTerms : List LogTerm :=
  positiveFamilyTerms Positive.argument Positive.coefficient ++
    negativeFamilyTerms Negative0.argument Negative0.coefficient ++
    negativeFamilyTerms Negative1.argument Negative1.coefficient ++
    negativeFamilyTerms Negative2.argument Negative2.coefficient ++
    negativeFamilyTerms Negative3.argument Negative3.coefficient ++
    negativeFamilyTerms Negative4.argument Negative4.coefficient ++
    negativeFamilyTerms Negative5.argument Negative5.coefficient ++
    negativeFamilyTerms Negative6.argument Negative6.coefficient ++
    negativeFamilyTerms Negative7.argument Negative7.coefficient ++
    negativeFamilyTerms Negative8.argument Negative8.coefficient ++
    negativeFamilyTerms Negative9.argument Negative9.coefficient ++
    negativeFamilyTerms Negative10.argument Negative10.coefficient ++
    negativeFamilyTerms Negative11.argument Negative11.coefficient ++
    negativeFamilyTerms Negative12.argument Negative12.coefficient ++
    negativeFamilyTerms Negative13.argument Negative13.coefficient ++
    negativeFamilyTerms Negative14.argument Negative14.coefficient

def scalarExpectedForm : LogLinearForm :=
  ⟨MatrixMultiplication.Generated.TotalQuotientVolumeScalar.constantNumerator,
    scalarExpectedTerms⟩

/-- The compact target form evaluates to the separately sealed scalar-coordinate expression. -/
theorem scalarExpectedForm_eval :
    scalarExpectedForm.eval commonBits =
      MatrixMultiplication.Generated.TotalQuotientVolumeScalar.scalarCoordinateSum := by
  simp only [LogLinearForm.eval, scalarExpectedForm, scalarExpectedTerms,
    LogLinearForm.termsValue_append]
  rw [termsValue_positiveFamilyTerms]
  rw [termsValue_negativeFamilyTerms, termsValue_negativeFamilyTerms,
    termsValue_negativeFamilyTerms, termsValue_negativeFamilyTerms,
    termsValue_negativeFamilyTerms, termsValue_negativeFamilyTerms,
    termsValue_negativeFamilyTerms, termsValue_negativeFamilyTerms,
    termsValue_negativeFamilyTerms, termsValue_negativeFamilyTerms,
    termsValue_negativeFamilyTerms, termsValue_negativeFamilyTerms,
    termsValue_negativeFamilyTerms, termsValue_negativeFamilyTerms,
    termsValue_negativeFamilyTerms]
  unfold MatrixMultiplication.Generated.TotalQuotientVolumeScalar.scalarCoordinateSum
    MatrixMultiplication.Generated.TotalQuotientVolumeScalar.negativeExactSum
    Positive.exact Negative0.exact Negative1.exact Negative2.exact Negative3.exact
    Negative4.exact Negative5.exact Negative6.exact Negative7.exact Negative8.exact
    Negative9.exact Negative10.exact Negative11.exact Negative12.exact Negative13.exact
    Negative14.exact
  simp only [commonBits,
    MatrixMultiplication.Generated.TotalQuotientVolumeScalar.bits]
  ring

end

end MatrixMultiplication.TotalQuotientVolumeReconstruction
