/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.TotalQuotientCompleteSplitRecurrence

/-!
# Trust audit for the total-weight complete-split recurrence

These declarations connect the executable level-two quotient used by the certificate recurrence
to the tensor library's total-weight map.  Auditing the connection prevents a generated table from
silently replacing the mathematical quotient.

The audited module's import closure reaches the generated `Generated.SimplifiedVolume*` primary
tables through `SimplifiedVolumeReconstruction`, so these checks live in the opt-in certificate
audit target rather than the ordinary focused one.
-/

#assert_axioms MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.cwSplitWordTotalDigit_source_val
#assert_axioms MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot_eq_zero
#assert_axioms MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlots_totalOne
#assert_axioms MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlots_totalTwo
#assert_axioms MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlots_totalThree
