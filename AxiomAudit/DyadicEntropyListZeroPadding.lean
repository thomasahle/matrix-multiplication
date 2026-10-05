/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.DyadicEntropyListZeroPadding

/-! Focused trust audit for zero-padding invariance of serialized dyadic entropy. -/

#assert_axioms MatrixMultiplication.DyadicEntropyForm.weightedEntropyList_append_replicate_zero
