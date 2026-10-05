/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.SignedDyadicLogStreaming

/-!
# Axiom audit for streaming dyadic-log forms

These checks cover the executable accumulator, its syntactic checkpoint calculus, and the bridge
showing that bounded streaming preserves the real value of the ordinary form sum.
-/

#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.streamStep
#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.streamFoldFrom
#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.streamFold
#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.streamFoldFrom_nil
#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.streamFoldFrom_cons
#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.streamFoldFrom_append
#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.streamFoldFrom_append_of_checkpoint
#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.streamFold_append
#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.eval_streamStep
#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.eval_streamFoldFrom
#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.eval_streamFold
