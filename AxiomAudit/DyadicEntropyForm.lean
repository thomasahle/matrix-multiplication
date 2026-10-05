/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AxiomAudit.DyadicEntropyFormDefs
import AxiomAudit.DyadicEntropyFormEval
import AxiomAudit.DyadicEntropyFormZeros
import MatrixMultiplication.DyadicEntropyForm

/-!
# Enforcing audit for dyadic entropy forms

These assertions cover both the zero-padding preprocessing law used by compact generated
certificates and the real-evaluation laws for exact entropy forms.
The imported leaf audits additionally cover every definition and theorem in the
definition-preserving split.  This umbrella retains its existing assertions as composition checks;
the refactor introduces no new mathematical claim.
-/

set_option autoImplicit false

#assert_axioms MatrixMultiplication.DyadicEntropyForm.sum_dropZeros
#assert_axioms MatrixMultiplication.DyadicEntropyForm.entropyForm_dropZeros
#assert_axioms MatrixMultiplication.DyadicEntropyForm.weightedEntropyForm_dropZeros
#assert_axioms MatrixMultiplication.DyadicEntropyForm.map_weightedEntropyForm_dropZeros
#assert_axioms MatrixMultiplication.DyadicEntropyForm.sum_map_weightedEntropyForm_dropZeros
#assert_axioms MatrixMultiplication.DyadicEntropyForm.entropyTermForm_eval
#assert_axioms MatrixMultiplication.DyadicEntropyForm.entropyForm_eval
#assert_axioms MatrixMultiplication.DyadicEntropyForm.weightedEntropyForm_eval
#assert_axioms MatrixMultiplication.DyadicEntropyForm.eval_at_add_bits
#assert_axioms MatrixMultiplication.DyadicEntropyForm.rescale_eval
#assert_axioms MatrixMultiplication.DyadicEntropyForm.scaleNat_eval_add_bits
#assert_axioms MatrixMultiplication.DyadicEntropyForm.scaleNat_weightedEntropyForm_eval
