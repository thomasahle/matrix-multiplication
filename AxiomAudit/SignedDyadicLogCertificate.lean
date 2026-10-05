/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.SignedDyadicLogCertificate

/-!
# Enforcing audit for compositional signed-dyadic-log certificates

These assertions cover the generic exact-form reassembly laws used by generated certificate
checkers.  In particular, independent bounded normalization of term shards is transported through
real evaluation without trusting the external certificate producer.
-/

#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.ext
#assert_axioms
  MatrixMultiplication.SignedDyadicLogForm.Form.sum_constantNumerator
#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.sum_terms
#assert_axioms
  MatrixMultiplication.SignedDyadicLogCertificate.LowerBound.sum_lower_le_eval_sum_of_forall₂
