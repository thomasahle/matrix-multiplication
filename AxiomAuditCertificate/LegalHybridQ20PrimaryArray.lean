/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.Generated.LegalHybridQ20PrimaryArray

set_option autoImplicit false

/-!
# Trust audit for the legal-hybrid q20 exact-array boundary

This companion audits the lightweight structural helper used to assemble the bounded q20 top-law
blocks for the candidate described in `better_bound/paper.tex:148-159` (draft status).
It contains no certificate payload or endpoint.
The surrounding recursive framework is described in [duan2023faster] and [alman2025more].
-/

#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.ArrayCore.concatArrays
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.ArrayCore.concatArrays_toList
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.ArrayCore.concatArrays_size
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.ArrayCore.concatArrays_sum
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.ArrayCore.all_append
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.ArrayCore.all_mono
#assert_axioms
  MatrixMultiplication.Generated.LegalHybridQ20Primary.ArrayCore.strictlyIncreasing_append_of_cut
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.ArrayCore.appendMassChunk
#assert_axioms
  MatrixMultiplication.Generated.LegalHybridQ20Primary.ArrayCore.appendMassChunk_isValid
#assert_axioms
  MatrixMultiplication.Generated.LegalHybridQ20Primary.ArrayCore.appendMassChunk_valueCount
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.ArrayCore.appendMassChunk_total
