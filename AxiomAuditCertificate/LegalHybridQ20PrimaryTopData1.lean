/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.Generated.LegalHybridQ20PrimaryTopData1

set_option autoImplicit false

/-!
# Trust audit for legal-hybrid q20 top chunk one

This companion covers every declaration in the second bounded source-image leaf for the q20 top
law of the candidate described in `better_bound/paper.tex:148-159` (draft status). It asserts no
semantic or endpoint theorem.
The surrounding recursive framework is described in [duan2023faster] and [alman2025more].
-/

#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.DataBlock0.data
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.DataBlock0.data_isValid
#assert_axioms
  MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.DataBlock0.valueCount_eq
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.DataBlock0.total_eq
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.DataBlock1.data
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.DataBlock1.data_isValid
#assert_axioms
  MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.DataBlock1.valueCount_eq
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.DataBlock1.total_eq
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.DataBlock2.data
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.DataBlock2.data_isValid
#assert_axioms
  MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.DataBlock2.valueCount_eq
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.DataBlock2.total_eq
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.DataBlock3.data
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.DataBlock3.data_isValid
#assert_axioms
  MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.DataBlock3.valueCount_eq
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.DataBlock3.total_eq
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.rawData
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.rawData_isValid
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.rawData_valueCount
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.rawData_total
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.checked
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.data
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.data_isValid
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.valueCount_eq
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.total_eq
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.data_eq_rawData
