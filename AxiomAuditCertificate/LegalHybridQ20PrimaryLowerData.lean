/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.Generated.LegalHybridQ20PrimaryLowerData

set_option autoImplicit false

/-!
# Trust audit for the legal-hybrid q20 narrow lower-data aggregate

This companion audits the six aliases to the pre-existing lower primary chunk families used in
`better_bound/paper.tex:2057-2075`. Their payload leaves retain their existing audit companions.
-/

#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower.pos3AChunks
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower.pos3AlphaChunks
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower.edgeZero2Chunks
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower.zero3Chunks
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower.zero4Chunks
#assert_axioms MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower.muChunks
