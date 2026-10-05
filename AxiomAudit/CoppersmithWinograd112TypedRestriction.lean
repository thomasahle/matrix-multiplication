/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinograd112TypedRestriction

/-! # Axiom audit for the raw `(1,1,2)` cell addressed as the `112` C-tensor partition

The block dictionary and its four address values, the cell of the raw square and its exact
four-address support, the blockwise coordinate maps and their basis values, the four constituent
identities, and the resulting letter-level restriction. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cw112RawDict
#assert_axioms AlgebraicComplexity.Examples.cw112RawDict_110_002
#assert_axioms AlgebraicComplexity.Examples.cw112RawDict_002_110
#assert_axioms AlgebraicComplexity.Examples.cw112RawDict_011_101
#assert_axioms AlgebraicComplexity.Examples.cw112RawDict_101_011
#assert_axioms AlgebraicComplexity.Examples.cw112RawCellKeep
#assert_axioms AlgebraicComplexity.Examples.cw112RawCellKeepDecidable
#assert_axioms AlgebraicComplexity.Examples.cw112RawCellSupport
#assert_axioms AlgebraicComplexity.Examples.mem_cwSquareRawPower_support_iff
#assert_axioms AlgebraicComplexity.Examples.mem_cwSquareRawPower_support_of
#assert_axioms AlgebraicComplexity.Examples.cw112RawCell_support
#assert_axioms AlgebraicComplexity.Examples.cw112RawBlockMap
#assert_axioms AlgebraicComplexity.Examples.cw112RawBlockMap_X_middle_zero
#assert_axioms AlgebraicComplexity.Examples.cw112RawBlockMap_X_zero_middle
#assert_axioms AlgebraicComplexity.Examples.cw112RawBlockMap_Y_middle_zero
#assert_axioms AlgebraicComplexity.Examples.cw112RawBlockMap_Y_zero_middle
#assert_axioms AlgebraicComplexity.Examples.cw112RawBlockMap_Z_zero_last
#assert_axioms AlgebraicComplexity.Examples.cw112RawBlockMap_Z_last_zero
#assert_axioms AlgebraicComplexity.Examples.cw112RawBlockMap_Z_middle_middle
#assert_axioms AlgebraicComplexity.Examples.map_cw112RawBlockMap_raw110002
#assert_axioms AlgebraicComplexity.Examples.map_cw112RawBlockMap_raw002110
#assert_axioms AlgebraicComplexity.Examples.map_cw112RawBlockMap_raw011101
#assert_axioms AlgebraicComplexity.Examples.map_cw112RawBlockMap_raw101011
#assert_axioms AlgebraicComplexity.Examples.map_blockInclude_pure_congr
#assert_axioms AlgebraicComplexity.Examples.map_cw112RawBlockMap_constituent
#assert_axioms AlgebraicComplexity.Examples.cw112BlockSupport_eq_image
#assert_axioms AlgebraicComplexity.Examples.cw112RawDict_injOn
#assert_axioms AlgebraicComplexity.Examples.cw112RawCell_restricts_partitioned
