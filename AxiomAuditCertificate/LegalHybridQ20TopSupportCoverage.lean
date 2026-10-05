/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.LegalHybridQ20TopSupportCoverage
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Audit of the actual q20 labelled child-row support

Every declaration of the q20 support checker and its active-slot corollaries is asserted here.
The ordered-child convention is [alman2025more],
`papers/sources/2404.16349/constituent.tex:41-47,115-146`; its certificate-specific application
is the input construction in `better_bound/paper.tex:1085-1124`. The checked child-index tables
are transported back to the semantic pair lookup before applying any active-slot corollary;
their proof terms do not enter the Boolean evaluation. This proves row support only,
not lower-law normalization, an assembled restriction, cleanup, repair, or an exponent endpoint.
-/

open MatrixMultiplication.LegalHybridQ20TopSupportCoverage

#assert_axioms positiveChildRowAddresses
#assert_axioms positiveChildRowAddresses_eq_pos3ARows
#assert_axioms boundaryChildRowAddresses
#assert_axioms boundaryChildRowAddresses_eq_zero3Rows
#assert_axioms topAtomPairIndex
#assert_axioms topAtomRegion
#assert_axioms ChildRowCovered
#assert_axioms childRowCoveredDecidable
#assert_axioms TopAtomRowsCovered
#assert_axioms topAtomRowsCoveredDecidable
#assert_axioms topAtomRowsCoveredCheck
#assert_axioms topAtomBlock
#assert_axioms topAtomShard
#assert_axioms topAtomShards_flatten
#assert_axioms topAtomBlock0_shard_checked
#assert_axioms topAtomBlock1_shard_checked
#assert_axioms topAtomBlock2_shard_checked
#assert_axioms topAtomBlock3_shard_checked
#assert_axioms topAtomBlock4_shard_checked
#assert_axioms topAtomBlock5_shard_checked
#assert_axioms topAtomBlock6_shard_checked
#assert_axioms topAtomBlock7_shard_checked
#assert_axioms topAtomBlock8_shard_checked
#assert_axioms topAtomBlock9_shard_checked
#assert_axioms topAtomBlock10_shard_checked
#assert_axioms topAtomBlock11_shard_checked
#assert_axioms topAtomShard_checked
#assert_axioms topSupportAtomIndices_eq_blocks
#assert_axioms topAtomRowsCovered_of_mem
#assert_axioms atom_mem_topSupport_of_massEntry
#assert_axioms topAtomPairIndex_exact
#assert_axioms topAtomRegion_exact
#assert_axioms q20_pairIndexAt_eq
#assert_axioms activeChildRowsCovered
#assert_axioms leftPositiveRow_mem
#assert_axioms rightPositiveRow_mem
#assert_axioms leftBoundaryRow_mem
#assert_axioms rightBoundaryRow_mem
