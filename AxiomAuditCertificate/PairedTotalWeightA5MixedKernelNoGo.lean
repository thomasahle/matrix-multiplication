/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.PairedTotalWeightA5MixedKernelNoGo

set_option autoImplicit false

/-!
# Axiom audit for the paired Total-Weight mixed-kernel obstruction

This companion audits the exact finite no-go theorem for the mixed positive/boundary reader used
in [alman2025more, Definition Y-Compatibility and Claim 6.18],
`papers/sources/2404.16349/constituent.tex:235-276,388-436`, and compared with the fixed-map
description at `better_bound/paper.tex:1263-1265,1325-1331,1641-1654,2122-2130`.  It audits no
counting, tensor restriction, asymptotic estimate, or exponent endpoint.
-/

open MatrixMultiplication.PairedTotalWeightA5MixedKernelNoGo

#assert_axioms no_legLocalLabel_preserves_pairedTotalWeightA5_mixedKernels
