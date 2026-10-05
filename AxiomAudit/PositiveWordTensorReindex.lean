/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.PositiveWordTensorReindex

set_option autoImplicit false

/-!
# Axiom audit for heterogeneous positive-word product reindexing

This companion enforces that the structural reindex theorem uses only the repository's
allowlisted foundational axioms.  The theorem formalizes the product reordering used in
[dupont2026improving, Section 2], `papers/sources/2608.16884/main.tex:499-545`: the six
region-major products are put into the flat order expected by the later global extraction.

This audit covers only that isomorphism.  It asserts no support identity, hashing estimate,
whole-fiber survival statement, `E₂` count, or tensor restriction for the Total-Weight
construction.
-/

#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.positiveWordTensor_of_same_multiplicity
