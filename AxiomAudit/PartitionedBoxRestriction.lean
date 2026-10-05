/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.PartitionedBoxRestriction

set_option autoImplicit false

/-!
# Trust audit for support-monotone partitioned-box restriction

This companion checks the generic restriction theorem extracting a target box whose support is
contained in a source box.  The theorem abstracts the Cartesian-support conclusion of
Proposition `prop:grouped-cleanup` in the Total-Weight manuscript,
`better_bound/paper.tex:859-898`, especially lines `890-895`; that proposition formalizes the
cleanup route of Claim 6.18 in [alman2025more].
-/

open AlgebraicComplexity.Tensor

#assert_axioms Restricts.partitionedBox_of_support_subset
