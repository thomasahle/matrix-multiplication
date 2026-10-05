/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveMarkedPresence
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for recursive CW marked presence saturation

This focused leaf checks the two public boundaries of the orbit argument: generic transport of
approximate coarsened support along a same-tagged relaxed-ambient orbit, and saturation of the
entire relaxed marked family from one marked address that is actually present, as required by
[alman2025more], Section 6.2, Claim `claim:constituent-hash-quantities`, and Lemma
`lem:more-asym-hash-constituent`; `papers/sources/2404.16349/constituent.tex:177-232`.  The
paired normalization transport also follows Lemma `lem:paired-recursive-normalization` of the
Total-Weight manuscript; `better_bound/paper.tex:1009-1034`.  Its marked-family specialization is
the presence-propagation step at `better_bound/paper.tex:2783-2788`.
-/

open AlgebraicComplexity AlgebraicComplexity.Examples

#assert_axioms
  cwRecursiveApproximateCoarsened_mem_of_sameTaggedMultiplicity
#assert_axioms
  cwRecursiveRelaxedMarkedCoarseSupport_subset_approximateCoarsened_of_presentReference
