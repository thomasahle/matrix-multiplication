/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Census
import AxiomAudit.ConditionalWordTypeMultinomial
import AxiomAudit.CoppersmithWinogradCyclicVolumeEndpoint
import AxiomAudit.CoppersmithWinogradRecursiveApproximateCommonInputBox
import AxiomAudit.CoppersmithWinogradRecursiveApproximateInputBox
import AxiomAudit.CoppersmithWinogradRecursiveApproximateInputTransport
import AxiomAudit.CoppersmithWinogradRecursiveExactTargetChildPower
import AxiomAudit.CoppersmithWinogradRecursiveMarkedPresence
import AxiomAudit.CoppersmithWinogradExactInsideApproximate
import AxiomAudit.CyclicExternalAssembly
import AxiomAudit.HeterogeneousProductHoleBound
import AxiomAudit.MarkedLegwisePresentPartitionExtraction
import AxiomAudit.MarkedModeledFiberRepair
import AxiomAudit.PartitionedBoxEmbedding
import AxiomAudit.Q20EndpointAdapter
import AxiomAudit.RawCyclicRowExtractionTiny
import AxiomAudit.ReaderIndexedParentType
import AxiomAudit.ReaderIndexedParentTypeIdentityCount

set_option autoImplicit false

/-!
# Axiom census for the raw-cyclic extraction seam

This focused census closes the trust-policy scope around the finite raw-cyclic Mode-B seam used by
the forthcoming legal-hybrid appendix of the Total-Weight manuscript (`better_bound/paper.tex`).
It covers the raw one-hash extraction and its nonempty rank-one client, exact-inside-approximate
selection, paired recursive input-box identification and transport, the common pre-cleanup input
box and its genuine one-sample client, same-type marked presence saturation, cyclic external
assembly, present/missing all-leg extraction, marked damaged-fiber repair, the heterogeneous
product-hole bound, and exact finite reader-indexed parent-type and identity-reader cellwise counts.
It does not assert that the concrete `q20` recursive certificate instantiates those generic
interfaces.

The ordinary hashing and sparse-repair ingredients follow [alman2025more],
`papers/sources/2404.16349/constituent.tex:173-177,338-348,376-440,473-497`; the joint raw-cyclic
specialization is new Total-Weight infrastructure.  Importing
`AxiomAudit.RawCyclicRowExtractionTiny` also executes the existing satisfiability audit: its target
is a nonempty indexed direct sum whose child is a genuine nonzero rank-one tensor over every
nontrivial commutative semiring.

`AxiomAudit.CensusAll` imports this module explicitly because the generated census-root manifest is
concurrently owned.  The command below checks every project declaration in this focused import
closure against the standard allowlist.

This census also covers the conditional q20 stage-family endpoint
(`MatrixMultiplication.Q20EndpointAdapter`, TW-21): its companion is imported here so the
enforcing census reaches it while the generated root manifests are held by R7-9.  The same
holds for the generic cyclic CW source budget
`AlgebraicComplexity.Examples.retained_add_omega_mul_volume_le_cwPowerBudget_of_cyclicSequence`
(`AlgebraicComplexity/Examples/CoppersmithWinogradCyclicVolumeEndpoint.lean`), which that
endpoint's cyclic corollary applies.

It further covers the partitioned box embedding and the recursive exact-target child-power
extraction (Codex CW, the four-file child-power image), registered here at the coordinator's
request so the enforcing census reaches them while the generated roots are regenerated.
-/

#axiom_census
