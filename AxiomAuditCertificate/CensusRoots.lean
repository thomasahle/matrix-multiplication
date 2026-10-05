/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradLevelFourOccurrenceExactTargetFamilyGrowth
import MatrixMultiplication.BetaFourSemanticAgreement
import MatrixMultiplication.CertifiedLevelFourOccurrenceExtractionClients
import MatrixMultiplication.CoppersmithWinogradDepthThreeForestResiduals
import MatrixMultiplication.FineAddressStage
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityData
import MatrixMultiplication.Generated.TotalQuotientOuterFloorLevelThreeOrientation
import MatrixMultiplication.Generated.TotalQuotientOuterFloorLevelThreeWeights
import MatrixMultiplication.Generated.TotalQuotientOuterFloorRootRegion0Branch1
import MatrixMultiplication.Generated.TotalQuotientOuterFloorRootRegion0Branch2
import MatrixMultiplication.Generated.TotalQuotientOuterFloorRootRegion4Branch1
import MatrixMultiplication.Generated.TotalQuotientOuterFloorRootRegion4Branch2
import MatrixMultiplication.Generated.TotalQuotientOuterFloorRootRegion5Branch1
import MatrixMultiplication.Generated.TotalQuotientOuterFloorRootRegion5Branch2
import MatrixMultiplication.MergedLeafBudget
import MatrixMultiplication.PairedTotalWeightA5ReplacementManifest
import MatrixMultiplication.SimplifiedExponentLevelFourBranchProjection
import MatrixMultiplication.SimplifiedExponentRecurrenceRateEquivalence
import MatrixMultiplication.SimplifiedRecursiveDiagonalRegionalFamilyStage
import MatrixMultiplication.SimplifiedRecursiveRegionalFamilies
import MatrixMultiplication.SparseTopBranchSupport
import MatrixMultiplication.TotalQuotientExponentLevelTwoCertificate
import MatrixMultiplication.TotalQuotientNormalizedCompression
import MatrixMultiplication.TotalWeightEndpointComposition
import MatrixMultiplication.TotalWeightLevelFourInnerGrowthDatum
import MatrixMultiplication.TotalWeightOuterCeiling

/-!
# Census import roots for the opt-in AxiomAuditCertificate target

GENERATED FILE -- regenerate with `bash scripts/regen_census_roots.sh --write`; do not edit by
hand.

`#axiom_census` can only see modules it imports, so the census closure has to equal the build.
Some modules are built only because a focused `#assert_axioms` audit imports them, which puts
them inside the build but outside every census closure -- a hole in the trust policy rather than
a cosmetic gap, since `AxiomAuditCertificate.Census` is what actually walks `Environment.constants`.

This module imports the 26 maximal such modules for this tier, which pulls 551 of them in total
(importing a module pulls its whole cone, so only the roots are listed). It declares nothing; it
exists purely to widen the closure of `AxiomAuditCertificate.Census`.

Tier split: a root that reaches `MatrixMultiplication.Generated.*` belongs to the opt-in
certificate census instead, so this file is where the generated numeral tables are covered.
-/
