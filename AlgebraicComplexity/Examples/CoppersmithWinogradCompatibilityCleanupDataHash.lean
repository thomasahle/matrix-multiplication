/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityCleanupData
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityCoarseExtraction

/-!
# Oriented hashing constructs compatibility-cleanup data

This module proves that the concrete oriented affine hash followed by the paper-order exact
profile/compatibility cleanup populates every field of `CWCompatibilityCleanupData`.  Consequently
later repair and endpoint clients consume a constructed grouped-family restriction rather than
taking it as a hypothesis.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v w

/-- Semantic cleanup data constructed from one concrete oriented hash seed. -/
noncomputable def cwOrientedHashCompatibilityCleanupData
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    {depth : ℕ} (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type w} [Fintype Part] [DecidableEq Part]
    {n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    CWCompatibilityCleanupData K q partAt term hmultiplicity sigma targets
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize := by
  classical
  let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
  let coarseKept := encoding.orientedXIsolatedCoarseSupport
    K q term hmultiplicity sigma B seed
  let finalSupport := cwOrientedGroupedCleanupFinalSupport
    K q partAt term hmultiplicity sigma targets pooled coarseKept
  let fineAmbient := cwFineSupportOverCoarseSupport selected.support coarseKept
  let hashed := selected.withSupport fineAmbient
  have hcoarseX : Set.InjOn
      (fun address : BlockAddress (fun _c ↦
        PositiveWord (CWCoarseDigit depth) n) ↦ address (sigma .X)) coarseKept := by
    exact encoding.orientedX_injectiveOn_orientedXIsolatedCoarseSupport
      K q term hmultiplicity sigma B seed
  have hgrouped :=
    cwSelectedExactInterfaceTerm_orientedGroupedCleanup_withCoarseGroup
      K q partAt term hmultiplicity sigma targets pooled coarseKept hcoarseX
  let G := Classical.choose hgrouped
  have hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address :=
    (Classical.choose_spec hgrouped).1
  have hcleanup : Restricts hashed.realize
      (Tensor.indexedDirectSum (fun coarse : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦
          (G.fiber coarse).realize)) :=
    (Classical.choose_spec hgrouped).2
  have hhash : Restricts selected.realize hashed.realize := by
    simpa [selected, coarseKept, fineAmbient, hashed] using
      cwSelectedExactInterfaceTerm_restricts_orientedXIsolatedFine
        encoding K q term hmultiplicity sigma B hB seed
  have hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport selected.support coarseKept)
      finalSupport Finset.univ := by
    simpa [selected, coarseKept, finalSupport,
      cwOrientedGroupedCleanupFinalSupport] using
      cwSelectedExactInterfaceTerm_orientedGroupedCleanup_isProjectionClosed
        K q partAt term hmultiplicity sigma targets pooled coarseKept hcoarseX
  have hExact : ∀ address ∈ finalSupport, ∀ logicalLeg,
      (cwExactInterfaceCompatibilityModel depth n partAt).MatchesExact
        (logicalAddress sigma address) logicalLeg
        (targets.exactProfile logicalLeg) := by
    intro address haddress logicalLeg
    exact mem_cwOrientedGroupedCleanupFinalSupport_matchesExact
      K q partAt term hmultiplicity sigma targets pooled coarseKept
        address haddress logicalLeg
  exact {
    coarseKept := coarseKept
    finalSupport := finalSupport
    projection_closed := hclosed
    exact_profiles := hExact
    grouping := G
    group_eq := hgroup
    source_restricts := hhash.trans hcleanup
  }

end AlgebraicComplexity.Examples
