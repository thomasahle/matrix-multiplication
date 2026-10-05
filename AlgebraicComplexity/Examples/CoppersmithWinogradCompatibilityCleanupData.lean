/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetFiber

/-!
# Semantic data from a finite CW compatibility cleanup

`CWCompatibilityCleanupData` is the narrow boundary between hashing/compatibility cleanup and
target-specific hole repair.  It stores the actual finite supports, their exact-profile and
projection-closure proofs, the canonical coarse grouping, and the restriction to the grouped
family.

Paper clients should obtain this record from a proved finite extraction theorem.  In particular,
an endpoint should not postulate the `source_restricts` field separately: the oriented hash
constructor supplies it from variable zero-outs.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v w

/-- Complete semantic output of one finite grouped CW compatibility cleanup. -/
structure CWCompatibilityCleanupData
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    {S : Leg → Type w} [∀ c, AddCommMonoid (S c)] [∀ c, Module K (S c)]
    (source : Tensor3 K S) where
  /-- Coarse constituents retained by the hashing step. -/
  coarseKept : Finset (BlockAddress (fun _c ↦
    PositiveWord (CWCoarseDigit depth) n))
  /-- Fine support after exact-profile compatibility cleanup. -/
  finalSupport : Finset (BlockAddress (fun _c ↦
    PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n))
  /-- The cleanup is a Cartesian deletion inside the fine preimage of `coarseKept`. -/
  projection_closed : IsProjectionClosed
    (cwFineSupportOverCoarseSupport
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
    finalSupport Finset.univ
  /-- Every survivor has exactly the certificate-prescribed profile on every logical leg. -/
  exact_profiles : ∀ address ∈ finalSupport, ∀ logicalLeg,
    (cwExactInterfaceCompatibilityModel depth n partAt).MatchesExact
      (logicalAddress sigma address) logicalLeg
      (targets.exactProfile logicalLeg)
  /-- Grouping of fine survivors by their outer coarse address. -/
  grouping : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
    finalSupport).LegGrouping
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
  /-- The grouping is literally the outer coarse-word map. -/
  group_eq : ∀ address,
    grouping.group address = cwExactInterfaceCoarseGroup depth n address
  /-- The source genuinely restricts to the entire grouped cleaned family. -/
  source_restricts : Restricts source
    (Tensor.indexedDirectSum (fun coarse : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦
        (grouping.fiber coarse).realize))

end AlgebraicComplexity.Examples
