/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.PairedTotalWeightA5Row
import MatrixMultiplication.SimplifiedRecursiveLevelFourBoundaryCore
import MatrixMultiplication.TotalQuotientCompleteSplitRecurrence

set_option autoImplicit false

/-!
# Frozen manifest interface for the paired total-weight replacement

The complete-split laws and their recursive child splits are the mathematical objects defined in
[alman2025more, `papers/sources/2404.16349/prelim.tex:249-278` and
`papers/sources/2404.16349/constituent.tex:41-47`].  This project's replacement certificate is
determined by its primary tables: its positive top table and total-weight beta-three rows are
reconstructed from those tables rather than supplied as unrelated caches.  A manifest then
enumerates every positive diagonal level-four parent exactly once by an equivalence with `Fin 225`.

The sparse table layout, the order of the 225 rows, and the manifest serialization are
project-specific checker representation invariants, not statements of [alman2025more].

This file contains no concrete certificate values, selected-node list, cardinality estimate, tensor
restriction, numerical floor, or endpoint premise.  Directed numerical checking is deliberately a
separate regional aggregate: after grouping by region, the exact checker is linear and should not
serialize 225 redundant pointwise floor proofs.
-/

namespace MatrixMultiplication.PairedTotalWeightA5ReplacementManifest

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.PairedTotalWeightA5Row
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveLevelFourBoundary
open MatrixMultiplication.SimplifiedVolumeReconstruction
open scoped BigOperators

/-- Replacement b20 top rows, reconstructed from the supplied primary tables. -/
def replacementTop (primary : PrimaryTables) : TopBranchRows :=
  reconstructedTopBranchRows primary

/-- Replacement beta-three rows for the total-weight complete-split quotient. -/
def replacementBetaThree (primary : PrimaryTables) : BetaThreeRows :=
  reconstructedBetaThreeRowsFor
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot primary

/-- The replacement beta-three rows satisfy the nonpositive recurrence by construction. -/
theorem replacementBetaThree_followsNonpositive (primary : PrimaryTables) :
    FollowsNonpositiveBetaThreeRecurrence primary (replacementBetaThree primary) :=
  reconstructedBetaThreeRowsFor_followsNonpositiveBetaThreeRecurrence
    MatrixMultiplication.TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot primary

/-- Positive diagonal `(region, parent)` keys of a supplied replacement top table. -/
abbrev ActiveKey (primary : PrimaryTables) :=
  { key : Fin 6 × Fin positiveLevelFourShapeCount //
      0 < levelFourParentSamples
        (replacementTop primary) key.1 key.1 key.2 }

/-- Frozen replacement data, with exact coverage of its 225 positive diagonal rows.

The raw key map, its positivity, injectivity, and surjectivity reconstruct `keyEquiv`, which
simultaneously certifies cardinality, absence of duplicates, and completeness.  The semantic
reference, competitor, and regional numerical facts are derived in separate layers. -/
structure Manifest where
  primary : PrimaryTables
  row : Fin 225 → Row (replacementTop primary)
  key : Fin 225 → Fin 6 × Fin positiveLevelFourShapeCount
  key_positive : ∀ i, 0 < levelFourParentSamples
    (replacementTop primary) (key i).1 (key i).1 (key i).2
  key_injective : Function.Injective key
  key_surjective : ∀ active : Fin 6 × Fin positiveLevelFourShapeCount,
    0 < levelFourParentSamples
      (replacementTop primary) active.1 active.1 active.2 →
    ∃ i, key i = active
  row_key_data : ∀ i, ((row i).region, (row i).parent) = key i

namespace Manifest

private def activeKey (data : Manifest) (i : Fin 225) : ActiveKey data.primary :=
  ⟨data.key i, data.key_positive i⟩

private theorem activeKey_bijective (data : Manifest) :
    Function.Bijective data.activeKey := by
  constructor
  · intro i j hij
    exact data.key_injective (congrArg Subtype.val hij)
  · rintro ⟨active, hactive⟩
    obtain ⟨i, hi⟩ := data.key_surjective active hactive
    exact ⟨i, Subtype.ext hi⟩

/-- Exact equivalence between serialized rows and intrinsically positive parent keys. -/
noncomputable def keyEquiv (data : Manifest) : Fin 225 ≃ ActiveKey data.primary :=
  Equiv.ofBijective data.activeKey data.activeKey_bijective

/-- Each serialized row has the key selected by the manifest equivalence. -/
theorem row_key (data : Manifest) (i : Fin 225) :
    ((data.row i).region, (data.row i).parent) = (data.keyEquiv i).1 :=
  data.row_key_data i

/-- Top rows canonically reconstructed from this manifest's primary tables. -/
abbrev top (data : Manifest) : TopBranchRows :=
  replacementTop data.primary

/-- Total-weight beta-three rows canonically reconstructed from the same primary tables. -/
abbrev betaThree (data : Manifest) : BetaThreeRows :=
  replacementBetaThree data.primary

/-- The manifest's derived beta-three rows satisfy the exact nonpositive recurrence. -/
theorem betaThree_followsNonpositive (data : Manifest) :
    FollowsNonpositiveBetaThreeRecurrence data.primary data.betaThree :=
  replacementBetaThree_followsNonpositive data.primary

/-- Every enumerated row is attached to a genuinely positive diagonal parent. -/
theorem row_parentSamples_pos (data : Manifest) (i : Fin 225) :
    0 < levelFourParentSamples data.top
      (data.row i).region (data.row i).region (data.row i).parent := by
  have hkey := (data.keyEquiv i).2
  rw [← data.row_key i] at hkey
  exact hkey

end Manifest

end MatrixMultiplication.PairedTotalWeightA5ReplacementManifest
