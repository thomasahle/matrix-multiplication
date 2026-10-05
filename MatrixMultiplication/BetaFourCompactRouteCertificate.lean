/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.BetaFourLocalContributions

/-!
# Compact certificates for parent-local beta-four routes

This leaf module packages the guard-free route computation from
`BetaFourLocalContributions` into small positive/zero slot certificates and a parent-level
`flatMap` certificate.  It is intentionally separate from the routed arithmetic core: changing
certificate packaging should not invalidate every sparse-routing and dense-band client.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

namespace BetaFourLocalSlotData

/-- A checked compact route for one positive parent-local slot.

The certificate stores the two already-verified child support tables but not the routed output
rows. Its expected route is computed by the guard-free constructor. The proof fields are exactly
what is needed to connect that compact computation to the semantic guarded route.
-/
structure CheckedRoute (parent coordinate : ℕ) (parentSupport : List ℕ) where
  data : BetaFourLocalSlotData
  leftSupport : List ℕ
  rightSupport : List ℕ
  leftSupport_eq : data.routedLeftSupport parent coordinate = leftSupport
  rightSupport_eq : data.routedRightSupport parent coordinate = rightSupport
  split_ne : data.splitNumerator ≠ 0

namespace CheckedRoute

/-- Compute the compact route of one checked slot without serializing every routed row.

Only symbols selected by `nonzeroSymbols` are visited, so the zero guards in the semantic route
are known to succeed. Numerators remain stored once in the slot data.
-/
def expectedRoutedContributions
    (certificate : CheckedRoute parent coordinate parentSupport) :
    List (Option BetaFourRoutedContribution) :=
  (nonzeroSymbols certificate.data.leftNumerators).flatMap fun leftSymbol ↦
    certificate.data.routedContributionsForLeftUncheckedFromSupports
      parentSupport certificate.leftSupport certificate.rightSupport leftSymbol

/-- A checked slot's guarded semantic route equals its compact unchecked computation.

Proof sketch: replace the two semantic child supports by the stored tables, expand the sparse
left-symbol fold, and discharge every left guard from membership in `nonzeroSymbols`. The generic
fixed-left theorem similarly discharges every right guard.
-/
theorem routedContributions_eq
    (certificate : CheckedRoute parent coordinate parentSupport)
    (parentSupport_eq : BetaFourLocalSlotData.routedParentSupport parent coordinate =
      parentSupport) :
    certificate.data.routedContributions parent coordinate =
      certificate.expectedRoutedContributions := by
  rw [certificate.data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne
    parent coordinate parentSupport certificate.leftSupport certificate.rightSupport
    parentSupport_eq certificate.leftSupport_eq certificate.rightSupport_eq certificate.split_ne]
  unfold expectedRoutedContributions
  apply List.flatMap_congr
  intro leftSymbol hmem
  exact certificate.data.routedContributionsForLeftFromSupports_eq_unchecked
    parentSupport certificate.leftSupport certificate.rightSupport leftSymbol
      (getD_ne_zero_of_mem_nonzeroSymbols certificate.data.leftNumerators leftSymbol hmem)

end CheckedRoute

/-- A compact route certificate for either a positive or a zero-weight local slot.

Positive slots carry checked support tables and use guard-free sparse routing. A zero slot carries
only the proof that its split numerator vanishes. This sum type lets parent certificates preserve
the exact source slot list without serializing empty or repeated routed rows.
-/
inductive CompactRoute (parent coordinate : ℕ) (parentSupport : List ℕ) where
  | positive (certificate : CheckedRoute parent coordinate parentSupport)
  | zero (data : BetaFourLocalSlotData) (split_eq : data.splitNumerator = 0)

namespace CompactRoute

/-- Source slot represented by a compact route certificate. -/
def data : CompactRoute parent coordinate parentSupport → BetaFourLocalSlotData
  | .positive certificate => certificate.data
  | .zero data _ => data

/-- Routed output represented by a compact route certificate. -/
def expectedRoutedContributions :
    CompactRoute parent coordinate parentSupport → List (Option BetaFourRoutedContribution)
  | .positive certificate => certificate.expectedRoutedContributions
  | .zero _ _ => []

/-- Every compact slot certificate computes its exact semantic route. -/
theorem routedContributions_eq
    (certificate : CompactRoute parent coordinate parentSupport)
    (parentSupport_eq : routedParentSupport parent coordinate = parentSupport) :
    certificate.data.routedContributions parent coordinate =
      certificate.expectedRoutedContributions := by
  cases certificate with
  | positive certificate => exact certificate.routedContributions_eq parentSupport_eq
  | zero data split_eq =>
      exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end CompactRoute

end BetaFourLocalSlotData

namespace BetaFourLocalData

/-- A parent-local compact routing certificate assembled from checked positive and zero slots.

The common parent support is stored once. Each child slot stores only its source data, two child
supports, and the small proofs connecting those tables to the semantic enumerators.
-/
structure CheckedRoute (parent coordinate : ℕ) where
  parentSupport : List ℕ
  parentSupport_eq : BetaFourLocalSlotData.routedParentSupport parent coordinate = parentSupport
  slots : List (BetaFourLocalSlotData.CompactRoute parent coordinate parentSupport)

namespace CheckedRoute

/-- Source-local data represented by a checked compact route. -/
def localData (certificate : CheckedRoute parent coordinate) : BetaFourLocalData :=
  { slots := certificate.slots.map BetaFourLocalSlotData.CompactRoute.data }

/-- Compact routed output represented by a checked parent-local certificate. -/
def expectedRoutedContributions (certificate : CheckedRoute parent coordinate) :
    List (Option BetaFourRoutedContribution) :=
  certificate.slots.flatMap BetaFourLocalSlotData.CompactRoute.expectedRoutedContributions

/-- The semantic route of a checked parent-local certificate equals its compact computation.

Proof sketch: `localData` maps each certificate to its source slot, and routing then `flatMap`s the
semantic slot routes. Fuse the map and `flatMap`, then apply the checked slot theorem pointwise.
-/
theorem routedContributions_eq (certificate : CheckedRoute parent coordinate) :
    certificate.localData.routedContributions parent coordinate =
      certificate.expectedRoutedContributions := by
  unfold localData BetaFourLocalData.routedContributions expectedRoutedContributions
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro slot hmem
  exact slot.routedContributions_eq certificate.parentSupport_eq

end CheckedRoute

end BetaFourLocalData

end MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
