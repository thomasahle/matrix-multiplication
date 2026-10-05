import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk10Parent0LocalDataPart0

/-!
# Parent-local beta-four routing assembly for region 0, branch 2, parent 86

The imported line-budgeted modules check every fixed-left row from untrusted certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module only composes those results by proved `flatMap` laws.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk10.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Exact split and child rows consumed by this one parent convolution. -/
def localData : BetaFourLocalData := { slots := [Slot0.data, Slot1.data, Slot2.data, Slot3.data, Slot4.data, Slot5.data, Slot6.data, Slot7.data, Slot8.data, Slot9.data, Slot10.data, Slot11.data, Slot12.data, Slot13.data, Slot14.data, Slot15.data, Slot16.data, Slot17.data, Slot18.data, Slot19.data] }

/-- Compact route-once result assembled from the independently checked slot rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Slot0.expectedRoutedContributions ++ Slot1.expectedRoutedContributions ++ Slot2.expectedRoutedContributions ++ Slot3.expectedRoutedContributions ++ Slot4.expectedRoutedContributions ++ Slot5.expectedRoutedContributions ++ Slot6.expectedRoutedContributions ++ Slot7.expectedRoutedContributions ++ Slot8.expectedRoutedContributions ++ Slot9.expectedRoutedContributions ++ Slot10.expectedRoutedContributions ++ Slot11.expectedRoutedContributions ++ Slot12.expectedRoutedContributions ++ Slot13.expectedRoutedContributions ++ Slot14.expectedRoutedContributions ++ Slot15.expectedRoutedContributions ++ Slot16.expectedRoutedContributions ++ Slot17.expectedRoutedContributions ++ Slot18.expectedRoutedContributions ++ Slot19.expectedRoutedContributions

/-- The bounded slot certificates compose to the exact parent-local routed contribution list.

Proof sketch: the data-level route is a `flatMap` over the at-most-thirty slot records.  Rewriting
each slot with its independently checked fixed-left-row certificate leaves exactly the advertised
append tree. -/
theorem routedContributions_eq_local :
    localData.routedContributions parent coordinate = expectedRoutedContributions := by
  simp only [BetaFourLocalData.routedContributions, localData,
    List.flatMap_cons, List.flatMap_nil]
  rw [Slot0.routedContributions_eq, Slot1.routedContributions_eq, Slot2.routedContributions_eq, Slot3.routedContributions_eq, Slot4.routedContributions_eq, Slot5.routedContributions_eq, Slot6.routedContributions_eq, Slot7.routedContributions_eq, Slot8.routedContributions_eq, Slot9.routedContributions_eq, Slot10.routedContributions_eq, Slot11.routedContributions_eq, Slot12.routedContributions_eq, Slot13.routedContributions_eq, Slot14.routedContributions_eq, Slot15.routedContributions_eq, Slot16.routedContributions_eq, Slot17.routedContributions_eq, Slot18.routedContributions_eq, Slot19.routedContributions_eq]
  rfl

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk10.Parent0
