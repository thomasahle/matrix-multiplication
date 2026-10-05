import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent3LocalDataPart0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent3LocalDataPart1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent3LocalDataPart2

/-!
# Parent-local beta-four routing assembly for region 1, branch 1, parent 8

The imported line-budgeted modules check every fixed-left row from untrusted certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module only composes those results by proved `flatMap` laws.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Exact split and child rows consumed by this one parent convolution. -/
def localData : BetaFourLocalData := { slots := [Slot0.data, Slot1.data, Slot2.data, Slot3.data, Slot4.data, Slot5.data, Slot6.data, Slot7.data, Slot8.data, Slot9.data, Slot10.data, Slot11.data, Slot12.data, Slot13.data] }

/-- Compact route-once result assembled from the independently checked slot rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Slot0.expectedRoutedContributions ++ Slot1.expectedRoutedContributions ++ Slot2.expectedRoutedContributions ++ Slot3.expectedRoutedContributions ++ Slot4.expectedRoutedContributions ++ Slot5.expectedRoutedContributions ++ Slot6.expectedRoutedContributions ++ Slot7.expectedRoutedContributions ++ Slot8.expectedRoutedContributions ++ Slot9.expectedRoutedContributions ++ Slot10.expectedRoutedContributions ++ Slot11.expectedRoutedContributions ++ Slot12.expectedRoutedContributions ++ Slot13.expectedRoutedContributions

/-- The bounded slot certificates compose to the exact parent-local routed contribution list.

Proof sketch: the data-level route is a `flatMap` over the at-most-thirty slot records.  Rewriting
each slot with its independently checked fixed-left-row certificate leaves exactly the advertised
append tree. -/
theorem routedContributions_eq_local :
    localData.routedContributions parent coordinate = expectedRoutedContributions := by
  simp only [BetaFourLocalData.routedContributions, localData,
    List.flatMap_cons, List.flatMap_nil]
  rw [Slot0.routedContributions_eq, Slot1.routedContributions_eq, Slot2.routedContributions_eq, Slot3.routedContributions_eq, Slot4.routedContributions_eq, Slot5.routedContributions_eq, Slot6.routedContributions_eq, Slot7.routedContributions_eq, Slot8.routedContributions_eq, Slot9.routedContributions_eq, Slot10.routedContributions_eq, Slot11.routedContributions_eq, Slot12.routedContributions_eq, Slot13.routedContributions_eq]
  rfl

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent3
