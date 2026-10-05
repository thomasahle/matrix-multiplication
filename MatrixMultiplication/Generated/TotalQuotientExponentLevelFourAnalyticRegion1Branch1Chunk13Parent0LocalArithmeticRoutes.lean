import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk13Parent0LocalArithmeticRoutePart0

/-! Assembly of bounded sparse route chunks for region 1, branch 1, parent 54;
untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Route chunks whose direct containers and actual contribution counts are independently bounded. -/
def routeChunks : List (List (List (Option BetaFourRoutedContribution))) :=
  [
    RouteChunk0.rows,
    RouteChunk1.rows,
    RouteChunk2.rows,
    RouteChunk3.rows,
    RouteChunk4.rows,
    RouteChunk5.rows,
    RouteChunk6.rows,
    RouteChunk7.rows,
    RouteChunk8.rows,
    RouteChunk9.rows,
    RouteChunk10.rows,
    RouteChunk11.rows,
    RouteChunk12.rows,
    RouteChunk13.rows
  ]

/-- Checked fixed-left rows, regrouped without changing their order. -/
def expectedRoutedRows : List (List (Option BetaFourRoutedContribution)) := routeChunks.flatten

/-- The fixed-left row list flattens to the parent-local route certificate. -/
theorem expectedRoutedRows_flatten :
    expectedRoutedRows.flatten = expectedRoutedContributions := by
  rfl

/-- One independently normalized sparse row per bounded route chunk. -/
def partialRows : List (List BetaFourRoutedContribution) :=
  [
    RouteChunk0.normalized,
    RouteChunk1.normalized,
    RouteChunk2.normalized,
    RouteChunk3.normalized,
    RouteChunk4.normalized,
    RouteChunk5.normalized,
    RouteChunk6.normalized,
    RouteChunk7.normalized,
    RouteChunk8.normalized,
    RouteChunk9.normalized,
    RouteChunk10.normalized,
    RouteChunk11.normalized,
    RouteChunk12.normalized,
    RouteChunk13.normalized
  ]

/-- Local normalization theorems compose without another closed computation. -/
theorem routeChunks_normalized : List.Forall₂
    (fun source normalized ↦ BetaFourRoutedContribution.canonicalizeRows source = normalized)
    routeChunks partialRows := by
  unfold routeChunks partialRows
  exact List.Forall₂.cons RouteChunk0.normalized_eq (List.Forall₂.cons RouteChunk1.normalized_eq (List.Forall₂.cons RouteChunk2.normalized_eq (List.Forall₂.cons RouteChunk3.normalized_eq (List.Forall₂.cons RouteChunk4.normalized_eq (List.Forall₂.cons RouteChunk5.normalized_eq (List.Forall₂.cons RouteChunk6.normalized_eq (List.Forall₂.cons RouteChunk7.normalized_eq (List.Forall₂.cons RouteChunk8.normalized_eq (List.Forall₂.cons RouteChunk9.normalized_eq (List.Forall₂.cons RouteChunk10.normalized_eq (List.Forall₂.cons RouteChunk11.normalized_eq (List.Forall₂.cons RouteChunk12.normalized_eq (List.Forall₂.cons RouteChunk13.normalized_eq (List.Forall₂.nil))))))))))))))

/-- Local support checks compose without scanning the complete route flatten. -/
theorem routeChunks_bounded : routeChunks.Forall fun source ↦
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length source.flatten := by
  unfold routeChunks
  simp only [List.Forall, RouteChunk0.targetsBelowSupport, RouteChunk1.targetsBelowSupport, RouteChunk2.targetsBelowSupport, RouteChunk3.targetsBelowSupport, RouteChunk4.targetsBelowSupport, RouteChunk5.targetsBelowSupport, RouteChunk6.targetsBelowSupport, RouteChunk7.targetsBelowSupport, RouteChunk8.targetsBelowSupport, RouteChunk9.targetsBelowSupport, RouteChunk10.targetsBelowSupport, RouteChunk11.targetsBelowSupport, RouteChunk12.targetsBelowSupport, RouteChunk13.targetsBelowSupport, and_true]

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent0
