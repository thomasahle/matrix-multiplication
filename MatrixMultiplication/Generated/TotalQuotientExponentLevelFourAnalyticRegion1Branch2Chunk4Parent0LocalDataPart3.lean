import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk4Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 3, for region 1, branch 2,
parent 18; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot9

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨9, 542, #[209765531648, 21993537667072, 0, 237068353536000, 0, 0, 0, 0, 0, 0, 0, 21993554444288, 0, 0, 0, 0, 0, 0, 209765531648], #[1661028270080, 139076460085248, 0, 0, 0, 0, 139076510416896, 0, 0, 0, 0, 0, 0, 0, 1660977938432, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 3, 11, 18]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 34, numerator := 188847151160383400868577280 }, some { target := 35, numerator := 15812008593511112782085357568 }, some { target := 40, numerator := 15812014315863049362563137536 }, some { target := 48, numerator := 188841428808446820390797312 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 79, numerator := 19800283200649150341232721920 }, some { target := 80, numerator := 1657860583010462083896104189952 }, some { target := 85, numerator := 1657861182988741988420633493504 }, some { target := 93, numerator := 19799683222369245816703418368 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 154, numerator := 213427262543221834603560960000 }, some { target := 155, numerator := 17870080055149531334732414976000 }, some { target := 160, numerator := 17870086522315711120253386752000 }, some { target := 168, numerator := 213420795377042049082589184000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 492, numerator := 19800298304796247868498247680 }, some { target := 493, numerator := 1657861847667631844042691575808 }, some { target := 498, numerator := 1657862447646369426879352406016 }, some { target := 506, numerator := 19799698326058665031837417472 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 890, numerator := 188847151160383400868577280 }, some { target := 891, numerator := 15812008593511112782085357568 }, some { target := 896, numerator := 15812014315863049362563137536 }, some { target := 904, numerator := 188841428808446820390797312 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 18 = expected := by
  rfl

end Left18

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left3.expected ++ Left11.expected ++ Left18.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left3.routed_eq, Left11.routed_eq, Left18.routed_eq]
  rfl

end Slot9

namespace Slot10

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨10, 36, #[3909644976128, 0, 136827826601984, 0, 0, 136827893710848, 0, 0, 0, 0, 0, 0, 3909611421696, 0, 0, 0, 0, 0, 0], #[24086361145344, 0, 233302254419968, 0, 0, 0, 0, 24086361145344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 2, 5, 12]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 10, numerator := 3390088350423557866260529152 }, some { target := 12, numerator := 32836643528845117458474860544 }, some { target := 17, numerator := 3390088350423557866260529152 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 118644640065644168515059449856 }, some { target := 57, numerator := 1149200654890584123155448594432 }, some { target := 62, numerator := 118644640065644168515059449856 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 144, numerator := 118644698256344205394949701632 }, some { target := 146, numerator := 1149201218529957582624578863104 }, some { target := 151, numerator := 118644698256344205394949701632 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 482, numerator := 3390059255073539426315403264 }, some { target := 484, numerator := 32836361709158387723909726208 }, some { target := 489, numerator := 3390059255073539426315403264 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left2.expected ++ Left5.expected ++ Left12.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left2.routed_eq, Left5.routed_eq, Left12.routed_eq]
  rfl

end Slot10

namespace Slot11

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨11, 1, #[51941589647360, 0, 0, 177591814193152, 0, 51941572870144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 3, 5]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1, numerator := 3655064434076276698948567040 }, some { target := 2, numerator := 3655064434076276698948567040 }, some { target := 3, numerator := 3655064434076276698948567040 }, some { target := 4, numerator := 3655064434076276698948567040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 51, numerator := 12496912941005151717900156928 }, some { target := 52, numerator := 12496912941005151717900156928 }, some { target := 53, numerator := 12496912941005151717900156928 }, some { target := 54, numerator := 12496912941005151717900156928 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 140, numerator := 3655063253484655981537263616 }, some { target := 141, numerator := 3655063253484655981537263616 }, some { target := 142, numerator := 3655063253484655981537263616 }, some { target := 143, numerator := 3655063253484655981537263616 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left3.expected ++ Left5.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left3.routed_eq, Left5.routed_eq]
  rfl

end Slot11

namespace Slot12

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨12, 3, #[2130303778816, 50989851738112, 38139309588480, 44255343017984, 2130303778816, 44186623541248, 44392781971456, 2130303778816, 50989851738112, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 250, numerator := 21080643979530096233938944 }, some { target := 251, numerator := 20641463896623219229065216 }, some { target := 252, numerator := 16249663067554449180327936 }, some { target := 253, numerator := 510766436420697956668145664 }, some { target := 254, numerator := 16249663067554449180327936 }, some { target := 255, numerator := 16249663067554449180327936 }, some { target := 256, numerator := 16688843150461326185201664 }, some { target := 257, numerator := 16688843150461326185201664 }, some { target := 258, numerator := 282392793309121914133807104 }, some { target := 259, numerator := 15371302901740695170580480 }, some { target := 260, numerator := 510766436420697956668145664 }, some { target := 261, numerator := 282392793309121914133807104 }, some { target := 262, numerator := 21080643979530096233938944 }, some { target := 263, numerator := 16249663067554449180327936 }, some { target := 264, numerator := 15371302901740695170580480 }, some { target := 265, numerator := 20641463896623219229065216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 466, numerator := 504575413961655851792990208 }, some { target := 467, numerator := 494063426170788021547302912 }, some { target := 468, numerator := 388943548262109719090429952 }, some { target := 469, numerator := 12225441800779286575734325248 }, some { target := 470, numerator := 388943548262109719090429952 }, some { target := 471, numerator := 388943548262109719090429952 }, some { target := 472, numerator := 399455536052977549336117248 }, some { target := 473, numerator := 399455536052977549336117248 }, some { target := 474, numerator := 6759208149528014847976931328 }, some { target := 475, numerator := 367919572680374058599055360 }, some { target := 476, numerator := 12225441800779286575734325248 }, some { target := 477, numerator := 6759208149528014847976931328 }, some { target := 478, numerator := 504575413961655851792990208 }, some { target := 479, numerator := 388943548262109719090429952 }, some { target := 480, numerator := 367919572680374058599055360 }, some { target := 481, numerator := 494063426170788021547302912 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 562, numerator := 377411529310942045478584320 }, some { target := 563, numerator := 369548789116964086197780480 }, some { target := 564, numerator := 290921387177184493389742080 }, some { target := 565, numerator := 9144366845596366643574865920 }, some { target := 566, numerator := 290921387177184493389742080 }, some { target := 567, numerator := 290921387177184493389742080 }, some { target := 568, numerator := 298784127371162452670545920 }, some { target := 569, numerator := 298784127371162452670545920 }, some { target := 570, numerator := 5055741944727827817556869120 }, some { target := 571, numerator := 275195906789228574828134400 }, some { target := 572, numerator := 9144366845596366643574865920 }, some { target := 573, numerator := 5055741944727827817556869120 }, some { target := 574, numerator := 377411529310942045478584320 }, some { target := 575, numerator := 290921387177184493389742080 }, some { target := 576, numerator := 275195906789228574828134400 }, some { target := 577, numerator := 369548789116964086197780480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 597, numerator := 437933378155399418537312256 }, some { target := 598, numerator := 428809766110495263984451584 }, some { target := 599, numerator := 337573645661453718455844864 }, some { target := 600, numerator := 10610760808223531744976961536 }, some { target := 601, numerator := 337573645661453718455844864 }, some { target := 602, numerator := 337573645661453718455844864 }, some { target := 603, numerator := 346697257706357873008705536 }, some { target := 604, numerator := 346697257706357873008705536 }, some { target := 605, numerator := 5866482544873371377489412096 }, some { target := 606, numerator := 319326421571645409350123520 }, some { target := 607, numerator := 10610760808223531744976961536 }, some { target := 608, numerator := 5866482544873371377489412096 }, some { target := 609, numerator := 437933378155399418537312256 }, some { target := 610, numerator := 337573645661453718455844864 }, some { target := 611, numerator := 319326421571645409350123520 }, some { target := 612, numerator := 428809766110495263984451584 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 733, numerator := 21080643979530096233938944 }, some { target := 734, numerator := 20641463896623219229065216 }, some { target := 735, numerator := 16249663067554449180327936 }, some { target := 736, numerator := 510766436420697956668145664 }, some { target := 737, numerator := 16249663067554449180327936 }, some { target := 738, numerator := 16249663067554449180327936 }, some { target := 739, numerator := 16688843150461326185201664 }, some { target := 740, numerator := 16688843150461326185201664 }, some { target := 741, numerator := 282392793309121914133807104 }, some { target := 742, numerator := 15371302901740695170580480 }, some { target := 743, numerator := 510766436420697956668145664 }, some { target := 744, numerator := 282392793309121914133807104 }, some { target := 745, numerator := 21080643979530096233938944 }, some { target := 746, numerator := 16249663067554449180327936 }, some { target := 747, numerator := 15371302901740695170580480 }, some { target := 748, numerator := 20641463896623219229065216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 829, numerator := 437253357381866189626540032 }, some { target := 830, numerator := 428143912436410644009320448 }, some { target := 831, numerator := 337049462981855187837124608 }, some { target := 832, numerator := 10594284471564799552826376192 }, some { target := 833, numerator := 337049462981855187837124608 }, some { target := 834, numerator := 337049462981855187837124608 }, some { target := 835, numerator := 346158907927310733454344192 }, some { target := 836, numerator := 346158907927310733454344192 }, some { target := 837, numerator := 5857373099927915831872192512 }, some { target := 838, numerator := 318830573090944096602685440 }, some { target := 839, numerator := 10594284471564799552826376192 }, some { target := 840, numerator := 5857373099927915831872192512 }, some { target := 841, numerator := 437253357381866189626540032 }, some { target := 842, numerator := 337049462981855187837124608 }, some { target := 843, numerator := 318830573090944096602685440 }, some { target := 844, numerator := 428143912436410644009320448 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 864, numerator := 439293419702465876358856704 }, some { target := 865, numerator := 430141473458664503934713856 }, some { target := 866, numerator := 338622011020650779693285376 }, some { target := 867, numerator := 10643713481540996129278132224 }, some { target := 868, numerator := 338622011020650779693285376 }, some { target := 869, numerator := 338622011020650779693285376 }, some { target := 870, numerator := 347773957264452152117428224 }, some { target := 871, numerator := 347773957264452152117428224 }, some { target := 872, numerator := 5884701434764282468723851264 }, some { target := 873, numerator := 320318118533048034844999680 }, some { target := 874, numerator := 10643713481540996129278132224 }, some { target := 875, numerator := 5884701434764282468723851264 }, some { target := 876, numerator := 439293419702465876358856704 }, some { target := 877, numerator := 338622011020650779693285376 }, some { target := 878, numerator := 320318118533048034844999680 }, some { target := 879, numerator := 430141473458664503934713856 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 925, numerator := 21080643979530096233938944 }, some { target := 926, numerator := 20641463896623219229065216 }, some { target := 927, numerator := 16249663067554449180327936 }, some { target := 928, numerator := 510766436420697956668145664 }, some { target := 929, numerator := 16249663067554449180327936 }, some { target := 930, numerator := 16249663067554449180327936 }, some { target := 931, numerator := 16688843150461326185201664 }, some { target := 932, numerator := 16688843150461326185201664 }, some { target := 933, numerator := 282392793309121914133807104 }, some { target := 934, numerator := 15371302901740695170580480 }, some { target := 935, numerator := 510766436420697956668145664 }, some { target := 936, numerator := 282392793309121914133807104 }, some { target := 937, numerator := 21080643979530096233938944 }, some { target := 938, numerator := 16249663067554449180327936 }, some { target := 939, numerator := 15371302901740695170580480 }, some { target := 940, numerator := 20641463896623219229065216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 960, numerator := 504575413961655851792990208 }, some { target := 961, numerator := 494063426170788021547302912 }, some { target := 962, numerator := 388943548262109719090429952 }, some { target := 963, numerator := 12225441800779286575734325248 }, some { target := 964, numerator := 388943548262109719090429952 }, some { target := 965, numerator := 388943548262109719090429952 }, some { target := 966, numerator := 399455536052977549336117248 }, some { target := 967, numerator := 399455536052977549336117248 }, some { target := 968, numerator := 6759208149528014847976931328 }, some { target := 969, numerator := 367919572680374058599055360 }, some { target := 970, numerator := 12225441800779286575734325248 }, some { target := 971, numerator := 6759208149528014847976931328 }, some { target := 972, numerator := 504575413961655851792990208 }, some { target := 973, numerator := 388943548262109719090429952 }, some { target := 974, numerator := 367919572680374058599055360 }, some { target := 975, numerator := 494063426170788021547302912 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 986, numerator := 21080643979530096233938944 }, some { target := 987, numerator := 20641463896623219229065216 }, some { target := 988, numerator := 16249663067554449180327936 }, some { target := 989, numerator := 510766436420697956668145664 }, some { target := 990, numerator := 16249663067554449180327936 }, some { target := 991, numerator := 16249663067554449180327936 }, some { target := 992, numerator := 16688843150461326185201664 }, some { target := 993, numerator := 16688843150461326185201664 }, some { target := 994, numerator := 282392793309121914133807104 }, some { target := 995, numerator := 15371302901740695170580480 }, some { target := 996, numerator := 510766436420697956668145664 }, some { target := 997, numerator := 282392793309121914133807104 }, some { target := 998, numerator := 21080643979530096233938944 }, some { target := 999, numerator := 16249663067554449180327936 }, some { target := 1000, numerator := 15371302901740695170580480 }, some { target := 1001, numerator := 20641463896623219229065216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq]
  rfl

end Slot12

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent0
