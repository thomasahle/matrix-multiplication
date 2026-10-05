import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 2,
parent 8; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 1, #[1661028270080, 139076460085248, 0, 0, 0, 0, 139076510416896, 0, 0, 0, 0, 0, 0, 0, 1660977938432, 0, 0, 0, 0], #[70437463654400, 69956427317248, 70437463654400, 70643622084608, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 6, 14]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        1 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 263, numerator := 116998618402690906980352000 }, some { target := 264, numerator := 116199603447745700786339840 }, some { target := 265, numerator := 116998618402690906980352000 }, some { target := 266, numerator := 117341053383381709634928640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 338, numerator := 9796193102437268325610291200 }, some { target := 339, numerator := 9729292271493794298020757504 }, some { target := 340, numerator := 9796193102437268325610291200 }, some { target := 341, numerator := 9824864887127328623148662784 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 599, numerator := 9796196647670894991664742400 }, some { target := 600, numerator := 9729295792516069367331422208 }, some { target := 601, numerator := 9796196647670894991664742400 }, some { target := 602, numerator := 9824868442737248830664736768 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 773, numerator := 116995073169064240925900800 }, some { target := 774, numerator := 116196082425470631475675136 }, some { target := 775, numerator := 116995073169064240925900800 }, some { target := 776, numerator := 117337497773461502118854656 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left6.expected ++ Left14.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left6.routed_eq, Left14.routed_eq]
  rfl

end Slot8

namespace Slot9

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨9, 27, #[209765531648, 21993537667072, 0, 237068353536000, 0, 0, 0, 0, 0, 0, 0, 21993554444288, 0, 0, 0, 0, 0, 0, 209765531648], #[2130303778816, 52226802319360, 2130303778816, 43774306680832, 43018392436736, 2130303778816, 43087111913472, 38620345925632, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

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
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 131, numerator := 12065336227847204279156736 }, some { target := 132, numerator := 295795339779479846843842560 }, some { target := 133, numerator := 12065336227847204279156736 }, some { target := 134, numerator := 247923199262537713736220672 }, some { target := 135, numerator := 243641950923624189637165056 }, some { target := 136, numerator := 12065336227847204279156736 }, some { target := 137, numerator := 244031155318070873646170112 }, some { target := 138, numerator := 218732869679036413060841472 }, some { target := 139, numerator := 295795339779479846843842560 }, some { target := 140, numerator := 12065336227847204279156736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 227, numerator := 1265028742845778892427362304 }, some { target := 228, numerator := 31013607889122321233703075840 }, some { target := 229, numerator := 1265028742845778892427362304 }, some { target := 230, numerator := 25994300296540682402459025408 }, some { target := 231, numerator := 25545419129724438279339638784 }, some { target := 232, numerator := 1265028742845778892427362304 }, some { target := 233, numerator := 25586226508525915017805037568 }, some { target := 234, numerator := 22933746886429927017554116608 }, some { target := 235, numerator := 31013607889122321233703075840 }, some { target := 236, numerator := 1265028742845778892427362304 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 13635745453136562358321152000 }, some { target := 303, numerator := 334295694980122173945937920000 }, some { target := 304, numerator := 13635745453136562358321152000 }, some { target := 305, numerator := 280192575924128716846792704000 }, some { target := 306, numerator := 275354085602048001171259392000 }, some { target := 307, numerator := 13635745453136562358321152000 }, some { target := 308, numerator := 275793948358600793505398784000 }, some { target := 309, numerator := 247202869182669291786338304000 }, some { target := 310, numerator := 334295694980122173945937920000 }, some { target := 311, numerator := 13635745453136562358321152000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 589, numerator := 1265029707841078248358281216 }, some { target := 590, numerator := 31013631547071595766203023360 }, some { target := 591, numerator := 1265029707841078248358281216 }, some { target := 592, numerator := 25994320125637640135620165632 }, some { target := 593, numerator := 25545438616403709144267227136 }, some { target := 594, numerator := 1265029707841078248358281216 }, some { target := 595, numerator := 25586246026334066507117494272 }, some { target := 596, numerator := 22933764380860837921850130432 }, some { target := 597, numerator := 31013631547071595766203023360 }, some { target := 598, numerator := 1265029707841078248358281216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 763, numerator := 12065336227847204279156736 }, some { target := 764, numerator := 295795339779479846843842560 }, some { target := 765, numerator := 12065336227847204279156736 }, some { target := 766, numerator := 247923199262537713736220672 }, some { target := 767, numerator := 243641950923624189637165056 }, some { target := 768, numerator := 12065336227847204279156736 }, some { target := 769, numerator := 244031155318070873646170112 }, some { target := 770, numerator := 218732869679036413060841472 }, some { target := 771, numerator := 295795339779479846843842560 }, some { target := 772, numerator := 12065336227847204279156736 }]

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
def data : BetaFourLocalSlotData := ⟨10, 229, #[3909644976128, 0, 136827826601984, 0, 0, 136827893710848, 0, 0, 0, 0, 0, 0, 3909611421696, 0, 0, 0, 0, 0, 0], #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 80, numerator := 2953206976757656705969422336 }, some { target := 81, numerator := 2891681831408538857928392704 }, some { target := 82, numerator := 2276430377917360377518096384 }, some { target := 83, numerator := 71553744041024057271717462016 }, some { target := 84, numerator := 2276430377917360377518096384 }, some { target := 85, numerator := 2276430377917360377518096384 }, some { target := 86, numerator := 2337955523266478225559126016 }, some { target := 87, numerator := 2337955523266478225559126016 }, some { target := 88, numerator := 39560668459482776290382053376 }, some { target := 89, numerator := 2153380087219124681436037120 }, some { target := 90, numerator := 71553744041024057271717462016 }, some { target := 91, numerator := 39560668459482776290382053376 }, some { target := 92, numerator := 2953206976757656705969422336 }, some { target := 93, numerator := 2276430377917360377518096384 }, some { target := 94, numerator := 2153380087219124681436037120 }, some { target := 95, numerator := 2891681831408538857928392704 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 176, numerator := 103354881223961195762530910208 }, some { target := 177, numerator := 101201654531795337517478182912 }, some { target := 178, numerator := 79669387610136755066950909952 }, some { target := 179, numerator := 2504202642988893138996321845248 }, some { target := 180, numerator := 79669387610136755066950909952 }, some { target := 181, numerator := 79669387610136755066950909952 }, some { target := 182, numerator := 81822614302302613312003637248 }, some { target := 183, numerator := 81822614302302613312003637248 }, some { target := 184, numerator := 1384524763062646851568903651328 }, some { target := 185, numerator := 75362934225805038576845455360 }, some { target := 186, numerator := 2504202642988893138996321845248 }, some { target := 187, numerator := 1384524763062646851568903651328 }, some { target := 188, numerator := 103354881223961195762530910208 }, some { target := 189, numerator := 79669387610136755066950909952 }, some { target := 190, numerator := 75362934225805038576845455360 }, some { target := 191, numerator := 101201654531795337517478182912 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 286, numerator := 103354931915613910316378750976 }, some { target := 287, numerator := 101201704167371953851454193664 }, some { target := 288, numerator := 79669426684952389202208620544 }, some { target := 289, numerator := 2504203871205395368707260153856 }, some { target := 290, numerator := 79669426684952389202208620544 }, some { target := 291, numerator := 79669426684952389202208620544 }, some { target := 292, numerator := 81822654433194345667133177856 }, some { target := 293, numerator := 81822654433194345667133177856 }, some { target := 294, numerator := 1384525442119578006946490351616 }, some { target := 295, numerator := 75362971188468476272359505920 }, some { target := 296, numerator := 2504203871205395368707260153856 }, some { target := 297, numerator := 1384525442119578006946490351616 }, some { target := 298, numerator := 103354931915613910316378750976 }, some { target := 299, numerator := 79669426684952389202208620544 }, some { target := 300, numerator := 75362971188468476272359505920 }, some { target := 301, numerator := 101201704167371953851454193664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 573, numerator := 2953181630931299429045501952 }, some { target := 574, numerator := 2891657013620230690940387328 }, some { target := 575, numerator := 2276410840509543309889241088 }, some { target := 576, numerator := 71553129932772942416248307712 }, some { target := 577, numerator := 2276410840509543309889241088 }, some { target := 578, numerator := 2276410840509543309889241088 }, some { target := 579, numerator := 2337935457820612047994355712 }, some { target := 580, numerator := 2337935457820612047994355712 }, some { target := 581, numerator := 39560328931017198601588703232 }, some { target := 582, numerator := 2153361605887405833679011840 }, some { target := 583, numerator := 71553129932772942416248307712 }, some { target := 584, numerator := 39560328931017198601588703232 }, some { target := 585, numerator := 2953181630931299429045501952 }, some { target := 586, numerator := 2276410840509543309889241088 }, some { target := 587, numerator := 2153361605887405833679011840 }, some { target := 588, numerator := 2891657013620230690940387328 }]

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
def data : BetaFourLocalSlotData := ⟨11, 126, #[51941589647360, 0, 0, 177591814193152, 0, 51941572870144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 26, numerator := 2698465539220376156645621760 }, some { target := 27, numerator := 71959081045876697510549913600 }, some { target := 28, numerator := 68810871250119591994463354880 }, some { target := 29, numerator := 2248721282683646797204684800 }, some { target := 30, numerator := 70609848276266509432227102720 }, some { target := 31, numerator := 2248721282683646797204684800 }, some { target := 32, numerator := 68810871250119591994463354880 }, some { target := 33, numerator := 39127750318695454271361515520 }, some { target := 34, numerator := 70609848276266509432227102720 }, some { target := 35, numerator := 1102323172771523659989736488960 }, some { target := 36, numerator := 43175448627526018506329948160 }, some { target := 37, numerator := 71959081045876697510549913600 }, some { target := 38, numerator := 68810871250119591994463354880 }, some { target := 39, numerator := 2248721282683646797204684800 }, some { target := 40, numerator := 43175448627526018506329948160 }, some { target := 41, numerator := 2248721282683646797204684800 }, some { target := 42, numerator := 69260615506656321353904291840 }, some { target := 43, numerator := 39127750318695454271361515520 }, some { target := 44, numerator := 2698465539220376156645621760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 157, numerator := 9226236507226459666730975232 }, some { target := 158, numerator := 246032973526038924446159339520 }, some { target := 159, numerator := 235269030934274721501639868416 }, some { target := 160, numerator := 7688530422688716388942479360 }, some { target := 161, numerator := 241419855272425694612793851904 }, some { target := 162, numerator := 7688530422688716388942479360 }, some { target := 163, numerator := 235269030934274721501639868416 }, some { target := 164, numerator := 133780429354783665167599140864 }, some { target := 165, numerator := 241419855272425694612793851904 }, some { target := 166, numerator := 3768917613202008773859603382272 }, some { target := 167, numerator := 147619784115623354667695603712 }, some { target := 168, numerator := 246032973526038924446159339520 }, some { target := 169, numerator := 235269030934274721501639868416 }, some { target := 170, numerator := 7688530422688716388942479360 }, some { target := 171, numerator := 147619784115623354667695603712 }, some { target := 172, numerator := 7688530422688716388942479360 }, some { target := 173, numerator := 236806737018812464779428364288 }, some { target := 174, numerator := 133780429354783665167599140864 }, some { target := 175, numerator := 9226236507226459666730975232 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 2698464667611718673869307904 }, some { target := 268, numerator := 71959057802979164636514877440 }, some { target := 269, numerator := 68810849024098826183667351552 }, some { target := 270, numerator := 2248720556343098894891089920 }, some { target := 271, numerator := 70609825469173305299580223488 }, some { target := 272, numerator := 2248720556343098894891089920 }, some { target := 273, numerator := 68810849024098826183667351552 }, some { target := 274, numerator := 39127737680369920771104964608 }, some { target := 275, numerator := 70609825469173305299580223488 }, some { target := 276, numerator := 1102322816719387078275612278784 }, some { target := 277, numerator := 43175434681787498781908926464 }, some { target := 278, numerator := 71959057802979164636514877440 }, some { target := 279, numerator := 68810849024098826183667351552 }, some { target := 280, numerator := 2248720556343098894891089920 }, some { target := 281, numerator := 43175434681787498781908926464 }, some { target := 282, numerator := 2248720556343098894891089920 }, some { target := 283, numerator := 69260593135367445962645569536 }, some { target := 284, numerator := 39127737680369920771104964608 }, some { target := 285, numerator := 2698464667611718673869307904 }]

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
def data : BetaFourLocalSlotData := ⟨12, 3, #[140769314734080, 0, 140705661976576, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 2]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        1 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes_eq

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
  [some { target := 10, numerator := 1015727333146183621568102400 }, some { target := 11, numerator := 1044748114093217439327191040 }, some { target := 12, numerator := 1015727333146183621568102400 }, some { target := 13, numerator := 899644209358048350531747840 }, some { target := 14, numerator := 42109153154146069568437616640 }, some { target := 15, numerator := 11463208474078358014840012800 }, some { target := 16, numerator := 1044748114093217439327191040 }, some { target := 17, numerator := 42109153154146069568437616640 }, some { target := 18, numerator := 1015727333146183621568102400 }, some { target := 19, numerator := 1015727333146183621568102400 }, some { target := 20, numerator := 870623428411014532772659200 }, some { target := 21, numerator := 1015727333146183621568102400 }, some { target := 22, numerator := 11463208474078358014840012800 }, some { target := 23, numerator := 870623428411014532772659200 }, some { target := 24, numerator := 1015727333146183621568102400 }, some { target := 25, numerator := 899644209358048350531747840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 141, numerator := 1015268043806393391938273280 }, some { target := 142, numerator := 1044275702200861774565081088 }, some { target := 143, numerator := 1015268043806393391938273280 }, some { target := 144, numerator := 899237410228519861431042048 }, some { target := 145, numerator := 42090112330373623191498129408 }, some { target := 146, numerator := 11458025065815011137589084160 }, some { target := 147, numerator := 1044275702200861774565081088 }, some { target := 148, numerator := 42090112330373623191498129408 }, some { target := 149, numerator := 1015268043806393391938273280 }, some { target := 150, numerator := 1015268043806393391938273280 }, some { target := 151, numerator := 870229751834051478804234240 }, some { target := 152, numerator := 1015268043806393391938273280 }, some { target := 153, numerator := 11458025065815011137589084160 }, some { target := 154, numerator := 870229751834051478804234240 }, some { target := 155, numerator := 1015268043806393391938273280 }, some { target := 156, numerator := 899237410228519861431042048 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left2.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left2.routed_eq]
  rfl

end Slot12

namespace Slot13

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨13, 0, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot13

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent3
