import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk13Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 5, for region 1, branch 1,
parent 57; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot21

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨21, 1, #[140737471578112, 0, 140737505132544, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

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
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1, numerator := 9942204755307403596944900096 }, some { target := 2, numerator := 9913190539095417010572492800 }, some { target := 3, numerator := 9845490701267448309036875776 }, some { target := 4, numerator := 9913190539095417010572492800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 90, numerator := 9942207125714017068622282752 }, some { target := 91, numerator := 9913192902584501454608793600 }, some { target := 92, numerator := 9845493048615631688577318912 }, some { target := 93, numerator := 9913192902584501454608793600 }]

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

end Slot21

namespace Slot22

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨22, 7, #[49796387700736, 0, 0, 181882218086400, 0, 49796370923520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

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
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 5, numerator := 742570030231851405810860032 }, some { target := 6, numerator := 18204942676651840916653342720 }, some { target := 7, numerator := 13462076031945177098893656064 }, some { target := 8, numerator := 15019077708237768756239007744 }, some { target := 9, numerator := 742570030231851405810860032 }, some { target := 10, numerator := 14995123836294805807664463872 }, some { target := 11, numerator := 15258616427667398241984446464 }, some { target := 12, numerator := 742570030231851405810860032 }, some { target := 13, numerator := 18204942676651840916653342720 }, some { target := 14, numerator := 742570030231851405810860032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 94, numerator := 2712250635422256182643916800 }, some { target := 95, numerator := 66493886545835958026108928000 }, some { target := 96, numerator := 49170479261526063698254233600 }, some { target := 97, numerator := 54857456400314665371539865600 }, some { target := 98, numerator := 2712250635422256182643916800 }, some { target := 99, numerator := 54769964444333302268873932800 }, some { target := 100, numerator := 55732375960128296398199193600 }, some { target := 101, numerator := 2712250635422256182643916800 }, some { target := 102, numerator := 66493886545835958026108928000 }, some { target := 103, numerator := 2712250635422256182643916800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 742569780047884906125066240 }, some { target := 217, numerator := 18204936543109436408227430400 }, some { target := 218, numerator := 13462071496351977975557652480 }, some { target := 219, numerator := 15019072648065285036787630080 }, some { target := 220, numerator := 742569780047884906125066240 }, some { target := 221, numerator := 14995118784192772620461015040 }, some { target := 222, numerator := 15258611286790409200053780480 }, some { target := 223, numerator := 742569780047884906125066240 }, some { target := 224, numerator := 18204936543109436408227430400 }, some { target := 225, numerator := 742569780047884906125066240 }]

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

end Slot22

namespace Slot23

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨23, 25, #[2473901162496, 2817498546176, 2199023255552, 29480655519744, 2611340115968, 2199023255552, 2611340115968, 2542620639232, 96069828476928, 2542620639232, 29480655519744, 96069828476928, 2473901162496, 2542620639232, 2542620639232, 2817498546176, 0, 0, 0], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 29, numerator := 199756102225385992539340800 }, some { target := 30, numerator := 148754544210393824231424000 }, some { target := 31, numerator := 157254803879559185616076800 }, some { target := 32, numerator := 204006232059968673231667200 }, some { target := 33, numerator := 2732833483636663685165875200 }, some { target := 34, numerator := 4942900997619657645175603200 }, some { target := 35, numerator := 148754544210393824231424000 }, some { target := 36, numerator := 2732833483636663685165875200 }, some { target := 37, numerator := 161504933714141866308403200 }, some { target := 38, numerator := 161504933714141866308403200 }, some { target := 39, numerator := 157254803879559185616076800 }, some { target := 40, numerator := 157254803879559185616076800 }, some { target := 41, numerator := 4942900997619657645175603200 }, some { target := 42, numerator := 157254803879559185616076800 }, some { target := 43, numerator := 199756102225385992539340800 }, some { target := 44, numerator := 204006232059968673231667200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 227500005312245158169804800 }, some { target := 56, numerator := 169414897572948522041344000 }, some { target := 57, numerator := 179095748862831294729420800 }, some { target := 58, numerator := 232340430957186544513843200 }, some { target := 59, numerator := 3112393689697311419216691200 }, some { target := 60, numerator := 5629415025066832318116659200 }, some { target := 61, numerator := 169414897572948522041344000 }, some { target := 62, numerator := 3112393689697311419216691200 }, some { target := 63, numerator := 183936174507772681073459200 }, some { target := 64, numerator := 183936174507772681073459200 }, some { target := 65, numerator := 179095748862831294729420800 }, some { target := 66, numerator := 179095748862831294729420800 }, some { target := 67, numerator := 5629415025066832318116659200 }, some { target := 68, numerator := 179095748862831294729420800 }, some { target := 69, numerator := 227500005312245158169804800 }, some { target := 70, numerator := 232340430957186544513843200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 104, numerator := 177560979755898660034969600 }, some { target := 105, numerator := 132226261520350065983488000 }, some { target := 106, numerator := 139782047892941498325401600 }, some { target := 107, numerator := 181338872942194376205926400 }, some { target := 108, numerator := 2429185318788145497925222400 }, some { target := 109, numerator := 4393689775661917906822758400 }, some { target := 110, numerator := 132226261520350065983488000 }, some { target := 111, numerator := 2429185318788145497925222400 }, some { target := 112, numerator := 143559941079237214496358400 }, some { target := 113, numerator := 143559941079237214496358400 }, some { target := 114, numerator := 139782047892941498325401600 }, some { target := 115, numerator := 139782047892941498325401600 }, some { target := 116, numerator := 4393689775661917906822758400 }, some { target := 117, numerator := 139782047892941498325401600 }, some { target := 118, numerator := 177560979755898660034969600 }, some { target := 119, numerator := 181338872942194376205926400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 130, numerator := 2380426884852516411093811200 }, some { target := 131, numerator := 1772658318507193072091136000 }, some { target := 132, numerator := 1873953079564746961924915200 }, some { target := 133, numerator := 2431074265381293356010700800 }, some { target := 134, numerator := 32566265680003575581560012800 }, some { target := 135, numerator := 58902903554967586938342604800 }, some { target := 136, numerator := 1772658318507193072091136000 }, some { target := 137, numerator := 32566265680003575581560012800 }, some { target := 138, numerator := 1924600460093523906841804800 }, some { target := 139, numerator := 1924600460093523906841804800 }, some { target := 140, numerator := 1873953079564746961924915200 }, some { target := 141, numerator := 1873953079564746961924915200 }, some { target := 142, numerator := 58902903554967586938342604800 }, some { target := 143, numerator := 1873953079564746961924915200 }, some { target := 144, numerator := 2380426884852516411093811200 }, some { target := 145, numerator := 2431074265381293356010700800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 165, numerator := 210853663460129658791526400 }, some { target := 166, numerator := 157018685555415703355392000 }, some { target := 167, numerator := 165991181872868029261414400 }, some { target := 168, numerator := 215339911618855821744537600 }, some { target := 169, numerator := 2884657566060922778786201600 }, some { target := 170, numerator := 5217506608598527514352025600 }, some { target := 171, numerator := 157018685555415703355392000 }, some { target := 172, numerator := 2884657566060922778786201600 }, some { target := 173, numerator := 170477430031594192214425600 }, some { target := 174, numerator := 170477430031594192214425600 }, some { target := 175, numerator := 165991181872868029261414400 }, some { target := 176, numerator := 165991181872868029261414400 }, some { target := 177, numerator := 5217506608598527514352025600 }, some { target := 178, numerator := 165991181872868029261414400 }, some { target := 179, numerator := 210853663460129658791526400 }, some { target := 180, numerator := 215339911618855821744537600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 226, numerator := 177560979755898660034969600 }, some { target := 227, numerator := 132226261520350065983488000 }, some { target := 228, numerator := 139782047892941498325401600 }, some { target := 229, numerator := 181338872942194376205926400 }, some { target := 230, numerator := 2429185318788145497925222400 }, some { target := 231, numerator := 4393689775661917906822758400 }, some { target := 232, numerator := 132226261520350065983488000 }, some { target := 233, numerator := 2429185318788145497925222400 }, some { target := 234, numerator := 143559941079237214496358400 }, some { target := 235, numerator := 143559941079237214496358400 }, some { target := 236, numerator := 139782047892941498325401600 }, some { target := 237, numerator := 139782047892941498325401600 }, some { target := 238, numerator := 4393689775661917906822758400 }, some { target := 239, numerator := 139782047892941498325401600 }, some { target := 240, numerator := 177560979755898660034969600 }, some { target := 241, numerator := 181338872942194376205926400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 261, numerator := 210853663460129658791526400 }, some { target := 262, numerator := 157018685555415703355392000 }, some { target := 263, numerator := 165991181872868029261414400 }, some { target := 264, numerator := 215339911618855821744537600 }, some { target := 265, numerator := 2884657566060922778786201600 }, some { target := 266, numerator := 5217506608598527514352025600 }, some { target := 267, numerator := 157018685555415703355392000 }, some { target := 268, numerator := 2884657566060922778786201600 }, some { target := 269, numerator := 170477430031594192214425600 }, some { target := 270, numerator := 170477430031594192214425600 }, some { target := 271, numerator := 165991181872868029261414400 }, some { target := 272, numerator := 165991181872868029261414400 }, some { target := 273, numerator := 5217506608598527514352025600 }, some { target := 274, numerator := 165991181872868029261414400 }, some { target := 275, numerator := 210853663460129658791526400 }, some { target := 276, numerator := 215339911618855821744537600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 371, numerator := 205304882842757825665433600 }, some { target := 372, numerator := 152886614882904763793408000 }, some { target := 373, numerator := 161622992876213607438745600 }, some { target := 374, numerator := 209673071839412247488102400 }, some { target := 375, numerator := 2808745524848793231976038400 }, some { target := 376, numerator := 5080203803109092579763814400 }, some { target := 377, numerator := 152886614882904763793408000 }, some { target := 378, numerator := 2808745524848793231976038400 }, some { target := 379, numerator := 165991181872868029261414400 }, some { target := 380, numerator := 165991181872868029261414400 }, some { target := 381, numerator := 161622992876213607438745600 }, some { target := 382, numerator := 161622992876213607438745600 }, some { target := 383, numerator := 5080203803109092579763814400 }, some { target := 384, numerator := 161622992876213607438745600 }, some { target := 385, numerator := 205304882842757825665433600 }, some { target := 386, numerator := 209673071839412247488102400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 397, numerator := 7757195303085822710277734400 }, some { target := 398, numerator := 5776634800170293507653632000 }, some { target := 399, numerator := 6106728217322881708090982400 }, some { target := 400, numerator := 7922242011662116810496409600 }, some { target := 401, numerator := 106125033614557106440608153600 }, some { target := 402, numerator := 191949322074230038554319257600 }, some { target := 403, numerator := 5776634800170293507653632000 }, some { target := 404, numerator := 106125033614557106440608153600 }, some { target := 405, numerator := 6271774925899175808309657600 }, some { target := 406, numerator := 6271774925899175808309657600 }, some { target := 407, numerator := 6106728217322881708090982400 }, some { target := 408, numerator := 6106728217322881708090982400 }, some { target := 409, numerator := 191949322074230038554319257600 }, some { target := 410, numerator := 6106728217322881708090982400 }, some { target := 411, numerator := 7757195303085822710277734400 }, some { target := 412, numerator := 7922242011662116810496409600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 432, numerator := 205304882842757825665433600 }, some { target := 433, numerator := 152886614882904763793408000 }, some { target := 434, numerator := 161622992876213607438745600 }, some { target := 435, numerator := 209673071839412247488102400 }, some { target := 436, numerator := 2808745524848793231976038400 }, some { target := 437, numerator := 5080203803109092579763814400 }, some { target := 438, numerator := 152886614882904763793408000 }, some { target := 439, numerator := 2808745524848793231976038400 }, some { target := 440, numerator := 165991181872868029261414400 }, some { target := 441, numerator := 165991181872868029261414400 }, some { target := 442, numerator := 161622992876213607438745600 }, some { target := 443, numerator := 161622992876213607438745600 }, some { target := 444, numerator := 5080203803109092579763814400 }, some { target := 445, numerator := 161622992876213607438745600 }, some { target := 446, numerator := 205304882842757825665433600 }, some { target := 447, numerator := 209673071839412247488102400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 493, numerator := 2380426884852516411093811200 }, some { target := 494, numerator := 1772658318507193072091136000 }, some { target := 495, numerator := 1873953079564746961924915200 }, some { target := 496, numerator := 2431074265381293356010700800 }, some { target := 497, numerator := 32566265680003575581560012800 }, some { target := 498, numerator := 58902903554967586938342604800 }, some { target := 499, numerator := 1772658318507193072091136000 }, some { target := 500, numerator := 32566265680003575581560012800 }, some { target := 501, numerator := 1924600460093523906841804800 }, some { target := 502, numerator := 1924600460093523906841804800 }, some { target := 503, numerator := 1873953079564746961924915200 }, some { target := 504, numerator := 1873953079564746961924915200 }, some { target := 505, numerator := 58902903554967586938342604800 }, some { target := 506, numerator := 1873953079564746961924915200 }, some { target := 507, numerator := 2380426884852516411093811200 }, some { target := 508, numerator := 2431074265381293356010700800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 528, numerator := 7757195303085822710277734400 }, some { target := 529, numerator := 5776634800170293507653632000 }, some { target := 530, numerator := 6106728217322881708090982400 }, some { target := 531, numerator := 7922242011662116810496409600 }, some { target := 532, numerator := 106125033614557106440608153600 }, some { target := 533, numerator := 191949322074230038554319257600 }, some { target := 534, numerator := 5776634800170293507653632000 }, some { target := 535, numerator := 106125033614557106440608153600 }, some { target := 536, numerator := 6271774925899175808309657600 }, some { target := 537, numerator := 6271774925899175808309657600 }, some { target := 538, numerator := 6106728217322881708090982400 }, some { target := 539, numerator := 6106728217322881708090982400 }, some { target := 540, numerator := 191949322074230038554319257600 }, some { target := 541, numerator := 6106728217322881708090982400 }, some { target := 542, numerator := 7757195303085822710277734400 }, some { target := 543, numerator := 7922242011662116810496409600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 624, numerator := 199756102225385992539340800 }, some { target := 625, numerator := 148754544210393824231424000 }, some { target := 626, numerator := 157254803879559185616076800 }, some { target := 627, numerator := 204006232059968673231667200 }, some { target := 628, numerator := 2732833483636663685165875200 }, some { target := 629, numerator := 4942900997619657645175603200 }, some { target := 630, numerator := 148754544210393824231424000 }, some { target := 631, numerator := 2732833483636663685165875200 }, some { target := 632, numerator := 161504933714141866308403200 }, some { target := 633, numerator := 161504933714141866308403200 }, some { target := 634, numerator := 157254803879559185616076800 }, some { target := 635, numerator := 157254803879559185616076800 }, some { target := 636, numerator := 4942900997619657645175603200 }, some { target := 637, numerator := 157254803879559185616076800 }, some { target := 638, numerator := 199756102225385992539340800 }, some { target := 639, numerator := 204006232059968673231667200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 760, numerator := 205304882842757825665433600 }, some { target := 761, numerator := 152886614882904763793408000 }, some { target := 762, numerator := 161622992876213607438745600 }, some { target := 763, numerator := 209673071839412247488102400 }, some { target := 764, numerator := 2808745524848793231976038400 }, some { target := 765, numerator := 5080203803109092579763814400 }, some { target := 766, numerator := 152886614882904763793408000 }, some { target := 767, numerator := 2808745524848793231976038400 }, some { target := 768, numerator := 165991181872868029261414400 }, some { target := 769, numerator := 165991181872868029261414400 }, some { target := 770, numerator := 161622992876213607438745600 }, some { target := 771, numerator := 161622992876213607438745600 }, some { target := 772, numerator := 5080203803109092579763814400 }, some { target := 773, numerator := 161622992876213607438745600 }, some { target := 774, numerator := 205304882842757825665433600 }, some { target := 775, numerator := 209673071839412247488102400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 795, numerator := 205304882842757825665433600 }, some { target := 796, numerator := 152886614882904763793408000 }, some { target := 797, numerator := 161622992876213607438745600 }, some { target := 798, numerator := 209673071839412247488102400 }, some { target := 799, numerator := 2808745524848793231976038400 }, some { target := 800, numerator := 5080203803109092579763814400 }, some { target := 801, numerator := 152886614882904763793408000 }, some { target := 802, numerator := 2808745524848793231976038400 }, some { target := 803, numerator := 165991181872868029261414400 }, some { target := 804, numerator := 165991181872868029261414400 }, some { target := 805, numerator := 161622992876213607438745600 }, some { target := 806, numerator := 161622992876213607438745600 }, some { target := 807, numerator := 5080203803109092579763814400 }, some { target := 808, numerator := 161622992876213607438745600 }, some { target := 809, numerator := 205304882842757825665433600 }, some { target := 810, numerator := 209673071839412247488102400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 891, numerator := 227500005312245158169804800 }, some { target := 892, numerator := 169414897572948522041344000 }, some { target := 893, numerator := 179095748862831294729420800 }, some { target := 894, numerator := 232340430957186544513843200 }, some { target := 895, numerator := 3112393689697311419216691200 }, some { target := 896, numerator := 5629415025066832318116659200 }, some { target := 897, numerator := 169414897572948522041344000 }, some { target := 898, numerator := 3112393689697311419216691200 }, some { target := 899, numerator := 183936174507772681073459200 }, some { target := 900, numerator := 183936174507772681073459200 }, some { target := 901, numerator := 179095748862831294729420800 }, some { target := 902, numerator := 179095748862831294729420800 }, some { target := 903, numerator := 5629415025066832318116659200 }, some { target := 904, numerator := 179095748862831294729420800 }, some { target := 905, numerator := 227500005312245158169804800 }, some { target := 906, numerator := 232340430957186544513843200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected ++ Left10.expected ++ Left11.expected ++ Left12.expected ++ Left13.expected ++ Left14.expected ++ Left15.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq, Left10.routed_eq, Left11.routed_eq, Left12.routed_eq, Left13.routed_eq, Left14.routed_eq, Left15.routed_eq]
  rfl

end Slot23

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent3
