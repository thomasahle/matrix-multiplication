import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk13Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 7, for region 1, branch 2,
parent 54; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot25

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨25, 9, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[24086361145344, 0, 233302254419968, 0, 0, 0, 0, 24086361145344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        0 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes_eq

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
  [some { target := 0, numerator := 61017371481871367800646270976 }, some { target := 2, numerator := 591018719664636302740603011072 }, some { target := 7, numerator := 61017371481871367800646270976 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq]
  rfl

end Slot25

namespace Slot26

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨26, 25, #[2199023255552, 2611340115968, 1992864825344, 20547123544064, 2473901162496, 1992864825344, 2473901162496, 2473901162496, 105965433126912, 2473901162496, 20547123544064, 105965433126912, 2199023255552, 2473901162496, 2473901162496, 2611340115968, 0, 0, 0], #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0]⟩

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
  [some { target := 80, numerator := 181338872942194376205926400 }, some { target := 81, numerator := 177560979755898660034969600 }, some { target := 82, numerator := 139782047892941498325401600 }, some { target := 83, numerator := 4393689775661917906822758400 }, some { target := 84, numerator := 139782047892941498325401600 }, some { target := 85, numerator := 139782047892941498325401600 }, some { target := 86, numerator := 143559941079237214496358400 }, some { target := 87, numerator := 143559941079237214496358400 }, some { target := 88, numerator := 2429185318788145497925222400 }, some { target := 89, numerator := 132226261520350065983488000 }, some { target := 90, numerator := 4393689775661917906822758400 }, some { target := 91, numerator := 2429185318788145497925222400 }, some { target := 92, numerator := 181338872942194376205926400 }, some { target := 93, numerator := 139782047892941498325401600 }, some { target := 94, numerator := 132226261520350065983488000 }, some { target := 95, numerator := 177560979755898660034969600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 115, numerator := 215339911618855821744537600 }, some { target := 116, numerator := 210853663460129658791526400 }, some { target := 117, numerator := 165991181872868029261414400 }, some { target := 118, numerator := 5217506608598527514352025600 }, some { target := 119, numerator := 165991181872868029261414400 }, some { target := 120, numerator := 165991181872868029261414400 }, some { target := 121, numerator := 170477430031594192214425600 }, some { target := 122, numerator := 170477430031594192214425600 }, some { target := 123, numerator := 2884657566060922778786201600 }, some { target := 124, numerator := 157018685555415703355392000 }, some { target := 125, numerator := 5217506608598527514352025600 }, some { target := 126, numerator := 2884657566060922778786201600 }, some { target := 127, numerator := 215339911618855821744537600 }, some { target := 128, numerator := 165991181872868029261414400 }, some { target := 129, numerator := 157018685555415703355392000 }, some { target := 130, numerator := 210853663460129658791526400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 176, numerator := 164338353603863653436620800 }, some { target := 177, numerator := 160914637903783160656691200 }, some { target := 178, numerator := 126677480902978232857395200 }, some { target := 179, numerator := 3981781359193613103058124800 }, some { target := 180, numerator := 126677480902978232857395200 }, some { target := 181, numerator := 126677480902978232857395200 }, some { target := 182, numerator := 130101196603058725637324800 }, some { target := 183, numerator := 130101196603058725637324800 }, some { target := 184, numerator := 2201449195151756857494732800 }, some { target := 185, numerator := 119830049502817247297536000 }, some { target := 186, numerator := 3981781359193613103058124800 }, some { target := 187, numerator := 2201449195151756857494732800 }, some { target := 188, numerator := 164338353603863653436620800 }, some { target := 189, numerator := 126677480902978232857395200 }, some { target := 190, numerator := 119830049502817247297536000 }, some { target := 191, numerator := 160914637903783160656691200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 211, numerator := 1694385094053628702674124800 }, some { target := 212, numerator := 1659085404594178104701747200 }, some { target := 213, numerator := 1306088509999672124977971200 }, some { target := 214, numerator := 41053538841341045441875148800 }, some { target := 215, numerator := 1306088509999672124977971200 }, some { target := 216, numerator := 1306088509999672124977971200 }, some { target := 217, numerator := 1341388199459122722950348800 }, some { target := 218, numerator := 1341388199459122722950348800 }, some { target := 219, numerator := 22697700322426734496238796800 }, some { target := 220, numerator := 1235489131080770929033216000 }, some { target := 221, numerator := 41053538841341045441875148800 }, some { target := 222, numerator := 22697700322426734496238796800 }, some { target := 223, numerator := 1694385094053628702674124800 }, some { target := 224, numerator := 1306088509999672124977971200 }, some { target := 225, numerator := 1235489131080770929033216000 }, some { target := 226, numerator := 1659085404594178104701747200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 237, numerator := 204006232059968673231667200 }, some { target := 238, numerator := 199756102225385992539340800 }, some { target := 239, numerator := 157254803879559185616076800 }, some { target := 240, numerator := 4942900997619657645175603200 }, some { target := 241, numerator := 157254803879559185616076800 }, some { target := 242, numerator := 157254803879559185616076800 }, some { target := 243, numerator := 161504933714141866308403200 }, some { target := 244, numerator := 161504933714141866308403200 }, some { target := 245, numerator := 2732833483636663685165875200 }, some { target := 246, numerator := 148754544210393824231424000 }, some { target := 247, numerator := 4942900997619657645175603200 }, some { target := 248, numerator := 2732833483636663685165875200 }, some { target := 249, numerator := 204006232059968673231667200 }, some { target := 250, numerator := 157254803879559185616076800 }, some { target := 251, numerator := 148754544210393824231424000 }, some { target := 252, numerator := 199756102225385992539340800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 286, numerator := 164338353603863653436620800 }, some { target := 287, numerator := 160914637903783160656691200 }, some { target := 288, numerator := 126677480902978232857395200 }, some { target := 289, numerator := 3981781359193613103058124800 }, some { target := 290, numerator := 126677480902978232857395200 }, some { target := 291, numerator := 126677480902978232857395200 }, some { target := 292, numerator := 130101196603058725637324800 }, some { target := 293, numerator := 130101196603058725637324800 }, some { target := 294, numerator := 2201449195151756857494732800 }, some { target := 295, numerator := 119830049502817247297536000 }, some { target := 296, numerator := 3981781359193613103058124800 }, some { target := 297, numerator := 2201449195151756857494732800 }, some { target := 298, numerator := 164338353603863653436620800 }, some { target := 299, numerator := 126677480902978232857395200 }, some { target := 300, numerator := 119830049502817247297536000 }, some { target := 301, numerator := 160914637903783160656691200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 312, numerator := 204006232059968673231667200 }, some { target := 313, numerator := 199756102225385992539340800 }, some { target := 314, numerator := 157254803879559185616076800 }, some { target := 315, numerator := 4942900997619657645175603200 }, some { target := 316, numerator := 157254803879559185616076800 }, some { target := 317, numerator := 157254803879559185616076800 }, some { target := 318, numerator := 161504933714141866308403200 }, some { target := 319, numerator := 161504933714141866308403200 }, some { target := 320, numerator := 2732833483636663685165875200 }, some { target := 321, numerator := 148754544210393824231424000 }, some { target := 322, numerator := 4942900997619657645175603200 }, some { target := 323, numerator := 2732833483636663685165875200 }, some { target := 324, numerator := 204006232059968673231667200 }, some { target := 325, numerator := 157254803879559185616076800 }, some { target := 326, numerator := 148754544210393824231424000 }, some { target := 327, numerator := 199756102225385992539340800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 204006232059968673231667200 }, some { target := 393, numerator := 199756102225385992539340800 }, some { target := 394, numerator := 157254803879559185616076800 }, some { target := 395, numerator := 4942900997619657645175603200 }, some { target := 396, numerator := 157254803879559185616076800 }, some { target := 397, numerator := 157254803879559185616076800 }, some { target := 398, numerator := 161504933714141866308403200 }, some { target := 399, numerator := 161504933714141866308403200 }, some { target := 400, numerator := 2732833483636663685165875200 }, some { target := 401, numerator := 148754544210393824231424000 }, some { target := 402, numerator := 4942900997619657645175603200 }, some { target := 403, numerator := 2732833483636663685165875200 }, some { target := 404, numerator := 204006232059968673231667200 }, some { target := 405, numerator := 157254803879559185616076800 }, some { target := 406, numerator := 148754544210393824231424000 }, some { target := 407, numerator := 199756102225385992539340800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 427, numerator := 8738266939901991503423078400 }, some { target := 428, numerator := 8556219711987366680435097600 }, some { target := 429, numerator := 6735747432841118450555289600 }, some { target := 430, numerator := 211720926064708669135021670400 }, some { target := 431, numerator := 6735747432841118450555289600 }, some { target := 432, numerator := 6735747432841118450555289600 }, some { target := 433, numerator := 6917794660755743273543270400 }, some { target := 434, numerator := 6917794660755743273543270400 }, some { target := 435, numerator := 117056367549103761181271654400 }, some { target := 436, numerator := 6371652977011868804579328000 }, some { target := 437, numerator := 211720926064708669135021670400 }, some { target := 438, numerator := 117056367549103761181271654400 }, some { target := 439, numerator := 8738266939901991503423078400 }, some { target := 440, numerator := 6735747432841118450555289600 }, some { target := 441, numerator := 6371652977011868804579328000 }, some { target := 442, numerator := 8556219711987366680435097600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 453, numerator := 204006232059968673231667200 }, some { target := 454, numerator := 199756102225385992539340800 }, some { target := 455, numerator := 157254803879559185616076800 }, some { target := 456, numerator := 4942900997619657645175603200 }, some { target := 457, numerator := 157254803879559185616076800 }, some { target := 458, numerator := 157254803879559185616076800 }, some { target := 459, numerator := 161504933714141866308403200 }, some { target := 460, numerator := 161504933714141866308403200 }, some { target := 461, numerator := 2732833483636663685165875200 }, some { target := 462, numerator := 148754544210393824231424000 }, some { target := 463, numerator := 4942900997619657645175603200 }, some { target := 464, numerator := 2732833483636663685165875200 }, some { target := 465, numerator := 204006232059968673231667200 }, some { target := 466, numerator := 157254803879559185616076800 }, some { target := 467, numerator := 148754544210393824231424000 }, some { target := 468, numerator := 199756102225385992539340800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 502, numerator := 1694385094053628702674124800 }, some { target := 503, numerator := 1659085404594178104701747200 }, some { target := 504, numerator := 1306088509999672124977971200 }, some { target := 505, numerator := 41053538841341045441875148800 }, some { target := 506, numerator := 1306088509999672124977971200 }, some { target := 507, numerator := 1306088509999672124977971200 }, some { target := 508, numerator := 1341388199459122722950348800 }, some { target := 509, numerator := 1341388199459122722950348800 }, some { target := 510, numerator := 22697700322426734496238796800 }, some { target := 511, numerator := 1235489131080770929033216000 }, some { target := 512, numerator := 41053538841341045441875148800 }, some { target := 513, numerator := 22697700322426734496238796800 }, some { target := 514, numerator := 1694385094053628702674124800 }, some { target := 515, numerator := 1306088509999672124977971200 }, some { target := 516, numerator := 1235489131080770929033216000 }, some { target := 517, numerator := 1659085404594178104701747200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 528, numerator := 8738266939901991503423078400 }, some { target := 529, numerator := 8556219711987366680435097600 }, some { target := 530, numerator := 6735747432841118450555289600 }, some { target := 531, numerator := 211720926064708669135021670400 }, some { target := 532, numerator := 6735747432841118450555289600 }, some { target := 533, numerator := 6735747432841118450555289600 }, some { target := 534, numerator := 6917794660755743273543270400 }, some { target := 535, numerator := 6917794660755743273543270400 }, some { target := 536, numerator := 117056367549103761181271654400 }, some { target := 537, numerator := 6371652977011868804579328000 }, some { target := 538, numerator := 211720926064708669135021670400 }, some { target := 539, numerator := 117056367549103761181271654400 }, some { target := 540, numerator := 8738266939901991503423078400 }, some { target := 541, numerator := 6735747432841118450555289600 }, some { target := 542, numerator := 6371652977011868804579328000 }, some { target := 543, numerator := 8556219711987366680435097600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 573, numerator := 181338872942194376205926400 }, some { target := 574, numerator := 177560979755898660034969600 }, some { target := 575, numerator := 139782047892941498325401600 }, some { target := 576, numerator := 4393689775661917906822758400 }, some { target := 577, numerator := 139782047892941498325401600 }, some { target := 578, numerator := 139782047892941498325401600 }, some { target := 579, numerator := 143559941079237214496358400 }, some { target := 580, numerator := 143559941079237214496358400 }, some { target := 581, numerator := 2429185318788145497925222400 }, some { target := 582, numerator := 132226261520350065983488000 }, some { target := 583, numerator := 4393689775661917906822758400 }, some { target := 584, numerator := 2429185318788145497925222400 }, some { target := 585, numerator := 181338872942194376205926400 }, some { target := 586, numerator := 139782047892941498325401600 }, some { target := 587, numerator := 132226261520350065983488000 }, some { target := 588, numerator := 177560979755898660034969600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 642, numerator := 204006232059968673231667200 }, some { target := 643, numerator := 199756102225385992539340800 }, some { target := 644, numerator := 157254803879559185616076800 }, some { target := 645, numerator := 4942900997619657645175603200 }, some { target := 646, numerator := 157254803879559185616076800 }, some { target := 647, numerator := 157254803879559185616076800 }, some { target := 648, numerator := 161504933714141866308403200 }, some { target := 649, numerator := 161504933714141866308403200 }, some { target := 650, numerator := 2732833483636663685165875200 }, some { target := 651, numerator := 148754544210393824231424000 }, some { target := 652, numerator := 4942900997619657645175603200 }, some { target := 653, numerator := 2732833483636663685165875200 }, some { target := 654, numerator := 204006232059968673231667200 }, some { target := 655, numerator := 157254803879559185616076800 }, some { target := 656, numerator := 148754544210393824231424000 }, some { target := 657, numerator := 199756102225385992539340800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 668, numerator := 204006232059968673231667200 }, some { target := 669, numerator := 199756102225385992539340800 }, some { target := 670, numerator := 157254803879559185616076800 }, some { target := 671, numerator := 4942900997619657645175603200 }, some { target := 672, numerator := 157254803879559185616076800 }, some { target := 673, numerator := 157254803879559185616076800 }, some { target := 674, numerator := 161504933714141866308403200 }, some { target := 675, numerator := 161504933714141866308403200 }, some { target := 676, numerator := 2732833483636663685165875200 }, some { target := 677, numerator := 148754544210393824231424000 }, some { target := 678, numerator := 4942900997619657645175603200 }, some { target := 679, numerator := 2732833483636663685165875200 }, some { target := 680, numerator := 204006232059968673231667200 }, some { target := 681, numerator := 157254803879559185616076800 }, some { target := 682, numerator := 148754544210393824231424000 }, some { target := 683, numerator := 199756102225385992539340800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 713, numerator := 215339911618855821744537600 }, some { target := 714, numerator := 210853663460129658791526400 }, some { target := 715, numerator := 165991181872868029261414400 }, some { target := 716, numerator := 5217506608598527514352025600 }, some { target := 717, numerator := 165991181872868029261414400 }, some { target := 718, numerator := 165991181872868029261414400 }, some { target := 719, numerator := 170477430031594192214425600 }, some { target := 720, numerator := 170477430031594192214425600 }, some { target := 721, numerator := 2884657566060922778786201600 }, some { target := 722, numerator := 157018685555415703355392000 }, some { target := 723, numerator := 5217506608598527514352025600 }, some { target := 724, numerator := 2884657566060922778786201600 }, some { target := 725, numerator := 215339911618855821744537600 }, some { target := 726, numerator := 165991181872868029261414400 }, some { target := 727, numerator := 157018685555415703355392000 }, some { target := 728, numerator := 210853663460129658791526400 }]

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

end Slot26

namespace Slot27

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨27, 145, #[50466754920448, 0, 0, 180541483646976, 0, 50466738143232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

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
  [some { target := 26, numerator := 3017202621906511684027023360 }, some { target := 27, numerator := 80458736584173644907387289600 }, some { target := 28, numerator := 76938666858616047942689095680 }, some { target := 29, numerator := 2514335518255426403355852800 }, some { target := 30, numerator := 78950135273220389065373777920 }, some { target := 31, numerator := 2514335518255426403355852800 }, some { target := 32, numerator := 76938666858616047942689095680 }, some { target := 33, numerator := 43749438017644419418391838720 }, some { target := 34, numerator := 78950135273220389065373777920 }, some { target := 35, numerator := 1232527271048810022925039042560 }, some { target := 36, numerator := 48275241950504186944432373760 }, some { target := 37, numerator := 80458736584173644907387289600 }, some { target := 38, numerator := 76938666858616047942689095680 }, some { target := 39, numerator := 2514335518255426403355852800 }, some { target := 40, numerator := 48275241950504186944432373760 }, some { target := 41, numerator := 2514335518255426403355852800 }, some { target := 42, numerator := 77441533962267133223360266240 }, some { target := 43, numerator := 43749438017644419418391838720 }, some { target := 44, numerator := 3017202621906511684027023360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 157, numerator := 10793843168264323751812792320 }, some { target := 158, numerator := 287835817820381966715007795200 }, some { target := 159, numerator := 275243000790740255671226204160 }, some { target := 160, numerator := 8994869306886936459843993600 }, some { target := 161, numerator := 282438896236249804839101399040 }, some { target := 162, numerator := 8994869306886936459843993600 }, some { target := 163, numerator := 275243000790740255671226204160 }, some { target := 164, numerator := 156510725939832694401285488640 }, some { target := 165, numerator := 282438896236249804839101399040 }, some { target := 166, numerator := 4409284934235976252615525662720 }, some { target := 167, numerator := 172701490692229180029004677120 }, some { target := 168, numerator := 287835817820381966715007795200 }, some { target := 169, numerator := 275243000790740255671226204160 }, some { target := 170, numerator := 8994869306886936459843993600 }, some { target := 171, numerator := 172701490692229180029004677120 }, some { target := 172, numerator := 8994869306886936459843993600 }, some { target := 173, numerator := 277041974652117642963195002880 }, some { target := 174, numerator := 156510725939832694401285488640 }, some { target := 175, numerator := 10793843168264323751812792320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 3017201618864802676070154240 }, some { target := 268, numerator := 80458709836394738028537446400 }, some { target := 269, numerator := 76938641281052468239788933120 }, some { target := 270, numerator := 2514334682387335563391795200 }, some { target := 271, numerator := 78950109026962336690502369280 }, some { target := 272, numerator := 2514334682387335563391795200 }, some { target := 273, numerator := 76938641281052468239788933120 }, some { target := 274, numerator := 43749423473539638803017236480 }, some { target := 275, numerator := 78950109026962336690502369280 }, some { target := 276, numerator := 1232526861306271893174658007040 }, some { target := 277, numerator := 48275225901836842817122467840 }, some { target := 278, numerator := 80458709836394738028537446400 }, some { target := 279, numerator := 76938641281052468239788933120 }, some { target := 280, numerator := 2514334682387335563391795200 }, some { target := 281, numerator := 48275225901836842817122467840 }, some { target := 282, numerator := 2514334682387335563391795200 }, some { target := 283, numerator := 77441508217529935352467292160 }, some { target := 284, numerator := 43749423473539638803017236480 }, some { target := 285, numerator := 3017201618864802676070154240 }]

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

end Slot27

namespace Slot28

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨28, 63, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  [some { target := 10, numerator := 21325451458002058641816944640 }, some { target := 11, numerator := 21934750071087831745868857344 }, some { target := 12, numerator := 21325451458002058641816944640 }, some { target := 13, numerator := 18888257005658966225609293824 }, some { target := 14, numerator := 884092287587456773979325333504 }, some { target := 15, numerator := 240672952168880376100505518080 }, some { target := 16, numerator := 21934750071087831745868857344 }, some { target := 17, numerator := 884092287587456773979325333504 }, some { target := 18, numerator := 21325451458002058641816944640 }, some { target := 19, numerator := 21325451458002058641816944640 }, some { target := 20, numerator := 18278958392573193121557381120 }, some { target := 21, numerator := 21325451458002058641816944640 }, some { target := 22, numerator := 240672952168880376100505518080 }, some { target := 23, numerator := 18278958392573193121557381120 }, some { target := 24, numerator := 21325451458002058641816944640 }, some { target := 25, numerator := 18888257005658966225609293824 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 141, numerator := 21325451458002058641816944640 }, some { target := 142, numerator := 21934750071087831745868857344 }, some { target := 143, numerator := 21325451458002058641816944640 }, some { target := 144, numerator := 18888257005658966225609293824 }, some { target := 145, numerator := 884092287587456773979325333504 }, some { target := 146, numerator := 240672952168880376100505518080 }, some { target := 147, numerator := 21934750071087831745868857344 }, some { target := 148, numerator := 884092287587456773979325333504 }, some { target := 149, numerator := 21325451458002058641816944640 }, some { target := 150, numerator := 21325451458002058641816944640 }, some { target := 151, numerator := 18278958392573193121557381120 }, some { target := 152, numerator := 21325451458002058641816944640 }, some { target := 153, numerator := 240672952168880376100505518080 }, some { target := 154, numerator := 18278958392573193121557381120 }, some { target := 155, numerator := 21325451458002058641816944640 }, some { target := 156, numerator := 18888257005658966225609293824 }]

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

end Slot28

namespace Slot29

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨29, 3, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        0 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes_eq

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
  [some { target := 0, numerator := 1450710983537555009647411200 }, some { target := 1, numerator := 29072248110092602393334120448 }, some { target := 2, numerator := 48801917486203350524538912768 }, some { target := 3, numerator := 46828950548592275711418433536 }, some { target := 4, numerator := 1450710983537555009647411200 }, some { target := 5, numerator := 46828950548592275711418433536 }, some { target := 6, numerator := 31277328805069686007998185472 }, some { target := 7, numerator := 1508739422879057210033307648 }, some { target := 8, numerator := 29072248110092602393334120448 }, some { target := 9, numerator := 1392682544196052809261514752 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq]
  rfl

end Slot29

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent0
