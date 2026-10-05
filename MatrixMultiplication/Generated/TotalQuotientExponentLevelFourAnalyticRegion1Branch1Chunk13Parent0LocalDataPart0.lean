import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk13Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 54; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 3, #[1649267441664, 34428457844736, 1786706395136, 37039797960704, 55456617725952, 1717986918400, 55456617725952, 57793079934976, 34428457844736, 1717986918400, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2473901162496, 2817498546176, 2199023255552, 29480655519744, 2611340115968, 2199023255552, 2611340115968, 2542620639232, 96069828476928, 2542620639232, 29480655519744, 96069828476928, 2473901162496, 2542620639232, 2542620639232, 2817498546176, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 35, numerator := 12240373923598120393900032 }, some { target := 36, numerator := 13940425857431192670830592 }, some { target := 37, numerator := 10880332376531662572355584 }, some { target := 38, numerator := 145864455922877601360642048 }, some { target := 39, numerator := 12920394697131349304672256 }, some { target := 40, numerator := 10880332376531662572355584 }, some { target := 41, numerator := 12920394697131349304672256 }, some { target := 42, numerator := 12580384310364734849286144 }, some { target := 43, numerator := 475334520699727008629784576 }, some { target := 44, numerator := 12580384310364734849286144 }, some { target := 45, numerator := 145864455922877601360642048 }, some { target := 46, numerator := 475334520699727008629784576 }, some { target := 47, numerator := 12240373923598120393900032 }, some { target := 48, numerator := 12580384310364734849286144 }, some { target := 49, numerator := 12580384310364734849286144 }, some { target := 50, numerator := 13940425857431192670830592 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 70, numerator := 255517805655110763222663168 }, some { target := 71, numerator := 291006389773876147003588608 }, some { target := 72, numerator := 227126938360098456197922816 }, some { target := 73, numerator := 3044920517390069928403402752 }, some { target := 74, numerator := 269713239302616916735033344 }, some { target := 75, numerator := 227126938360098456197922816 }, some { target := 76, numerator := 269713239302616916735033344 }, some { target := 77, numerator := 262615522478863839978848256 }, some { target := 78, numerator := 9922608119606801305146753024 }, some { target := 79, numerator := 262615522478863839978848256 }, some { target := 80, numerator := 3044920517390069928403402752 }, some { target := 81, numerator := 9922608119606801305146753024 }, some { target := 82, numerator := 255517805655110763222663168 }, some { target := 83, numerator := 262615522478863839978848256 }, some { target := 84, numerator := 262615522478863839978848256 }, some { target := 85, numerator := 291006389773876147003588608 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 96, numerator := 13260405083897963760058368 }, some { target := 97, numerator := 15102128012217125393399808 }, some { target := 98, numerator := 11787026741242634453385216 }, some { target := 99, numerator := 158019827249784068140695552 }, some { target := 100, numerator := 13997094255225628413394944 }, some { target := 101, numerator := 11787026741242634453385216 }, some { target := 102, numerator := 13997094255225628413394944 }, some { target := 103, numerator := 13628749669561796086726656 }, some { target := 104, numerator := 514945730758037592682266624 }, some { target := 105, numerator := 13628749669561796086726656 }, some { target := 106, numerator := 158019827249784068140695552 }, some { target := 107, numerator := 514945730758037592682266624 }, some { target := 108, numerator := 13260405083897963760058368 }, some { target := 109, numerator := 13628749669561796086726656 }, some { target := 110, numerator := 13628749669561796086726656 }, some { target := 111, numerator := 15102128012217125393399808 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 145, numerator := 274898397700807787179671552 }, some { target := 146, numerator := 313078730714808868732403712 }, some { target := 147, numerator := 244354131289606921937485824 }, some { target := 148, numerator := 3275872572601292797224419328 }, some { target := 149, numerator := 290170530906408219800764416 }, some { target := 150, numerator := 244354131289606921937485824 }, some { target := 151, numerator := 290170530906408219800764416 }, some { target := 152, numerator := 282534464303608003490217984 }, some { target := 153, numerator := 10675221110714702402143911936 }, some { target := 154, numerator := 282534464303608003490217984 }, some { target := 155, numerator := 3275872572601292797224419328 }, some { target := 156, numerator := 10675221110714702402143911936 }, some { target := 157, numerator := 274898397700807787179671552 }, some { target := 158, numerator := 282534464303608003490217984 }, some { target := 159, numerator := 282534464303608003490217984 }, some { target := 160, numerator := 313078730714808868732403712 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 171, numerator := 411582573180986798244888576 }, some { target := 172, numerator := 468746819456123853556678656 }, some { target := 173, numerator := 365851176160877153995456512 }, some { target := 174, numerator := 4904692330406759345751588864 }, some { target := 175, numerator := 434448271691041620369604608 }, some { target := 176, numerator := 365851176160877153995456512 }, some { target := 177, numerator := 434448271691041620369604608 }, some { target := 178, numerator := 423015422436014209307246592 }, some { target := 179, numerator := 15983123258528320665176506368 }, some { target := 180, numerator := 423015422436014209307246592 }, some { target := 181, numerator := 4904692330406759345751588864 }, some { target := 182, numerator := 15983123258528320665176506368 }, some { target := 183, numerator := 411582573180986798244888576 }, some { target := 184, numerator := 423015422436014209307246592 }, some { target := 185, numerator := 423015422436014209307246592 }, some { target := 186, numerator := 468746819456123853556678656 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 12750389503748042076979200 }, some { target := 217, numerator := 14521276934824159032115200 }, some { target := 218, numerator := 11333679558887148512870400 }, some { target := 219, numerator := 151942141586330834750668800 }, some { target := 220, numerator := 13458744476178488859033600 }, some { target := 221, numerator := 11333679558887148512870400 }, some { target := 222, numerator := 13458744476178488859033600 }, some { target := 223, numerator := 13104566989963265468006400 }, some { target := 224, numerator := 495140125728882300656025600 }, some { target := 225, numerator := 13104566989963265468006400 }, some { target := 226, numerator := 151942141586330834750668800 }, some { target := 227, numerator := 495140125728882300656025600 }, some { target := 228, numerator := 12750389503748042076979200 }, some { target := 229, numerator := 13104566989963265468006400 }, some { target := 230, numerator := 13104566989963265468006400 }, some { target := 231, numerator := 14521276934824159032115200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 285, numerator := 411582573180986798244888576 }, some { target := 286, numerator := 468746819456123853556678656 }, some { target := 287, numerator := 365851176160877153995456512 }, some { target := 288, numerator := 4904692330406759345751588864 }, some { target := 289, numerator := 434448271691041620369604608 }, some { target := 290, numerator := 365851176160877153995456512 }, some { target := 291, numerator := 434448271691041620369604608 }, some { target := 292, numerator := 423015422436014209307246592 }, some { target := 293, numerator := 15983123258528320665176506368 }, some { target := 294, numerator := 423015422436014209307246592 }, some { target := 295, numerator := 4904692330406759345751588864 }, some { target := 296, numerator := 15983123258528320665176506368 }, some { target := 297, numerator := 411582573180986798244888576 }, some { target := 298, numerator := 423015422436014209307246592 }, some { target := 299, numerator := 423015422436014209307246592 }, some { target := 300, numerator := 468746819456123853556678656 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 311, numerator := 428923102906084135469580288 }, some { target := 312, numerator := 488495756087484709840355328 }, some { target := 313, numerator := 381264980360963675972960256 }, some { target := 314, numerator := 5111333642964169281012498432 }, some { target := 315, numerator := 452752164178644365217890304 }, some { target := 316, numerator := 381264980360963675972960256 }, some { target := 317, numerator := 452752164178644365217890304 }, some { target := 318, numerator := 440837633542364250343735296 }, some { target := 319, numerator := 16656513829519600594068701184 }, some { target := 320, numerator := 440837633542364250343735296 }, some { target := 321, numerator := 5111333642964169281012498432 }, some { target := 322, numerator := 16656513829519600594068701184 }, some { target := 323, numerator := 428923102906084135469580288 }, some { target := 324, numerator := 440837633542364250343735296 }, some { target := 325, numerator := 440837633542364250343735296 }, some { target := 326, numerator := 488495756087484709840355328 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 356, numerator := 255517805655110763222663168 }, some { target := 357, numerator := 291006389773876147003588608 }, some { target := 358, numerator := 227126938360098456197922816 }, some { target := 359, numerator := 3044920517390069928403402752 }, some { target := 360, numerator := 269713239302616916735033344 }, some { target := 361, numerator := 227126938360098456197922816 }, some { target := 362, numerator := 269713239302616916735033344 }, some { target := 363, numerator := 262615522478863839978848256 }, some { target := 364, numerator := 9922608119606801305146753024 }, some { target := 365, numerator := 262615522478863839978848256 }, some { target := 366, numerator := 3044920517390069928403402752 }, some { target := 367, numerator := 9922608119606801305146753024 }, some { target := 368, numerator := 255517805655110763222663168 }, some { target := 369, numerator := 262615522478863839978848256 }, some { target := 370, numerator := 262615522478863839978848256 }, some { target := 371, numerator := 291006389773876147003588608 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 427, numerator := 12750389503748042076979200 }, some { target := 428, numerator := 14521276934824159032115200 }, some { target := 429, numerator := 11333679558887148512870400 }, some { target := 430, numerator := 151942141586330834750668800 }, some { target := 431, numerator := 13458744476178488859033600 }, some { target := 432, numerator := 11333679558887148512870400 }, some { target := 433, numerator := 13458744476178488859033600 }, some { target := 434, numerator := 13104566989963265468006400 }, some { target := 435, numerator := 495140125728882300656025600 }, some { target := 436, numerator := 13104566989963265468006400 }, some { target := 437, numerator := 151942141586330834750668800 }, some { target := 438, numerator := 495140125728882300656025600 }, some { target := 439, numerator := 12750389503748042076979200 }, some { target := 440, numerator := 13104566989963265468006400 }, some { target := 441, numerator := 13104566989963265468006400 }, some { target := 442, numerator := 14521276934824159032115200 }]

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

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 60, #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0], #[49796387700736, 0, 0, 181882218086400, 0, 49796370923520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

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
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 86, numerator := 6364885973415869192664514560 }, some { target := 89, numerator := 23247862589333624422662144000 }, some { target := 91, numerator := 6364883828981870623929139200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 112, numerator := 7186161582888884572363161600 }, some { target := 115, numerator := 26247586794408930799779840000 }, some { target := 117, numerator := 7186159161753724897984512000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 161, numerator := 6159567071047615347739852800 }, some { target := 164, numerator := 22497931538064797828382720000 }, some { target := 166, numerator := 6159564995788907055415296000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 187, numerator := 81100966435460268745241395200 }, some { target := 190, numerator := 296222765251186504740372480000 }, some { target := 192, numerator := 81100939111220609562968064000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 201, numerator := 7186161582888884572363161600 }, some { target := 204, numerator := 26247586794408930799779840000 }, some { target := 206, numerator := 7186159161753724897984512000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 232, numerator := 6159567071047615347739852800 }, some { target := 235, numerator := 22497931538064797828382720000 }, some { target := 237, numerator := 6159564995788907055415296000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 246, numerator := 7186161582888884572363161600 }, some { target := 249, numerator := 26247586794408930799779840000 }, some { target := 251, numerator := 7186159161753724897984512000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 301, numerator := 7186161582888884572363161600 }, some { target := 304, numerator := 26247586794408930799779840000 }, some { target := 306, numerator := 7186159161753724897984512000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 327, numerator := 297917727336336328985684213760 }, some { target := 330, numerator := 1088149955391067388299444224000 }, some { target := 332, numerator := 297917626962990137913586483200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 341, numerator := 7391480485257138417287823360 }, some { target := 344, numerator := 26997517845677757394059264000 }, some { target := 346, numerator := 7391477994946688466498355200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 372, numerator := 81100966435460268745241395200 }, some { target := 375, numerator := 296222765251186504740372480000 }, some { target := 377, numerator := 81100939111220609562968064000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 386, numerator := 297917727336336328985684213760 }, some { target := 389, numerator := 1088149955391067388299444224000 }, some { target := 391, numerator := 297917626962990137913586483200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 406, numerator := 6364885973415869192664514560 }, some { target := 409, numerator := 23247862589333624422662144000 }, some { target := 411, numerator := 6364883828981870623929139200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 443, numerator := 7186161582888884572363161600 }, some { target := 446, numerator := 26247586794408930799779840000 }, some { target := 448, numerator := 7186159161753724897984512000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 457, numerator := 7391480485257138417287823360 }, some { target := 460, numerator := 26997517845677757394059264000 }, some { target := 462, numerator := 7391477994946688466498355200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 477, numerator := 7186161582888884572363161600 }, some { target := 480, numerator := 26247586794408930799779840000 }, some { target := 482, numerator := 7186159161753724897984512000 }]

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

end Slot1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent0
