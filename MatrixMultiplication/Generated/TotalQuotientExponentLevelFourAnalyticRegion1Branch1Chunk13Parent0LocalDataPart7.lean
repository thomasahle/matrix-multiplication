import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk13Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 7, for region 1, branch 1,
parent 54; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot28

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨28, 63, #[49796387700736, 0, 0, 181882218086400, 0, 49796370923520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0]⟩

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
  [some { target := 35, numerator := 6683130272086662652297740288 }, some { target := 36, numerator := 7545469662033328800981319680 }, some { target := 37, numerator := 6467545424599996115126845440 }, some { target := 38, numerator := 85156014757233282182503464960 }, some { target := 39, numerator := 7545469662033328800981319680 }, some { target := 40, numerator := 6467545424599996115126845440 }, some { target := 41, numerator := 7545469662033328800981319680 }, some { target := 42, numerator := 7545469662033328800981319680 }, some { target := 43, numerator := 312813613703153145434968424448 }, some { target := 44, numerator := 7761054509519995338152214528 }, some { target := 45, numerator := 85156014757233282182503464960 }, some { target := 46, numerator := 312813613703153145434968424448 }, some { target := 47, numerator := 6683130272086662652297740288 }, some { target := 48, numerator := 7545469662033328800981319680 }, some { target := 49, numerator := 7761054509519995338152214528 }, some { target := 50, numerator := 7545469662033328800981319680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 145, numerator := 24410255718800305643795251200 }, some { target := 146, numerator := 27559966134129377339768832000 }, some { target := 147, numerator := 23622828114968037719801856000 }, some { target := 148, numerator := 311033903513745829977391104000 }, some { target := 149, numerator := 27559966134129377339768832000 }, some { target := 150, numerator := 23622828114968037719801856000 }, some { target := 151, numerator := 27559966134129377339768832000 }, some { target := 152, numerator := 27559966134129377339768832000 }, some { target := 153, numerator := 1142557453160620757714416435200 }, some { target := 154, numerator := 28347393737961645263762227200 }, some { target := 155, numerator := 311033903513745829977391104000 }, some { target := 156, numerator := 1142557453160620757714416435200 }, some { target := 157, numerator := 24410255718800305643795251200 }, some { target := 158, numerator := 27559966134129377339768832000 }, some { target := 159, numerator := 28347393737961645263762227200 }, some { target := 160, numerator := 27559966134129377339768832000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 6683128020430964155125596160 }, some { target := 217, numerator := 7545467119841411142883737600 }, some { target := 218, numerator := 6467543245578352408186060800 }, some { target := 219, numerator := 85155986066781640041116467200 }, some { target := 220, numerator := 7545467119841411142883737600 }, some { target := 221, numerator := 6467543245578352408186060800 }, some { target := 222, numerator := 7545467119841411142883737600 }, some { target := 223, numerator := 7545467119841411142883737600 }, some { target := 224, numerator := 312813508311139644809265807360 }, some { target := 225, numerator := 7761051894694022889823272960 }, some { target := 226, numerator := 85155986066781640041116467200 }, some { target := 227, numerator := 312813508311139644809265807360 }, some { target := 228, numerator := 6683128020430964155125596160 }, some { target := 229, numerator := 7545467119841411142883737600 }, some { target := 230, numerator := 7761051894694022889823272960 }, some { target := 231, numerator := 7545467119841411142883737600 }]

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

end Slot28

namespace Slot29

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨29, 3, #[2473901162496, 2817498546176, 2199023255552, 29480655519744, 2611340115968, 2199023255552, 2611340115968, 2542620639232, 96069828476928, 2542620639232, 29480655519744, 96069828476928, 2473901162496, 2542620639232, 2542620639232, 2817498546176, 0, 0, 0], #[1649267441664, 34428457844736, 1786706395136, 37039797960704, 55456617725952, 1717986918400, 55456617725952, 57793079934976, 34428457844736, 1717986918400, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 86, numerator := 12240373923598120393900032 }, some { target := 87, numerator := 255517805655110763222663168 }, some { target := 88, numerator := 13260405083897963760058368 }, some { target := 89, numerator := 274898397700807787179671552 }, some { target := 90, numerator := 411582573180986798244888576 }, some { target := 91, numerator := 12750389503748042076979200 }, some { target := 92, numerator := 411582573180986798244888576 }, some { target := 93, numerator := 428923102906084135469580288 }, some { target := 94, numerator := 255517805655110763222663168 }, some { target := 95, numerator := 12750389503748042076979200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 112, numerator := 13940425857431192670830592 }, some { target := 113, numerator := 291006389773876147003588608 }, some { target := 114, numerator := 15102128012217125393399808 }, some { target := 115, numerator := 313078730714808868732403712 }, some { target := 116, numerator := 468746819456123853556678656 }, some { target := 117, numerator := 14521276934824159032115200 }, some { target := 118, numerator := 468746819456123853556678656 }, some { target := 119, numerator := 488495756087484709840355328 }, some { target := 120, numerator := 291006389773876147003588608 }, some { target := 121, numerator := 14521276934824159032115200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 161, numerator := 10880332376531662572355584 }, some { target := 162, numerator := 227126938360098456197922816 }, some { target := 163, numerator := 11787026741242634453385216 }, some { target := 164, numerator := 244354131289606921937485824 }, some { target := 165, numerator := 365851176160877153995456512 }, some { target := 166, numerator := 11333679558887148512870400 }, some { target := 167, numerator := 365851176160877153995456512 }, some { target := 168, numerator := 381264980360963675972960256 }, some { target := 169, numerator := 227126938360098456197922816 }, some { target := 170, numerator := 11333679558887148512870400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 187, numerator := 145864455922877601360642048 }, some { target := 188, numerator := 3044920517390069928403402752 }, some { target := 189, numerator := 158019827249784068140695552 }, some { target := 190, numerator := 3275872572601292797224419328 }, some { target := 191, numerator := 4904692330406759345751588864 }, some { target := 192, numerator := 151942141586330834750668800 }, some { target := 193, numerator := 4904692330406759345751588864 }, some { target := 194, numerator := 5111333642964169281012498432 }, some { target := 195, numerator := 3044920517390069928403402752 }, some { target := 196, numerator := 151942141586330834750668800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 201, numerator := 12920394697131349304672256 }, some { target := 202, numerator := 269713239302616916735033344 }, some { target := 203, numerator := 13997094255225628413394944 }, some { target := 204, numerator := 290170530906408219800764416 }, some { target := 205, numerator := 434448271691041620369604608 }, some { target := 206, numerator := 13458744476178488859033600 }, some { target := 207, numerator := 434448271691041620369604608 }, some { target := 208, numerator := 452752164178644365217890304 }, some { target := 209, numerator := 269713239302616916735033344 }, some { target := 210, numerator := 13458744476178488859033600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 232, numerator := 10880332376531662572355584 }, some { target := 233, numerator := 227126938360098456197922816 }, some { target := 234, numerator := 11787026741242634453385216 }, some { target := 235, numerator := 244354131289606921937485824 }, some { target := 236, numerator := 365851176160877153995456512 }, some { target := 237, numerator := 11333679558887148512870400 }, some { target := 238, numerator := 365851176160877153995456512 }, some { target := 239, numerator := 381264980360963675972960256 }, some { target := 240, numerator := 227126938360098456197922816 }, some { target := 241, numerator := 11333679558887148512870400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 246, numerator := 12920394697131349304672256 }, some { target := 247, numerator := 269713239302616916735033344 }, some { target := 248, numerator := 13997094255225628413394944 }, some { target := 249, numerator := 290170530906408219800764416 }, some { target := 250, numerator := 434448271691041620369604608 }, some { target := 251, numerator := 13458744476178488859033600 }, some { target := 252, numerator := 434448271691041620369604608 }, some { target := 253, numerator := 452752164178644365217890304 }, some { target := 254, numerator := 269713239302616916735033344 }, some { target := 255, numerator := 13458744476178488859033600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 301, numerator := 12580384310364734849286144 }, some { target := 302, numerator := 262615522478863839978848256 }, some { target := 303, numerator := 13628749669561796086726656 }, some { target := 304, numerator := 282534464303608003490217984 }, some { target := 305, numerator := 423015422436014209307246592 }, some { target := 306, numerator := 13104566989963265468006400 }, some { target := 307, numerator := 423015422436014209307246592 }, some { target := 308, numerator := 440837633542364250343735296 }, some { target := 309, numerator := 262615522478863839978848256 }, some { target := 310, numerator := 13104566989963265468006400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 327, numerator := 475334520699727008629784576 }, some { target := 328, numerator := 9922608119606801305146753024 }, some { target := 329, numerator := 514945730758037592682266624 }, some { target := 330, numerator := 10675221110714702402143911936 }, some { target := 331, numerator := 15983123258528320665176506368 }, some { target := 332, numerator := 495140125728882300656025600 }, some { target := 333, numerator := 15983123258528320665176506368 }, some { target := 334, numerator := 16656513829519600594068701184 }, some { target := 335, numerator := 9922608119606801305146753024 }, some { target := 336, numerator := 495140125728882300656025600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 341, numerator := 12580384310364734849286144 }, some { target := 342, numerator := 262615522478863839978848256 }, some { target := 343, numerator := 13628749669561796086726656 }, some { target := 344, numerator := 282534464303608003490217984 }, some { target := 345, numerator := 423015422436014209307246592 }, some { target := 346, numerator := 13104566989963265468006400 }, some { target := 347, numerator := 423015422436014209307246592 }, some { target := 348, numerator := 440837633542364250343735296 }, some { target := 349, numerator := 262615522478863839978848256 }, some { target := 350, numerator := 13104566989963265468006400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 372, numerator := 145864455922877601360642048 }, some { target := 373, numerator := 3044920517390069928403402752 }, some { target := 374, numerator := 158019827249784068140695552 }, some { target := 375, numerator := 3275872572601292797224419328 }, some { target := 376, numerator := 4904692330406759345751588864 }, some { target := 377, numerator := 151942141586330834750668800 }, some { target := 378, numerator := 4904692330406759345751588864 }, some { target := 379, numerator := 5111333642964169281012498432 }, some { target := 380, numerator := 3044920517390069928403402752 }, some { target := 381, numerator := 151942141586330834750668800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 386, numerator := 475334520699727008629784576 }, some { target := 387, numerator := 9922608119606801305146753024 }, some { target := 388, numerator := 514945730758037592682266624 }, some { target := 389, numerator := 10675221110714702402143911936 }, some { target := 390, numerator := 15983123258528320665176506368 }, some { target := 391, numerator := 495140125728882300656025600 }, some { target := 392, numerator := 15983123258528320665176506368 }, some { target := 393, numerator := 16656513829519600594068701184 }, some { target := 394, numerator := 9922608119606801305146753024 }, some { target := 395, numerator := 495140125728882300656025600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 406, numerator := 12240373923598120393900032 }, some { target := 407, numerator := 255517805655110763222663168 }, some { target := 408, numerator := 13260405083897963760058368 }, some { target := 409, numerator := 274898397700807787179671552 }, some { target := 410, numerator := 411582573180986798244888576 }, some { target := 411, numerator := 12750389503748042076979200 }, some { target := 412, numerator := 411582573180986798244888576 }, some { target := 413, numerator := 428923102906084135469580288 }, some { target := 414, numerator := 255517805655110763222663168 }, some { target := 415, numerator := 12750389503748042076979200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 443, numerator := 12580384310364734849286144 }, some { target := 444, numerator := 262615522478863839978848256 }, some { target := 445, numerator := 13628749669561796086726656 }, some { target := 446, numerator := 282534464303608003490217984 }, some { target := 447, numerator := 423015422436014209307246592 }, some { target := 448, numerator := 13104566989963265468006400 }, some { target := 449, numerator := 423015422436014209307246592 }, some { target := 450, numerator := 440837633542364250343735296 }, some { target := 451, numerator := 262615522478863839978848256 }, some { target := 452, numerator := 13104566989963265468006400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 457, numerator := 12580384310364734849286144 }, some { target := 458, numerator := 262615522478863839978848256 }, some { target := 459, numerator := 13628749669561796086726656 }, some { target := 460, numerator := 282534464303608003490217984 }, some { target := 461, numerator := 423015422436014209307246592 }, some { target := 462, numerator := 13104566989963265468006400 }, some { target := 463, numerator := 423015422436014209307246592 }, some { target := 464, numerator := 440837633542364250343735296 }, some { target := 465, numerator := 262615522478863839978848256 }, some { target := 466, numerator := 13104566989963265468006400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 477, numerator := 13940425857431192670830592 }, some { target := 478, numerator := 291006389773876147003588608 }, some { target := 479, numerator := 15102128012217125393399808 }, some { target := 480, numerator := 313078730714808868732403712 }, some { target := 481, numerator := 468746819456123853556678656 }, some { target := 482, numerator := 14521276934824159032115200 }, some { target := 483, numerator := 468746819456123853556678656 }, some { target := 484, numerator := 488495756087484709840355328 }, some { target := 485, numerator := 291006389773876147003588608 }, some { target := 486, numerator := 14521276934824159032115200 }]

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

end Slot29

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent0
