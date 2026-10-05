import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk9Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 4, for region 1, branch 2,
parent 41; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot15

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨15, 12, #[51810056273920, 0, 0, 177854864162816, 0, 51810056273920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 1, numerator := 43749703149238226331956674560 }, some { target := 2, numerator := 43749703149238226331956674560 }, some { target := 3, numerator := 43749703149238226331956674560 }, some { target := 4, numerator := 43749703149238226331956674560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 51, numerator := 150185081244316560116718501888 }, some { target := 52, numerator := 150185081244316560116718501888 }, some { target := 53, numerator := 150185081244316560116718501888 }, some { target := 54, numerator := 150185081244316560116718501888 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 140, numerator := 43749703149238226331956674560 }, some { target := 141, numerator := 43749703149238226331956674560 }, some { target := 142, numerator := 43749703149238226331956674560 }, some { target := 143, numerator := 43749703149238226331956674560 }]

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

end Slot15

namespace Slot16

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨16, 63, #[343597383680, 5772436045824, 12506944765952, 412316860416, 6597069766656, 481036337152, 12506944765952, 12506944765952, 6597069766656, 154343944749056, 12369505812480, 5772436045824, 12506944765952, 481036337152, 12369505812480, 481036337152, 12506944765952, 12506944765952, 412316860416], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]

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
  [some { target := 34, numerator := 52064090473637838480998400 }, some { target := 35, numerator := 53551635915741776723312640 }, some { target := 36, numerator := 52064090473637838480998400 }, some { target := 37, numerator := 46113908705222085511741440 }, some { target := 38, numerator := 2158428436492814389597962240 }, some { target := 39, numerator := 587580449631055605714124800 }, some { target := 40, numerator := 53551635915741776723312640 }, some { target := 41, numerator := 2158428436492814389597962240 }, some { target := 42, numerator := 52064090473637838480998400 }, some { target := 43, numerator := 52064090473637838480998400 }, some { target := 44, numerator := 44626363263118147269427200 }, some { target := 45, numerator := 52064090473637838480998400 }, some { target := 46, numerator := 587580449631055605714124800 }, some { target := 47, numerator := 44626363263118147269427200 }, some { target := 48, numerator := 52064090473637838480998400 }, some { target := 49, numerator := 46113908705222085511741440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 79, numerator := 874676719957115686480773120 }, some { target := 80, numerator := 899667483384461848951652352 }, some { target := 81, numerator := 874676719957115686480773120 }, some { target := 82, numerator := 774713666247731036597256192 }, some { target := 83, numerator := 36261597733079281745245765632 }, some { target := 84, numerator := 9871351553801734175997296640 }, some { target := 85, numerator := 899667483384461848951652352 }, some { target := 86, numerator := 36261597733079281745245765632 }, some { target := 87, numerator := 874676719957115686480773120 }, some { target := 88, numerator := 874676719957115686480773120 }, some { target := 89, numerator := 749722902820384874126376960 }, some { target := 90, numerator := 874676719957115686480773120 }, some { target := 91, numerator := 9871351553801734175997296640 }, some { target := 92, numerator := 749722902820384874126376960 }, some { target := 93, numerator := 874676719957115686480773120 }, some { target := 94, numerator := 774713666247731036597256192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 105, numerator := 1895132893240417320708341760 }, some { target := 106, numerator := 1949279547333000672728580096 }, some { target := 107, numerator := 1895132893240417320708341760 }, some { target := 108, numerator := 1678546276870083912627388416 }, some { target := 109, numerator := 78566795088338443781365825536 }, some { target := 110, numerator := 21387928366570424047994142720 }, some { target := 111, numerator := 1949279547333000672728580096 }, some { target := 112, numerator := 78566795088338443781365825536 }, some { target := 113, numerator := 1895132893240417320708341760 }, some { target := 114, numerator := 1895132893240417320708341760 }, some { target := 115, numerator := 1624399622777500560607150080 }, some { target := 116, numerator := 1895132893240417320708341760 }, some { target := 117, numerator := 21387928366570424047994142720 }, some { target := 118, numerator := 1624399622777500560607150080 }, some { target := 119, numerator := 1895132893240417320708341760 }, some { target := 120, numerator := 1678546276870083912627388416 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 154, numerator := 62476908568365406177198080 }, some { target := 155, numerator := 64261963098890132067975168 }, some { target := 156, numerator := 62476908568365406177198080 }, some { target := 157, numerator := 55336690446266502614089728 }, some { target := 158, numerator := 2590114123791377267517554688 }, some { target := 159, numerator := 705096539557266726856949760 }, some { target := 160, numerator := 64261963098890132067975168 }, some { target := 161, numerator := 2590114123791377267517554688 }, some { target := 162, numerator := 62476908568365406177198080 }, some { target := 163, numerator := 62476908568365406177198080 }, some { target := 164, numerator := 53551635915741776723312640 }, some { target := 165, numerator := 62476908568365406177198080 }, some { target := 166, numerator := 705096539557266726856949760 }, some { target := 167, numerator := 53551635915741776723312640 }, some { target := 168, numerator := 62476908568365406177198080 }, some { target := 169, numerator := 55336690446266502614089728 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 180, numerator := 999630537093846498835169280 }, some { target := 181, numerator := 1028191409582242113087602688 }, some { target := 182, numerator := 999630537093846498835169280 }, some { target := 183, numerator := 885387047140264041825435648 }, some { target := 184, numerator := 41441825980662036280280875008 }, some { target := 185, numerator := 11281544632916267629711196160 }, some { target := 186, numerator := 1028191409582242113087602688 }, some { target := 187, numerator := 41441825980662036280280875008 }, some { target := 188, numerator := 999630537093846498835169280 }, some { target := 189, numerator := 999630537093846498835169280 }, some { target := 190, numerator := 856826174651868427573002240 }, some { target := 191, numerator := 999630537093846498835169280 }, some { target := 192, numerator := 11281544632916267629711196160 }, some { target := 193, numerator := 856826174651868427573002240 }, some { target := 194, numerator := 999630537093846498835169280 }, some { target := 195, numerator := 885387047140264041825435648 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 215, numerator := 72889726663092973873397760 }, some { target := 216, numerator := 74972290282038487412637696 }, some { target := 217, numerator := 72889726663092973873397760 }, some { target := 218, numerator := 64559472187310919716438016 }, some { target := 219, numerator := 3021799811089940145437147136 }, some { target := 220, numerator := 822612629483477847999774720 }, some { target := 221, numerator := 74972290282038487412637696 }, some { target := 222, numerator := 3021799811089940145437147136 }, some { target := 223, numerator := 72889726663092973873397760 }, some { target := 224, numerator := 72889726663092973873397760 }, some { target := 225, numerator := 62476908568365406177198080 }, some { target := 226, numerator := 72889726663092973873397760 }, some { target := 227, numerator := 822612629483477847999774720 }, some { target := 228, numerator := 62476908568365406177198080 }, some { target := 229, numerator := 72889726663092973873397760 }, some { target := 230, numerator := 64559472187310919716438016 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 295, numerator := 1895132893240417320708341760 }, some { target := 296, numerator := 1949279547333000672728580096 }, some { target := 297, numerator := 1895132893240417320708341760 }, some { target := 298, numerator := 1678546276870083912627388416 }, some { target := 299, numerator := 78566795088338443781365825536 }, some { target := 300, numerator := 21387928366570424047994142720 }, some { target := 301, numerator := 1949279547333000672728580096 }, some { target := 302, numerator := 78566795088338443781365825536 }, some { target := 303, numerator := 1895132893240417320708341760 }, some { target := 304, numerator := 1895132893240417320708341760 }, some { target := 305, numerator := 1624399622777500560607150080 }, some { target := 306, numerator := 1895132893240417320708341760 }, some { target := 307, numerator := 21387928366570424047994142720 }, some { target := 308, numerator := 1624399622777500560607150080 }, some { target := 309, numerator := 1895132893240417320708341760 }, some { target := 310, numerator := 1678546276870083912627388416 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 321, numerator := 1895132893240417320708341760 }, some { target := 322, numerator := 1949279547333000672728580096 }, some { target := 323, numerator := 1895132893240417320708341760 }, some { target := 324, numerator := 1678546276870083912627388416 }, some { target := 325, numerator := 78566795088338443781365825536 }, some { target := 326, numerator := 21387928366570424047994142720 }, some { target := 327, numerator := 1949279547333000672728580096 }, some { target := 328, numerator := 78566795088338443781365825536 }, some { target := 329, numerator := 1895132893240417320708341760 }, some { target := 330, numerator := 1895132893240417320708341760 }, some { target := 331, numerator := 1624399622777500560607150080 }, some { target := 332, numerator := 1895132893240417320708341760 }, some { target := 333, numerator := 21387928366570424047994142720 }, some { target := 334, numerator := 1624399622777500560607150080 }, some { target := 335, numerator := 1895132893240417320708341760 }, some { target := 336, numerator := 1678546276870083912627388416 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 370, numerator := 999630537093846498835169280 }, some { target := 371, numerator := 1028191409582242113087602688 }, some { target := 372, numerator := 999630537093846498835169280 }, some { target := 373, numerator := 885387047140264041825435648 }, some { target := 374, numerator := 41441825980662036280280875008 }, some { target := 375, numerator := 11281544632916267629711196160 }, some { target := 376, numerator := 1028191409582242113087602688 }, some { target := 377, numerator := 41441825980662036280280875008 }, some { target := 378, numerator := 999630537093846498835169280 }, some { target := 379, numerator := 999630537093846498835169280 }, some { target := 380, numerator := 856826174651868427573002240 }, some { target := 381, numerator := 999630537093846498835169280 }, some { target := 382, numerator := 11281544632916267629711196160 }, some { target := 383, numerator := 856826174651868427573002240 }, some { target := 384, numerator := 999630537093846498835169280 }, some { target := 385, numerator := 885387047140264041825435648 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 396, numerator := 23387189440758117045664481280 }, some { target := 397, numerator := 24055394853351206104112037888 }, some { target := 398, numerator := 23387189440758117045664481280 }, some { target := 399, numerator := 20714367790385760811874254848 }, some { target := 400, numerator := 969566053672572223807404638208 }, some { target := 401, numerator := 263941137974270178086784860160 }, some { target := 402, numerator := 24055394853351206104112037888 }, some { target := 403, numerator := 969566053672572223807404638208 }, some { target := 404, numerator := 23387189440758117045664481280 }, some { target := 405, numerator := 23387189440758117045664481280 }, some { target := 406, numerator := 20046162377792671753426698240 }, some { target := 407, numerator := 23387189440758117045664481280 }, some { target := 408, numerator := 263941137974270178086784860160 }, some { target := 409, numerator := 20046162377792671753426698240 }, some { target := 410, numerator := 23387189440758117045664481280 }, some { target := 411, numerator := 20714367790385760811874254848 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 431, numerator := 1874307257050962185315942400 }, some { target := 432, numerator := 1927858892966703962039255040 }, some { target := 433, numerator := 1874307257050962185315942400 }, some { target := 434, numerator := 1660100713387995078422691840 }, some { target := 435, numerator := 77703423713741318025526640640 }, some { target := 436, numerator := 21152896186718001805708492800 }, some { target := 437, numerator := 1927858892966703962039255040 }, some { target := 438, numerator := 77703423713741318025526640640 }, some { target := 439, numerator := 1874307257050962185315942400 }, some { target := 440, numerator := 1874307257050962185315942400 }, some { target := 441, numerator := 1606549077472253301699379200 }, some { target := 442, numerator := 1874307257050962185315942400 }, some { target := 443, numerator := 21152896186718001805708492800 }, some { target := 444, numerator := 1606549077472253301699379200 }, some { target := 445, numerator := 1874307257050962185315942400 }, some { target := 446, numerator := 1660100713387995078422691840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 492, numerator := 874676719957115686480773120 }, some { target := 493, numerator := 899667483384461848951652352 }, some { target := 494, numerator := 874676719957115686480773120 }, some { target := 495, numerator := 774713666247731036597256192 }, some { target := 496, numerator := 36261597733079281745245765632 }, some { target := 497, numerator := 9871351553801734175997296640 }, some { target := 498, numerator := 899667483384461848951652352 }, some { target := 499, numerator := 36261597733079281745245765632 }, some { target := 500, numerator := 874676719957115686480773120 }, some { target := 501, numerator := 874676719957115686480773120 }, some { target := 502, numerator := 749722902820384874126376960 }, some { target := 503, numerator := 874676719957115686480773120 }, some { target := 504, numerator := 9871351553801734175997296640 }, some { target := 505, numerator := 749722902820384874126376960 }, some { target := 506, numerator := 874676719957115686480773120 }, some { target := 507, numerator := 774713666247731036597256192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 527, numerator := 1895132893240417320708341760 }, some { target := 528, numerator := 1949279547333000672728580096 }, some { target := 529, numerator := 1895132893240417320708341760 }, some { target := 530, numerator := 1678546276870083912627388416 }, some { target := 531, numerator := 78566795088338443781365825536 }, some { target := 532, numerator := 21387928366570424047994142720 }, some { target := 533, numerator := 1949279547333000672728580096 }, some { target := 534, numerator := 78566795088338443781365825536 }, some { target := 535, numerator := 1895132893240417320708341760 }, some { target := 536, numerator := 1895132893240417320708341760 }, some { target := 537, numerator := 1624399622777500560607150080 }, some { target := 538, numerator := 1895132893240417320708341760 }, some { target := 539, numerator := 21387928366570424047994142720 }, some { target := 540, numerator := 1624399622777500560607150080 }, some { target := 541, numerator := 1895132893240417320708341760 }, some { target := 542, numerator := 1678546276870083912627388416 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 637, numerator := 72889726663092973873397760 }, some { target := 638, numerator := 74972290282038487412637696 }, some { target := 639, numerator := 72889726663092973873397760 }, some { target := 640, numerator := 64559472187310919716438016 }, some { target := 641, numerator := 3021799811089940145437147136 }, some { target := 642, numerator := 822612629483477847999774720 }, some { target := 643, numerator := 74972290282038487412637696 }, some { target := 644, numerator := 3021799811089940145437147136 }, some { target := 645, numerator := 72889726663092973873397760 }, some { target := 646, numerator := 72889726663092973873397760 }, some { target := 647, numerator := 62476908568365406177198080 }, some { target := 648, numerator := 72889726663092973873397760 }, some { target := 649, numerator := 822612629483477847999774720 }, some { target := 650, numerator := 62476908568365406177198080 }, some { target := 651, numerator := 72889726663092973873397760 }, some { target := 652, numerator := 64559472187310919716438016 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 663, numerator := 1874307257050962185315942400 }, some { target := 664, numerator := 1927858892966703962039255040 }, some { target := 665, numerator := 1874307257050962185315942400 }, some { target := 666, numerator := 1660100713387995078422691840 }, some { target := 667, numerator := 77703423713741318025526640640 }, some { target := 668, numerator := 21152896186718001805708492800 }, some { target := 669, numerator := 1927858892966703962039255040 }, some { target := 670, numerator := 77703423713741318025526640640 }, some { target := 671, numerator := 1874307257050962185315942400 }, some { target := 672, numerator := 1874307257050962185315942400 }, some { target := 673, numerator := 1606549077472253301699379200 }, some { target := 674, numerator := 1874307257050962185315942400 }, some { target := 675, numerator := 21152896186718001805708492800 }, some { target := 676, numerator := 1606549077472253301699379200 }, some { target := 677, numerator := 1874307257050962185315942400 }, some { target := 678, numerator := 1660100713387995078422691840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 698, numerator := 72889726663092973873397760 }, some { target := 699, numerator := 74972290282038487412637696 }, some { target := 700, numerator := 72889726663092973873397760 }, some { target := 701, numerator := 64559472187310919716438016 }, some { target := 702, numerator := 3021799811089940145437147136 }, some { target := 703, numerator := 822612629483477847999774720 }, some { target := 704, numerator := 74972290282038487412637696 }, some { target := 705, numerator := 3021799811089940145437147136 }, some { target := 706, numerator := 72889726663092973873397760 }, some { target := 707, numerator := 72889726663092973873397760 }, some { target := 708, numerator := 62476908568365406177198080 }, some { target := 709, numerator := 72889726663092973873397760 }, some { target := 710, numerator := 822612629483477847999774720 }, some { target := 711, numerator := 62476908568365406177198080 }, some { target := 712, numerator := 72889726663092973873397760 }, some { target := 713, numerator := 64559472187310919716438016 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 759, numerator := 1895132893240417320708341760 }, some { target := 760, numerator := 1949279547333000672728580096 }, some { target := 761, numerator := 1895132893240417320708341760 }, some { target := 762, numerator := 1678546276870083912627388416 }, some { target := 763, numerator := 78566795088338443781365825536 }, some { target := 764, numerator := 21387928366570424047994142720 }, some { target := 765, numerator := 1949279547333000672728580096 }, some { target := 766, numerator := 78566795088338443781365825536 }, some { target := 767, numerator := 1895132893240417320708341760 }, some { target := 768, numerator := 1895132893240417320708341760 }, some { target := 769, numerator := 1624399622777500560607150080 }, some { target := 770, numerator := 1895132893240417320708341760 }, some { target := 771, numerator := 21387928366570424047994142720 }, some { target := 772, numerator := 1624399622777500560607150080 }, some { target := 773, numerator := 1895132893240417320708341760 }, some { target := 774, numerator := 1678546276870083912627388416 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 794, numerator := 1895132893240417320708341760 }, some { target := 795, numerator := 1949279547333000672728580096 }, some { target := 796, numerator := 1895132893240417320708341760 }, some { target := 797, numerator := 1678546276870083912627388416 }, some { target := 798, numerator := 78566795088338443781365825536 }, some { target := 799, numerator := 21387928366570424047994142720 }, some { target := 800, numerator := 1949279547333000672728580096 }, some { target := 801, numerator := 78566795088338443781365825536 }, some { target := 802, numerator := 1895132893240417320708341760 }, some { target := 803, numerator := 1895132893240417320708341760 }, some { target := 804, numerator := 1624399622777500560607150080 }, some { target := 805, numerator := 1895132893240417320708341760 }, some { target := 806, numerator := 21387928366570424047994142720 }, some { target := 807, numerator := 1624399622777500560607150080 }, some { target := 808, numerator := 1895132893240417320708341760 }, some { target := 809, numerator := 1678546276870083912627388416 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 890, numerator := 62476908568365406177198080 }, some { target := 891, numerator := 64261963098890132067975168 }, some { target := 892, numerator := 62476908568365406177198080 }, some { target := 893, numerator := 55336690446266502614089728 }, some { target := 894, numerator := 2590114123791377267517554688 }, some { target := 895, numerator := 705096539557266726856949760 }, some { target := 896, numerator := 64261963098890132067975168 }, some { target := 897, numerator := 2590114123791377267517554688 }, some { target := 898, numerator := 62476908568365406177198080 }, some { target := 899, numerator := 62476908568365406177198080 }, some { target := 900, numerator := 53551635915741776723312640 }, some { target := 901, numerator := 62476908568365406177198080 }, some { target := 902, numerator := 705096539557266726856949760 }, some { target := 903, numerator := 53551635915741776723312640 }, some { target := 904, numerator := 62476908568365406177198080 }, some { target := 905, numerator := 55336690446266502614089728 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 18 = expected := by
  rfl

end Left18

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected ++ Left10.expected ++ Left11.expected ++ Left12.expected ++ Left13.expected ++ Left14.expected ++ Left15.expected ++ Left16.expected ++ Left17.expected ++ Left18.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq, Left10.routed_eq, Left11.routed_eq, Left12.routed_eq, Left13.routed_eq, Left14.routed_eq, Left15.routed_eq, Left16.routed_eq, Left17.routed_eq, Left18.routed_eq]
  rfl

end Slot16

namespace Slot17

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨17, 31, #[3710583308288, 0, 137026905047040, 0, 0, 137026871492608, 0, 0, 0, 0, 0, 0, 3710616862720, 0, 0, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 10, numerator := 197616741081437527290675200 }, some { target := 11, numerator := 3960239491272008046905131008 }, some { target := 12, numerator := 6647827169979558418058313728 }, some { target := 13, numerator := 6379068402108803380942995456 }, some { target := 14, numerator := 197616741081437527290675200 }, some { target := 15, numerator := 6379068402108803380942995456 }, some { target := 16, numerator := 4260616937715793088386957312 }, some { target := 17, numerator := 205521410724695028382302208 }, some { target := 18, numerator := 3960239491272008046905131008 }, some { target := 19, numerator := 189712071438180026199048192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 7297723340529263355887616000 }, some { target := 56, numerator := 146246375744206437651987824640 }, some { target := 57, numerator := 245495413175404419292059402240 }, some { target := 58, numerator := 235570509432284621128052244480 }, some { target := 59, numerator := 7297723340529263355887616000 }, some { target := 60, numerator := 235570509432284621128052244480 }, some { target := 61, numerator := 157338915221810917952937000960 }, some { target := 62, numerator := 7589632274150433890123120640 }, some { target := 63, numerator := 146246375744206437651987824640 }, some { target := 64, numerator := 7005814406908092821652111360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 144, numerator := 7297721553500931215274803200 }, some { target := 145, numerator := 146246339932158661554107056128 }, some { target := 146, numerator := 245495353059771326081844379648 }, some { target := 147, numerator := 235570451747010059629070647296 }, some { target := 148, numerator := 7297721553500931215274803200 }, some { target := 149, numerator := 235570451747010059629070647296 }, some { target := 150, numerator := 157338876693480077001324756992 }, some { target := 151, numerator := 7589630415640968463885795328 }, some { target := 152, numerator := 146246339932158661554107056128 }, some { target := 153, numerator := 7005812691360893966663811072 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 482, numerator := 197618528109769667903488000 }, some { target := 483, numerator := 3960275303319784144785899520 }, some { target := 484, numerator := 6647887285612651628273336320 }, some { target := 485, numerator := 6379126087383364879924592640 }, some { target := 486, numerator := 197618528109769667903488000 }, some { target := 487, numerator := 6379126087383364879924592640 }, some { target := 488, numerator := 4260655466046634039999201280 }, some { target := 489, numerator := 205523269234160454619627520 }, some { target := 490, numerator := 3960275303319784144785899520 }, some { target := 491, numerator := 189713786985378881187348480 }]

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

end Slot17

namespace Slot18

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨18, 8, #[49931561730048, 0, 0, 181611853250560, 0, 49931561730048, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 1, numerator := 29371678002633553196278087680 }, some { target := 2, numerator := 26846262697734219650429878272 }, some { target := 3, numerator := 29371678002633553196278087680 }, some { target := 4, numerator := 26846262697734219650429878272 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 51, numerator := 106831124249152505375201689600 }, some { target := 52, numerator := 97645644407169299305558179840 }, some { target := 53, numerator := 106831124249152505375201689600 }, some { target := 54, numerator := 97645644407169299305558179840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 140, numerator := 29371678002633553196278087680 }, some { target := 141, numerator := 26846262697734219650429878272 }, some { target := 142, numerator := 29371678002633553196278087680 }, some { target := 143, numerator := 26846262697734219650429878272 }]

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

end Slot18

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9.Parent3
