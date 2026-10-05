import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk7Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 33; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 3, #[1649267441664, 34428457844736, 1786706395136, 37039797960704, 55456617725952, 1717986918400, 55456617725952, 57793079934976, 34428457844736, 1717986918400, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3298534883328, 2473901162496, 2611340115968, 3367254360064, 45079976738816, 78821239816192, 2405181685760, 45079976738816, 2542620639232, 2611340115968, 2611340115968, 2542620639232, 78821239816192, 2542620639232, 3298534883328, 3367254360064, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 14, numerator := 16320498564797493858533376 }, some { target := 15, numerator := 12240373923598120393900032 }, some { target := 16, numerator := 12920394697131349304672256 }, some { target := 17, numerator := 16660508951564108313919488 }, some { target := 18, numerator := 223046813718899082733289472 }, some { target := 19, numerator := 389991913621306780327870464 }, some { target := 20, numerator := 11900363536831505938513920 }, some { target := 21, numerator := 223046813718899082733289472 }, some { target := 22, numerator := 12580384310364734849286144 }, some { target := 23, numerator := 12920394697131349304672256 }, some { target := 24, numerator := 12920394697131349304672256 }, some { target := 25, numerator := 12580384310364734849286144 }, some { target := 26, numerator := 389991913621306780327870464 }, some { target := 27, numerator := 12580384310364734849286144 }, some { target := 28, numerator := 16320498564797493858533376 }, some { target := 29, numerator := 16660508951564108313919488 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 40, numerator := 340690407540147684296884224 }, some { target := 41, numerator := 255517805655110763222663168 }, some { target := 42, numerator := 269713239302616916735033344 }, some { target := 43, numerator := 347788124363900761053069312 }, some { target := 44, numerator := 4656102236382018352057417728 }, some { target := 45, numerator := 8141081196844779039344295936 }, some { target := 46, numerator := 248420088831357686466478080 }, some { target := 47, numerator := 4656102236382018352057417728 }, some { target := 48, numerator := 262615522478863839978848256 }, some { target := 49, numerator := 269713239302616916735033344 }, some { target := 50, numerator := 269713239302616916735033344 }, some { target := 51, numerator := 262615522478863839978848256 }, some { target := 52, numerator := 8141081196844779039344295936 }, some { target := 53, numerator := 262615522478863839978848256 }, some { target := 54, numerator := 340690407540147684296884224 }, some { target := 55, numerator := 347788124363900761053069312 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 75, numerator := 17680540111863951680077824 }, some { target := 76, numerator := 13260405083897963760058368 }, some { target := 77, numerator := 13997094255225628413394944 }, some { target := 78, numerator := 18048884697527784006746112 }, some { target := 79, numerator := 241634048195474006294396928 }, some { target := 80, numerator := 422491239756415678688526336 }, some { target := 81, numerator := 12892060498234131433390080 }, some { target := 82, numerator := 241634048195474006294396928 }, some { target := 83, numerator := 13628749669561796086726656 }, some { target := 84, numerator := 13997094255225628413394944 }, some { target := 85, numerator := 13997094255225628413394944 }, some { target := 86, numerator := 13628749669561796086726656 }, some { target := 87, numerator := 422491239756415678688526336 }, some { target := 88, numerator := 13628749669561796086726656 }, some { target := 89, numerator := 17680540111863951680077824 }, some { target := 90, numerator := 18048884697527784006746112 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 136, numerator := 366531196934410382906228736 }, some { target := 137, numerator := 274898397700807787179671552 }, some { target := 138, numerator := 290170530906408219800764416 }, some { target := 139, numerator := 374167263537210599216775168 }, some { target := 140, numerator := 5009259691436941899718459392 }, some { target := 141, numerator := 8758568393411848108196757504 }, some { target := 142, numerator := 267262331098007570869125120 }, some { target := 143, numerator := 5009259691436941899718459392 }, some { target := 144, numerator := 282534464303608003490217984 }, some { target := 145, numerator := 290170530906408219800764416 }, some { target := 146, numerator := 290170530906408219800764416 }, some { target := 147, numerator := 282534464303608003490217984 }, some { target := 148, numerator := 8758568393411848108196757504 }, some { target := 149, numerator := 282534464303608003490217984 }, some { target := 150, numerator := 366531196934410382906228736 }, some { target := 151, numerator := 374167263537210599216775168 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 171, numerator := 548776764241315730993184768 }, some { target := 172, numerator := 411582573180986798244888576 }, some { target := 173, numerator := 434448271691041620369604608 }, some { target := 174, numerator := 560209613496343142055542784 }, some { target := 175, numerator := 7499949111297981656906858496 }, some { target := 176, numerator := 13113478095516440488524644352 }, some { target := 177, numerator := 400149723925959387182530560 }, some { target := 178, numerator := 7499949111297981656906858496 }, some { target := 179, numerator := 423015422436014209307246592 }, some { target := 180, numerator := 434448271691041620369604608 }, some { target := 181, numerator := 434448271691041620369604608 }, some { target := 182, numerator := 423015422436014209307246592 }, some { target := 183, numerator := 13113478095516440488524644352 }, some { target := 184, numerator := 423015422436014209307246592 }, some { target := 185, numerator := 548776764241315730993184768 }, some { target := 186, numerator := 560209613496343142055542784 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 17000519338330722769305600 }, some { target := 268, numerator := 12750389503748042076979200 }, some { target := 269, numerator := 13458744476178488859033600 }, some { target := 270, numerator := 17354696824545946160332800 }, some { target := 271, numerator := 232340430957186544513843200 }, some { target := 272, numerator := 406241576688861229508198400 }, some { target := 273, numerator := 12396212017532818685952000 }, some { target := 274, numerator := 232340430957186544513843200 }, some { target := 275, numerator := 13104566989963265468006400 }, some { target := 276, numerator := 13458744476178488859033600 }, some { target := 277, numerator := 13458744476178488859033600 }, some { target := 278, numerator := 13104566989963265468006400 }, some { target := 279, numerator := 406241576688861229508198400 }, some { target := 280, numerator := 13104566989963265468006400 }, some { target := 281, numerator := 17000519338330722769305600 }, some { target := 282, numerator := 17354696824545946160332800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 403, numerator := 548776764241315730993184768 }, some { target := 404, numerator := 411582573180986798244888576 }, some { target := 405, numerator := 434448271691041620369604608 }, some { target := 406, numerator := 560209613496343142055542784 }, some { target := 407, numerator := 7499949111297981656906858496 }, some { target := 408, numerator := 13113478095516440488524644352 }, some { target := 409, numerator := 400149723925959387182530560 }, some { target := 410, numerator := 7499949111297981656906858496 }, some { target := 411, numerator := 423015422436014209307246592 }, some { target := 412, numerator := 434448271691041620369604608 }, some { target := 413, numerator := 434448271691041620369604608 }, some { target := 414, numerator := 423015422436014209307246592 }, some { target := 415, numerator := 13113478095516440488524644352 }, some { target := 416, numerator := 423015422436014209307246592 }, some { target := 417, numerator := 548776764241315730993184768 }, some { target := 418, numerator := 560209613496343142055542784 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 438, numerator := 571897470541445513959440384 }, some { target := 439, numerator := 428923102906084135469580288 }, some { target := 440, numerator := 452752164178644365217890304 }, some { target := 441, numerator := 583812001177725628833595392 }, some { target := 442, numerator := 7815932097399755357445685248 }, some { target := 443, numerator := 13665966639813291760655794176 }, some { target := 444, numerator := 417008572269804020595425280 }, some { target := 445, numerator := 7815932097399755357445685248 }, some { target := 446, numerator := 440837633542364250343735296 }, some { target := 447, numerator := 452752164178644365217890304 }, some { target := 448, numerator := 452752164178644365217890304 }, some { target := 449, numerator := 440837633542364250343735296 }, some { target := 450, numerator := 13665966639813291760655794176 }, some { target := 451, numerator := 440837633542364250343735296 }, some { target := 452, numerator := 571897470541445513959440384 }, some { target := 453, numerator := 583812001177725628833595392 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 534, numerator := 340690407540147684296884224 }, some { target := 535, numerator := 255517805655110763222663168 }, some { target := 536, numerator := 269713239302616916735033344 }, some { target := 537, numerator := 347788124363900761053069312 }, some { target := 538, numerator := 4656102236382018352057417728 }, some { target := 539, numerator := 8141081196844779039344295936 }, some { target := 540, numerator := 248420088831357686466478080 }, some { target := 541, numerator := 4656102236382018352057417728 }, some { target := 542, numerator := 262615522478863839978848256 }, some { target := 543, numerator := 269713239302616916735033344 }, some { target := 544, numerator := 269713239302616916735033344 }, some { target := 545, numerator := 262615522478863839978848256 }, some { target := 546, numerator := 8141081196844779039344295936 }, some { target := 547, numerator := 262615522478863839978848256 }, some { target := 548, numerator := 340690407540147684296884224 }, some { target := 549, numerator := 347788124363900761053069312 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 750, numerator := 17000519338330722769305600 }, some { target := 751, numerator := 12750389503748042076979200 }, some { target := 752, numerator := 13458744476178488859033600 }, some { target := 753, numerator := 17354696824545946160332800 }, some { target := 754, numerator := 232340430957186544513843200 }, some { target := 755, numerator := 406241576688861229508198400 }, some { target := 756, numerator := 12396212017532818685952000 }, some { target := 757, numerator := 232340430957186544513843200 }, some { target := 758, numerator := 13104566989963265468006400 }, some { target := 759, numerator := 13458744476178488859033600 }, some { target := 760, numerator := 13458744476178488859033600 }, some { target := 761, numerator := 13104566989963265468006400 }, some { target := 762, numerator := 406241576688861229508198400 }, some { target := 763, numerator := 13104566989963265468006400 }, some { target := 764, numerator := 17000519338330722769305600 }, some { target := 765, numerator := 17354696824545946160332800 }]

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
def data : BetaFourLocalSlotData := ⟨1, 317, #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0], #[206963736576, 24461784907776, 0, 232137462644736, 0, 0, 0, 0, 0, 0, 0, 24461801684992, 0, 0, 0, 0, 0, 0, 206963736576]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 56, numerator := 139763914743517041836163072 }, some { target := 57, numerator := 16519197405721353243404009472 }, some { target := 59, numerator := 156763890498958008055435886592 }, some { target := 67, numerator := 16519208735480979014889242624 }, some { target := 74, numerator := 139763914743517041836163072 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 91, numerator := 157797968258809563363409920 }, some { target := 92, numerator := 18650706748395076242552913920 }, some { target := 94, numerator := 176991489273017105869040517120 }, some { target := 102, numerator := 18650719540059169855520112640 }, some { target := 109, numerator := 157797968258809563363409920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 152, numerator := 135255401364693911454351360 }, some { target := 153, numerator := 15986320070052922493616783360 }, some { target := 155, numerator := 151706990805443233602034728960 }, some { target := 163, numerator := 15986331034336431304731525120 }, some { target := 170, numerator := 135255401364693911454351360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 187, numerator := 1780862784635136500815626240 }, some { target := 188, numerator := 210486547589030146165954314240 }, some { target := 190, numerator := 1997475378938335909093457264640 }, some { target := 198, numerator := 210486691952096345512298414080 }, some { target := 205, numerator := 1780862784635136500815626240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 222, numerator := 157797968258809563363409920 }, some { target := 223, numerator := 18650706748395076242552913920 }, some { target := 225, numerator := 176991489273017105869040517120 }, some { target := 233, numerator := 18650719540059169855520112640 }, some { target := 240, numerator := 157797968258809563363409920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 283, numerator := 135255401364693911454351360 }, some { target := 284, numerator := 15986320070052922493616783360 }, some { target := 286, numerator := 151706990805443233602034728960 }, some { target := 294, numerator := 15986331034336431304731525120 }, some { target := 301, numerator := 135255401364693911454351360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 318, numerator := 157797968258809563363409920 }, some { target := 319, numerator := 18650706748395076242552913920 }, some { target := 321, numerator := 176991489273017105869040517120 }, some { target := 329, numerator := 18650719540059169855520112640 }, some { target := 336, numerator := 157797968258809563363409920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 419, numerator := 157797968258809563363409920 }, some { target := 420, numerator := 18650706748395076242552913920 }, some { target := 422, numerator := 176991489273017105869040517120 }, some { target := 430, numerator := 18650719540059169855520112640 }, some { target := 437, numerator := 157797968258809563363409920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 454, numerator := 6541852912672362184008794112 }, some { target := 455, numerator := 773205014054893017941265088512 }, some { target := 457, numerator := 7337561455289937731885079724032 }, some { target := 465, numerator := 773205544360738727438848098304 }, some { target := 472, numerator := 6541852912672362184008794112 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 489, numerator := 162306481637632693745221632 }, some { target := 490, numerator := 19183584084063506992340140032 }, some { target := 492, numerator := 182048388966531880322441674752 }, some { target := 500, numerator := 19183597241203717565677830144 }, some { target := 507, numerator := 162306481637632693745221632 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 550, numerator := 1780862784635136500815626240 }, some { target := 551, numerator := 210486547589030146165954314240 }, some { target := 553, numerator := 1997475378938335909093457264640 }, some { target := 561, numerator := 210486691952096345512298414080 }, some { target := 568, numerator := 1780862784635136500815626240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 585, numerator := 6541852912672362184008794112 }, some { target := 586, numerator := 773205014054893017941265088512 }, some { target := 588, numerator := 7337561455289937731885079724032 }, some { target := 596, numerator := 773205544360738727438848098304 }, some { target := 603, numerator := 6541852912672362184008794112 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 660, numerator := 139763914743517041836163072 }, some { target := 661, numerator := 16519197405721353243404009472 }, some { target := 663, numerator := 156763890498958008055435886592 }, some { target := 671, numerator := 16519208735480979014889242624 }, some { target := 678, numerator := 139763914743517041836163072 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 766, numerator := 157797968258809563363409920 }, some { target := 767, numerator := 18650706748395076242552913920 }, some { target := 769, numerator := 176991489273017105869040517120 }, some { target := 777, numerator := 18650719540059169855520112640 }, some { target := 784, numerator := 157797968258809563363409920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 801, numerator := 162306481637632693745221632 }, some { target := 802, numerator := 19183584084063506992340140032 }, some { target := 804, numerator := 182048388966531880322441674752 }, some { target := 812, numerator := 19183597241203717565677830144 }, some { target := 819, numerator := 162306481637632693745221632 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 876, numerator := 157797968258809563363409920 }, some { target := 877, numerator := 18650706748395076242552913920 }, some { target := 879, numerator := 176991489273017105869040517120 }, some { target := 887, numerator := 18650719540059169855520112640 }, some { target := 894, numerator := 157797968258809563363409920 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7.Parent3
