import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk5Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 23; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 6, #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416], #[2130303778816, 51608327028736, 39101382262784, 43568148250624, 2130303778816, 43568148250624, 43499428773888, 2130303778816, 51608327028736, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

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
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 11, numerator := 5270160994882524058484736 }, some { target := 12, numerator := 127673900230863727997485056 }, some { target := 13, numerator := 96732955035101812557348864 }, some { target := 14, numerator := 107783292605016782357397504 }, some { target := 15, numerator := 5270160994882524058484736 }, some { target := 16, numerator := 107783292605016782357397504 }, some { target := 17, numerator := 107613287411633475129704448 }, some { target := 18, numerator := 5270160994882524058484736 }, some { target := 19, numerator := 127673900230863727997485056 }, some { target := 20, numerator := 5270160994882524058484736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 31, numerator := 76417334425796598848028672 }, some { target := 32, numerator := 1851271553347524055963533312 }, some { target := 33, numerator := 1402627848008976282081558528 }, some { target := 34, numerator := 1562857742772743344182263808 }, some { target := 35, numerator := 76417334425796598848028672 }, some { target := 36, numerator := 1562857742772743344182263808 }, some { target := 37, numerator := 1560392667468685389380714496 }, some { target := 38, numerator := 76417334425796598848028672 }, some { target := 39, numerator := 1851271553347524055963533312 }, some { target := 40, numerator := 76417334425796598848028672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 45, numerator := 135267465535318117501108224 }, some { target := 46, numerator := 3276963439258835685268783104 }, some { target := 47, numerator := 2482812512567613188971954176 }, some { target := 48, numerator := 2766437843528764080506535936 }, some { target := 49, numerator := 135267465535318117501108224 }, some { target := 50, numerator := 2766437843528764080506535936 }, some { target := 51, numerator := 2762074376898592528329080832 }, some { target := 52, numerator := 135267465535318117501108224 }, some { target := 53, numerator := 3276963439258835685268783104 }, some { target := 54, numerator := 135267465535318117501108224 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 76, numerator := 4391800829068770048737280 }, some { target := 77, numerator := 106394916859053106664570880 }, some { target := 78, numerator := 80610795862584843797790720 }, some { target := 79, numerator := 89819410504180651964497920 }, some { target := 80, numerator := 4391800829068770048737280 }, some { target := 81, numerator := 89819410504180651964497920 }, some { target := 82, numerator := 89677739509694562608087040 }, some { target := 83, numerator := 4391800829068770048737280 }, some { target := 84, numerator := 106394916859053106664570880 }, some { target := 85, numerator := 4391800829068770048737280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 90, numerator := 84322575918120384935755776 }, some { target := 91, numerator := 2042782403693819647959760896 }, some { target := 92, numerator := 1547727280561629000917581824 }, some { target := 93, numerator := 1724532681680268517718360064 }, some { target := 94, numerator := 84322575918120384935755776 }, some { target := 95, numerator := 1724532681680268517718360064 }, some { target := 96, numerator := 1721812598586135602075271168 }, some { target := 97, numerator := 84322575918120384935755776 }, some { target := 98, numerator := 2042782403693819647959760896 }, some { target := 99, numerator := 84322575918120384935755776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 116, numerator := 4391800829068770048737280 }, some { target := 117, numerator := 106394916859053106664570880 }, some { target := 118, numerator := 80610795862584843797790720 }, some { target := 119, numerator := 89819410504180651964497920 }, some { target := 120, numerator := 4391800829068770048737280 }, some { target := 121, numerator := 89819410504180651964497920 }, some { target := 122, numerator := 89677739509694562608087040 }, some { target := 123, numerator := 4391800829068770048737280 }, some { target := 124, numerator := 106394916859053106664570880 }, some { target := 125, numerator := 4391800829068770048737280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 171, numerator := 134389105369504363491360768 }, some { target := 172, numerator := 3255684455887025063935868928 }, some { target := 173, numerator := 2466690353395096220212396032 }, some { target := 174, numerator := 2748473961427927950113636352 }, some { target := 175, numerator := 134389105369504363491360768 }, some { target := 176, numerator := 2748473961427927950113636352 }, some { target := 177, numerator := 2744138828996653615807463424 }, some { target := 178, numerator := 134389105369504363491360768 }, some { target := 179, numerator := 3255684455887025063935868928 }, some { target := 180, numerator := 134389105369504363491360768 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 185, numerator := 140537626530200641559592960 }, some { target := 186, numerator := 3404637339489699413266268160 }, some { target := 187, numerator := 2579545467602715001529303040 }, some { target := 188, numerator := 2874221136133780862863933440 }, some { target := 189, numerator := 140537626530200641559592960 }, some { target := 190, numerator := 2874221136133780862863933440 }, some { target := 191, numerator := 2869687664310226003458785280 }, some { target := 192, numerator := 140537626530200641559592960 }, some { target := 193, numerator := 3404637339489699413266268160 }, some { target := 194, numerator := 140537626530200641559592960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 84322575918120384935755776 }, some { target := 217, numerator := 2042782403693819647959760896 }, some { target := 218, numerator := 1547727280561629000917581824 }, some { target := 219, numerator := 1724532681680268517718360064 }, some { target := 220, numerator := 84322575918120384935755776 }, some { target := 221, numerator := 1724532681680268517718360064 }, some { target := 222, numerator := 1721812598586135602075271168 }, some { target := 223, numerator := 84322575918120384935755776 }, some { target := 224, numerator := 2042782403693819647959760896 }, some { target := 225, numerator := 84322575918120384935755776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 230, numerator := 2152860766409511077891014656 }, some { target := 231, numerator := 52154788244307832886972645376 }, some { target := 232, numerator := 39515412131839090429677010944 }, some { target := 233, numerator := 44029475029149355592996880384 }, some { target := 234, numerator := 2152860766409511077891014656 }, some { target := 235, numerator := 44029475029149355592996880384 }, some { target := 236, numerator := 43960027907652274590484267008 }, some { target := 237, numerator := 2152860766409511077891014656 }, some { target := 238, numerator := 52154788244307832886972645376 }, some { target := 239, numerator := 2152860766409511077891014656 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 256, numerator := 137902546032759379530350592 }, some { target := 257, numerator := 3340800389374267549267525632 }, some { target := 258, numerator := 2531178990085164095250628608 }, some { target := 259, numerator := 2820329489831272471685234688 }, some { target := 260, numerator := 137902546032759379530350592 }, some { target := 261, numerator := 2820329489831272471685234688 }, some { target := 262, numerator := 2815881020604409265893933056 }, some { target := 263, numerator := 137902546032759379530350592 }, some { target := 264, numerator := 3340800389374267549267525632 }, some { target := 265, numerator := 137902546032759379530350592 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 305, numerator := 76417334425796598848028672 }, some { target := 306, numerator := 1851271553347524055963533312 }, some { target := 307, numerator := 1402627848008976282081558528 }, some { target := 308, numerator := 1562857742772743344182263808 }, some { target := 309, numerator := 76417334425796598848028672 }, some { target := 310, numerator := 1562857742772743344182263808 }, some { target := 311, numerator := 1560392667468685389380714496 }, some { target := 312, numerator := 76417334425796598848028672 }, some { target := 313, numerator := 1851271553347524055963533312 }, some { target := 314, numerator := 76417334425796598848028672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 331, numerator := 134389105369504363491360768 }, some { target := 332, numerator := 3255684455887025063935868928 }, some { target := 333, numerator := 2466690353395096220212396032 }, some { target := 334, numerator := 2748473961427927950113636352 }, some { target := 335, numerator := 134389105369504363491360768 }, some { target := 336, numerator := 2748473961427927950113636352 }, some { target := 337, numerator := 2744138828996653615807463424 }, some { target := 338, numerator := 134389105369504363491360768 }, some { target := 339, numerator := 3255684455887025063935868928 }, some { target := 340, numerator := 134389105369504363491360768 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 432, numerator := 4391800829068770048737280 }, some { target := 433, numerator := 106394916859053106664570880 }, some { target := 434, numerator := 80610795862584843797790720 }, some { target := 435, numerator := 89819410504180651964497920 }, some { target := 436, numerator := 4391800829068770048737280 }, some { target := 437, numerator := 89819410504180651964497920 }, some { target := 438, numerator := 89677739509694562608087040 }, some { target := 439, numerator := 4391800829068770048737280 }, some { target := 440, numerator := 106394916859053106664570880 }, some { target := 441, numerator := 4391800829068770048737280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 446, numerator := 137902546032759379530350592 }, some { target := 447, numerator := 3340800389374267549267525632 }, some { target := 448, numerator := 2531178990085164095250628608 }, some { target := 449, numerator := 2820329489831272471685234688 }, some { target := 450, numerator := 137902546032759379530350592 }, some { target := 451, numerator := 2820329489831272471685234688 }, some { target := 452, numerator := 2815881020604409265893933056 }, some { target := 453, numerator := 137902546032759379530350592 }, some { target := 454, numerator := 3340800389374267549267525632 }, some { target := 455, numerator := 137902546032759379530350592 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 472, numerator := 4391800829068770048737280 }, some { target := 473, numerator := 106394916859053106664570880 }, some { target := 474, numerator := 80610795862584843797790720 }, some { target := 475, numerator := 89819410504180651964497920 }, some { target := 476, numerator := 4391800829068770048737280 }, some { target := 477, numerator := 89819410504180651964497920 }, some { target := 478, numerator := 89677739509694562608087040 }, some { target := 479, numerator := 4391800829068770048737280 }, some { target := 480, numerator := 106394916859053106664570880 }, some { target := 481, numerator := 4391800829068770048737280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 521, numerator := 134389105369504363491360768 }, some { target := 522, numerator := 3255684455887025063935868928 }, some { target := 523, numerator := 2466690353395096220212396032 }, some { target := 524, numerator := 2748473961427927950113636352 }, some { target := 525, numerator := 134389105369504363491360768 }, some { target := 526, numerator := 2748473961427927950113636352 }, some { target := 527, numerator := 2744138828996653615807463424 }, some { target := 528, numerator := 134389105369504363491360768 }, some { target := 529, numerator := 3255684455887025063935868928 }, some { target := 530, numerator := 134389105369504363491360768 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 547, numerator := 140537626530200641559592960 }, some { target := 548, numerator := 3404637339489699413266268160 }, some { target := 549, numerator := 2579545467602715001529303040 }, some { target := 550, numerator := 2874221136133780862863933440 }, some { target := 551, numerator := 140537626530200641559592960 }, some { target := 552, numerator := 2874221136133780862863933440 }, some { target := 553, numerator := 2869687664310226003458785280 }, some { target := 554, numerator := 140537626530200641559592960 }, some { target := 555, numerator := 3404637339489699413266268160 }, some { target := 556, numerator := 140537626530200641559592960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 643, numerator := 5270160994882524058484736 }, some { target := 644, numerator := 127673900230863727997485056 }, some { target := 645, numerator := 96732955035101812557348864 }, some { target := 646, numerator := 107783292605016782357397504 }, some { target := 647, numerator := 5270160994882524058484736 }, some { target := 648, numerator := 107783292605016782357397504 }, some { target := 649, numerator := 107613287411633475129704448 }, some { target := 650, numerator := 5270160994882524058484736 }, some { target := 651, numerator := 127673900230863727997485056 }, some { target := 652, numerator := 5270160994882524058484736 }]

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

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 50, #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0], #[797874061312, 139939614294016, 0, 0, 0, 0, 139939631071232, 0, 0, 0, 0, 0, 0, 0, 797857284096, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 128849296787281380848435200 }, some { target := 56, numerator := 22598956111967747103627673600 }, some { target := 61, numerator := 22598958821333282929718067200 }, some { target := 69, numerator := 128846587421745554758041600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 100, numerator := 95951603990528687865856000 }, some { target := 101, numerator := 16829009870614279758020608000 }, some { target := 106, numerator := 16829011888226912820002816000 }, some { target := 114, numerator := 95949586377895625883648000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 101434552789987470029619200 }, some { target := 127, numerator := 17790667577506524315621785600 }, some { target := 132, numerator := 17790669710411307838288691200 }, some { target := 140, numerator := 101432419885203947362713600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 195, numerator := 131590771187010771930316800 }, some { target := 196, numerator := 23079784965413869382428262400 }, some { target := 201, numerator := 23079787732425480438861004800 }, some { target := 209, numerator := 131588004175399715497574400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 240, numerator := 1762768039025998465649868800 }, some { target := 241, numerator := 309172952765856625268778598400 }, some { target := 246, numerator := 309172989832282998378908876800 }, some { target := 254, numerator := 1762730972599625355519590400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 266, numerator := 3188334726885281828228300800 }, some { target := 267, numerator := 559203956557840210245084774400 }, some { target := 272, numerator := 559204023600225703133236428800 }, some { target := 280, numerator := 3188267684499788940076646400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 315, numerator := 95951603990528687865856000 }, some { target := 316, numerator := 16829009870614279758020608000 }, some { target := 321, numerator := 16829011888226912820002816000 }, some { target := 329, numerator := 95949586377895625883648000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 341, numerator := 1762768039025998465649868800 }, some { target := 342, numerator := 309172952765856625268778598400 }, some { target := 347, numerator := 309172989832282998378908876800 }, some { target := 355, numerator := 1762730972599625355519590400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 376, numerator := 104176027189716861111500800 }, some { target := 377, numerator := 18271496430952646594422374400 }, some { target := 382, numerator := 18271498621503505347431628800 }, some { target := 390, numerator := 104173836638858108102246400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 456, numerator := 104176027189716861111500800 }, some { target := 457, numerator := 18271496430952646594422374400 }, some { target := 462, numerator := 18271498621503505347431628800 }, some { target := 470, numerator := 104173836638858108102246400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 482, numerator := 101434552789987470029619200 }, some { target := 483, numerator := 17790667577506524315621785600 }, some { target := 488, numerator := 17790669710411307838288691200 }, some { target := 496, numerator := 101432419885203947362713600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 531, numerator := 101434552789987470029619200 }, some { target := 532, numerator := 17790667577506524315621785600 }, some { target := 537, numerator := 17790669710411307838288691200 }, some { target := 545, numerator := 101432419885203947362713600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 557, numerator := 3188334726885281828228300800 }, some { target := 558, numerator := 559203956557840210245084774400 }, some { target := 563, numerator := 559204023600225703133236428800 }, some { target := 571, numerator := 3188267684499788940076646400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 592, numerator := 101434552789987470029619200 }, some { target := 593, numerator := 17790667577506524315621785600 }, some { target := 598, numerator := 17790669710411307838288691200 }, some { target := 606, numerator := 101432419885203947362713600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 128849296787281380848435200 }, some { target := 654, numerator := 22598956111967747103627673600 }, some { target := 659, numerator := 22598958821333282929718067200 }, some { target := 667, numerator := 128846587421745554758041600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 688, numerator := 131590771187010771930316800 }, some { target := 689, numerator := 23079784965413869382428262400 }, some { target := 694, numerator := 23079787732425480438861004800 }, some { target := 702, numerator := 131588004175399715497574400 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent1
