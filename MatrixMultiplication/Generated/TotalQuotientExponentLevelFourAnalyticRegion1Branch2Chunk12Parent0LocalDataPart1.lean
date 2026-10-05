import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk12Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 2,
parent 50; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot5

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨5, 52, #[1653998616576, 139083489738752, 0, 0, 0, 0, 139083456184320, 0, 0, 0, 0, 0, 0, 0, 1654032171008, 0, 0, 0, 0], #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0]⟩

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
  [some { target := 55, numerator := 265968891520419241383690240 }, some { target := 56, numerator := 206864693404770521076203520 }, some { target := 57, numerator := 236416792462594881229946880 }, some { target := 58, numerator := 277789731143548985445187584 }, some { target := 59, numerator := 3280282995418503977065512960 }, some { target := 60, numerator := 7376203924832960294374342656 }, some { target := 61, numerator := 206864693404770521076203520 }, some { target := 62, numerator := 3280282995418503977065512960 }, some { target := 63, numerator := 236416792462594881229946880 }, some { target := 64, numerator := 230506372651030009199198208 }, some { target := 65, numerator := 230506372651030009199198208 }, some { target := 66, numerator := 230506372651030009199198208 }, some { target := 67, numerator := 7376203924832960294374342656 }, some { target := 68, numerator := 230506372651030009199198208 }, some { target := 69, numerator := 265968891520419241383690240 }, some { target := 70, numerator := 277789731143548985445187584 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 100, numerator := 22365122451665438909115924480 }, some { target := 101, numerator := 17395095240184230262645719040 }, some { target := 102, numerator := 19880108845924834585880821760 }, some { target := 103, numerator := 23359127893961680638409965568 }, some { target := 104, numerator := 275836510237207079879096401920 }, some { target := 105, numerator := 620259395992854839079481638912 }, some { target := 106, numerator := 17395095240184230262645719040 }, some { target := 107, numerator := 275836510237207079879096401920 }, some { target := 108, numerator := 19880108845924834585880821760 }, some { target := 109, numerator := 19383106124776713721233801216 }, some { target := 110, numerator := 19383106124776713721233801216 }, some { target := 111, numerator := 19383106124776713721233801216 }, some { target := 112, numerator := 620259395992854839079481638912 }, some { target := 113, numerator := 19383106124776713721233801216 }, some { target := 114, numerator := 22365122451665438909115924480 }, some { target := 115, numerator := 23359127893961680638409965568 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 315, numerator := 22365117055992797349072076800 }, some { target := 316, numerator := 17395091043549953493722726400 }, some { target := 317, numerator := 19880104049771375421397401600 }, some { target := 318, numerator := 23359122258481366120141946880 }, some { target := 319, numerator := 275836443690577833971888947200 }, some { target := 320, numerator := 620259246352866913147598929920 }, some { target := 321, numerator := 17395091043549953493722726400 }, some { target := 322, numerator := 275836443690577833971888947200 }, some { target := 323, numerator := 19880104049771375421397401600 }, some { target := 324, numerator := 19383101448527091035862466560 }, some { target := 325, numerator := 19383101448527091035862466560 }, some { target := 326, numerator := 19383101448527091035862466560 }, some { target := 327, numerator := 620259246352866913147598929920 }, some { target := 328, numerator := 19383101448527091035862466560 }, some { target := 329, numerator := 22365117055992797349072076800 }, some { target := 330, numerator := 23359122258481366120141946880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 265974287193060801427537920 }, some { target := 654, numerator := 206868890039047289999196160 }, some { target := 655, numerator := 236421588616054045713367040 }, some { target := 656, numerator := 277795366623863503713206272 }, some { target := 657, numerator := 3280349542047749884272967680 }, some { target := 658, numerator := 7376353564820886226257051648 }, some { target := 659, numerator := 206868890039047289999196160 }, some { target := 660, numerator := 3280349542047749884272967680 }, some { target := 661, numerator := 236421588616054045713367040 }, some { target := 662, numerator := 230511048900652694570532864 }, some { target := 663, numerator := 230511048900652694570532864 }, some { target := 664, numerator := 230511048900652694570532864 }, some { target := 665, numerator := 7376353564820886226257051648 }, some { target := 666, numerator := 230511048900652694570532864 }, some { target := 667, numerator := 265974287193060801427537920 }, some { target := 668, numerator := 277795366623863503713206272 }]

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

end Slot5

namespace Slot6

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨6, 50, #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0], #[1653998616576, 139083489738752, 0, 0, 0, 0, 139083456184320, 0, 0, 0, 0, 0, 0, 0, 1654032171008, 0, 0, 0, 0]⟩

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
  [some { target := 55, numerator := 255739318769633885945856000 }, some { target := 56, numerator := 21504925434293691258765312000 }, some { target := 61, numerator := 21504920246146920527953920000 }, some { target := 69, numerator := 255744506916404616757248000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 100, numerator := 198908359043048577957888000 }, some { target := 101, numerator := 16726053115561759867928576000 }, some { target := 106, numerator := 16726049080336493743964160000 }, some { target := 114, numerator := 198912394268314701922304000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 227323838906341231951872000 }, some { target := 127, numerator := 19115489274927725563346944000 }, some { target := 132, numerator := 19115484663241707135959040000 }, some { target := 140, numerator := 227328450592359659339776000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 195, numerator := 267105510714950947543449600 }, some { target := 196, numerator := 22460699898040077536932659200 }, some { target := 201, numerator := 22460694479309005884751872000 }, some { target := 209, numerator := 267110929446022599724236800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 240, numerator := 3154118264825484593332224000 }, some { target := 241, numerator := 265227413689622192191438848000 }, some { target := 246, numerator := 265227349702478686511431680000 }, some { target := 254, numerator := 3154182251968990273339392000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 266, numerator := 7092503773877846436898406400 }, some { target := 267, numerator := 596403265377745037576424652800 }, some { target := 272, numerator := 596403121493141262641922048000 }, some { target := 280, numerator := 7092647658481621371401011200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 315, numerator := 198908359043048577957888000 }, some { target := 316, numerator := 16726053115561759867928576000 }, some { target := 321, numerator := 16726049080336493743964160000 }, some { target := 329, numerator := 198912394268314701922304000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 341, numerator := 3154118264825484593332224000 }, some { target := 342, numerator := 265227413689622192191438848000 }, some { target := 347, numerator := 265227349702478686511431680000 }, some { target := 355, numerator := 3154182251968990273339392000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 376, numerator := 227323838906341231951872000 }, some { target := 377, numerator := 19115489274927725563346944000 }, some { target := 382, numerator := 19115484663241707135959040000 }, some { target := 390, numerator := 227328450592359659339776000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 456, numerator := 221640742933682701153075200 }, some { target := 457, numerator := 18637602043054532424263270400 }, some { target := 462, numerator := 18637597546660664457560064000 }, some { target := 470, numerator := 221645239327550667856281600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 482, numerator := 221640742933682701153075200 }, some { target := 483, numerator := 18637602043054532424263270400 }, some { target := 488, numerator := 18637597546660664457560064000 }, some { target := 496, numerator := 221645239327550667856281600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 531, numerator := 221640742933682701153075200 }, some { target := 532, numerator := 18637602043054532424263270400 }, some { target := 537, numerator := 18637597546660664457560064000 }, some { target := 545, numerator := 221645239327550667856281600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 557, numerator := 7092503773877846436898406400 }, some { target := 558, numerator := 596403265377745037576424652800 }, some { target := 563, numerator := 596403121493141262641922048000 }, some { target := 571, numerator := 7092647658481621371401011200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 592, numerator := 221640742933682701153075200 }, some { target := 593, numerator := 18637602043054532424263270400 }, some { target := 598, numerator := 18637597546660664457560064000 }, some { target := 606, numerator := 221645239327550667856281600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 255739318769633885945856000 }, some { target := 654, numerator := 21504925434293691258765312000 }, some { target := 659, numerator := 21504920246146920527953920000 }, some { target := 667, numerator := 255744506916404616757248000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 688, numerator := 267105510714950947543449600 }, some { target := 689, numerator := 22460699898040077536932659200 }, some { target := 694, numerator := 22460694479309005884751872000 }, some { target := 702, numerator := 267110929446022599724236800 }]

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

end Slot6

namespace Slot7

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨7, 27, #[147035521024, 23473808211968, 0, 234233306021888, 0, 0, 0, 0, 0, 0, 0, 23473808211968, 0, 0, 0, 0, 0, 0, 147018743808], #[2130303778816, 50989851738112, 38139309588480, 44255343017984, 2130303778816, 44186623541248, 44392781971456, 2130303778816, 50989851738112, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 11, numerator := 8457218803555378573344768 }, some { target := 12, numerator := 202427624265744867787800576 }, some { target := 13, numerator := 151411497934620487361495040 }, some { target := 14, numerator := 175691900306118187136581632 }, some { target := 15, numerator := 8457218803555378573344768 }, some { target := 16, numerator := 175419086796326078150344704 }, some { target := 17, numerator := 176237527325702405109055488 }, some { target := 18, numerator := 8457218803555378573344768 }, some { target := 19, numerator := 202427624265744867787800576 }, some { target := 20, numerator := 8457218803555378573344768 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 31, numerator := 1350171243103252033333886976 }, some { target := 32, numerator := 32317002012342355120443359232 }, some { target := 33, numerator := 24172420642654996080655073280 }, some { target := 34, numerator := 28048718727693364821516877824 }, some { target := 35, numerator := 1350171243103252033333886976 }, some { target := 36, numerator := 28005164816625517981731913728 }, some { target := 37, numerator := 28135826549829058501086806016 }, some { target := 38, numerator := 1350171243103252033333886976 }, some { target := 39, numerator := 32317002012342355120443359232 }, some { target := 40, numerator := 1350171243103252033333886976 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 76, numerator := 13472678617460798439781564416 }, some { target := 77, numerator := 322475081746964917494126477312 }, some { target := 78, numerator := 241204407506153004325121556480 }, some { target := 79, numerator := 279884033214346909523204112384 }, some { target := 80, numerator := 13472678617460798439781564416 }, some { target := 81, numerator := 279449430678299786992888578048 }, some { target := 82, numerator := 280753238286441154583835181056 }, some { target := 83, numerator := 13472678617460798439781564416 }, some { target := 84, numerator := 322475081746964917494126477312 }, some { target := 85, numerator := 13472678617460798439781564416 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 305, numerator := 1350171243103252033333886976 }, some { target := 306, numerator := 32317002012342355120443359232 }, some { target := 307, numerator := 24172420642654996080655073280 }, some { target := 308, numerator := 28048718727693364821516877824 }, some { target := 309, numerator := 1350171243103252033333886976 }, some { target := 310, numerator := 28005164816625517981731913728 }, some { target := 311, numerator := 28135826549829058501086806016 }, some { target := 312, numerator := 1350171243103252033333886976 }, some { target := 313, numerator := 32317002012342355120443359232 }, some { target := 314, numerator := 1350171243103252033333886976 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 643, numerator := 8456253808256022642425856 }, some { target := 644, numerator := 202404526636321574215483392 }, some { target := 645, numerator := 151394221405873953759559680 }, some { target := 646, numerator := 175671853306996083281362944 }, some { target := 647, numerator := 8456253808256022642425856 }, some { target := 648, numerator := 175399070926084598679994368 }, some { target := 649, numerator := 176217418068819052484100096 }, some { target := 650, numerator := 8456253808256022642425856 }, some { target := 651, numerator := 202404526636321574215483392 }, some { target := 652, numerator := 8456253808256022642425856 }]

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

end Slot7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent0
