import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk16Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 2,
parent 69; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot6

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨6, 236, #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0], #[3710583308288, 0, 137026905047040, 0, 0, 137026871492608, 0, 0, 0, 0, 0, 0, 3710616862720, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 200, numerator := 2707986826174021341712220160 }, some { target := 202, numerator := 100002350808284873341324492800 }, some { target := 205, numerator := 100002326320232115491894722560 }, some { target := 212, numerator := 2708011314226779191141990400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 296, numerator := 2106211975913127710220615680 }, some { target := 298, numerator := 77779606184221568154363494400 }, some { target := 301, numerator := 77779587137958312049251450880 }, some { target := 308, numerator := 2106231022176383815332659200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 331, numerator := 2407099401043574525966417920 }, some { target := 333, numerator := 88890978496253220747843993600 }, some { target := 336, numerator := 88890956729095213770573086720 }, some { target := 343, numerator := 2407121168201581503237324800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 467, numerator := 2828341796226200068010541056 }, some { target := 469, numerator := 104446899733097534378716692480 }, some { target := 472, numerator := 104446874156686876180423376896 }, some { target := 479, numerator := 2828367372636858266303856640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 563, numerator := 33398504189479596547784048640 }, some { target := 565, numerator := 1233362326635513437876335411200 }, some { target := 568, numerator := 1233362024616196091066701578240 }, some { target := 575, numerator := 33398806208796943357417881600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 598, numerator := 75101501312559525210152239104 }, some { target := 600, numerator := 2773398529083100487332732600320 }, some { target := 603, numerator := 2773397849947770669641880305664 }, some { target := 610, numerator := 75102180447889342901004533760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 659, numerator := 2106211975913127710220615680 }, some { target := 661, numerator := 77779606184221568154363494400 }, some { target := 664, numerator := 77779587137958312049251450880 }, some { target := 671, numerator := 2106231022176383815332659200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 694, numerator := 33398504189479596547784048640 }, some { target := 696, numerator := 1233362326635513437876335411200 }, some { target := 699, numerator := 1233362024616196091066701578240 }, some { target := 706, numerator := 33398806208796943357417881600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 720, numerator := 2407099401043574525966417920 }, some { target := 722, numerator := 88890978496253220747843993600 }, some { target := 725, numerator := 88890956729095213770573086720 }, some { target := 732, numerator := 2407121168201581503237324800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 830, numerator := 2346921916017485162817257472 }, some { target := 832, numerator := 86668704033846890229147893760 }, some { target := 835, numerator := 86668682810867833426308759552 }, some { target := 842, numerator := 2346943138996541965656391680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 865, numerator := 2346921916017485162817257472 }, some { target := 867, numerator := 86668704033846890229147893760 }, some { target := 870, numerator := 86668682810867833426308759552 }, some { target := 877, numerator := 2346943138996541965656391680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 926, numerator := 2346921916017485162817257472 }, some { target := 928, numerator := 86668704033846890229147893760 }, some { target := 931, numerator := 86668682810867833426308759552 }, some { target := 938, numerator := 2346943138996541965656391680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 961, numerator := 75101501312559525210152239104 }, some { target := 963, numerator := 2773398529083100487332732600320 }, some { target := 966, numerator := 2773397849947770669641880305664 }, some { target := 973, numerator := 75102180447889342901004533760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 987, numerator := 2346921916017485162817257472 }, some { target := 989, numerator := 86668704033846890229147893760 }, some { target := 992, numerator := 86668682810867833426308759552 }, some { target := 999, numerator := 2346943138996541965656391680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1036, numerator := 2707986826174021341712220160 }, some { target := 1038, numerator := 100002350808284873341324492800 }, some { target := 1041, numerator := 100002326320232115491894722560 }, some { target := 1048, numerator := 2708011314226779191141990400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1062, numerator := 2828341796226200068010541056 }, some { target := 1064, numerator := 104446899733097534378716692480 }, some { target := 1067, numerator := 104446874156686876180423376896 }, some { target := 1074, numerator := 2828367372636858266303856640 }]

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
def data : BetaFourLocalSlotData := ⟨7, 570, #[147035521024, 23473808211968, 0, 234233306021888, 0, 0, 0, 0, 0, 0, 0, 23473808211968, 0, 0, 0, 0, 0, 0, 147018743808], #[343597383680, 5772436045824, 12506944765952, 412316860416, 6597069766656, 481036337152, 12506944765952, 12506944765952, 6597069766656, 154343944749056, 12369505812480, 5772436045824, 12506944765952, 481036337152, 12369505812480, 481036337152, 12506944765952, 12506944765952, 412316860416]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 71, numerator := 28796981589167059658342400 }, some { target := 72, numerator := 483789290698006602260152320 }, some { target := 73, numerator := 1048210129845680971563663360 }, some { target := 74, numerator := 34556377907000471590010880 }, some { target := 75, numerator := 552902046512007545440174080 }, some { target := 76, numerator := 40315774224833883521679360 }, some { target := 77, numerator := 1048210129845680971563663360 }, some { target := 78, numerator := 1048210129845680971563663360 }, some { target := 79, numerator := 552902046512007545440174080 }, some { target := 80, numerator := 12935604129853843198527406080 }, some { target := 81, numerator := 1036691337210014147700326400 }, some { target := 82, numerator := 483789290698006602260152320 }, some { target := 83, numerator := 1048210129845680971563663360 }, some { target := 84, numerator := 40315774224833883521679360 }, some { target := 85, numerator := 1036691337210014147700326400 }, some { target := 86, numerator := 40315774224833883521679360 }, some { target := 87, numerator := 1048210129845680971563663360 }, some { target := 88, numerator := 1048210129845680971563663360 }, some { target := 89, numerator := 34556377907000471590010880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 146, numerator := 4597357279383833088412876800 }, some { target := 147, numerator := 77235602293648395885336330240 }, some { target := 148, numerator := 167343804969571524418228715520 }, some { target := 149, numerator := 5516828735260599706095452160 }, some { target := 150, numerator := 88269259764169595297527234560 }, some { target := 151, numerator := 6436300191137366323778027520 }, some { target := 152, numerator := 167343804969571524418228715520 }, some { target := 153, numerator := 167343804969571524418228715520 }, some { target := 154, numerator := 88269259764169595297527234560 }, some { target := 155, numerator := 2065132889899217823315064258560 }, some { target := 156, numerator := 165504862057817991182863564800 }, some { target := 157, numerator := 77235602293648395885336330240 }, some { target := 158, numerator := 167343804969571524418228715520 }, some { target := 159, numerator := 6436300191137366323778027520 }, some { target := 160, numerator := 165504862057817991182863564800 }, some { target := 161, numerator := 6436300191137366323778027520 }, some { target := 162, numerator := 167343804969571524418228715520 }, some { target := 163, numerator := 167343804969571524418228715520 }, some { target := 164, numerator := 5516828735260599706095452160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 242, numerator := 45874712138307378199973068800 }, some { target := 243, numerator := 770695163923563953759547555840 }, some { target := 244, numerator := 1669839521834388566479019704320 }, some { target := 245, numerator := 55049654565968853839967682560 }, some { target := 246, numerator := 880794473055501661439482920960 }, some { target := 247, numerator := 64224596993630329479962296320 }, some { target := 248, numerator := 1669839521834388566479019704320 }, some { target := 249, numerator := 1669839521834388566479019704320 }, some { target := 250, numerator := 880794473055501661439482920960 }, some { target := 251, numerator := 20606920692527674287427902504960 }, some { target := 252, numerator := 1651489636979065615199030476800 }, some { target := 253, numerator := 770695163923563953759547555840 }, some { target := 254, numerator := 1669839521834388566479019704320 }, some { target := 255, numerator := 64224596993630329479962296320 }, some { target := 256, numerator := 1651489636979065615199030476800 }, some { target := 257, numerator := 64224596993630329479962296320 }, some { target := 258, numerator := 1669839521834388566479019704320 }, some { target := 259, numerator := 1669839521834388566479019704320 }, some { target := 260, numerator := 55049654565968853839967682560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 640, numerator := 4597357279383833088412876800 }, some { target := 641, numerator := 77235602293648395885336330240 }, some { target := 642, numerator := 167343804969571524418228715520 }, some { target := 643, numerator := 5516828735260599706095452160 }, some { target := 644, numerator := 88269259764169595297527234560 }, some { target := 645, numerator := 6436300191137366323778027520 }, some { target := 646, numerator := 167343804969571524418228715520 }, some { target := 647, numerator := 167343804969571524418228715520 }, some { target := 648, numerator := 88269259764169595297527234560 }, some { target := 649, numerator := 2065132889899217823315064258560 }, some { target := 650, numerator := 165504862057817991182863564800 }, some { target := 651, numerator := 77235602293648395885336330240 }, some { target := 652, numerator := 167343804969571524418228715520 }, some { target := 653, numerator := 6436300191137366323778027520 }, some { target := 654, numerator := 165504862057817991182863564800 }, some { target := 655, numerator := 6436300191137366323778027520 }, some { target := 656, numerator := 167343804969571524418228715520 }, some { target := 657, numerator := 167343804969571524418228715520 }, some { target := 658, numerator := 5516828735260599706095452160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1017, numerator := 28793695762878930144460800 }, some { target := 1018, numerator := 483734088816366026426941440 }, some { target := 1019, numerator := 1048090525768793057258373120 }, some { target := 1020, numerator := 34552434915454716173352960 }, some { target := 1021, numerator := 552838958647275458773647360 }, some { target := 1022, numerator := 40311174068030502202245120 }, some { target := 1023, numerator := 1048090525768793057258373120 }, some { target := 1024, numerator := 1048090525768793057258373120 }, some { target := 1025, numerator := 552838958647275458773647360 }, some { target := 1026, numerator := 12934128136685215420891791360 }, some { target := 1027, numerator := 1036573047463641485200588800 }, some { target := 1028, numerator := 483734088816366026426941440 }, some { target := 1029, numerator := 1048090525768793057258373120 }, some { target := 1030, numerator := 40311174068030502202245120 }, some { target := 1031, numerator := 1036573047463641485200588800 }, some { target := 1032, numerator := 40311174068030502202245120 }, some { target := 1033, numerator := 1048090525768793057258373120 }, some { target := 1034, numerator := 1048090525768793057258373120 }, some { target := 1035, numerator := 34552434915454716173352960 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16.Parent3
