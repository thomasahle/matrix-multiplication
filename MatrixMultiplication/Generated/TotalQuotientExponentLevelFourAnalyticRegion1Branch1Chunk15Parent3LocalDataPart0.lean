import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk15Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 65; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 8, #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416], #[1924145348608, 38482906972160, 1992864825344, 35802847379456, 53601191854080, 1924145348608, 53669911330816, 53669911330816, 38414187495424, 1992864825344, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 131, numerator := 6346860552976803167207424 }, some { target := 132, numerator := 126937211059536063344148480 }, some { target := 133, numerator := 6573534144154546137464832 }, some { target := 134, numerator := 118096941003604087504109568 }, some { target := 135, numerator := 176805401118639516800778240 }, some { target := 136, numerator := 6346860552976803167207424 }, some { target := 137, numerator := 177032074709817259771035648 }, some { target := 138, numerator := 177032074709817259771035648 }, some { target := 139, numerator := 126710537468358320373891072 }, some { target := 140, numerator := 6573534144154546137464832 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 227, numerator := 92029478018163645924507648 }, some { target := 228, numerator := 1840589560363272918490152960 }, some { target := 229, numerator := 95316245090240918993240064 }, some { target := 230, numerator := 1712405644552259268809588736 }, some { target := 231, numerator := 2563678316220272993611284480 }, some { target := 232, numerator := 92029478018163645924507648 }, some { target := 233, numerator := 2566965083292350266680016896 }, some { target := 234, numerator := 2566965083292350266680016896 }, some { target := 235, numerator := 1837302793291195645421420544 }, some { target := 236, numerator := 95316245090240918993240064 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 253, numerator := 162902754193071281291657216 }, some { target := 254, numerator := 3258055083861425625833144320 }, some { target := 255, numerator := 168720709699966684194930688 }, some { target := 256, numerator := 3031154819092504912605478912 }, some { target := 257, numerator := 4538005295378414264553308160 }, some { target := 258, numerator := 162902754193071281291657216 }, some { target := 259, numerator := 4543823250885309667456581632 }, some { target := 260, numerator := 4543823250885309667456581632 }, some { target := 261, numerator := 3252237128354530222929870848 }, some { target := 262, numerator := 168720709699966684194930688 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 5289050460814002639339520 }, some { target := 303, numerator := 105781009216280052786790400 }, some { target := 304, numerator := 5477945120128788447887360 }, some { target := 305, numerator := 98414117503003406253424640 }, some { target := 306, numerator := 147337834265532930667315200 }, some { target := 307, numerator := 5289050460814002639339520 }, some { target := 308, numerator := 147526728924847716475863040 }, some { target := 309, numerator := 147526728924847716475863040 }, some { target := 310, numerator := 105592114556965266978242560 }, some { target := 311, numerator := 5477945120128788447887360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 328, numerator := 101549768847628850675318784 }, some { target := 329, numerator := 2030995376952577013506375680 }, some { target := 330, numerator := 105176546306472738199437312 }, some { target := 331, numerator := 1889551056057665400065753088 }, some { target := 332, numerator := 2828886417898232268812451840 }, some { target := 333, numerator := 101549768847628850675318784 }, some { target := 334, numerator := 2832513195357076156336570368 }, some { target := 335, numerator := 2832513195357076156336570368 }, some { target := 336, numerator := 2027368599493733125982257152 }, some { target := 337, numerator := 105176546306472738199437312 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 342, numerator := 5289050460814002639339520 }, some { target := 343, numerator := 105781009216280052786790400 }, some { target := 344, numerator := 5477945120128788447887360 }, some { target := 345, numerator := 98414117503003406253424640 }, some { target := 346, numerator := 147337834265532930667315200 }, some { target := 347, numerator := 5289050460814002639339520 }, some { target := 348, numerator := 147526728924847716475863040 }, some { target := 349, numerator := 147526728924847716475863040 }, some { target := 350, numerator := 105592114556965266978242560 }, some { target := 351, numerator := 5477945120128788447887360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 443, numerator := 161844944100908480763789312 }, some { target := 444, numerator := 3236898882018169615275786240 }, some { target := 445, numerator := 167625120675940926505353216 }, some { target := 446, numerator := 3011471995591904231354793984 }, some { target := 447, numerator := 4508537728525307678419845120 }, some { target := 448, numerator := 161844944100908480763789312 }, some { target := 449, numerator := 4514317905100340124161409024 }, some { target := 450, numerator := 4514317905100340124161409024 }, some { target := 451, numerator := 3231118705443137169534222336 }, some { target := 452, numerator := 167625120675940926505353216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 469, numerator := 169249614746048084458864640 }, some { target := 470, numerator := 3384992294920961689177292800 }, some { target := 471, numerator := 175294243844121230332395520 }, some { target := 472, numerator := 3149251760096109000109588480 }, some { target := 473, numerator := 4714810696497053781354086400 }, some { target := 474, numerator := 169249614746048084458864640 }, some { target := 475, numerator := 4720855325595126927227617280 }, some { target := 476, numerator := 4720855325595126927227617280 }, some { target := 477, numerator := 3378947665822888543303761920 }, some { target := 478, numerator := 175294243844121230332395520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 518, numerator := 101549768847628850675318784 }, some { target := 519, numerator := 2030995376952577013506375680 }, some { target := 520, numerator := 105176546306472738199437312 }, some { target := 521, numerator := 1889551056057665400065753088 }, some { target := 522, numerator := 2828886417898232268812451840 }, some { target := 523, numerator := 101549768847628850675318784 }, some { target := 524, numerator := 2832513195357076156336570368 }, some { target := 525, numerator := 2832513195357076156336570368 }, some { target := 526, numerator := 2027368599493733125982257152 }, some { target := 527, numerator := 105176546306472738199437312 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 544, numerator := 2592692535891024093804232704 }, some { target := 545, numerator := 51853850717820481876084654080 }, some { target := 546, numerator := 2685288697887132097154383872 }, some { target := 547, numerator := 48242600399972269745428758528 }, some { target := 548, numerator := 72225006356964242613117911040 }, some { target := 549, numerator := 2592692535891024093804232704 }, some { target := 550, numerator := 72317602518960350616468062208 }, some { target := 551, numerator := 72317602518960350616468062208 }, some { target := 552, numerator := 51761254555824373872734502912 }, some { target := 553, numerator := 2685288697887132097154383872 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 558, numerator := 166076184469559682875260928 }, some { target := 559, numerator := 3321523689391193657505218560 }, some { target := 560, numerator := 172007476772043957263663104 }, some { target := 561, numerator := 3090203289594306956357533696 }, some { target := 562, numerator := 4626407995937734022953697280 }, some { target := 563, numerator := 166076184469559682875260928 }, some { target := 564, numerator := 4632339288240218297342099456 }, some { target := 565, numerator := 4632339288240218297342099456 }, some { target := 566, numerator := 3315592397088709383116816384 }, some { target := 567, numerator := 172007476772043957263663104 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 589, numerator := 92029478018163645924507648 }, some { target := 590, numerator := 1840589560363272918490152960 }, some { target := 591, numerator := 95316245090240918993240064 }, some { target := 592, numerator := 1712405644552259268809588736 }, some { target := 593, numerator := 2563678316220272993611284480 }, some { target := 594, numerator := 92029478018163645924507648 }, some { target := 595, numerator := 2566965083292350266680016896 }, some { target := 596, numerator := 2566965083292350266680016896 }, some { target := 597, numerator := 1837302793291195645421420544 }, some { target := 598, numerator := 95316245090240918993240064 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 603, numerator := 161844944100908480763789312 }, some { target := 604, numerator := 3236898882018169615275786240 }, some { target := 605, numerator := 167625120675940926505353216 }, some { target := 606, numerator := 3011471995591904231354793984 }, some { target := 607, numerator := 4508537728525307678419845120 }, some { target := 608, numerator := 161844944100908480763789312 }, some { target := 609, numerator := 4514317905100340124161409024 }, some { target := 610, numerator := 4514317905100340124161409024 }, some { target := 611, numerator := 3231118705443137169534222336 }, some { target := 612, numerator := 167625120675940926505353216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 658, numerator := 5289050460814002639339520 }, some { target := 659, numerator := 105781009216280052786790400 }, some { target := 660, numerator := 5477945120128788447887360 }, some { target := 661, numerator := 98414117503003406253424640 }, some { target := 662, numerator := 147337834265532930667315200 }, some { target := 663, numerator := 5289050460814002639339520 }, some { target := 664, numerator := 147526728924847716475863040 }, some { target := 665, numerator := 147526728924847716475863040 }, some { target := 666, numerator := 105592114556965266978242560 }, some { target := 667, numerator := 5477945120128788447887360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 684, numerator := 166076184469559682875260928 }, some { target := 685, numerator := 3321523689391193657505218560 }, some { target := 686, numerator := 172007476772043957263663104 }, some { target := 687, numerator := 3090203289594306956357533696 }, some { target := 688, numerator := 4626407995937734022953697280 }, some { target := 689, numerator := 166076184469559682875260928 }, some { target := 690, numerator := 4632339288240218297342099456 }, some { target := 691, numerator := 4632339288240218297342099456 }, some { target := 692, numerator := 3315592397088709383116816384 }, some { target := 693, numerator := 172007476772043957263663104 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 698, numerator := 5289050460814002639339520 }, some { target := 699, numerator := 105781009216280052786790400 }, some { target := 700, numerator := 5477945120128788447887360 }, some { target := 701, numerator := 98414117503003406253424640 }, some { target := 702, numerator := 147337834265532930667315200 }, some { target := 703, numerator := 5289050460814002639339520 }, some { target := 704, numerator := 147526728924847716475863040 }, some { target := 705, numerator := 147526728924847716475863040 }, some { target := 706, numerator := 105592114556965266978242560 }, some { target := 707, numerator := 5477945120128788447887360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 729, numerator := 161844944100908480763789312 }, some { target := 730, numerator := 3236898882018169615275786240 }, some { target := 731, numerator := 167625120675940926505353216 }, some { target := 732, numerator := 3011471995591904231354793984 }, some { target := 733, numerator := 4508537728525307678419845120 }, some { target := 734, numerator := 161844944100908480763789312 }, some { target := 735, numerator := 4514317905100340124161409024 }, some { target := 736, numerator := 4514317905100340124161409024 }, some { target := 737, numerator := 3231118705443137169534222336 }, some { target := 738, numerator := 167625120675940926505353216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 743, numerator := 169249614746048084458864640 }, some { target := 744, numerator := 3384992294920961689177292800 }, some { target := 745, numerator := 175294243844121230332395520 }, some { target := 746, numerator := 3149251760096109000109588480 }, some { target := 747, numerator := 4714810696497053781354086400 }, some { target := 748, numerator := 169249614746048084458864640 }, some { target := 749, numerator := 4720855325595126927227617280 }, some { target := 750, numerator := 4720855325595126927227617280 }, some { target := 751, numerator := 3378947665822888543303761920 }, some { target := 752, numerator := 175294243844121230332395520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 763, numerator := 6346860552976803167207424 }, some { target := 764, numerator := 126937211059536063344148480 }, some { target := 765, numerator := 6573534144154546137464832 }, some { target := 766, numerator := 118096941003604087504109568 }, some { target := 767, numerator := 176805401118639516800778240 }, some { target := 768, numerator := 6346860552976803167207424 }, some { target := 769, numerator := 177032074709817259771035648 }, some { target := 770, numerator := 177032074709817259771035648 }, some { target := 771, numerator := 126710537468358320373891072 }, some { target := 772, numerator := 6573534144154546137464832 }]

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
def data : BetaFourLocalSlotData := ⟨1, 3, #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0], #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 263, numerator := 1363668324525301709068566528 }, some { target := 265, numerator := 1363668324525301709068566528 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 338, numerator := 1015497688476288506753187840 }, some { target := 340, numerator := 1015497688476288506753187840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 352, numerator := 1073526127817790707139084288 }, some { target := 354, numerator := 1073526127817790707139084288 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 479, numerator := 1392682544196052809261514752 }, some { target := 481, numerator := 1392682544196052809261514752 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 554, numerator := 18656143248292957424065708032 }, some { target := 556, numerator := 18656143248292957424065708032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 568, numerator := 33743537477083529524398784512 }, some { target := 570, numerator := 33743537477083529524398784512 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 599, numerator := 1015497688476288506753187840 }, some { target := 601, numerator := 1015497688476288506753187840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 613, numerator := 18656143248292957424065708032 }, some { target := 615, numerator := 18656143248292957424065708032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 618, numerator := 1102540347488541807332032512 }, some { target := 620, numerator := 1102540347488541807332032512 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 694, numerator := 1102540347488541807332032512 }, some { target := 696, numerator := 1102540347488541807332032512 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 708, numerator := 1073526127817790707139084288 }, some { target := 710, numerator := 1073526127817790707139084288 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 739, numerator := 1073526127817790707139084288 }, some { target := 741, numerator := 1073526127817790707139084288 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 753, numerator := 33743537477083529524398784512 }, some { target := 755, numerator := 33743537477083529524398784512 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 758, numerator := 1073526127817790707139084288 }, some { target := 760, numerator := 1073526127817790707139084288 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 773, numerator := 1363668324525301709068566528 }, some { target := 775, numerator := 1363668324525301709068566528 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 778, numerator := 1392682544196052809261514752 }, some { target := 780, numerator := 1392682544196052809261514752 }]

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

namespace Slot2

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨2, 0, #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15.Parent3
