import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk15Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 7, for region 1, branch 1,
parent 65; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot28

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨28, 8, #[1924145348608, 38482906972160, 1992864825344, 35802847379456, 53601191854080, 1924145348608, 53669911330816, 53669911330816, 38414187495424, 1992864825344, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

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
  [some { target := 26, numerator := 6346860552976803167207424 }, some { target := 27, numerator := 92029478018163645924507648 }, some { target := 28, numerator := 162902754193071281291657216 }, some { target := 29, numerator := 5289050460814002639339520 }, some { target := 30, numerator := 101549768847628850675318784 }, some { target := 31, numerator := 5289050460814002639339520 }, some { target := 32, numerator := 161844944100908480763789312 }, some { target := 33, numerator := 169249614746048084458864640 }, some { target := 34, numerator := 101549768847628850675318784 }, some { target := 35, numerator := 2592692535891024093804232704 }, some { target := 36, numerator := 166076184469559682875260928 }, some { target := 37, numerator := 92029478018163645924507648 }, some { target := 38, numerator := 161844944100908480763789312 }, some { target := 39, numerator := 5289050460814002639339520 }, some { target := 40, numerator := 166076184469559682875260928 }, some { target := 41, numerator := 5289050460814002639339520 }, some { target := 42, numerator := 161844944100908480763789312 }, some { target := 43, numerator := 169249614746048084458864640 }, some { target := 44, numerator := 6346860552976803167207424 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 61, numerator := 126937211059536063344148480 }, some { target := 62, numerator := 1840589560363272918490152960 }, some { target := 63, numerator := 3258055083861425625833144320 }, some { target := 64, numerator := 105781009216280052786790400 }, some { target := 65, numerator := 2030995376952577013506375680 }, some { target := 66, numerator := 105781009216280052786790400 }, some { target := 67, numerator := 3236898882018169615275786240 }, some { target := 68, numerator := 3384992294920961689177292800 }, some { target := 69, numerator := 2030995376952577013506375680 }, some { target := 70, numerator := 51853850717820481876084654080 }, some { target := 71, numerator := 3321523689391193657505218560 }, some { target := 72, numerator := 1840589560363272918490152960 }, some { target := 73, numerator := 3236898882018169615275786240 }, some { target := 74, numerator := 105781009216280052786790400 }, some { target := 75, numerator := 3321523689391193657505218560 }, some { target := 76, numerator := 105781009216280052786790400 }, some { target := 77, numerator := 3236898882018169615275786240 }, some { target := 78, numerator := 3384992294920961689177292800 }, some { target := 79, numerator := 126937211059536063344148480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 96, numerator := 6573534144154546137464832 }, some { target := 97, numerator := 95316245090240918993240064 }, some { target := 98, numerator := 168720709699966684194930688 }, some { target := 99, numerator := 5477945120128788447887360 }, some { target := 100, numerator := 105176546306472738199437312 }, some { target := 101, numerator := 5477945120128788447887360 }, some { target := 102, numerator := 167625120675940926505353216 }, some { target := 103, numerator := 175294243844121230332395520 }, some { target := 104, numerator := 105176546306472738199437312 }, some { target := 105, numerator := 2685288697887132097154383872 }, some { target := 106, numerator := 172007476772043957263663104 }, some { target := 107, numerator := 95316245090240918993240064 }, some { target := 108, numerator := 167625120675940926505353216 }, some { target := 109, numerator := 5477945120128788447887360 }, some { target := 110, numerator := 172007476772043957263663104 }, some { target := 111, numerator := 5477945120128788447887360 }, some { target := 112, numerator := 167625120675940926505353216 }, some { target := 113, numerator := 175294243844121230332395520 }, some { target := 114, numerator := 6573534144154546137464832 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 157, numerator := 118096941003604087504109568 }, some { target := 158, numerator := 1712405644552259268809588736 }, some { target := 159, numerator := 3031154819092504912605478912 }, some { target := 160, numerator := 98414117503003406253424640 }, some { target := 161, numerator := 1889551056057665400065753088 }, some { target := 162, numerator := 98414117503003406253424640 }, some { target := 163, numerator := 3011471995591904231354793984 }, some { target := 164, numerator := 3149251760096109000109588480 }, some { target := 165, numerator := 1889551056057665400065753088 }, some { target := 166, numerator := 48242600399972269745428758528 }, some { target := 167, numerator := 3090203289594306956357533696 }, some { target := 168, numerator := 1712405644552259268809588736 }, some { target := 169, numerator := 3011471995591904231354793984 }, some { target := 170, numerator := 98414117503003406253424640 }, some { target := 171, numerator := 3090203289594306956357533696 }, some { target := 172, numerator := 98414117503003406253424640 }, some { target := 173, numerator := 3011471995591904231354793984 }, some { target := 174, numerator := 3149251760096109000109588480 }, some { target := 175, numerator := 118096941003604087504109568 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 192, numerator := 176805401118639516800778240 }, some { target := 193, numerator := 2563678316220272993611284480 }, some { target := 194, numerator := 4538005295378414264553308160 }, some { target := 195, numerator := 147337834265532930667315200 }, some { target := 196, numerator := 2828886417898232268812451840 }, some { target := 197, numerator := 147337834265532930667315200 }, some { target := 198, numerator := 4508537728525307678419845120 }, some { target := 199, numerator := 4714810696497053781354086400 }, some { target := 200, numerator := 2828886417898232268812451840 }, some { target := 201, numerator := 72225006356964242613117911040 }, some { target := 202, numerator := 4626407995937734022953697280 }, some { target := 203, numerator := 2563678316220272993611284480 }, some { target := 204, numerator := 4508537728525307678419845120 }, some { target := 205, numerator := 147337834265532930667315200 }, some { target := 206, numerator := 4626407995937734022953697280 }, some { target := 207, numerator := 147337834265532930667315200 }, some { target := 208, numerator := 4508537728525307678419845120 }, some { target := 209, numerator := 4714810696497053781354086400 }, some { target := 210, numerator := 176805401118639516800778240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 6346860552976803167207424 }, some { target := 268, numerator := 92029478018163645924507648 }, some { target := 269, numerator := 162902754193071281291657216 }, some { target := 270, numerator := 5289050460814002639339520 }, some { target := 271, numerator := 101549768847628850675318784 }, some { target := 272, numerator := 5289050460814002639339520 }, some { target := 273, numerator := 161844944100908480763789312 }, some { target := 274, numerator := 169249614746048084458864640 }, some { target := 275, numerator := 101549768847628850675318784 }, some { target := 276, numerator := 2592692535891024093804232704 }, some { target := 277, numerator := 166076184469559682875260928 }, some { target := 278, numerator := 92029478018163645924507648 }, some { target := 279, numerator := 161844944100908480763789312 }, some { target := 280, numerator := 5289050460814002639339520 }, some { target := 281, numerator := 166076184469559682875260928 }, some { target := 282, numerator := 5289050460814002639339520 }, some { target := 283, numerator := 161844944100908480763789312 }, some { target := 284, numerator := 169249614746048084458864640 }, some { target := 285, numerator := 6346860552976803167207424 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 373, numerator := 177032074709817259771035648 }, some { target := 374, numerator := 2566965083292350266680016896 }, some { target := 375, numerator := 4543823250885309667456581632 }, some { target := 376, numerator := 147526728924847716475863040 }, some { target := 377, numerator := 2832513195357076156336570368 }, some { target := 378, numerator := 147526728924847716475863040 }, some { target := 379, numerator := 4514317905100340124161409024 }, some { target := 380, numerator := 4720855325595126927227617280 }, some { target := 381, numerator := 2832513195357076156336570368 }, some { target := 382, numerator := 72317602518960350616468062208 }, some { target := 383, numerator := 4632339288240218297342099456 }, some { target := 384, numerator := 2566965083292350266680016896 }, some { target := 385, numerator := 4514317905100340124161409024 }, some { target := 386, numerator := 147526728924847716475863040 }, some { target := 387, numerator := 4632339288240218297342099456 }, some { target := 388, numerator := 147526728924847716475863040 }, some { target := 389, numerator := 4514317905100340124161409024 }, some { target := 390, numerator := 4720855325595126927227617280 }, some { target := 391, numerator := 177032074709817259771035648 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 408, numerator := 177032074709817259771035648 }, some { target := 409, numerator := 2566965083292350266680016896 }, some { target := 410, numerator := 4543823250885309667456581632 }, some { target := 411, numerator := 147526728924847716475863040 }, some { target := 412, numerator := 2832513195357076156336570368 }, some { target := 413, numerator := 147526728924847716475863040 }, some { target := 414, numerator := 4514317905100340124161409024 }, some { target := 415, numerator := 4720855325595126927227617280 }, some { target := 416, numerator := 2832513195357076156336570368 }, some { target := 417, numerator := 72317602518960350616468062208 }, some { target := 418, numerator := 4632339288240218297342099456 }, some { target := 419, numerator := 2566965083292350266680016896 }, some { target := 420, numerator := 4514317905100340124161409024 }, some { target := 421, numerator := 147526728924847716475863040 }, some { target := 422, numerator := 4632339288240218297342099456 }, some { target := 423, numerator := 147526728924847716475863040 }, some { target := 424, numerator := 4514317905100340124161409024 }, some { target := 425, numerator := 4720855325595126927227617280 }, some { target := 426, numerator := 177032074709817259771035648 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 483, numerator := 126710537468358320373891072 }, some { target := 484, numerator := 1837302793291195645421420544 }, some { target := 485, numerator := 3252237128354530222929870848 }, some { target := 486, numerator := 105592114556965266978242560 }, some { target := 487, numerator := 2027368599493733125982257152 }, some { target := 488, numerator := 105592114556965266978242560 }, some { target := 489, numerator := 3231118705443137169534222336 }, some { target := 490, numerator := 3378947665822888543303761920 }, some { target := 491, numerator := 2027368599493733125982257152 }, some { target := 492, numerator := 51761254555824373872734502912 }, some { target := 493, numerator := 3315592397088709383116816384 }, some { target := 494, numerator := 1837302793291195645421420544 }, some { target := 495, numerator := 3231118705443137169534222336 }, some { target := 496, numerator := 105592114556965266978242560 }, some { target := 497, numerator := 3315592397088709383116816384 }, some { target := 498, numerator := 105592114556965266978242560 }, some { target := 499, numerator := 3231118705443137169534222336 }, some { target := 500, numerator := 3378947665822888543303761920 }, some { target := 501, numerator := 126710537468358320373891072 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 623, numerator := 6573534144154546137464832 }, some { target := 624, numerator := 95316245090240918993240064 }, some { target := 625, numerator := 168720709699966684194930688 }, some { target := 626, numerator := 5477945120128788447887360 }, some { target := 627, numerator := 105176546306472738199437312 }, some { target := 628, numerator := 5477945120128788447887360 }, some { target := 629, numerator := 167625120675940926505353216 }, some { target := 630, numerator := 175294243844121230332395520 }, some { target := 631, numerator := 105176546306472738199437312 }, some { target := 632, numerator := 2685288697887132097154383872 }, some { target := 633, numerator := 172007476772043957263663104 }, some { target := 634, numerator := 95316245090240918993240064 }, some { target := 635, numerator := 167625120675940926505353216 }, some { target := 636, numerator := 5477945120128788447887360 }, some { target := 637, numerator := 172007476772043957263663104 }, some { target := 638, numerator := 5477945120128788447887360 }, some { target := 639, numerator := 167625120675940926505353216 }, some { target := 640, numerator := 175294243844121230332395520 }, some { target := 641, numerator := 6573534144154546137464832 }]

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

end Slot28

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15.Parent3
