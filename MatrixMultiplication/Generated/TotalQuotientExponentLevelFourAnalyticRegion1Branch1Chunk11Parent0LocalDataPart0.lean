import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk11Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 46; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 166, #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416], #[412316860416, 6184752906240, 10857677324288, 412316860416, 6871947673600, 412316860416, 10857677324288, 10788957847552, 6871947673600, 166507292131328, 10651518894080, 6184752906240, 10857677324288, 412316860416, 10651518894080, 412316860416, 10857677324288, 10857677324288, 412316860416]⟩

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
  [some { target := 71, numerator := 28220862101628999797047296 }, some { target := 72, numerator := 423312931524434996955709440 }, some { target := 73, numerator := 743149368676230327988912128 }, some { target := 74, numerator := 28220862101628999797047296 }, some { target := 75, numerator := 470347701693816663284121600 }, some { target := 76, numerator := 28220862101628999797047296 }, some { target := 77, numerator := 743149368676230327988912128 }, some { target := 78, numerator := 738445891659292161356070912 }, some { target := 79, numerator := 470347701693816663284121600 }, some { target := 80, numerator := 11396524812041177751374266368 }, some { target := 81, numerator := 729038937625415828090388480 }, some { target := 82, numerator := 423312931524434996955709440 }, some { target := 83, numerator := 743149368676230327988912128 }, some { target := 84, numerator := 28220862101628999797047296 }, some { target := 85, numerator := 729038937625415828090388480 }, some { target := 86, numerator := 28220862101628999797047296 }, some { target := 87, numerator := 743149368676230327988912128 }, some { target := 88, numerator := 743149368676230327988912128 }, some { target := 89, numerator := 28220862101628999797047296 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 146, numerator := 409202500473620497057185792 }, some { target := 147, numerator := 6138037507104307455857786880 }, some { target := 148, numerator := 10775665845805339755839225856 }, some { target := 149, numerator := 409202500473620497057185792 }, some { target := 150, numerator := 6820041674560341617619763200 }, some { target := 151, numerator := 409202500473620497057185792 }, some { target := 152, numerator := 10775665845805339755839225856 }, some { target := 153, numerator := 10707465429059736339663028224 }, some { target := 154, numerator := 6820041674560341617619763200 }, some { target := 155, numerator := 165249609774597077394926862336 }, some { target := 156, numerator := 10571064595568529507310632960 }, some { target := 157, numerator := 6138037507104307455857786880 }, some { target := 158, numerator := 10775665845805339755839225856 }, some { target := 159, numerator := 409202500473620497057185792 }, some { target := 160, numerator := 10571064595568529507310632960 }, some { target := 161, numerator := 409202500473620497057185792 }, some { target := 162, numerator := 10775665845805339755839225856 }, some { target := 163, numerator := 10775665845805339755839225856 }, some { target := 164, numerator := 409202500473620497057185792 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 181, numerator := 724335460608477661457547264 }, some { target := 182, numerator := 10865031909127164921863208960 }, some { target := 183, numerator := 19074167129356578418382077952 }, some { target := 184, numerator := 724335460608477661457547264 }, some { target := 185, numerator := 12072257676807961024292454400 }, some { target := 186, numerator := 724335460608477661457547264 }, some { target := 187, numerator := 19074167129356578418382077952 }, some { target := 188, numerator := 18953444552588498808139153408 }, some { target := 189, numerator := 12072257676807961024292454400 }, some { target := 190, numerator := 292510803509056895618606170112 }, some { target := 191, numerator := 18711999399052339587653304320 }, some { target := 192, numerator := 10865031909127164921863208960 }, some { target := 193, numerator := 19074167129356578418382077952 }, some { target := 194, numerator := 724335460608477661457547264 }, some { target := 195, numerator := 18711999399052339587653304320 }, some { target := 196, numerator := 724335460608477661457547264 }, some { target := 197, numerator := 19074167129356578418382077952 }, some { target := 198, numerator := 19074167129356578418382077952 }, some { target := 199, numerator := 724335460608477661457547264 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 242, numerator := 23517385084690833164206080 }, some { target := 243, numerator := 352760776270362497463091200 }, some { target := 244, numerator := 619291140563525273324093440 }, some { target := 245, numerator := 23517385084690833164206080 }, some { target := 246, numerator := 391956418078180552736768000 }, some { target := 247, numerator := 23517385084690833164206080 }, some { target := 248, numerator := 619291140563525273324093440 }, some { target := 249, numerator := 615371576382743467796725760 }, some { target := 250, numerator := 391956418078180552736768000 }, some { target := 251, numerator := 9497104010034314792811888640 }, some { target := 252, numerator := 607532448021179856741990400 }, some { target := 253, numerator := 352760776270362497463091200 }, some { target := 254, numerator := 619291140563525273324093440 }, some { target := 255, numerator := 23517385084690833164206080 }, some { target := 256, numerator := 607532448021179856741990400 }, some { target := 257, numerator := 23517385084690833164206080 }, some { target := 258, numerator := 619291140563525273324093440 }, some { target := 259, numerator := 619291140563525273324093440 }, some { target := 260, numerator := 23517385084690833164206080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 277, numerator := 451533793626063996752756736 }, some { target := 278, numerator := 6773006904390959951291351040 }, some { target := 279, numerator := 11890389898819685247822594048 }, some { target := 280, numerator := 451533793626063996752756736 }, some { target := 281, numerator := 7525563227101066612545945600 }, some { target := 282, numerator := 451533793626063996752756736 }, some { target := 283, numerator := 11890389898819685247822594048 }, some { target := 284, numerator := 11815134266548674581697134592 }, some { target := 285, numerator := 7525563227101066612545945600 }, some { target := 286, numerator := 182344396992658844021988261888 }, some { target := 287, numerator := 11664623002006653249446215680 }, some { target := 288, numerator := 6773006904390959951291351040 }, some { target := 289, numerator := 11890389898819685247822594048 }, some { target := 290, numerator := 451533793626063996752756736 }, some { target := 291, numerator := 11664623002006653249446215680 }, some { target := 292, numerator := 451533793626063996752756736 }, some { target := 293, numerator := 11890389898819685247822594048 }, some { target := 294, numerator := 11890389898819685247822594048 }, some { target := 295, numerator := 451533793626063996752756736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 312, numerator := 23517385084690833164206080 }, some { target := 313, numerator := 352760776270362497463091200 }, some { target := 314, numerator := 619291140563525273324093440 }, some { target := 315, numerator := 23517385084690833164206080 }, some { target := 316, numerator := 391956418078180552736768000 }, some { target := 317, numerator := 23517385084690833164206080 }, some { target := 318, numerator := 619291140563525273324093440 }, some { target := 319, numerator := 615371576382743467796725760 }, some { target := 320, numerator := 391956418078180552736768000 }, some { target := 321, numerator := 9497104010034314792811888640 }, some { target := 322, numerator := 607532448021179856741990400 }, some { target := 323, numerator := 352760776270362497463091200 }, some { target := 324, numerator := 619291140563525273324093440 }, some { target := 325, numerator := 23517385084690833164206080 }, some { target := 326, numerator := 607532448021179856741990400 }, some { target := 327, numerator := 23517385084690833164206080 }, some { target := 328, numerator := 619291140563525273324093440 }, some { target := 329, numerator := 619291140563525273324093440 }, some { target := 330, numerator := 23517385084690833164206080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 413, numerator := 719631983591539494824706048 }, some { target := 414, numerator := 10794479753873092422370590720 }, some { target := 415, numerator := 18950308901243873363717259264 }, some { target := 416, numerator := 719631983591539494824706048 }, some { target := 417, numerator := 11993866393192324913745100800 }, some { target := 418, numerator := 719631983591539494824706048 }, some { target := 419, numerator := 18950308901243873363717259264 }, some { target := 420, numerator := 18830370237311950114579808256 }, some { target := 421, numerator := 11993866393192324913745100800 }, some { target := 422, numerator := 290611382707050032660043792384 }, some { target := 423, numerator := 18590492909448103616304906240 }, some { target := 424, numerator := 10794479753873092422370590720 }, some { target := 425, numerator := 18950308901243873363717259264 }, some { target := 426, numerator := 719631983591539494824706048 }, some { target := 427, numerator := 18590492909448103616304906240 }, some { target := 428, numerator := 719631983591539494824706048 }, some { target := 429, numerator := 18950308901243873363717259264 }, some { target := 430, numerator := 18950308901243873363717259264 }, some { target := 431, numerator := 719631983591539494824706048 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 448, numerator := 752556322710106661254594560 }, some { target := 449, numerator := 11288344840651599918818918400 }, some { target := 450, numerator := 19817316498032808746370990080 }, some { target := 451, numerator := 752556322710106661254594560 }, some { target := 452, numerator := 12542605378501777687576576000 }, some { target := 453, numerator := 752556322710106661254594560 }, some { target := 454, numerator := 19817316498032808746370990080 }, some { target := 455, numerator := 19691890444247790969495224320 }, some { target := 456, numerator := 12542605378501777687576576000 }, some { target := 457, numerator := 303907328321098073369980436480 }, some { target := 458, numerator := 19441038336677755415743692800 }, some { target := 459, numerator := 11288344840651599918818918400 }, some { target := 460, numerator := 19817316498032808746370990080 }, some { target := 461, numerator := 752556322710106661254594560 }, some { target := 462, numerator := 19441038336677755415743692800 }, some { target := 463, numerator := 752556322710106661254594560 }, some { target := 464, numerator := 19817316498032808746370990080 }, some { target := 465, numerator := 19817316498032808746370990080 }, some { target := 466, numerator := 752556322710106661254594560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 509, numerator := 451533793626063996752756736 }, some { target := 510, numerator := 6773006904390959951291351040 }, some { target := 511, numerator := 11890389898819685247822594048 }, some { target := 512, numerator := 451533793626063996752756736 }, some { target := 513, numerator := 7525563227101066612545945600 }, some { target := 514, numerator := 451533793626063996752756736 }, some { target := 515, numerator := 11890389898819685247822594048 }, some { target := 516, numerator := 11815134266548674581697134592 }, some { target := 517, numerator := 7525563227101066612545945600 }, some { target := 518, numerator := 182344396992658844021988261888 }, some { target := 519, numerator := 11664623002006653249446215680 }, some { target := 520, numerator := 6773006904390959951291351040 }, some { target := 521, numerator := 11890389898819685247822594048 }, some { target := 522, numerator := 451533793626063996752756736 }, some { target := 523, numerator := 11664623002006653249446215680 }, some { target := 524, numerator := 451533793626063996752756736 }, some { target := 525, numerator := 11890389898819685247822594048 }, some { target := 526, numerator := 11890389898819685247822594048 }, some { target := 527, numerator := 451533793626063996752756736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 544, numerator := 11528222168515446417093820416 }, some { target := 545, numerator := 172923332527731696256407306240 }, some { target := 546, numerator := 303576517104240088983470604288 }, some { target := 547, numerator := 11528222168515446417093820416 }, some { target := 548, numerator := 192137036141924106951563673600 }, some { target := 549, numerator := 11528222168515446417093820416 }, some { target := 550, numerator := 303576517104240088983470604288 }, some { target := 551, numerator := 301655146742820847913954967552 }, some { target := 552, numerator := 192137036141924106951563673600 }, some { target := 553, numerator := 4655480385718821111436387811328 }, some { target := 554, numerator := 297812406019982365774923694080 }, some { target := 555, numerator := 172923332527731696256407306240 }, some { target := 556, numerator := 303576517104240088983470604288 }, some { target := 557, numerator := 11528222168515446417093820416 }, some { target := 558, numerator := 297812406019982365774923694080 }, some { target := 559, numerator := 11528222168515446417093820416 }, some { target := 560, numerator := 303576517104240088983470604288 }, some { target := 561, numerator := 303576517104240088983470604288 }, some { target := 562, numerator := 11528222168515446417093820416 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 579, numerator := 738445891659292161356070912 }, some { target := 580, numerator := 11076688374889382420341063680 }, some { target := 581, numerator := 19445741813694693582376534016 }, some { target := 582, numerator := 738445891659292161356070912 }, some { target := 583, numerator := 12307431527654869355934515200 }, some { target := 584, numerator := 738445891659292161356070912 }, some { target := 585, numerator := 19445741813694693582376534016 }, some { target := 586, numerator := 19322667498418144888817188864 }, some { target := 587, numerator := 12307431527654869355934515200 }, some { target := 588, numerator := 298209065915077484494293303296 }, some { target := 589, numerator := 19076518867865047501698498560 }, some { target := 590, numerator := 11076688374889382420341063680 }, some { target := 591, numerator := 19445741813694693582376534016 }, some { target := 592, numerator := 738445891659292161356070912 }, some { target := 593, numerator := 19076518867865047501698498560 }, some { target := 594, numerator := 738445891659292161356070912 }, some { target := 595, numerator := 19445741813694693582376534016 }, some { target := 596, numerator := 19445741813694693582376534016 }, some { target := 597, numerator := 738445891659292161356070912 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 640, numerator := 409202500473620497057185792 }, some { target := 641, numerator := 6138037507104307455857786880 }, some { target := 642, numerator := 10775665845805339755839225856 }, some { target := 643, numerator := 409202500473620497057185792 }, some { target := 644, numerator := 6820041674560341617619763200 }, some { target := 645, numerator := 409202500473620497057185792 }, some { target := 646, numerator := 10775665845805339755839225856 }, some { target := 647, numerator := 10707465429059736339663028224 }, some { target := 648, numerator := 6820041674560341617619763200 }, some { target := 649, numerator := 165249609774597077394926862336 }, some { target := 650, numerator := 10571064595568529507310632960 }, some { target := 651, numerator := 6138037507104307455857786880 }, some { target := 652, numerator := 10775665845805339755839225856 }, some { target := 653, numerator := 409202500473620497057185792 }, some { target := 654, numerator := 10571064595568529507310632960 }, some { target := 655, numerator := 409202500473620497057185792 }, some { target := 656, numerator := 10775665845805339755839225856 }, some { target := 657, numerator := 10775665845805339755839225856 }, some { target := 658, numerator := 409202500473620497057185792 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 675, numerator := 719631983591539494824706048 }, some { target := 676, numerator := 10794479753873092422370590720 }, some { target := 677, numerator := 18950308901243873363717259264 }, some { target := 678, numerator := 719631983591539494824706048 }, some { target := 679, numerator := 11993866393192324913745100800 }, some { target := 680, numerator := 719631983591539494824706048 }, some { target := 681, numerator := 18950308901243873363717259264 }, some { target := 682, numerator := 18830370237311950114579808256 }, some { target := 683, numerator := 11993866393192324913745100800 }, some { target := 684, numerator := 290611382707050032660043792384 }, some { target := 685, numerator := 18590492909448103616304906240 }, some { target := 686, numerator := 10794479753873092422370590720 }, some { target := 687, numerator := 18950308901243873363717259264 }, some { target := 688, numerator := 719631983591539494824706048 }, some { target := 689, numerator := 18590492909448103616304906240 }, some { target := 690, numerator := 719631983591539494824706048 }, some { target := 691, numerator := 18950308901243873363717259264 }, some { target := 692, numerator := 18950308901243873363717259264 }, some { target := 693, numerator := 719631983591539494824706048 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 776, numerator := 23517385084690833164206080 }, some { target := 777, numerator := 352760776270362497463091200 }, some { target := 778, numerator := 619291140563525273324093440 }, some { target := 779, numerator := 23517385084690833164206080 }, some { target := 780, numerator := 391956418078180552736768000 }, some { target := 781, numerator := 23517385084690833164206080 }, some { target := 782, numerator := 619291140563525273324093440 }, some { target := 783, numerator := 615371576382743467796725760 }, some { target := 784, numerator := 391956418078180552736768000 }, some { target := 785, numerator := 9497104010034314792811888640 }, some { target := 786, numerator := 607532448021179856741990400 }, some { target := 787, numerator := 352760776270362497463091200 }, some { target := 788, numerator := 619291140563525273324093440 }, some { target := 789, numerator := 23517385084690833164206080 }, some { target := 790, numerator := 607532448021179856741990400 }, some { target := 791, numerator := 23517385084690833164206080 }, some { target := 792, numerator := 619291140563525273324093440 }, some { target := 793, numerator := 619291140563525273324093440 }, some { target := 794, numerator := 23517385084690833164206080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 811, numerator := 738445891659292161356070912 }, some { target := 812, numerator := 11076688374889382420341063680 }, some { target := 813, numerator := 19445741813694693582376534016 }, some { target := 814, numerator := 738445891659292161356070912 }, some { target := 815, numerator := 12307431527654869355934515200 }, some { target := 816, numerator := 738445891659292161356070912 }, some { target := 817, numerator := 19445741813694693582376534016 }, some { target := 818, numerator := 19322667498418144888817188864 }, some { target := 819, numerator := 12307431527654869355934515200 }, some { target := 820, numerator := 298209065915077484494293303296 }, some { target := 821, numerator := 19076518867865047501698498560 }, some { target := 822, numerator := 11076688374889382420341063680 }, some { target := 823, numerator := 19445741813694693582376534016 }, some { target := 824, numerator := 738445891659292161356070912 }, some { target := 825, numerator := 19076518867865047501698498560 }, some { target := 826, numerator := 738445891659292161356070912 }, some { target := 827, numerator := 19445741813694693582376534016 }, some { target := 828, numerator := 19445741813694693582376534016 }, some { target := 829, numerator := 738445891659292161356070912 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 846, numerator := 23517385084690833164206080 }, some { target := 847, numerator := 352760776270362497463091200 }, some { target := 848, numerator := 619291140563525273324093440 }, some { target := 849, numerator := 23517385084690833164206080 }, some { target := 850, numerator := 391956418078180552736768000 }, some { target := 851, numerator := 23517385084690833164206080 }, some { target := 852, numerator := 619291140563525273324093440 }, some { target := 853, numerator := 615371576382743467796725760 }, some { target := 854, numerator := 391956418078180552736768000 }, some { target := 855, numerator := 9497104010034314792811888640 }, some { target := 856, numerator := 607532448021179856741990400 }, some { target := 857, numerator := 352760776270362497463091200 }, some { target := 858, numerator := 619291140563525273324093440 }, some { target := 859, numerator := 23517385084690833164206080 }, some { target := 860, numerator := 607532448021179856741990400 }, some { target := 861, numerator := 23517385084690833164206080 }, some { target := 862, numerator := 619291140563525273324093440 }, some { target := 863, numerator := 619291140563525273324093440 }, some { target := 864, numerator := 23517385084690833164206080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 907, numerator := 719631983591539494824706048 }, some { target := 908, numerator := 10794479753873092422370590720 }, some { target := 909, numerator := 18950308901243873363717259264 }, some { target := 910, numerator := 719631983591539494824706048 }, some { target := 911, numerator := 11993866393192324913745100800 }, some { target := 912, numerator := 719631983591539494824706048 }, some { target := 913, numerator := 18950308901243873363717259264 }, some { target := 914, numerator := 18830370237311950114579808256 }, some { target := 915, numerator := 11993866393192324913745100800 }, some { target := 916, numerator := 290611382707050032660043792384 }, some { target := 917, numerator := 18590492909448103616304906240 }, some { target := 918, numerator := 10794479753873092422370590720 }, some { target := 919, numerator := 18950308901243873363717259264 }, some { target := 920, numerator := 719631983591539494824706048 }, some { target := 921, numerator := 18590492909448103616304906240 }, some { target := 922, numerator := 719631983591539494824706048 }, some { target := 923, numerator := 18950308901243873363717259264 }, some { target := 924, numerator := 18950308901243873363717259264 }, some { target := 925, numerator := 719631983591539494824706048 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 942, numerator := 752556322710106661254594560 }, some { target := 943, numerator := 11288344840651599918818918400 }, some { target := 944, numerator := 19817316498032808746370990080 }, some { target := 945, numerator := 752556322710106661254594560 }, some { target := 946, numerator := 12542605378501777687576576000 }, some { target := 947, numerator := 752556322710106661254594560 }, some { target := 948, numerator := 19817316498032808746370990080 }, some { target := 949, numerator := 19691890444247790969495224320 }, some { target := 950, numerator := 12542605378501777687576576000 }, some { target := 951, numerator := 303907328321098073369980436480 }, some { target := 952, numerator := 19441038336677755415743692800 }, some { target := 953, numerator := 11288344840651599918818918400 }, some { target := 954, numerator := 19817316498032808746370990080 }, some { target := 955, numerator := 752556322710106661254594560 }, some { target := 956, numerator := 19441038336677755415743692800 }, some { target := 957, numerator := 752556322710106661254594560 }, some { target := 958, numerator := 19817316498032808746370990080 }, some { target := 959, numerator := 19817316498032808746370990080 }, some { target := 960, numerator := 752556322710106661254594560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1017, numerator := 28220862101628999797047296 }, some { target := 1018, numerator := 423312931524434996955709440 }, some { target := 1019, numerator := 743149368676230327988912128 }, some { target := 1020, numerator := 28220862101628999797047296 }, some { target := 1021, numerator := 470347701693816663284121600 }, some { target := 1022, numerator := 28220862101628999797047296 }, some { target := 1023, numerator := 743149368676230327988912128 }, some { target := 1024, numerator := 738445891659292161356070912 }, some { target := 1025, numerator := 470347701693816663284121600 }, some { target := 1026, numerator := 11396524812041177751374266368 }, some { target := 1027, numerator := 729038937625415828090388480 }, some { target := 1028, numerator := 423312931524434996955709440 }, some { target := 1029, numerator := 743149368676230327988912128 }, some { target := 1030, numerator := 28220862101628999797047296 }, some { target := 1031, numerator := 729038937625415828090388480 }, some { target := 1032, numerator := 28220862101628999797047296 }, some { target := 1033, numerator := 743149368676230327988912128 }, some { target := 1034, numerator := 743149368676230327988912128 }, some { target := 1035, numerator := 28220862101628999797047296 }]

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
def data : BetaFourLocalSlotData := ⟨1, 284, #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0], #[3517964091392, 0, 137219541041152, 0, 0, 137219490709504, 0, 0, 0, 0, 0, 0, 3517980868608, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 200, numerator := 3226914392709147564940722176 }, some { target := 202, numerator := 125867035718215657719077011456 }, some { target := 205, numerator := 125866989550626927242496704512 }, some { target := 212, numerator := 3226929781905391057134157824 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 296, numerator := 2403021356272769463253729280 }, some { target := 298, numerator := 93730771279522298301440327680 }, some { target := 301, numerator := 93730736899403030925263503360 }, some { target := 308, numerator := 2403032816312525255312670720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 331, numerator := 2540336862345499146868228096 }, some { target := 333, numerator := 99086815352637858204379774976 }, some { target := 336, numerator := 99086779007940346978135703552 }, some { target := 343, numerator := 2540348977244669555616251904 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 467, numerator := 3295572145745512406747971584 }, some { target := 469, numerator := 128545057754773437670546735104 }, some { target := 472, numerator := 128545010604895585268932804608 }, some { target := 479, numerator := 3295587862371463207285948416 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 563, numerator := 44146935202382593282061369344 }, some { target := 565, numerator := 1721968169506652508795032305664 }, some { target := 568, numerator := 1721967537894747110998412361728 }, some { target := 575, numerator := 44147145739684392547601350656 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 598, numerator := 79848966781292311021831061504 }, some { target := 600, numerator := 3114539628516698083559288602624 }, some { target := 603, numerator := 3114538486114449284745184411648 }, some { target := 610, numerator := 79849347582041910626532458496 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 659, numerator := 2403021356272769463253729280 }, some { target := 661, numerator := 93730771279522298301440327680 }, some { target := 664, numerator := 93730736899403030925263503360 }, some { target := 671, numerator := 2403032816312525255312670720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 694, numerator := 44146935202382593282061369344 }, some { target := 696, numerator := 1721968169506652508795032305664 }, some { target := 699, numerator := 1721967537894747110998412361728 }, some { target := 706, numerator := 44147145739684392547601350656 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 720, numerator := 2608994615381863988675477504 }, some { target := 722, numerator := 101764837389195638155849498624 }, some { target := 725, numerator := 101764800062209005004571803648 }, some { target := 732, numerator := 2609007057710741705768042496 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 830, numerator := 2608994615381863988675477504 }, some { target := 832, numerator := 101764837389195638155849498624 }, some { target := 835, numerator := 101764800062209005004571803648 }, some { target := 842, numerator := 2609007057710741705768042496 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 865, numerator := 2540336862345499146868228096 }, some { target := 867, numerator := 99086815352637858204379774976 }, some { target := 870, numerator := 99086779007940346978135703552 }, some { target := 877, numerator := 2540348977244669555616251904 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 926, numerator := 2540336862345499146868228096 }, some { target := 928, numerator := 99086815352637858204379774976 }, some { target := 931, numerator := 99086779007940346978135703552 }, some { target := 938, numerator := 2540348977244669555616251904 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 961, numerator := 79848966781292311021831061504 }, some { target := 963, numerator := 3114539628516698083559288602624 }, some { target := 966, numerator := 3114538486114449284745184411648 }, some { target := 973, numerator := 79849347582041910626532458496 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 987, numerator := 2540336862345499146868228096 }, some { target := 989, numerator := 99086815352637858204379774976 }, some { target := 992, numerator := 99086779007940346978135703552 }, some { target := 999, numerator := 2540348977244669555616251904 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1036, numerator := 3226914392709147564940722176 }, some { target := 1038, numerator := 125867035718215657719077011456 }, some { target := 1041, numerator := 125866989550626927242496704512 }, some { target := 1048, numerator := 3226929781905391057134157824 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1062, numerator := 3295572145745512406747971584 }, some { target := 1064, numerator := 128545057754773437670546735104 }, some { target := 1067, numerator := 128545010604895585268932804608 }, some { target := 1074, numerator := 3295587862371463207285948416 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent0
