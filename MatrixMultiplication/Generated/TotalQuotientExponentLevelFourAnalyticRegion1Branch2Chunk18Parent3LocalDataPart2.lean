import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk18Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 2,
parent 77; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot7

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨7, 539, #[343597383680, 5772436045824, 12506944765952, 412316860416, 6597069766656, 481036337152, 12506944765952, 12506944765952, 6597069766656, 154343944749056, 12369505812480, 5772436045824, 12506944765952, 481036337152, 12369505812480, 481036337152, 12506944765952, 12506944765952, 412316860416], #[3710583308288, 0, 137026905047040, 0, 0, 137026871492608, 0, 0, 0, 0, 0, 0, 3710616862720, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 110, numerator := 687196280276740820707573760 }, some { target := 112, numerator := 25377244390614664185957580800 }, some { target := 115, numerator := 25377238176367754355052380160 }, some { target := 122, numerator := 687202494523650651612774400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 206, numerator := 11544897508649245787887239168 }, some { target := 208, numerator := 426337705762326358324087357440 }, some { target := 211, numerator := 426337601362978273164879986688 }, some { target := 218, numerator := 11545001907997330947094609920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 241, numerator := 25013944602073365873755684864 }, some { target := 243, numerator := 923731695818373776368855941120 }, some { target := 246, numerator := 923731469619786258523906637824 }, some { target := 253, numerator := 25014170800660883718704988160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 824635536332088984849088512 }, some { target := 304, numerator := 30452693268737597023149096960 }, some { target := 307, numerator := 30452685811641305226062856192 }, some { target := 314, numerator := 824642993428380781935329280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 337, numerator := 13194168581313423757585416192 }, some { target := 339, numerator := 487243092299801552370385551360 }, some { target := 342, numerator := 487242972986260883617005699072 }, some { target := 349, numerator := 13194287894854092510965268480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 363, numerator := 962074792387437148990603264 }, some { target := 365, numerator := 35528142146860529860340613120 }, some { target := 368, numerator := 35528133446914856097073332224 }, some { target := 375, numerator := 962083492333110912257884160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 473, numerator := 25013944602073365873755684864 }, some { target := 475, numerator := 923731695818373776368855941120 }, some { target := 478, numerator := 923731469619786258523906637824 }, some { target := 485, numerator := 25014170800660883718704988160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 25013944602073365873755684864 }, some { target := 510, numerator := 923731695818373776368855941120 }, some { target := 513, numerator := 923731469619786258523906637824 }, some { target := 520, numerator := 25014170800660883718704988160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 569, numerator := 13194168581313423757585416192 }, some { target := 571, numerator := 487243092299801552370385551360 }, some { target := 574, numerator := 487242972986260883617005699072 }, some { target := 581, numerator := 13194287894854092510965268480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 604, numerator := 308688569100311976661842132992 }, some { target := 606, numerator := 11399458180264107152332145295360 }, some { target := 609, numerator := 11399455388824395256289529167872 }, some { target := 616, numerator := 308691360540023872704458260480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 630, numerator := 24739066089962669545472655360 }, some { target := 632, numerator := 913580798062127910694472908800 }, some { target := 635, numerator := 913580574349239156781885685760 }, some { target := 642, numerator := 24739289802851423458059878400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 11544897508649245787887239168 }, some { target := 681, numerator := 426337705762326358324087357440 }, some { target := 684, numerator := 426337601362978273164879986688 }, some { target := 691, numerator := 11545001907997330947094609920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 705, numerator := 25013944602073365873755684864 }, some { target := 707, numerator := 923731695818373776368855941120 }, some { target := 710, numerator := 923731469619786258523906637824 }, some { target := 717, numerator := 25014170800660883718704988160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 785, numerator := 962074792387437148990603264 }, some { target := 787, numerator := 35528142146860529860340613120 }, some { target := 790, numerator := 35528133446914856097073332224 }, some { target := 797, numerator := 962083492333110912257884160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 820, numerator := 24739066089962669545472655360 }, some { target := 822, numerator := 913580798062127910694472908800 }, some { target := 825, numerator := 913580574349239156781885685760 }, some { target := 832, numerator := 24739289802851423458059878400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 846, numerator := 962074792387437148990603264 }, some { target := 848, numerator := 35528142146860529860340613120 }, some { target := 851, numerator := 35528133446914856097073332224 }, some { target := 858, numerator := 962083492333110912257884160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 895, numerator := 25013944602073365873755684864 }, some { target := 897, numerator := 923731695818373776368855941120 }, some { target := 900, numerator := 923731469619786258523906637824 }, some { target := 907, numerator := 25014170800660883718704988160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 921, numerator := 25013944602073365873755684864 }, some { target := 923, numerator := 923731695818373776368855941120 }, some { target := 926, numerator := 923731469619786258523906637824 }, some { target := 933, numerator := 25014170800660883718704988160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 966, numerator := 824635536332088984849088512 }, some { target := 968, numerator := 30452693268737597023149096960 }, some { target := 971, numerator := 30452685811641305226062856192 }, some { target := 978, numerator := 824642993428380781935329280 }]

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

end Slot7

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 543, #[3710583308288, 0, 137026905047040, 0, 0, 137026871492608, 0, 0, 0, 0, 0, 0, 3710616862720, 0, 0, 0, 0, 0, 0], #[343597383680, 5772436045824, 12506944765952, 412316860416, 6597069766656, 481036337152, 12506944765952, 12506944765952, 6597069766656, 154343944749056, 12369505812480, 5772436045824, 12506944765952, 481036337152, 12369505812480, 481036337152, 12506944765952, 12506944765952, 412316860416]⟩

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
  [some { target := 56, numerator := 692296067143358563347333120 }, some { target := 57, numerator := 11630573928008423864235196416 }, some { target := 58, numerator := 25199576844018251705842925568 }, some { target := 59, numerator := 830755280572030276016799744 }, some { target := 60, numerator := 13292084489152484416268795904 }, some { target := 61, numerator := 969214494000701988686266368 }, some { target := 62, numerator := 25199576844018251705842925568 }, some { target := 63, numerator := 25199576844018251705842925568 }, some { target := 64, numerator := 13292084489152484416268795904 }, some { target := 65, numerator := 310979393360796666655622037504 }, some { target := 66, numerator := 24922658417160908280503992320 }, some { target := 67, numerator := 11630573928008423864235196416 }, some { target := 68, numerator := 25199576844018251705842925568 }, some { target := 69, numerator := 969214494000701988686266368 }, some { target := 70, numerator := 24922658417160908280503992320 }, some { target := 71, numerator := 969214494000701988686266368 }, some { target := 72, numerator := 25199576844018251705842925568 }, some { target := 73, numerator := 25199576844018251705842925568 }, some { target := 74, numerator := 830755280572030276016799744 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 152, numerator := 25565572734886387111270809600 }, some { target := 153, numerator := 429501621946091303469349601280 }, some { target := 154, numerator := 930586847549864490850257469440 }, some { target := 155, numerator := 30678687281863664533524971520 }, some { target := 156, numerator := 490858996509818632536399544320 }, some { target := 157, numerator := 35791801828840941955779133440 }, some { target := 158, numerator := 930586847549864490850257469440 }, some { target := 159, numerator := 930586847549864490850257469440 }, some { target := 160, numerator := 490858996509818632536399544320 }, some { target := 161, numerator := 11484055272510965090382847672320 }, some { target := 162, numerator := 920360618455909936005749145600 }, some { target := 163, numerator := 429501621946091303469349601280 }, some { target := 164, numerator := 930586847549864490850257469440 }, some { target := 165, numerator := 35791801828840941955779133440 }, some { target := 166, numerator := 920360618455909936005749145600 }, some { target := 167, numerator := 35791801828840941955779133440 }, some { target := 168, numerator := 930586847549864490850257469440 }, some { target := 169, numerator := 930586847549864490850257469440 }, some { target := 170, numerator := 30678687281863664533524971520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 283, numerator := 25565566474522617096091729920 }, some { target := 284, numerator := 429501516771979967214341062656 }, some { target := 285, numerator := 930586619672623262297738969088 }, some { target := 286, numerator := 30678679769427140515310075904 }, some { target := 287, numerator := 490858876310834248244961214464 }, some { target := 288, numerator := 35791793064331663934528421888 }, some { target := 289, numerator := 930586619672623262297738969088 }, some { target := 290, numerator := 930586619672623262297738969088 }, some { target := 291, numerator := 490858876310834248244961214464 }, some { target := 292, numerator := 11484052460355559599564405080064 }, some { target := 293, numerator := 920360393082814215459302277120 }, some { target := 294, numerator := 429501516771979967214341062656 }, some { target := 295, numerator := 930586619672623262297738969088 }, some { target := 296, numerator := 35791793064331663934528421888 }, some { target := 297, numerator := 920360393082814215459302277120 }, some { target := 298, numerator := 35791793064331663934528421888 }, some { target := 299, numerator := 930586619672623262297738969088 }, some { target := 300, numerator := 930586619672623262297738969088 }, some { target := 301, numerator := 30678679769427140515310075904 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 660, numerator := 692302327507128578526412800 }, some { target := 661, numerator := 11630679102119760119243735040 }, some { target := 662, numerator := 25199804721259480258361425920 }, some { target := 663, numerator := 830762793008554294231695360 }, some { target := 664, numerator := 13292204688136868707707125760 }, some { target := 665, numerator := 969223258509980009936977920 }, some { target := 666, numerator := 25199804721259480258361425920 }, some { target := 667, numerator := 25199804721259480258361425920 }, some { target := 668, numerator := 13292204688136868707707125760 }, some { target := 669, numerator := 310982205516202157474064629760 }, some { target := 670, numerator := 24922883790256628826950860800 }, some { target := 671, numerator := 11630679102119760119243735040 }, some { target := 672, numerator := 25199804721259480258361425920 }, some { target := 673, numerator := 969223258509980009936977920 }, some { target := 674, numerator := 24922883790256628826950860800 }, some { target := 675, numerator := 969223258509980009936977920 }, some { target := 676, numerator := 25199804721259480258361425920 }, some { target := 677, numerator := 25199804721259480258361425920 }, some { target := 678, numerator := 830762793008554294231695360 }]

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

end Slot8

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18.Parent3
