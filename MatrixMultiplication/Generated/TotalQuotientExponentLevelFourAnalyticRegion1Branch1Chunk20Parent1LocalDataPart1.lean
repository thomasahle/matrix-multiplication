import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk20Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 1,
parent 83; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot7

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨7, 555, #[3517964091392, 0, 137219541041152, 0, 0, 137219490709504, 0, 0, 0, 0, 0, 0, 3517980868608, 0, 0, 0, 0, 0, 0], #[412316860416, 6184752906240, 10857677324288, 412316860416, 6871947673600, 412316860416, 10857677324288, 10788957847552, 6871947673600, 166507292131328, 10651518894080, 6184752906240, 10857677324288, 412316860416, 10651518894080, 412316860416, 10857677324288, 10857677324288, 412316860416]⟩

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
  [some { target := 56, numerator := 805036329616531419782184960 }, some { target := 57, numerator := 12075544944247971296732774400 }, some { target := 58, numerator := 21199290013235327387597537280 }, some { target := 59, numerator := 805036329616531419782184960 }, some { target := 60, numerator := 13417272160275523663036416000 }, some { target := 61, numerator := 805036329616531419782184960 }, some { target := 62, numerator := 21199290013235327387597537280 }, some { target := 63, numerator := 21065117291632572150967173120 }, some { target := 64, numerator := 13417272160275523663036416000 }, some { target := 65, numerator := 325100504443475938355372359680 }, some { target := 66, numerator := 20796771848427061677706444800 }, some { target := 67, numerator := 12075544944247971296732774400 }, some { target := 68, numerator := 21199290013235327387597537280 }, some { target := 69, numerator := 805036329616531419782184960 }, some { target := 70, numerator := 20796771848427061677706444800 }, some { target := 71, numerator := 805036329616531419782184960 }, some { target := 72, numerator := 21199290013235327387597537280 }, some { target := 73, numerator := 21199290013235327387597537280 }, some { target := 74, numerator := 805036329616531419782184960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 152, numerator := 31400751344145800135190773760 }, some { target := 153, numerator := 471011270162187002027861606400 }, some { target := 154, numerator := 826886452062506070226690375680 }, some { target := 155, numerator := 31400751344145800135190773760 }, some { target := 156, numerator := 523345855735763335586512896000 }, some { target := 157, numerator := 31400751344145800135190773760 }, some { target := 158, numerator := 826886452062506070226690375680 }, some { target := 159, numerator := 821652993505148436870825246720 }, some { target := 160, numerator := 523345855735763335586512896000 }, some { target := 161, numerator := 12680670084477545621261207470080 }, some { target := 162, numerator := 811186076390433170159094988800 }, some { target := 163, numerator := 471011270162187002027861606400 }, some { target := 164, numerator := 826886452062506070226690375680 }, some { target := 165, numerator := 31400751344145800135190773760 }, some { target := 166, numerator := 811186076390433170159094988800 }, some { target := 167, numerator := 31400751344145800135190773760 }, some { target := 168, numerator := 826886452062506070226690375680 }, some { target := 169, numerator := 826886452062506070226690375680 }, some { target := 170, numerator := 31400751344145800135190773760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 283, numerator := 31400739826459969112789483520 }, some { target := 284, numerator := 471011097396899536691842252800 }, some { target := 285, numerator := 826886148763445853303456399360 }, some { target := 286, numerator := 31400739826459969112789483520 }, some { target := 287, numerator := 523345663774332818546491392000 }, some { target := 288, numerator := 31400739826459969112789483520 }, some { target := 289, numerator := 826886148763445853303456399360 }, some { target := 290, numerator := 821652692125702525117991485440 }, some { target := 291, numerator := 523345663774332818546491392000 }, some { target := 292, numerator := 12680665433252084193381486428160 }, some { target := 293, numerator := 811185778850215868747061657600 }, some { target := 294, numerator := 471011097396899536691842252800 }, some { target := 295, numerator := 826886148763445853303456399360 }, some { target := 296, numerator := 31400739826459969112789483520 }, some { target := 297, numerator := 811185778850215868747061657600 }, some { target := 298, numerator := 31400739826459969112789483520 }, some { target := 299, numerator := 826886148763445853303456399360 }, some { target := 300, numerator := 826886148763445853303456399360 }, some { target := 301, numerator := 31400739826459969112789483520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 660, numerator := 805040168845141760582615040 }, some { target := 661, numerator := 12075602532677126408739225600 }, some { target := 662, numerator := 21199391112922066362008862720 }, some { target := 663, numerator := 805040168845141760582615040 }, some { target := 664, numerator := 13417336147419029343043584000 }, some { target := 665, numerator := 805040168845141760582615040 }, some { target := 666, numerator := 21199391112922066362008862720 }, some { target := 667, numerator := 21065217751447876068578426880 }, some { target := 668, numerator := 13417336147419029343043584000 }, some { target := 669, numerator := 325102054851963080981946040320 }, some { target := 670, numerator := 20796871028499495481717555200 }, some { target := 671, numerator := 12075602532677126408739225600 }, some { target := 672, numerator := 21199391112922066362008862720 }, some { target := 673, numerator := 805040168845141760582615040 }, some { target := 674, numerator := 20796871028499495481717555200 }, some { target := 675, numerator := 805040168845141760582615040 }, some { target := 676, numerator := 21199391112922066362008862720 }, some { target := 677, numerator := 21199391112922066362008862720 }, some { target := 678, numerator := 805040168845141760582615040 }]

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

end Slot7

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 550, #[412316860416, 6184752906240, 10857677324288, 412316860416, 6871947673600, 412316860416, 10857677324288, 10788957847552, 6871947673600, 166507292131328, 10651518894080, 6184752906240, 10857677324288, 412316860416, 10651518894080, 412316860416, 10857677324288, 10857677324288, 412316860416], #[3517964091392, 0, 137219541041152, 0, 0, 137219490709504, 0, 0, 0, 0, 0, 0, 3517980868608, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 110, numerator := 797783750070436542126489600 }, some { target := 112, numerator := 31117861692396738872711577600 }, some { target := 115, numerator := 31117850278473843264926515200 }, some { target := 122, numerator := 797787554711401744721510400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 206, numerator := 11966756251056548131897344000 }, some { target := 208, numerator := 466767925385951083090673664000 }, some { target := 211, numerator := 466767754177107648973897728000 }, some { target := 218, numerator := 11966813320671026170822656000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 241, numerator := 21008305418521495609330892800 }, some { target := 243, numerator := 819437024566447456981404876800 }, some { target := 246, numerator := 819436723999811205976398233600 }, some { target := 253, numerator := 21008405607400245944333107200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 797783750070436542126489600 }, some { target := 304, numerator := 31117861692396738872711577600 }, some { target := 307, numerator := 31117850278473843264926515200 }, some { target := 314, numerator := 797787554711401744721510400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 337, numerator := 13296395834507275702108160000 }, some { target := 339, numerator := 518631028206612314545192960000 }, some { target := 342, numerator := 518630837974564054415441920000 }, some { target := 349, numerator := 13296459245190029078691840000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 363, numerator := 797783750070436542126489600 }, some { target := 365, numerator := 31117861692396738872711577600 }, some { target := 368, numerator := 31117850278473843264926515200 }, some { target := 375, numerator := 797787554711401744721510400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 473, numerator := 21008305418521495609330892800 }, some { target := 475, numerator := 819437024566447456981404876800 }, some { target := 478, numerator := 819436723999811205976398233600 }, some { target := 485, numerator := 21008405607400245944333107200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 20875341460176422852309811200 }, some { target := 510, numerator := 814250714284381333835952947200 }, some { target := 513, numerator := 814250415620065565432243814400 }, some { target := 520, numerator := 20875441014948345653546188800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 569, numerator := 13296395834507275702108160000 }, some { target := 571, numerator := 518631028206612314545192960000 }, some { target := 574, numerator := 518630837974564054415441920000 }, some { target := 581, numerator := 13296459245190029078691840000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 604, numerator := 322171671070111290262080716800 }, some { target := 606, numerator := 12566429813446216381430025420800 }, some { target := 609, numerator := 12566425204123687038486157721600 }, some { target := 616, numerator := 322173207510954404576703283200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 630, numerator := 20609413543486277338267648000 }, some { target := 632, numerator := 803878093720249087545049088000 }, some { target := 635, numerator := 803877798860574284343934976000 }, some { target := 642, numerator := 20609511830044545071972352000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 11966756251056548131897344000 }, some { target := 681, numerator := 466767925385951083090673664000 }, some { target := 684, numerator := 466767754177107648973897728000 }, some { target := 691, numerator := 11966813320671026170822656000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 705, numerator := 21008305418521495609330892800 }, some { target := 707, numerator := 819437024566447456981404876800 }, some { target := 710, numerator := 819436723999811205976398233600 }, some { target := 717, numerator := 21008405607400245944333107200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 785, numerator := 797783750070436542126489600 }, some { target := 787, numerator := 31117861692396738872711577600 }, some { target := 790, numerator := 31117850278473843264926515200 }, some { target := 797, numerator := 797787554711401744721510400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 820, numerator := 20609413543486277338267648000 }, some { target := 822, numerator := 803878093720249087545049088000 }, some { target := 825, numerator := 803877798860574284343934976000 }, some { target := 832, numerator := 20609511830044545071972352000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 846, numerator := 797783750070436542126489600 }, some { target := 848, numerator := 31117861692396738872711577600 }, some { target := 851, numerator := 31117850278473843264926515200 }, some { target := 858, numerator := 797787554711401744721510400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 895, numerator := 21008305418521495609330892800 }, some { target := 897, numerator := 819437024566447456981404876800 }, some { target := 900, numerator := 819436723999811205976398233600 }, some { target := 907, numerator := 21008405607400245944333107200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 921, numerator := 21008305418521495609330892800 }, some { target := 923, numerator := 819437024566447456981404876800 }, some { target := 926, numerator := 819436723999811205976398233600 }, some { target := 933, numerator := 21008405607400245944333107200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 966, numerator := 797783750070436542126489600 }, some { target := 968, numerator := 31117861692396738872711577600 }, some { target := 971, numerator := 31117850278473843264926515200 }, some { target := 978, numerator := 797787554711401744721510400 }]

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

end Slot8

namespace Slot9

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨9, 49, #[49796387700736, 0, 0, 181882218086400, 0, 49796370923520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3298534883328, 2473901162496, 2611340115968, 3367254360064, 45079976738816, 78821239816192, 2405181685760, 45079976738816, 2542620639232, 2611340115968, 2611340115968, 2542620639232, 78821239816192, 2542620639232, 3298534883328, 3367254360064, 0, 0, 0]⟩

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
  [some { target := 14, numerator := 8048500972835550721046740992 }, some { target := 15, numerator := 6036375729626663040785055744 }, some { target := 16, numerator := 6371729936828144320828669952 }, some { target := 17, numerator := 8216178076436291361068548096 }, some { target := 18, numerator := 109996179962085859854305460224 }, some { target := 19, numerator := 192325637830049514105012748288 }, some { target := 20, numerator := 5868698626025922400763248640 }, some { target := 21, numerator := 109996179962085859854305460224 }, some { target := 22, numerator := 6204052833227403680806862848 }, some { target := 23, numerator := 6371729936828144320828669952 }, some { target := 24, numerator := 6371729936828144320828669952 }, some { target := 25, numerator := 6204052833227403680806862848 }, some { target := 26, numerator := 192325637830049514105012748288 }, some { target := 27, numerator := 6204052833227403680806862848 }, some { target := 28, numerator := 8048500972835550721046740992 }, some { target := 29, numerator := 8216178076436291361068548096 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 136, numerator := 29397297209738002495753420800 }, some { target := 137, numerator := 22047972907303501871815065600 }, some { target := 138, numerator := 23272860291042585309138124800 }, some { target := 139, numerator := 30009740901607544214414950400 }, some { target := 140, numerator := 401763061866419367441963417600 }, some { target := 141, numerator := 702472914574364351304774451200 }, some { target := 142, numerator := 21435529215433960153153536000 }, some { target := 143, numerator := 401763061866419367441963417600 }, some { target := 144, numerator := 22660416599173043590476595200 }, some { target := 145, numerator := 23272860291042585309138124800 }, some { target := 146, numerator := 23272860291042585309138124800 }, some { target := 147, numerator := 22660416599173043590476595200 }, some { target := 148, numerator := 702472914574364351304774451200 }, some { target := 149, numerator := 22660416599173043590476595200 }, some { target := 150, numerator := 29397297209738002495753420800 }, some { target := 151, numerator := 30009740901607544214414950400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 8048498261164171885742653440 }, some { target := 268, numerator := 6036373695873128914306990080 }, some { target := 269, numerator := 6371727790088302742879600640 }, some { target := 270, numerator := 8216175308271758800028958720 }, some { target := 271, numerator := 109996142902577015771816263680 }, some { target := 272, numerator := 192325573032402190686392156160 }, some { target := 273, numerator := 5868696648765542000020684800 }, some { target := 274, numerator := 109996142902577015771816263680 }, some { target := 275, numerator := 6204050742980715828593295360 }, some { target := 276, numerator := 6371727790088302742879600640 }, some { target := 277, numerator := 6371727790088302742879600640 }, some { target := 278, numerator := 6204050742980715828593295360 }, some { target := 279, numerator := 192325573032402190686392156160 }, some { target := 280, numerator := 6204050742980715828593295360 }, some { target := 281, numerator := 8048498261164171885742653440 }, some { target := 282, numerator := 8216175308271758800028958720 }]

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

end Slot9

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20.Parent1
