import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk13Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 2,
parent 54; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot2

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨2, 145, #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416], #[50466754920448, 0, 0, 180541483646976, 0, 50466738143232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 131, numerator := 3017202621906511684027023360 }, some { target := 134, numerator := 10793843168264323751812792320 }, some { target := 136, numerator := 3017201618864802676070154240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 227, numerator := 80458736584173644907387289600 }, some { target := 230, numerator := 287835817820381966715007795200 }, some { target := 232, numerator := 80458709836394738028537446400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 253, numerator := 76938666858616047942689095680 }, some { target := 256, numerator := 275243000790740255671226204160 }, some { target := 258, numerator := 76938641281052468239788933120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 2514335518255426403355852800 }, some { target := 305, numerator := 8994869306886936459843993600 }, some { target := 307, numerator := 2514334682387335563391795200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 328, numerator := 78950135273220389065373777920 }, some { target := 331, numerator := 282438896236249804839101399040 }, some { target := 333, numerator := 78950109026962336690502369280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 342, numerator := 2514335518255426403355852800 }, some { target := 345, numerator := 8994869306886936459843993600 }, some { target := 347, numerator := 2514334682387335563391795200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 443, numerator := 76938666858616047942689095680 }, some { target := 446, numerator := 275243000790740255671226204160 }, some { target := 448, numerator := 76938641281052468239788933120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 469, numerator := 43749438017644419418391838720 }, some { target := 472, numerator := 156510725939832694401285488640 }, some { target := 474, numerator := 43749423473539638803017236480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 518, numerator := 78950135273220389065373777920 }, some { target := 521, numerator := 282438896236249804839101399040 }, some { target := 523, numerator := 78950109026962336690502369280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 544, numerator := 1232527271048810022925039042560 }, some { target := 547, numerator := 4409284934235976252615525662720 }, some { target := 549, numerator := 1232526861306271893174658007040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 558, numerator := 48275241950504186944432373760 }, some { target := 561, numerator := 172701490692229180029004677120 }, some { target := 563, numerator := 48275225901836842817122467840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 589, numerator := 80458736584173644907387289600 }, some { target := 592, numerator := 287835817820381966715007795200 }, some { target := 594, numerator := 80458709836394738028537446400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 603, numerator := 76938666858616047942689095680 }, some { target := 606, numerator := 275243000790740255671226204160 }, some { target := 608, numerator := 76938641281052468239788933120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 658, numerator := 2514335518255426403355852800 }, some { target := 661, numerator := 8994869306886936459843993600 }, some { target := 663, numerator := 2514334682387335563391795200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 684, numerator := 48275241950504186944432373760 }, some { target := 687, numerator := 172701490692229180029004677120 }, some { target := 689, numerator := 48275225901836842817122467840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 698, numerator := 2514335518255426403355852800 }, some { target := 701, numerator := 8994869306886936459843993600 }, some { target := 703, numerator := 2514334682387335563391795200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 729, numerator := 77441533962267133223360266240 }, some { target := 732, numerator := 277041974652117642963195002880 }, some { target := 734, numerator := 77441508217529935352467292160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 743, numerator := 43749438017644419418391838720 }, some { target := 746, numerator := 156510725939832694401285488640 }, some { target := 748, numerator := 43749423473539638803017236480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 763, numerator := 3017202621906511684027023360 }, some { target := 766, numerator := 10793843168264323751812792320 }, some { target := 768, numerator := 3017201618864802676070154240 }]

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

end Slot2

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 26, #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0], #[2199023255552, 2611340115968, 1992864825344, 20547123544064, 2473901162496, 1992864825344, 2473901162496, 2473901162496, 105965433126912, 2473901162496, 20547123544064, 105965433126912, 2199023255552, 2473901162496, 2473901162496, 2611340115968, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 80, numerator := 188592427859882151254163456 }, some { target := 81, numerator := 223953508083610054614319104 }, some { target := 82, numerator := 170911887748018199574085632 }, some { target := 83, numerator := 1762160497815773850781089792 }, some { target := 84, numerator := 212166481342367420160933888 }, some { target := 85, numerator := 170911887748018199574085632 }, some { target := 86, numerator := 212166481342367420160933888 }, some { target := 87, numerator := 212166481342367420160933888 }, some { target := 88, numerator := 9087797617498071163560001536 }, some { target := 89, numerator := 212166481342367420160933888 }, some { target := 90, numerator := 1762160497815773850781089792 }, some { target := 91, numerator := 9087797617498071163560001536 }, some { target := 92, numerator := 188592427859882151254163456 }, some { target := 93, numerator := 212166481342367420160933888 }, some { target := 94, numerator := 212166481342367420160933888 }, some { target := 95, numerator := 223953508083610054614319104 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 115, numerator := 184663418946134606436368384 }, some { target := 116, numerator := 219287809998534845143187456 }, some { target := 117, numerator := 167351223419934487082958848 }, some { target := 118, numerator := 1725448820777945228889817088 }, some { target := 119, numerator := 207746346314401432240914432 }, some { target := 120, numerator := 167351223419934487082958848 }, some { target := 121, numerator := 207746346314401432240914432 }, some { target := 122, numerator := 207746346314401432240914432 }, some { target := 123, numerator := 8898468500466861347652501504 }, some { target := 124, numerator := 207746346314401432240914432 }, some { target := 125, numerator := 1725448820777945228889817088 }, some { target := 126, numerator := 8898468500466861347652501504 }, some { target := 127, numerator := 184663418946134606436368384 }, some { target := 128, numerator := 207746346314401432240914432 }, some { target := 129, numerator := 207746346314401432240914432 }, some { target := 130, numerator := 219287809998534845143187456 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 176, numerator := 145373329808659158258417664 }, some { target := 177, numerator := 172630829147782750431870976 }, some { target := 178, numerator := 131744580139097362171691008 }, some { target := 179, numerator := 1358332050399659009977090048 }, some { target := 180, numerator := 163544996034741553040719872 }, some { target := 181, numerator := 131744580139097362171691008 }, some { target := 182, numerator := 163544996034741553040719872 }, some { target := 183, numerator := 163544996034741553040719872 }, some { target := 184, numerator := 7005177330154763188577501184 }, some { target := 185, numerator := 163544996034741553040719872 }, some { target := 186, numerator := 1358332050399659009977090048 }, some { target := 187, numerator := 7005177330154763188577501184 }, some { target := 188, numerator := 145373329808659158258417664 }, some { target := 189, numerator := 163544996034741553040719872 }, some { target := 190, numerator := 163544996034741553040719872 }, some { target := 191, numerator := 172630829147782750431870976 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 211, numerator := 4569437366688394623095668736 }, some { target := 212, numerator := 5426206872942468614926106624 }, some { target := 213, numerator := 4141052613561357627180449792 }, some { target := 214, numerator := 42695680394994687259550154752 }, some { target := 215, numerator := 5140617037524443950982627328 }, some { target := 216, numerator := 4141052613561357627180449792 }, some { target := 217, numerator := 5140617037524443950982627328 }, some { target := 218, numerator := 5140617037524443950982627328 }, some { target := 219, numerator := 220189763107297015900422537216 }, some { target := 220, numerator := 5140617037524443950982627328 }, some { target := 221, numerator := 42695680394994687259550154752 }, some { target := 222, numerator := 220189763107297015900422537216 }, some { target := 223, numerator := 4569437366688394623095668736 }, some { target := 224, numerator := 5140617037524443950982627328 }, some { target := 225, numerator := 5140617037524443950982627328 }, some { target := 226, numerator := 5426206872942468614926106624 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 237, numerator := 145373329808659158258417664 }, some { target := 238, numerator := 172630829147782750431870976 }, some { target := 239, numerator := 131744580139097362171691008 }, some { target := 240, numerator := 1358332050399659009977090048 }, some { target := 241, numerator := 163544996034741553040719872 }, some { target := 242, numerator := 131744580139097362171691008 }, some { target := 243, numerator := 163544996034741553040719872 }, some { target := 244, numerator := 163544996034741553040719872 }, some { target := 245, numerator := 7005177330154763188577501184 }, some { target := 246, numerator := 163544996034741553040719872 }, some { target := 247, numerator := 1358332050399659009977090048 }, some { target := 248, numerator := 7005177330154763188577501184 }, some { target := 249, numerator := 145373329808659158258417664 }, some { target := 250, numerator := 163544996034741553040719872 }, some { target := 251, numerator := 163544996034741553040719872 }, some { target := 252, numerator := 172630829147782750431870976 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 286, numerator := 145373329808659158258417664 }, some { target := 287, numerator := 172630829147782750431870976 }, some { target := 288, numerator := 131744580139097362171691008 }, some { target := 289, numerator := 1358332050399659009977090048 }, some { target := 290, numerator := 163544996034741553040719872 }, some { target := 291, numerator := 131744580139097362171691008 }, some { target := 292, numerator := 163544996034741553040719872 }, some { target := 293, numerator := 163544996034741553040719872 }, some { target := 294, numerator := 7005177330154763188577501184 }, some { target := 295, numerator := 163544996034741553040719872 }, some { target := 296, numerator := 1358332050399659009977090048 }, some { target := 297, numerator := 7005177330154763188577501184 }, some { target := 298, numerator := 145373329808659158258417664 }, some { target := 299, numerator := 163544996034741553040719872 }, some { target := 300, numerator := 163544996034741553040719872 }, some { target := 301, numerator := 172630829147782750431870976 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 312, numerator := 149302338722406703076212736 }, some { target := 313, numerator := 177296527232857959903002624 }, some { target := 314, numerator := 135305244467181074662817792 }, some { target := 315, numerator := 1395043727437487631868362752 }, some { target := 316, numerator := 167965131062707540960739328 }, some { target := 317, numerator := 135305244467181074662817792 }, some { target := 318, numerator := 167965131062707540960739328 }, some { target := 319, numerator := 167965131062707540960739328 }, some { target := 320, numerator := 7194506447185973004485001216 }, some { target := 321, numerator := 167965131062707540960739328 }, some { target := 322, numerator := 1395043727437487631868362752 }, some { target := 323, numerator := 7194506447185973004485001216 }, some { target := 324, numerator := 149302338722406703076212736 }, some { target := 325, numerator := 167965131062707540960739328 }, some { target := 326, numerator := 167965131062707540960739328 }, some { target := 327, numerator := 177296527232857959903002624 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 149302338722406703076212736 }, some { target := 393, numerator := 177296527232857959903002624 }, some { target := 394, numerator := 135305244467181074662817792 }, some { target := 395, numerator := 1395043727437487631868362752 }, some { target := 396, numerator := 167965131062707540960739328 }, some { target := 397, numerator := 135305244467181074662817792 }, some { target := 398, numerator := 167965131062707540960739328 }, some { target := 399, numerator := 167965131062707540960739328 }, some { target := 400, numerator := 7194506447185973004485001216 }, some { target := 401, numerator := 167965131062707540960739328 }, some { target := 402, numerator := 1395043727437487631868362752 }, some { target := 403, numerator := 7194506447185973004485001216 }, some { target := 404, numerator := 149302338722406703076212736 }, some { target := 405, numerator := 167965131062707540960739328 }, some { target := 406, numerator := 167965131062707540960739328 }, some { target := 407, numerator := 177296527232857959903002624 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 427, numerator := 2526352731539671317842231296 }, some { target := 428, numerator := 3000043868703359689937649664 }, some { target := 429, numerator := 2289507162957827131794522112 }, some { target := 430, numerator := 23605608335323803876088348672 }, some { target := 431, numerator := 2842146822982130232572510208 }, some { target := 432, numerator := 2289507162957827131794522112 }, some { target := 433, numerator := 2842146822982130232572510208 }, some { target := 434, numerator := 2842146822982130232572510208 }, some { target := 435, numerator := 121738622251067911628522520576 }, some { target := 436, numerator := 2842146822982130232572510208 }, some { target := 437, numerator := 23605608335323803876088348672 }, some { target := 438, numerator := 121738622251067911628522520576 }, some { target := 439, numerator := 2526352731539671317842231296 }, some { target := 440, numerator := 2842146822982130232572510208 }, some { target := 441, numerator := 2842146822982130232572510208 }, some { target := 442, numerator := 3000043868703359689937649664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 453, numerator := 137515311981164068622827520 }, some { target := 454, numerator := 163299432977632331489607680 }, some { target := 455, numerator := 124623251482929937189437440 }, some { target := 456, numerator := 1284908696324001766194544640 }, some { target := 457, numerator := 154704725978809577200680960 }, some { target := 458, numerator := 124623251482929937189437440 }, some { target := 459, numerator := 154704725978809577200680960 }, some { target := 460, numerator := 154704725978809577200680960 }, some { target := 461, numerator := 6626519096092343556762501120 }, some { target := 462, numerator := 154704725978809577200680960 }, some { target := 463, numerator := 1284908696324001766194544640 }, some { target := 464, numerator := 6626519096092343556762501120 }, some { target := 465, numerator := 137515311981164068622827520 }, some { target := 466, numerator := 154704725978809577200680960 }, some { target := 467, numerator := 154704725978809577200680960 }, some { target := 468, numerator := 163299432977632331489607680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 502, numerator := 4569437366688394623095668736 }, some { target := 503, numerator := 5426206872942468614926106624 }, some { target := 504, numerator := 4141052613561357627180449792 }, some { target := 505, numerator := 42695680394994687259550154752 }, some { target := 506, numerator := 5140617037524443950982627328 }, some { target := 507, numerator := 4141052613561357627180449792 }, some { target := 508, numerator := 5140617037524443950982627328 }, some { target := 509, numerator := 5140617037524443950982627328 }, some { target := 510, numerator := 220189763107297015900422537216 }, some { target := 511, numerator := 5140617037524443950982627328 }, some { target := 512, numerator := 42695680394994687259550154752 }, some { target := 513, numerator := 220189763107297015900422537216 }, some { target := 514, numerator := 4569437366688394623095668736 }, some { target := 515, numerator := 5140617037524443950982627328 }, some { target := 516, numerator := 5140617037524443950982627328 }, some { target := 517, numerator := 5426206872942468614926106624 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 528, numerator := 2526352731539671317842231296 }, some { target := 529, numerator := 3000043868703359689937649664 }, some { target := 530, numerator := 2289507162957827131794522112 }, some { target := 531, numerator := 23605608335323803876088348672 }, some { target := 532, numerator := 2842146822982130232572510208 }, some { target := 533, numerator := 2289507162957827131794522112 }, some { target := 534, numerator := 2842146822982130232572510208 }, some { target := 535, numerator := 2842146822982130232572510208 }, some { target := 536, numerator := 121738622251067911628522520576 }, some { target := 537, numerator := 2842146822982130232572510208 }, some { target := 538, numerator := 23605608335323803876088348672 }, some { target := 539, numerator := 121738622251067911628522520576 }, some { target := 540, numerator := 2526352731539671317842231296 }, some { target := 541, numerator := 2842146822982130232572510208 }, some { target := 542, numerator := 2842146822982130232572510208 }, some { target := 543, numerator := 3000043868703359689937649664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 573, numerator := 188592427859882151254163456 }, some { target := 574, numerator := 223953508083610054614319104 }, some { target := 575, numerator := 170911887748018199574085632 }, some { target := 576, numerator := 1762160497815773850781089792 }, some { target := 577, numerator := 212166481342367420160933888 }, some { target := 578, numerator := 170911887748018199574085632 }, some { target := 579, numerator := 212166481342367420160933888 }, some { target := 580, numerator := 212166481342367420160933888 }, some { target := 581, numerator := 9087797617498071163560001536 }, some { target := 582, numerator := 212166481342367420160933888 }, some { target := 583, numerator := 1762160497815773850781089792 }, some { target := 584, numerator := 9087797617498071163560001536 }, some { target := 585, numerator := 188592427859882151254163456 }, some { target := 586, numerator := 212166481342367420160933888 }, some { target := 587, numerator := 212166481342367420160933888 }, some { target := 588, numerator := 223953508083610054614319104 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 642, numerator := 145373329808659158258417664 }, some { target := 643, numerator := 172630829147782750431870976 }, some { target := 644, numerator := 131744580139097362171691008 }, some { target := 645, numerator := 1358332050399659009977090048 }, some { target := 646, numerator := 163544996034741553040719872 }, some { target := 647, numerator := 131744580139097362171691008 }, some { target := 648, numerator := 163544996034741553040719872 }, some { target := 649, numerator := 163544996034741553040719872 }, some { target := 650, numerator := 7005177330154763188577501184 }, some { target := 651, numerator := 163544996034741553040719872 }, some { target := 652, numerator := 1358332050399659009977090048 }, some { target := 653, numerator := 7005177330154763188577501184 }, some { target := 654, numerator := 145373329808659158258417664 }, some { target := 655, numerator := 163544996034741553040719872 }, some { target := 656, numerator := 163544996034741553040719872 }, some { target := 657, numerator := 172630829147782750431870976 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 668, numerator := 137515311981164068622827520 }, some { target := 669, numerator := 163299432977632331489607680 }, some { target := 670, numerator := 124623251482929937189437440 }, some { target := 671, numerator := 1284908696324001766194544640 }, some { target := 672, numerator := 154704725978809577200680960 }, some { target := 673, numerator := 124623251482929937189437440 }, some { target := 674, numerator := 154704725978809577200680960 }, some { target := 675, numerator := 154704725978809577200680960 }, some { target := 676, numerator := 6626519096092343556762501120 }, some { target := 677, numerator := 154704725978809577200680960 }, some { target := 678, numerator := 1284908696324001766194544640 }, some { target := 679, numerator := 6626519096092343556762501120 }, some { target := 680, numerator := 137515311981164068622827520 }, some { target := 681, numerator := 154704725978809577200680960 }, some { target := 682, numerator := 154704725978809577200680960 }, some { target := 683, numerator := 163299432977632331489607680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 713, numerator := 184663418946134606436368384 }, some { target := 714, numerator := 219287809998534845143187456 }, some { target := 715, numerator := 167351223419934487082958848 }, some { target := 716, numerator := 1725448820777945228889817088 }, some { target := 717, numerator := 207746346314401432240914432 }, some { target := 718, numerator := 167351223419934487082958848 }, some { target := 719, numerator := 207746346314401432240914432 }, some { target := 720, numerator := 207746346314401432240914432 }, some { target := 721, numerator := 8898468500466861347652501504 }, some { target := 722, numerator := 207746346314401432240914432 }, some { target := 723, numerator := 1725448820777945228889817088 }, some { target := 724, numerator := 8898468500466861347652501504 }, some { target := 725, numerator := 184663418946134606436368384 }, some { target := 726, numerator := 207746346314401432240914432 }, some { target := 727, numerator := 207746346314401432240914432 }, some { target := 728, numerator := 219287809998534845143187456 }]

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

end Slot3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent0
