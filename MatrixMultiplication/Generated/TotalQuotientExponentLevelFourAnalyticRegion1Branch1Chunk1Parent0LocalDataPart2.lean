import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 1,
parent 5; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 4, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 2]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        1 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes_eq

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
  [some { target := 10, numerator := 1818224432700402278758088704 }, some { target := 11, numerator := 1353996917968384675670917120 }, some { target := 12, numerator := 1431368170423720942852112384 }, some { target := 13, numerator := 1856910058928070412348686336 }, some { target := 14, numerator := 24874857664390609898754277376 }, some { target := 15, numerator := 44991383302778039365865046016 }, some { target := 16, numerator := 1353996917968384675670917120 }, some { target := 17, numerator := 24874857664390609898754277376 }, some { target := 18, numerator := 1470053796651389076442710016 }, some { target := 19, numerator := 1470053796651389076442710016 }, some { target := 20, numerator := 1431368170423720942852112384 }, some { target := 21, numerator := 1431368170423720942852112384 }, some { target := 22, numerator := 44991383302778039365865046016 }, some { target := 23, numerator := 1431368170423720942852112384 }, some { target := 24, numerator := 1818224432700402278758088704 }, some { target := 25, numerator := 1856910058928070412348686336 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 141, numerator := 1818224432700402278758088704 }, some { target := 142, numerator := 1353996917968384675670917120 }, some { target := 143, numerator := 1431368170423720942852112384 }, some { target := 144, numerator := 1856910058928070412348686336 }, some { target := 145, numerator := 24874857664390609898754277376 }, some { target := 146, numerator := 44991383302778039365865046016 }, some { target := 147, numerator := 1353996917968384675670917120 }, some { target := 148, numerator := 24874857664390609898754277376 }, some { target := 149, numerator := 1470053796651389076442710016 }, some { target := 150, numerator := 1470053796651389076442710016 }, some { target := 151, numerator := 1431368170423720942852112384 }, some { target := 152, numerator := 1431368170423720942852112384 }, some { target := 153, numerator := 44991383302778039365865046016 }, some { target := 154, numerator := 1431368170423720942852112384 }, some { target := 155, numerator := 1818224432700402278758088704 }, some { target := 156, numerator := 1856910058928070412348686336 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left2.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left2.routed_eq]
  rfl

end Slot8

namespace Slot9

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨9, 126, #[49882488373248, 0, 0, 181709966409728, 0, 49882521927680, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

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
  [some { target := 26, numerator := 2591491265470200054093447168 }, some { target := 27, numerator := 37576623349317900784354983936 }, some { target := 28, numerator := 66514942480401801388398477312 }, some { target := 29, numerator := 2159576054558500045077872640 }, some { target := 30, numerator := 41463860247523200865495154688 }, some { target := 31, numerator := 2159576054558500045077872640 }, some { target := 32, numerator := 66083027269490101379382902784 }, some { target := 33, numerator := 69106433745872001442491924480 }, some { target := 34, numerator := 41463860247523200865495154688 }, some { target := 35, numerator := 1058624181944576722097173168128 }, some { target := 36, numerator := 67810688113136901415445200896 }, some { target := 37, numerator := 37576623349317900784354983936 }, some { target := 38, numerator := 66083027269490101379382902784 }, some { target := 39, numerator := 2159576054558500045077872640 }, some { target := 40, numerator := 67810688113136901415445200896 }, some { target := 41, numerator := 2159576054558500045077872640 }, some { target := 42, numerator := 66083027269490101379382902784 }, some { target := 43, numerator := 69106433745872001442491924480 }, some { target := 44, numerator := 2591491265470200054093447168 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 157, numerator := 9440182439900839423506382848 }, some { target := 158, numerator := 136882645378562171640842551296 }, some { target := 159, numerator := 242298015957454878536663826432 }, some { target := 160, numerator := 7866818699917366186255319040 }, some { target := 161, numerator := 151042919038413430776102125568 }, some { target := 162, numerator := 7866818699917366186255319040 }, some { target := 163, numerator := 240724652217471405299412762624 }, some { target := 164, numerator := 251738198397355717960170209280 }, some { target := 165, numerator := 151042919038413430776102125568 }, some { target := 166, numerator := 3856314526699492904502357393408 }, some { target := 167, numerator := 247018107177405298248417017856 }, some { target := 168, numerator := 136882645378562171640842551296 }, some { target := 169, numerator := 240724652217471405299412762624 }, some { target := 170, numerator := 7866818699917366186255319040 }, some { target := 171, numerator := 247018107177405298248417017856 }, some { target := 172, numerator := 7866818699917366186255319040 }, some { target := 173, numerator := 240724652217471405299412762624 }, some { target := 174, numerator := 251738198397355717960170209280 }, some { target := 175, numerator := 9440182439900839423506382848 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 2591493008687515019646074880 }, some { target := 268, numerator := 37576648625968967784868085760 }, some { target := 269, numerator := 66514987222979552170915921920 }, some { target := 270, numerator := 2159577507239595849705062400 }, some { target := 271, numerator := 41463888139000240314337198080 }, some { target := 272, numerator := 2159577507239595849705062400 }, some { target := 273, numerator := 66083071721531633000974909440 }, some { target := 274, numerator := 69106480231667067190561996800 }, some { target := 275, numerator := 41463888139000240314337198080 }, some { target := 276, numerator := 1058624894048849885525421588480 }, some { target := 277, numerator := 67810733727323309680738959360 }, some { target := 278, numerator := 37576648625968967784868085760 }, some { target := 279, numerator := 66083071721531633000974909440 }, some { target := 280, numerator := 2159577507239595849705062400 }, some { target := 281, numerator := 67810733727323309680738959360 }, some { target := 282, numerator := 2159577507239595849705062400 }, some { target := 283, numerator := 66083071721531633000974909440 }, some { target := 284, numerator := 69106480231667067190561996800 }, some { target := 285, numerator := 2591493008687515019646074880 }]

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

namespace Slot10

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨10, 240, #[3434312892416, 0, 137303192240128, 0, 0, 137303158685696, 0, 0, 0, 0, 0, 0, 3434312892416, 0, 0, 0, 0, 0, 0], #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0]⟩

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
  [some { target := 80, numerator := 1755871135764074800286269440 }, some { target := 81, numerator := 1982435153282019935807078400 }, some { target := 82, numerator := 1699230131384588516406067200 }, some { target := 83, numerator := 22373196729897082132679884800 }, some { target := 84, numerator := 1982435153282019935807078400 }, some { target := 85, numerator := 1699230131384588516406067200 }, some { target := 86, numerator := 1982435153282019935807078400 }, some { target := 87, numerator := 1982435153282019935807078400 }, some { target := 88, numerator := 82186097354634597910173450240 }, some { target := 89, numerator := 2039076157661506219687280640 }, some { target := 90, numerator := 22373196729897082132679884800 }, some { target := 91, numerator := 82186097354634597910173450240 }, some { target := 92, numerator := 1755871135764074800286269440 }, some { target := 93, numerator := 1982435153282019935807078400 }, some { target := 94, numerator := 2039076157661506219687280640 }, some { target := 95, numerator := 1982435153282019935807078400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 176, numerator := 70199402225434647953166827520 }, some { target := 177, numerator := 79257389609361699301962547200 }, some { target := 178, numerator := 67934905379452885115967897600 }, some { target := 179, numerator := 894476254162796320693577318400 }, some { target := 180, numerator := 79257389609361699301962547200 }, some { target := 181, numerator := 67934905379452885115967897600 }, some { target := 182, numerator := 79257389609361699301962547200 }, some { target := 183, numerator := 79257389609361699301962547200 }, some { target := 184, numerator := 3285784923519537876775647313920 }, some { target := 185, numerator := 81521886455343462139161477120 }, some { target := 186, numerator := 894476254162796320693577318400 }, some { target := 187, numerator := 3285784923519537876775647313920 }, some { target := 188, numerator := 70199402225434647953166827520 }, some { target := 189, numerator := 79257389609361699301962547200 }, some { target := 190, numerator := 81521886455343462139161477120 }, some { target := 191, numerator := 79257389609361699301962547200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 286, numerator := 70199385069962659403283824640 }, some { target := 287, numerator := 79257370240280421906933350400 }, some { target := 288, numerator := 67934888777383218777371443200 }, some { target := 289, numerator := 894476035568879047235390668800 }, some { target := 290, numerator := 79257370240280421906933350400 }, some { target := 291, numerator := 67934888777383218777371443200 }, some { target := 292, numerator := 79257370240280421906933350400 }, some { target := 293, numerator := 79257370240280421906933350400 }, some { target := 294, numerator := 3285784120532768348198865469440 }, some { target := 295, numerator := 81521866532859862532845731840 }, some { target := 296, numerator := 894476035568879047235390668800 }, some { target := 297, numerator := 3285784120532768348198865469440 }, some { target := 298, numerator := 70199385069962659403283824640 }, some { target := 299, numerator := 79257370240280421906933350400 }, some { target := 300, numerator := 81521866532859862532845731840 }, some { target := 301, numerator := 79257370240280421906933350400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 573, numerator := 1755871135764074800286269440 }, some { target := 574, numerator := 1982435153282019935807078400 }, some { target := 575, numerator := 1699230131384588516406067200 }, some { target := 576, numerator := 22373196729897082132679884800 }, some { target := 577, numerator := 1982435153282019935807078400 }, some { target := 578, numerator := 1699230131384588516406067200 }, some { target := 579, numerator := 1982435153282019935807078400 }, some { target := 580, numerator := 1982435153282019935807078400 }, some { target := 581, numerator := 82186097354634597910173450240 }, some { target := 582, numerator := 2039076157661506219687280640 }, some { target := 583, numerator := 22373196729897082132679884800 }, some { target := 584, numerator := 82186097354634597910173450240 }, some { target := 585, numerator := 1755871135764074800286269440 }, some { target := 586, numerator := 1982435153282019935807078400 }, some { target := 587, numerator := 2039076157661506219687280640 }, some { target := 588, numerator := 1982435153282019935807078400 }]

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

end Slot10

namespace Slot11

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨11, 29, #[139552882688, 22870029762560, 0, 235455811420160, 0, 0, 0, 0, 0, 0, 0, 22870029762560, 0, 0, 0, 0, 0, 0, 139552882688], #[1649267441664, 34428457844736, 1786706395136, 37039797960704, 55456617725952, 1717986918400, 55456617725952, 57793079934976, 34428457844736, 1717986918400, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 131, numerator := 6674640748422548189872128 }, some { target := 132, numerator := 139333125623320693463580672 }, some { target := 133, numerator := 7230860810791093872361472 }, some { target := 134, numerator := 149901306808323061430878208 }, some { target := 135, numerator := 224434795165708182884450304 }, some { target := 136, numerator := 6952750779606821031116800 }, some { target := 137, numerator := 224434795165708182884450304 }, some { target := 138, numerator := 233890536225973459486769152 }, some { target := 139, numerator := 139333125623320693463580672 }, some { target := 140, numerator := 6952750779606821031116800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 227, numerator := 1093845068841029188567695360 }, some { target := 228, numerator := 22834015812056484311350640640 }, some { target := 229, numerator := 1184998824577781620948336640 }, some { target := 230, numerator := 24565937171054780526582824960 }, some { target := 231, numerator := 36780540439779606465588756480 }, some { target := 232, numerator := 1139421946709405404758016000 }, some { target := 233, numerator := 36780540439779606465588756480 }, some { target := 234, numerator := 38330154287304397816059658240 }, some { target := 235, numerator := 22834015812056484311350640640 }, some { target := 236, numerator := 1139421946709405404758016000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 11261558508049607016012840960 }, some { target := 303, numerator := 235085033855535546459268055040 }, some { target := 304, numerator := 12200021717053740934013911040 }, some { target := 305, numerator := 252915834826614090901288386560 }, some { target := 306, numerator := 378669904833168035913431777280 }, some { target := 307, numerator := 11730790112551673975013376000 }, some { target := 308, numerator := 378669904833168035913431777280 }, some { target := 309, numerator := 394623779386238312519449968640 }, some { target := 310, numerator := 235085033855535546459268055040 }, some { target := 311, numerator := 11730790112551673975013376000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 589, numerator := 1093845068841029188567695360 }, some { target := 590, numerator := 22834015812056484311350640640 }, some { target := 591, numerator := 1184998824577781620948336640 }, some { target := 592, numerator := 24565937171054780526582824960 }, some { target := 593, numerator := 36780540439779606465588756480 }, some { target := 594, numerator := 1139421946709405404758016000 }, some { target := 595, numerator := 36780540439779606465588756480 }, some { target := 596, numerator := 38330154287304397816059658240 }, some { target := 597, numerator := 22834015812056484311350640640 }, some { target := 598, numerator := 1139421946709405404758016000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 763, numerator := 6674640748422548189872128 }, some { target := 764, numerator := 139333125623320693463580672 }, some { target := 765, numerator := 7230860810791093872361472 }, some { target := 766, numerator := 149901306808323061430878208 }, some { target := 767, numerator := 224434795165708182884450304 }, some { target := 768, numerator := 6952750779606821031116800 }, some { target := 769, numerator := 224434795165708182884450304 }, some { target := 770, numerator := 233890536225973459486769152 }, some { target := 771, numerator := 139333125623320693463580672 }, some { target := 772, numerator := 6952750779606821031116800 }]

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

end Slot11

namespace Slot12

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨12, 1, #[706035580928, 140031452774400, 0, 0, 0, 0, 140031452774400, 0, 0, 0, 0, 0, 0, 0, 706035580928, 0, 0, 0, 0], #[67207648247808, 73529840107520, 67207648247808, 73529840107520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 263, numerator := 47450990973445802582605824 }, some { target := 264, numerator := 51914683375855837181378560 }, some { target := 265, numerator := 47450990973445802582605824 }, some { target := 266, numerator := 51914683375855837181378560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 338, numerator := 9411184621691412860318515200 }, some { target := 339, numerator := 10296490332525369898303488000 }, some { target := 340, numerator := 9411184621691412860318515200 }, some { target := 341, numerator := 10296490332525369898303488000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 599, numerator := 9411184621691412860318515200 }, some { target := 600, numerator := 10296490332525369898303488000 }, some { target := 601, numerator := 9411184621691412860318515200 }, some { target := 602, numerator := 10296490332525369898303488000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 773, numerator := 47450990973445802582605824 }, some { target := 774, numerator := 51914683375855837181378560 }, some { target := 775, numerator := 47450990973445802582605824 }, some { target := 776, numerator := 51914683375855837181378560 }]

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

end Slot12

namespace Slot13

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨13, 0, #[5963008442368, 0, 269517133447168, 0, 0, 0, 0, 5994834821120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot13

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent0
