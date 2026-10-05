import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk8Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 36; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 22, #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0], #[3298534883328, 2473901162496, 2611340115968, 3367254360064, 45079976738816, 78821239816192, 2405181685760, 45079976738816, 2542620639232, 2611340115968, 2611340115968, 2542620639232, 78821239816192, 2542620639232, 3298534883328, 3367254360064, 0, 0, 0]⟩

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
  [some { target := 55, numerator := 234380493277786231246159872 }, some { target := 56, numerator := 175785369958339673434619904 }, some { target := 57, numerator := 185551223844914099736543232 }, some { target := 58, numerator := 239263420221073444397121536 }, some { target := 59, numerator := 3203200074796411827030851584 }, some { target := 60, numerator := 5600717203950433484153028608 }, some { target := 61, numerator := 170902443015052460283658240 }, some { target := 62, numerator := 3203200074796411827030851584 }, some { target := 63, numerator := 180668296901626886585581568 }, some { target := 64, numerator := 185551223844914099736543232 }, some { target := 65, numerator := 185551223844914099736543232 }, some { target := 66, numerator := 180668296901626886585581568 }, some { target := 67, numerator := 5600717203950433484153028608 }, some { target := 68, numerator := 180668296901626886585581568 }, some { target := 69, numerator := 234380493277786231246159872 }, some { target := 70, numerator := 239263420221073444397121536 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 100, numerator := 174538665206862087098204160 }, some { target := 101, numerator := 130903998905146565323653120 }, some { target := 102, numerator := 138176443288765818952744960 }, some { target := 103, numerator := 178174887398671713912750080 }, some { target := 104, numerator := 2385361757827115190342123520 }, some { target := 105, numerator := 4170746854005641956284170240 }, some { target := 106, numerator := 127267776713336938509107200 }, some { target := 107, numerator := 2385361757827115190342123520 }, some { target := 108, numerator := 134540221096956192138199040 }, some { target := 109, numerator := 138176443288765818952744960 }, some { target := 110, numerator := 138176443288765818952744960 }, some { target := 111, numerator := 134540221096956192138199040 }, some { target := 112, numerator := 4170746854005641956284170240 }, some { target := 113, numerator := 134540221096956192138199040 }, some { target := 114, numerator := 174538665206862087098204160 }, some { target := 115, numerator := 178174887398671713912750080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 184512303218682777789530112 }, some { target := 127, numerator := 138384227414012083342147584 }, some { target := 128, numerator := 146072240048123865750044672 }, some { target := 129, numerator := 188356309535738668993478656 }, some { target := 130, numerator := 2521668143988664629790244864 }, some { target := 131, numerator := 4409075245663107210928979968 }, some { target := 132, numerator := 134540221096956192138199040 }, some { target := 133, numerator := 2521668143988664629790244864 }, some { target := 134, numerator := 142228233731067974546096128 }, some { target := 135, numerator := 146072240048123865750044672 }, some { target := 136, numerator := 146072240048123865750044672 }, some { target := 137, numerator := 142228233731067974546096128 }, some { target := 138, numerator := 4409075245663107210928979968 }, some { target := 139, numerator := 142228233731067974546096128 }, some { target := 140, numerator := 184512303218682777789530112 }, some { target := 141, numerator := 188356309535738668993478656 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 195, numerator := 239367312283696576591822848 }, some { target := 196, numerator := 179525484212772432443867136 }, some { target := 197, numerator := 189499122224593123135193088 }, some { target := 198, numerator := 244354131289606921937485824 }, some { target := 199, numerator := 3271353267877186546754912256 }, some { target := 200, numerator := 5719881399779166111475433472 }, some { target := 201, numerator := 174538665206862087098204160 }, some { target := 202, numerator := 3271353267877186546754912256 }, some { target := 203, numerator := 184512303218682777789530112 }, some { target := 204, numerator := 189499122224593123135193088 }, some { target := 205, numerator := 189499122224593123135193088 }, some { target := 206, numerator := 184512303218682777789530112 }, some { target := 207, numerator := 5719881399779166111475433472 }, some { target := 208, numerator := 184512303218682777789530112 }, some { target := 209, numerator := 239367312283696576591822848 }, some { target := 210, numerator := 244354131289606921937485824 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 240, numerator := 3206524620800352057261293568 }, some { target := 241, numerator := 2404893465600264042945970176 }, some { target := 242, numerator := 2538498658133612045331857408 }, some { target := 243, numerator := 3273327217067026058454237184 }, some { target := 244, numerator := 43822503150938144782571012096 }, some { target := 245, numerator := 76622577917875079368306327552 }, some { target := 246, numerator := 2338090869333590041753026560 }, some { target := 247, numerator := 43822503150938144782571012096 }, some { target := 248, numerator := 2471696061866938044138913792 }, some { target := 249, numerator := 2538498658133612045331857408 }, some { target := 250, numerator := 2538498658133612045331857408 }, some { target := 251, numerator := 2471696061866938044138913792 }, some { target := 252, numerator := 76622577917875079368306327552 }, some { target := 253, numerator := 2471696061866938044138913792 }, some { target := 254, numerator := 3206524620800352057261293568 }, some { target := 255, numerator := 3273327217067026058454237184 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 266, numerator := 5799670503873731637006041088 }, some { target := 267, numerator := 4349752877905298727754530816 }, some { target := 268, numerator := 4591405815566704212629782528 }, some { target := 269, numerator := 5920496972704434379443666944 }, some { target := 270, numerator := 79262163552940999039082561536 }, some { target := 271, numerator := 138587959748816045575956856832 }, some { target := 272, numerator := 4228926409074595985316904960 }, some { target := 273, numerator := 79262163552940999039082561536 }, some { target := 274, numerator := 4470579346736001470192156672 }, some { target := 275, numerator := 4591405815566704212629782528 }, some { target := 276, numerator := 4591405815566704212629782528 }, some { target := 277, numerator := 4470579346736001470192156672 }, some { target := 278, numerator := 138587959748816045575956856832 }, some { target := 279, numerator := 4470579346736001470192156672 }, some { target := 280, numerator := 5799670503873731637006041088 }, some { target := 281, numerator := 5920496972704434379443666944 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 315, numerator := 174538665206862087098204160 }, some { target := 316, numerator := 130903998905146565323653120 }, some { target := 317, numerator := 138176443288765818952744960 }, some { target := 318, numerator := 178174887398671713912750080 }, some { target := 319, numerator := 2385361757827115190342123520 }, some { target := 320, numerator := 4170746854005641956284170240 }, some { target := 321, numerator := 127267776713336938509107200 }, some { target := 322, numerator := 2385361757827115190342123520 }, some { target := 323, numerator := 134540221096956192138199040 }, some { target := 324, numerator := 138176443288765818952744960 }, some { target := 325, numerator := 138176443288765818952744960 }, some { target := 326, numerator := 134540221096956192138199040 }, some { target := 327, numerator := 4170746854005641956284170240 }, some { target := 328, numerator := 134540221096956192138199040 }, some { target := 329, numerator := 174538665206862087098204160 }, some { target := 330, numerator := 178174887398671713912750080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 341, numerator := 3206524620800352057261293568 }, some { target := 342, numerator := 2404893465600264042945970176 }, some { target := 343, numerator := 2538498658133612045331857408 }, some { target := 344, numerator := 3273327217067026058454237184 }, some { target := 345, numerator := 43822503150938144782571012096 }, some { target := 346, numerator := 76622577917875079368306327552 }, some { target := 347, numerator := 2338090869333590041753026560 }, some { target := 348, numerator := 43822503150938144782571012096 }, some { target := 349, numerator := 2471696061866938044138913792 }, some { target := 350, numerator := 2538498658133612045331857408 }, some { target := 351, numerator := 2538498658133612045331857408 }, some { target := 352, numerator := 2471696061866938044138913792 }, some { target := 353, numerator := 76622577917875079368306327552 }, some { target := 354, numerator := 2471696061866938044138913792 }, some { target := 355, numerator := 3206524620800352057261293568 }, some { target := 356, numerator := 3273327217067026058454237184 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 376, numerator := 189499122224593123135193088 }, some { target := 377, numerator := 142124341668444842351394816 }, some { target := 378, numerator := 150020138427802889148694528 }, some { target := 379, numerator := 193447020604272146533842944 }, some { target := 380, numerator := 2589821337069439349514305536 }, some { target := 381, numerator := 4528239441491839838251384832 }, some { target := 382, numerator := 138176443288765818952744960 }, some { target := 383, numerator := 2589821337069439349514305536 }, some { target := 384, numerator := 146072240048123865750044672 }, some { target := 385, numerator := 150020138427802889148694528 }, some { target := 386, numerator := 150020138427802889148694528 }, some { target := 387, numerator := 146072240048123865750044672 }, some { target := 388, numerator := 4528239441491839838251384832 }, some { target := 389, numerator := 146072240048123865750044672 }, some { target := 390, numerator := 189499122224593123135193088 }, some { target := 391, numerator := 193447020604272146533842944 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 456, numerator := 189499122224593123135193088 }, some { target := 457, numerator := 142124341668444842351394816 }, some { target := 458, numerator := 150020138427802889148694528 }, some { target := 459, numerator := 193447020604272146533842944 }, some { target := 460, numerator := 2589821337069439349514305536 }, some { target := 461, numerator := 4528239441491839838251384832 }, some { target := 462, numerator := 138176443288765818952744960 }, some { target := 463, numerator := 2589821337069439349514305536 }, some { target := 464, numerator := 146072240048123865750044672 }, some { target := 465, numerator := 150020138427802889148694528 }, some { target := 466, numerator := 150020138427802889148694528 }, some { target := 467, numerator := 146072240048123865750044672 }, some { target := 468, numerator := 4528239441491839838251384832 }, some { target := 469, numerator := 146072240048123865750044672 }, some { target := 470, numerator := 189499122224593123135193088 }, some { target := 471, numerator := 193447020604272146533842944 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 482, numerator := 184512303218682777789530112 }, some { target := 483, numerator := 138384227414012083342147584 }, some { target := 484, numerator := 146072240048123865750044672 }, some { target := 485, numerator := 188356309535738668993478656 }, some { target := 486, numerator := 2521668143988664629790244864 }, some { target := 487, numerator := 4409075245663107210928979968 }, some { target := 488, numerator := 134540221096956192138199040 }, some { target := 489, numerator := 2521668143988664629790244864 }, some { target := 490, numerator := 142228233731067974546096128 }, some { target := 491, numerator := 146072240048123865750044672 }, some { target := 492, numerator := 146072240048123865750044672 }, some { target := 493, numerator := 142228233731067974546096128 }, some { target := 494, numerator := 4409075245663107210928979968 }, some { target := 495, numerator := 142228233731067974546096128 }, some { target := 496, numerator := 184512303218682777789530112 }, some { target := 497, numerator := 188356309535738668993478656 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 531, numerator := 184512303218682777789530112 }, some { target := 532, numerator := 138384227414012083342147584 }, some { target := 533, numerator := 146072240048123865750044672 }, some { target := 534, numerator := 188356309535738668993478656 }, some { target := 535, numerator := 2521668143988664629790244864 }, some { target := 536, numerator := 4409075245663107210928979968 }, some { target := 537, numerator := 134540221096956192138199040 }, some { target := 538, numerator := 2521668143988664629790244864 }, some { target := 539, numerator := 142228233731067974546096128 }, some { target := 540, numerator := 146072240048123865750044672 }, some { target := 541, numerator := 146072240048123865750044672 }, some { target := 542, numerator := 142228233731067974546096128 }, some { target := 543, numerator := 4409075245663107210928979968 }, some { target := 544, numerator := 142228233731067974546096128 }, some { target := 545, numerator := 184512303218682777789530112 }, some { target := 546, numerator := 188356309535738668993478656 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 557, numerator := 5799670503873731637006041088 }, some { target := 558, numerator := 4349752877905298727754530816 }, some { target := 559, numerator := 4591405815566704212629782528 }, some { target := 560, numerator := 5920496972704434379443666944 }, some { target := 561, numerator := 79262163552940999039082561536 }, some { target := 562, numerator := 138587959748816045575956856832 }, some { target := 563, numerator := 4228926409074595985316904960 }, some { target := 564, numerator := 79262163552940999039082561536 }, some { target := 565, numerator := 4470579346736001470192156672 }, some { target := 566, numerator := 4591405815566704212629782528 }, some { target := 567, numerator := 4591405815566704212629782528 }, some { target := 568, numerator := 4470579346736001470192156672 }, some { target := 569, numerator := 138587959748816045575956856832 }, some { target := 570, numerator := 4470579346736001470192156672 }, some { target := 571, numerator := 5799670503873731637006041088 }, some { target := 572, numerator := 5920496972704434379443666944 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 592, numerator := 184512303218682777789530112 }, some { target := 593, numerator := 138384227414012083342147584 }, some { target := 594, numerator := 146072240048123865750044672 }, some { target := 595, numerator := 188356309535738668993478656 }, some { target := 596, numerator := 2521668143988664629790244864 }, some { target := 597, numerator := 4409075245663107210928979968 }, some { target := 598, numerator := 134540221096956192138199040 }, some { target := 599, numerator := 2521668143988664629790244864 }, some { target := 600, numerator := 142228233731067974546096128 }, some { target := 601, numerator := 146072240048123865750044672 }, some { target := 602, numerator := 146072240048123865750044672 }, some { target := 603, numerator := 142228233731067974546096128 }, some { target := 604, numerator := 4409075245663107210928979968 }, some { target := 605, numerator := 142228233731067974546096128 }, some { target := 606, numerator := 184512303218682777789530112 }, some { target := 607, numerator := 188356309535738668993478656 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 234380493277786231246159872 }, some { target := 654, numerator := 175785369958339673434619904 }, some { target := 655, numerator := 185551223844914099736543232 }, some { target := 656, numerator := 239263420221073444397121536 }, some { target := 657, numerator := 3203200074796411827030851584 }, some { target := 658, numerator := 5600717203950433484153028608 }, some { target := 659, numerator := 170902443015052460283658240 }, some { target := 660, numerator := 3203200074796411827030851584 }, some { target := 661, numerator := 180668296901626886585581568 }, some { target := 662, numerator := 185551223844914099736543232 }, some { target := 663, numerator := 185551223844914099736543232 }, some { target := 664, numerator := 180668296901626886585581568 }, some { target := 665, numerator := 5600717203950433484153028608 }, some { target := 666, numerator := 180668296901626886585581568 }, some { target := 667, numerator := 234380493277786231246159872 }, some { target := 668, numerator := 239263420221073444397121536 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 688, numerator := 239367312283696576591822848 }, some { target := 689, numerator := 179525484212772432443867136 }, some { target := 690, numerator := 189499122224593123135193088 }, some { target := 691, numerator := 244354131289606921937485824 }, some { target := 692, numerator := 3271353267877186546754912256 }, some { target := 693, numerator := 5719881399779166111475433472 }, some { target := 694, numerator := 174538665206862087098204160 }, some { target := 695, numerator := 3271353267877186546754912256 }, some { target := 696, numerator := 184512303218682777789530112 }, some { target := 697, numerator := 189499122224593123135193088 }, some { target := 698, numerator := 189499122224593123135193088 }, some { target := 699, numerator := 184512303218682777789530112 }, some { target := 700, numerator := 5719881399779166111475433472 }, some { target := 701, numerator := 184512303218682777789530112 }, some { target := 702, numerator := 239367312283696576591822848 }, some { target := 703, numerator := 244354131289606921937485824 }]

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

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 29, #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[206963736576, 24461784907776, 0, 232137462644736, 0, 0, 0, 0, 0, 0, 0, 24461801684992, 0, 0, 0, 0, 0, 0, 206963736576]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

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
  [some { target := 142, numerator := 12785973273066227802046464 }, some { target := 143, numerator := 1511219951942962915011723264 }, some { target := 145, numerator := 14341176102428335121790664704 }, some { target := 153, numerator := 1511220988419395556567154688 }, some { target := 160, numerator := 12785973273066227802046464 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 282, numerator := 313462570565494617082429440 }, some { target := 283, numerator := 37049263337956510174480957440 }, some { target := 285, numerator := 351590123801468861050351779840 }, some { target := 293, numerator := 37049288748346471709388308480 }, some { target := 300, numerator := 313462570565494617082429440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 357, numerator := 231797321918168387895164928 }, some { target := 358, numerator := 27396955257804682523760918528 }, some { target := 360, numerator := 259991644179507236724075921408 }, some { target := 368, numerator := 27396974048119364606152933376 }, some { target := 375, numerator := 231797321918168387895164928 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 258606620716533059093004288 }, some { target := 393, numerator := 30565642253814120893946789888 }, some { target := 395, numerator := 290061852136211810366540218368 }, some { target := 403, numerator := 30565663217385839160245354496 }, some { target := 410, numerator := 258606620716533059093004288 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 498, numerator := 12785973273066227802046464 }, some { target := 499, numerator := 1511219951942962915011723264 }, some { target := 501, numerator := 14341176102428335121790664704 }, some { target := 509, numerator := 1511220988419395556567154688 }, some { target := 516, numerator := 12785973273066227802046464 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 573, numerator := 258194169965788987228422144 }, some { target := 574, numerator := 30516893223106283380559314944 }, some { target := 576, numerator := 289599233552262509233579229184 }, some { target := 584, numerator := 30516914153243278013259317248 }, some { target := 591, numerator := 258194169965788987228422144 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 608, numerator := 262731128223973777738825728 }, some { target := 609, numerator := 31053132560892496027821539328 }, some { target := 611, numerator := 294688037975704821696150110208 }, some { target := 619, numerator := 31053153858811450630105726976 }, some { target := 626, numerator := 262731128223973777738825728 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 669, numerator := 12785973273066227802046464 }, some { target := 670, numerator := 1511219951942962915011723264 }, some { target := 672, numerator := 14341176102428335121790664704 }, some { target := 680, numerator := 1511220988419395556567154688 }, some { target := 687, numerator := 12785973273066227802046464 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 704, numerator := 313462570565494617082429440 }, some { target := 705, numerator := 37049263337956510174480957440 }, some { target := 707, numerator := 351590123801468861050351779840 }, some { target := 715, numerator := 37049288748346471709388308480 }, some { target := 722, numerator := 313462570565494617082429440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 739, numerator := 12785973273066227802046464 }, some { target := 740, numerator := 1511219951942962915011723264 }, some { target := 742, numerator := 14341176102428335121790664704 }, some { target := 750, numerator := 1511220988419395556567154688 }, some { target := 757, numerator := 12785973273066227802046464 }]

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

end Slot1

namespace Slot2

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨2, 14, #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3506605916160, 0, 137230882439168, 0, 0, 137230882439168, 0, 0, 0, 0, 0, 0, 3506605916160, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

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
  [some { target := 411, numerator := 3468070803972007028242513920 }, some { target := 413, numerator := 135722812363177937630727766016 }, some { target := 416, numerator := 135722812363177937630727766016 }, some { target := 423, numerator := 3468070803972007028242513920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 627, numerator := 3457949974777536190611456000 }, some { target := 629, numerator := 135326734116981893065657548800 }, some { target := 632, numerator := 135326734116981893065657548800 }, some { target := 639, numerator := 3457949974777536190611456000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 723, numerator := 3434334706657104236138987520 }, some { target := 725, numerator := 134402551542524455747160375296 }, some { target := 728, numerator := 134402551542524455747160375296 }, some { target := 735, numerator := 3434334706657104236138987520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 758, numerator := 3457949974777536190611456000 }, some { target := 760, numerator := 135326734116981893065657548800 }, some { target := 763, numerator := 135326734116981893065657548800 }, some { target := 770, numerator := 3457949974777536190611456000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq]
  rfl

end Slot2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent2
