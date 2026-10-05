import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk8Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 36; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left1.expected,
    Slot0.Left2.expected,
    Slot0.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 55, numerator := 234380493277786231246159872 }, { target := 56, numerator := 175785369958339673434619904 }, { target := 57, numerator := 185551223844914099736543232 }, { target := 58, numerator := 239263420221073444397121536 }, { target := 59, numerator := 3203200074796411827030851584 }, { target := 60, numerator := 5600717203950433484153028608 }, { target := 61, numerator := 170902443015052460283658240 }, { target := 62, numerator := 3203200074796411827030851584 }, { target := 63, numerator := 180668296901626886585581568 }, { target := 64, numerator := 185551223844914099736543232 }, { target := 65, numerator := 185551223844914099736543232 }, { target := 66, numerator := 180668296901626886585581568 }, { target := 67, numerator := 5600717203950433484153028608 }, { target := 68, numerator := 180668296901626886585581568 }, { target := 69, numerator := 234380493277786231246159872 }, { target := 70, numerator := 239263420221073444397121536 }, { target := 100, numerator := 174538665206862087098204160 }, { target := 101, numerator := 130903998905146565323653120 }, { target := 102, numerator := 138176443288765818952744960 }, { target := 103, numerator := 178174887398671713912750080 }, { target := 104, numerator := 2385361757827115190342123520 }, { target := 105, numerator := 4170746854005641956284170240 }, { target := 106, numerator := 127267776713336938509107200 }, { target := 107, numerator := 2385361757827115190342123520 }, { target := 108, numerator := 134540221096956192138199040 }, { target := 109, numerator := 138176443288765818952744960 }, { target := 110, numerator := 138176443288765818952744960 }, { target := 111, numerator := 134540221096956192138199040 }, { target := 112, numerator := 4170746854005641956284170240 }, { target := 113, numerator := 134540221096956192138199040 }, { target := 114, numerator := 174538665206862087098204160 }, { target := 115, numerator := 178174887398671713912750080 }, { target := 126, numerator := 184512303218682777789530112 }, { target := 127, numerator := 138384227414012083342147584 }, { target := 128, numerator := 146072240048123865750044672 }, { target := 129, numerator := 188356309535738668993478656 }, { target := 130, numerator := 2521668143988664629790244864 }, { target := 131, numerator := 4409075245663107210928979968 }, { target := 132, numerator := 134540221096956192138199040 }, { target := 133, numerator := 2521668143988664629790244864 }, { target := 134, numerator := 142228233731067974546096128 }, { target := 135, numerator := 146072240048123865750044672 }, { target := 136, numerator := 146072240048123865750044672 }, { target := 137, numerator := 142228233731067974546096128 }, { target := 138, numerator := 4409075245663107210928979968 }, { target := 139, numerator := 142228233731067974546096128 }, { target := 140, numerator := 184512303218682777789530112 }, { target := 141, numerator := 188356309535738668993478656 }, { target := 195, numerator := 239367312283696576591822848 }, { target := 196, numerator := 179525484212772432443867136 }, { target := 197, numerator := 189499122224593123135193088 }, { target := 198, numerator := 244354131289606921937485824 }, { target := 199, numerator := 3271353267877186546754912256 }, { target := 200, numerator := 5719881399779166111475433472 }, { target := 201, numerator := 174538665206862087098204160 }, { target := 202, numerator := 3271353267877186546754912256 }, { target := 203, numerator := 184512303218682777789530112 }, { target := 204, numerator := 189499122224593123135193088 }, { target := 205, numerator := 189499122224593123135193088 }, { target := 206, numerator := 184512303218682777789530112 }, { target := 207, numerator := 5719881399779166111475433472 }, { target := 208, numerator := 184512303218682777789530112 }, { target := 209, numerator := 239367312283696576591822848 }, { target := 210, numerator := 244354131289606921937485824 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk0

namespace RouteChunk1

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left4.expected,
    Slot0.Left5.expected,
    Slot0.Left6.expected,
    Slot0.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 240, numerator := 3206524620800352057261293568 }, { target := 241, numerator := 2404893465600264042945970176 }, { target := 242, numerator := 2538498658133612045331857408 }, { target := 243, numerator := 3273327217067026058454237184 }, { target := 244, numerator := 43822503150938144782571012096 }, { target := 245, numerator := 76622577917875079368306327552 }, { target := 246, numerator := 2338090869333590041753026560 }, { target := 247, numerator := 43822503150938144782571012096 }, { target := 248, numerator := 2471696061866938044138913792 }, { target := 249, numerator := 2538498658133612045331857408 }, { target := 250, numerator := 2538498658133612045331857408 }, { target := 251, numerator := 2471696061866938044138913792 }, { target := 252, numerator := 76622577917875079368306327552 }, { target := 253, numerator := 2471696061866938044138913792 }, { target := 254, numerator := 3206524620800352057261293568 }, { target := 255, numerator := 3273327217067026058454237184 }, { target := 266, numerator := 5799670503873731637006041088 }, { target := 267, numerator := 4349752877905298727754530816 }, { target := 268, numerator := 4591405815566704212629782528 }, { target := 269, numerator := 5920496972704434379443666944 }, { target := 270, numerator := 79262163552940999039082561536 }, { target := 271, numerator := 138587959748816045575956856832 }, { target := 272, numerator := 4228926409074595985316904960 }, { target := 273, numerator := 79262163552940999039082561536 }, { target := 274, numerator := 4470579346736001470192156672 }, { target := 275, numerator := 4591405815566704212629782528 }, { target := 276, numerator := 4591405815566704212629782528 }, { target := 277, numerator := 4470579346736001470192156672 }, { target := 278, numerator := 138587959748816045575956856832 }, { target := 279, numerator := 4470579346736001470192156672 }, { target := 280, numerator := 5799670503873731637006041088 }, { target := 281, numerator := 5920496972704434379443666944 }, { target := 315, numerator := 174538665206862087098204160 }, { target := 316, numerator := 130903998905146565323653120 }, { target := 317, numerator := 138176443288765818952744960 }, { target := 318, numerator := 178174887398671713912750080 }, { target := 319, numerator := 2385361757827115190342123520 }, { target := 320, numerator := 4170746854005641956284170240 }, { target := 321, numerator := 127267776713336938509107200 }, { target := 322, numerator := 2385361757827115190342123520 }, { target := 323, numerator := 134540221096956192138199040 }, { target := 324, numerator := 138176443288765818952744960 }, { target := 325, numerator := 138176443288765818952744960 }, { target := 326, numerator := 134540221096956192138199040 }, { target := 327, numerator := 4170746854005641956284170240 }, { target := 328, numerator := 134540221096956192138199040 }, { target := 329, numerator := 174538665206862087098204160 }, { target := 330, numerator := 178174887398671713912750080 }, { target := 341, numerator := 3206524620800352057261293568 }, { target := 342, numerator := 2404893465600264042945970176 }, { target := 343, numerator := 2538498658133612045331857408 }, { target := 344, numerator := 3273327217067026058454237184 }, { target := 345, numerator := 43822503150938144782571012096 }, { target := 346, numerator := 76622577917875079368306327552 }, { target := 347, numerator := 2338090869333590041753026560 }, { target := 348, numerator := 43822503150938144782571012096 }, { target := 349, numerator := 2471696061866938044138913792 }, { target := 350, numerator := 2538498658133612045331857408 }, { target := 351, numerator := 2538498658133612045331857408 }, { target := 352, numerator := 2471696061866938044138913792 }, { target := 353, numerator := 76622577917875079368306327552 }, { target := 354, numerator := 2471696061866938044138913792 }, { target := 355, numerator := 3206524620800352057261293568 }, { target := 356, numerator := 3273327217067026058454237184 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk1

namespace RouteChunk2

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 376, numerator := 189499122224593123135193088 }, { target := 377, numerator := 142124341668444842351394816 }, { target := 378, numerator := 150020138427802889148694528 }, { target := 379, numerator := 193447020604272146533842944 }, { target := 380, numerator := 2589821337069439349514305536 }, { target := 381, numerator := 4528239441491839838251384832 }, { target := 382, numerator := 138176443288765818952744960 }, { target := 383, numerator := 2589821337069439349514305536 }, { target := 384, numerator := 146072240048123865750044672 }, { target := 385, numerator := 150020138427802889148694528 }, { target := 386, numerator := 150020138427802889148694528 }, { target := 387, numerator := 146072240048123865750044672 }, { target := 388, numerator := 4528239441491839838251384832 }, { target := 389, numerator := 146072240048123865750044672 }, { target := 390, numerator := 189499122224593123135193088 }, { target := 391, numerator := 193447020604272146533842944 }, { target := 456, numerator := 189499122224593123135193088 }, { target := 457, numerator := 142124341668444842351394816 }, { target := 458, numerator := 150020138427802889148694528 }, { target := 459, numerator := 193447020604272146533842944 }, { target := 460, numerator := 2589821337069439349514305536 }, { target := 461, numerator := 4528239441491839838251384832 }, { target := 462, numerator := 138176443288765818952744960 }, { target := 463, numerator := 2589821337069439349514305536 }, { target := 464, numerator := 146072240048123865750044672 }, { target := 465, numerator := 150020138427802889148694528 }, { target := 466, numerator := 150020138427802889148694528 }, { target := 467, numerator := 146072240048123865750044672 }, { target := 468, numerator := 4528239441491839838251384832 }, { target := 469, numerator := 146072240048123865750044672 }, { target := 470, numerator := 189499122224593123135193088 }, { target := 471, numerator := 193447020604272146533842944 }, { target := 482, numerator := 184512303218682777789530112 }, { target := 483, numerator := 138384227414012083342147584 }, { target := 484, numerator := 146072240048123865750044672 }, { target := 485, numerator := 188356309535738668993478656 }, { target := 486, numerator := 2521668143988664629790244864 }, { target := 487, numerator := 4409075245663107210928979968 }, { target := 488, numerator := 134540221096956192138199040 }, { target := 489, numerator := 2521668143988664629790244864 }, { target := 490, numerator := 142228233731067974546096128 }, { target := 491, numerator := 146072240048123865750044672 }, { target := 492, numerator := 146072240048123865750044672 }, { target := 493, numerator := 142228233731067974546096128 }, { target := 494, numerator := 4409075245663107210928979968 }, { target := 495, numerator := 142228233731067974546096128 }, { target := 496, numerator := 184512303218682777789530112 }, { target := 497, numerator := 188356309535738668993478656 }, { target := 531, numerator := 184512303218682777789530112 }, { target := 532, numerator := 138384227414012083342147584 }, { target := 533, numerator := 146072240048123865750044672 }, { target := 534, numerator := 188356309535738668993478656 }, { target := 535, numerator := 2521668143988664629790244864 }, { target := 536, numerator := 4409075245663107210928979968 }, { target := 537, numerator := 134540221096956192138199040 }, { target := 538, numerator := 2521668143988664629790244864 }, { target := 539, numerator := 142228233731067974546096128 }, { target := 540, numerator := 146072240048123865750044672 }, { target := 541, numerator := 146072240048123865750044672 }, { target := 542, numerator := 142228233731067974546096128 }, { target := 543, numerator := 4409075245663107210928979968 }, { target := 544, numerator := 142228233731067974546096128 }, { target := 545, numerator := 184512303218682777789530112 }, { target := 546, numerator := 188356309535738668993478656 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk2

namespace RouteChunk3

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected,
    Slot0.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 557, numerator := 5799670503873731637006041088 }, { target := 558, numerator := 4349752877905298727754530816 }, { target := 559, numerator := 4591405815566704212629782528 }, { target := 560, numerator := 5920496972704434379443666944 }, { target := 561, numerator := 79262163552940999039082561536 }, { target := 562, numerator := 138587959748816045575956856832 }, { target := 563, numerator := 4228926409074595985316904960 }, { target := 564, numerator := 79262163552940999039082561536 }, { target := 565, numerator := 4470579346736001470192156672 }, { target := 566, numerator := 4591405815566704212629782528 }, { target := 567, numerator := 4591405815566704212629782528 }, { target := 568, numerator := 4470579346736001470192156672 }, { target := 569, numerator := 138587959748816045575956856832 }, { target := 570, numerator := 4470579346736001470192156672 }, { target := 571, numerator := 5799670503873731637006041088 }, { target := 572, numerator := 5920496972704434379443666944 }, { target := 592, numerator := 184512303218682777789530112 }, { target := 593, numerator := 138384227414012083342147584 }, { target := 594, numerator := 146072240048123865750044672 }, { target := 595, numerator := 188356309535738668993478656 }, { target := 596, numerator := 2521668143988664629790244864 }, { target := 597, numerator := 4409075245663107210928979968 }, { target := 598, numerator := 134540221096956192138199040 }, { target := 599, numerator := 2521668143988664629790244864 }, { target := 600, numerator := 142228233731067974546096128 }, { target := 601, numerator := 146072240048123865750044672 }, { target := 602, numerator := 146072240048123865750044672 }, { target := 603, numerator := 142228233731067974546096128 }, { target := 604, numerator := 4409075245663107210928979968 }, { target := 605, numerator := 142228233731067974546096128 }, { target := 606, numerator := 184512303218682777789530112 }, { target := 607, numerator := 188356309535738668993478656 }, { target := 653, numerator := 234380493277786231246159872 }, { target := 654, numerator := 175785369958339673434619904 }, { target := 655, numerator := 185551223844914099736543232 }, { target := 656, numerator := 239263420221073444397121536 }, { target := 657, numerator := 3203200074796411827030851584 }, { target := 658, numerator := 5600717203950433484153028608 }, { target := 659, numerator := 170902443015052460283658240 }, { target := 660, numerator := 3203200074796411827030851584 }, { target := 661, numerator := 180668296901626886585581568 }, { target := 662, numerator := 185551223844914099736543232 }, { target := 663, numerator := 185551223844914099736543232 }, { target := 664, numerator := 180668296901626886585581568 }, { target := 665, numerator := 5600717203950433484153028608 }, { target := 666, numerator := 180668296901626886585581568 }, { target := 667, numerator := 234380493277786231246159872 }, { target := 668, numerator := 239263420221073444397121536 }, { target := 688, numerator := 239367312283696576591822848 }, { target := 689, numerator := 179525484212772432443867136 }, { target := 690, numerator := 189499122224593123135193088 }, { target := 691, numerator := 244354131289606921937485824 }, { target := 692, numerator := 3271353267877186546754912256 }, { target := 693, numerator := 5719881399779166111475433472 }, { target := 694, numerator := 174538665206862087098204160 }, { target := 695, numerator := 3271353267877186546754912256 }, { target := 696, numerator := 184512303218682777789530112 }, { target := 697, numerator := 189499122224593123135193088 }, { target := 698, numerator := 189499122224593123135193088 }, { target := 699, numerator := 184512303218682777789530112 }, { target := 700, numerator := 5719881399779166111475433472 }, { target := 701, numerator := 184512303218682777789530112 }, { target := 702, numerator := 239367312283696576591822848 }, { target := 703, numerator := 244354131289606921937485824 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk3

namespace RouteChunk4

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot1.Left4.expected,
    Slot1.Left5.expected,
    Slot1.Left6.expected,
    Slot1.Left7.expected,
    Slot1.Left8.expected,
    Slot1.Left9.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 142, numerator := 12785973273066227802046464 }, { target := 143, numerator := 1511219951942962915011723264 }, { target := 145, numerator := 14341176102428335121790664704 }, { target := 153, numerator := 1511220988419395556567154688 }, { target := 160, numerator := 12785973273066227802046464 }, { target := 282, numerator := 313462570565494617082429440 }, { target := 283, numerator := 37049263337956510174480957440 }, { target := 285, numerator := 351590123801468861050351779840 }, { target := 293, numerator := 37049288748346471709388308480 }, { target := 300, numerator := 313462570565494617082429440 }, { target := 357, numerator := 231797321918168387895164928 }, { target := 358, numerator := 27396955257804682523760918528 }, { target := 360, numerator := 259991644179507236724075921408 }, { target := 368, numerator := 27396974048119364606152933376 }, { target := 375, numerator := 231797321918168387895164928 }, { target := 392, numerator := 258606620716533059093004288 }, { target := 393, numerator := 30565642253814120893946789888 }, { target := 395, numerator := 290061852136211810366540218368 }, { target := 403, numerator := 30565663217385839160245354496 }, { target := 410, numerator := 258606620716533059093004288 }, { target := 411, numerator := 3468070803972007028242513920 }, { target := 413, numerator := 135722812363177937630727766016 }, { target := 416, numerator := 135722812363177937630727766016 }, { target := 423, numerator := 3468070803972007028242513920 }, { target := 498, numerator := 12785973273066227802046464 }, { target := 499, numerator := 1511219951942962915011723264 }, { target := 501, numerator := 14341176102428335121790664704 }, { target := 509, numerator := 1511220988419395556567154688 }, { target := 516, numerator := 12785973273066227802046464 }, { target := 573, numerator := 258194169965788987228422144 }, { target := 574, numerator := 30516893223106283380559314944 }, { target := 576, numerator := 289599233552262509233579229184 }, { target := 584, numerator := 30516914153243278013259317248 }, { target := 591, numerator := 258194169965788987228422144 }, { target := 608, numerator := 262731128223973777738825728 }, { target := 609, numerator := 31053132560892496027821539328 }, { target := 611, numerator := 294688037975704821696150110208 }, { target := 619, numerator := 31053153858811450630105726976 }, { target := 626, numerator := 262731128223973777738825728 }, { target := 627, numerator := 3457949974777536190611456000 }, { target := 629, numerator := 135326734116981893065657548800 }, { target := 632, numerator := 135326734116981893065657548800 }, { target := 639, numerator := 3457949974777536190611456000 }, { target := 669, numerator := 12785973273066227802046464 }, { target := 670, numerator := 1511219951942962915011723264 }, { target := 672, numerator := 14341176102428335121790664704 }, { target := 680, numerator := 1511220988419395556567154688 }, { target := 687, numerator := 12785973273066227802046464 }, { target := 704, numerator := 313462570565494617082429440 }, { target := 705, numerator := 37049263337956510174480957440 }, { target := 707, numerator := 351590123801468861050351779840 }, { target := 715, numerator := 37049288748346471709388308480 }, { target := 722, numerator := 313462570565494617082429440 }, { target := 723, numerator := 3434334706657104236138987520 }, { target := 725, numerator := 134402551542524455747160375296 }, { target := 728, numerator := 134402551542524455747160375296 }, { target := 735, numerator := 3434334706657104236138987520 }, { target := 739, numerator := 12785973273066227802046464 }, { target := 740, numerator := 1511219951942962915011723264 }, { target := 742, numerator := 14341176102428335121790664704 }, { target := 750, numerator := 1511220988419395556567154688 }, { target := 757, numerator := 12785973273066227802046464 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk4

namespace RouteChunk5

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot2.Left3.expected,
    Slot3.Left0.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left3.expected,
    Slot4.Left11.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 11, numerator := 8324120933377545731047424 }, { target := 12, numerator := 201658542611823769161826304 }, { target := 13, numerator := 152787897131994307127934976 }, { target := 14, numerator := 170241699089076257854324736 }, { target := 15, numerator := 8324120933377545731047424 }, { target := 16, numerator := 170241699089076257854324736 }, { target := 17, numerator := 169973179058967304766226432 }, { target := 18, numerator := 8324120933377545731047424 }, { target := 19, numerator := 201658542611823769161826304 }, { target := 20, numerator := 8324120933377545731047424 }, { target := 31, numerator := 1364163103094846746662010880 }, { target := 32, numerator := 33047951304007416346553876480 }, { target := 33, numerator := 25038993730998961253247877120 }, { target := 34, numerator := 27899335721359123786571448320 }, { target := 35, numerator := 1364163103094846746662010880 }, { target := 36, numerator := 27899335721359123786571448320 }, { target := 37, numerator := 27855330459968967439904931840 }, { target := 38, numerator := 1364163103094846746662010880 }, { target := 39, numerator := 33047951304007416346553876480 }, { target := 40, numerator := 1364163103094846746662010880 }, { target := 55, numerator := 60276039973280665254756352 }, { target := 56, numerator := 10571851115401994789491572736 }, { target := 61, numerator := 10571852382850319395346972672 }, { target := 69, numerator := 60274772524956059399356416 }, { target := 76, numerator := 14044587334751521393533255680 }, { target := 77, numerator := 340241454464464276340112097280 }, { target := 78, numerator := 257786135273342441061949112320 }, { target := 79, numerator := 287234463555885953661293035520 }, { target := 80, numerator := 14044587334751521393533255680 }, { target := 81, numerator := 287234463555885953661293035520 }, { target := 82, numerator := 286781412351539130390533898240 }, { target := 83, numerator := 14044587334751521393533255680 }, { target := 84, numerator := 340241454464464276340112097280 }, { target := 85, numerator := 14044587334751521393533255680 }, { target := 305, numerator := 1364163103094846746662010880 }, { target := 306, numerator := 33047951304007416346553876480 }, { target := 307, numerator := 25038993730998961253247877120 }, { target := 308, numerator := 27899335721359123786571448320 }, { target := 309, numerator := 1364163103094846746662010880 }, { target := 310, numerator := 27899335721359123786571448320 }, { target := 311, numerator := 27855330459968967439904931840 }, { target := 312, numerator := 1364163103094846746662010880 }, { target := 313, numerator := 33047951304007416346553876480 }, { target := 314, numerator := 1364163103094846746662010880 }, { target := 643, numerator := 8324120933377545731047424 }, { target := 644, numerator := 201658542611823769161826304 }, { target := 645, numerator := 152787897131994307127934976 }, { target := 646, numerator := 170241699089076257854324736 }, { target := 647, numerator := 8324120933377545731047424 }, { target := 648, numerator := 170241699089076257854324736 }, { target := 649, numerator := 169973179058967304766226432 }, { target := 650, numerator := 8324120933377545731047424 }, { target := 651, numerator := 201658542611823769161826304 }, { target := 652, numerator := 8324120933377545731047424 }, { target := 758, numerator := 3457949974777536190611456000 }, { target := 760, numerator := 135326734116981893065657548800 }, { target := 763, numerator := 135326734116981893065657548800 }, { target := 770, numerator := 3457949974777536190611456000 }, { target := 774, numerator := 124778796790142697563486158848 }, { target := 777, numerator := 463522134850471364181601812480 }, { target := 779, numerator := 124752530987764976596807581696 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk5

namespace RouteChunk6

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left1.expected,
    Slot5.Left6.expected,
    Slot5.Left14.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left7.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left2.expected,
    Slot7.Left3.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 3454477195349905648851615744 }, { target := 3, numerator := 3454477195349905648851615744 }, { target := 4, numerator := 3454477195349905648851615744 }, { target := 5, numerator := 3454477195349905648851615744 }, { target := 11, numerator := 22669671434707975064780800 }, { target := 13, numerator := 1024627907259061817363660800 }, { target := 18, numerator := 22790666324491812995072000 }, { target := 22, numerator := 135194757619764615008575553536 }, { target := 23, numerator := 135194757619764615008575553536 }, { target := 24, numerator := 135194757619764615008575553536 }, { target := 25, numerator := 135194757619764615008575553536 }, { target := 72, numerator := 135194807204612685139850297344 }, { target := 73, numerator := 135194807204612685139850297344 }, { target := 74, numerator := 135194807204612685139850297344 }, { target := 75, numerator := 135194807204612685139850297344 }, { target := 100, numerator := 11954838641208716217129369600 }, { target := 101, numerator := 2096766381459987038955424972800 }, { target := 106, numerator := 2096766632839145547875588505600 }, { target := 114, numerator := 11954587262050207296965836800 }, { target := 142, numerator := 22669671434707975064780800 }, { target := 143, numerator := 7302385375693772336765337600 }, { target := 145, numerator := 77663939330607082034723553280 }, { target := 153, numerator := 7302407385083514771692584960 }, { target := 160, numerator := 22669671434707975064780800 }, { target := 301, numerator := 3454526780197975780126359552 }, { target := 302, numerator := 3454526780197975780126359552 }, { target := 303, numerator := 3454526780197975780126359552 }, { target := 304, numerator := 3454526780197975780126359552 }, { target := 315, numerator := 11954838641208716217129369600 }, { target := 316, numerator := 2096766381459987038955424972800 }, { target := 321, numerator := 2096766632839145547875588505600 }, { target := 329, numerator := 11954587262050207296965836800 }, { target := 357, numerator := 1024627907259061817363660800 }, { target := 358, numerator := 330054534184415364149516697600 }, { target := 360, numerator := 3510268768341315961419496161280 }, { target := 368, numerator := 330055528968791343821184040960 }, { target := 375, numerator := 1024627907259061817363660800 }, { target := 411, numerator := 3701225566446327480912445440 }, { target := 413, numerator := 144851526021176373223473807360 }, { target := 416, numerator := 144851579147799305506982461440 }, { target := 423, numerator := 3701278693069259764421099520 }, { target := 627, numerator := 3701225566446327480912445440 }, { target := 629, numerator := 144851526021176373223473807360 }, { target := 632, numerator := 144851579147799305506982461440 }, { target := 639, numerator := 3701278693069259764421099520 }, { target := 653, numerator := 60276039973280665254756352 }, { target := 654, numerator := 10571851115401994789491572736 }, { target := 659, numerator := 10571852382850319395346972672 }, { target := 667, numerator := 60274772524956059399356416 }, { target := 669, numerator := 22790666324491812995072000 }, { target := 670, numerator := 7341360414050015703465984000 }, { target := 672, numerator := 78078455253634465278407475200 }, { target := 680, numerator := 7341382540910524918818406400 }, { target := 687, numerator := 22790666324491812995072000 }, { target := 723, numerator := 3701225566446327480912445440 }, { target := 725, numerator := 144851526021176373223473807360 }, { target := 728, numerator := 144851579147799305506982461440 }, { target := 735, numerator := 3701278693069259764421099520 }, { target := 758, numerator := 3701225566446327480912445440 }, { target := 760, numerator := 144851526021176373223473807360 }, { target := 763, numerator := 144851579147799305506982461440 }, { target := 770, numerator := 3701278693069259764421099520 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk6

namespace RouteChunk7

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left6.expected,
    Slot10.Left14.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left2.expected,
    Slot11.Left3.expected,
    Slot11.Left4.expected,
    Slot11.Left5.expected,
    Slot11.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 31, numerator := 7302385375693772336765337600 }, { target := 33, numerator := 330054534184415364149516697600 }, { target := 38, numerator := 7341360414050015703465984000 }, { target := 55, numerator := 63092677355209668304044032 }, { target := 56, numerator := 12513475960891366507649433600 }, { target := 61, numerator := 12513475960891366507649433600 }, { target := 69, numerator := 63092677355209668304044032 }, { target := 76, numerator := 77663939330607082034723553280 }, { target := 78, numerator := 3510268768341315961419496161280 }, { target := 83, numerator := 78078455253634465278407475200 }, { target := 100, numerator := 11065862849766573985262206976 }, { target := 101, numerator := 2194746118911388302458014924800 }, { target := 106, numerator := 2194746118911388302458014924800 }, { target := 114, numerator := 11065862849766573985262206976 }, { target := 142, numerator := 8621410966712458078584832 }, { target := 143, numerator := 1412883213919662701899939840 }, { target := 145, numerator := 14546179739564075729016586240 }, { target := 153, numerator := 1412883213919662701899939840 }, { target := 160, numerator := 8621410966712458078584832 }, { target := 282, numerator := 208860633419388903774748672 }, { target := 283, numerator := 34228235279150538358930800640 }, { target := 285, numerator := 352392934981052286209401815040 }, { target := 293, numerator := 34228235279150538358930800640 }, { target := 300, numerator := 208860633419388903774748672 }, { target := 305, numerator := 7302407385083514771692584960 }, { target := 307, numerator := 330055528968791343821184040960 }, { target := 312, numerator := 7341382540910524918818406400 }, { target := 315, numerator := 11065864176441455815690289152 }, { target := 316, numerator := 2194746382037236461327718809600 }, { target := 321, numerator := 2194746382037236461327718809600 }, { target := 329, numerator := 11065864176441455815690289152 }, { target := 357, numerator := 158244607743851246668218368 }, { target := 358, numerator := 25933243507106067012292444160 }, { target := 360, numerator := 266992782961676099671304437760 }, { target := 368, numerator := 25933243507106067012292444160 }, { target := 375, numerator := 158244607743851246668218368 }, { target := 392, numerator := 176321759770828981349122048 }, { target := 393, numerator := 28895740568550521064663285760 }, { target := 395, numerator := 297492837254310452006339215360 }, { target := 403, numerator := 28895740568550521064663285760 }, { target := 410, numerator := 176321759770828981349122048 }, { target := 498, numerator := 8621410966712458078584832 }, { target := 499, numerator := 1412883213919662701899939840 }, { target := 501, numerator := 14546179739564075729016586240 }, { target := 509, numerator := 1412883213919662701899939840 }, { target := 516, numerator := 8621410966712458078584832 }, { target := 573, numerator := 176321759770828981349122048 }, { target := 574, numerator := 28895740568550521064663285760 }, { target := 576, numerator := 297492837254310452006339215360 }, { target := 584, numerator := 28895740568550521064663285760 }, { target := 591, numerator := 176321759770828981349122048 }, { target := 608, numerator := 176043649739644708507877376 }, { target := 609, numerator := 28850163690682144848472965120 }, { target := 611, numerator := 297023605649808385047338680320 }, { target := 619, numerator := 28850163690682144848472965120 }, { target := 626, numerator := 176043649739644708507877376 }, { target := 643, numerator := 22669671434707975064780800 }, { target := 645, numerator := 1024627907259061817363660800 }, { target := 650, numerator := 22790666324491812995072000 }, { target := 653, numerator := 63091350680327837875961856 }, { target := 654, numerator := 12513212835043207637945548800 }, { target := 659, numerator := 12513212835043207637945548800 }, { target := 667, numerator := 63091350680327837875961856 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk7

namespace RouteChunk8

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot11.Left7.expected,
    Slot11.Left8.expected,
    Slot11.Left9.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 124778796790142697563486158848 }, { target := 2, numerator := 3468070803972007028242513920 }, { target := 3, numerator := 3457949974777536190611456000 }, { target := 4, numerator := 3434334706657104236138987520 }, { target := 5, numerator := 3457949974777536190611456000 }, { target := 11, numerator := 12345077642960495808872448 }, { target := 12, numerator := 302653516408063768217518080 }, { target := 13, numerator := 223804310817541891760848896 }, { target := 14, numerator := 249689151036652608779452416 }, { target := 15, numerator := 12345077642960495808872448 }, { target := 16, numerator := 249290922725589366979166208 }, { target := 17, numerator := 253671434147285026782314496 }, { target := 18, numerator := 12345077642960495808872448 }, { target := 19, numerator := 302653516408063768217518080 }, { target := 20, numerator := 12345077642960495808872448 }, { target := 21, numerator := 463522134850471364181601812480 }, { target := 22, numerator := 135722812363177937630727766016 }, { target := 23, numerator := 135326734116981893065657548800 }, { target := 24, numerator := 134402551542524455747160375296 }, { target := 25, numerator := 135326734116981893065657548800 }, { target := 31, numerator := 1459108919117343504149250048 }, { target := 32, numerator := 35771702533199389133981614080 }, { target := 33, numerator := 26452232662707969333286404096 }, { target := 34, numerator := 29511654589889496035534831616 }, { target := 35, numerator := 1459108919117343504149250048 }, { target := 36, numerator := 29464586560240549470884855808 }, { target := 37, numerator := 29982334886378961682034589696 }, { target := 38, numerator := 1459108919117343504149250048 }, { target := 39, numerator := 35771702533199389133981614080 }, { target := 40, numerator := 1459108919117343504149250048 }, { target := 71, numerator := 124752530987764976596807581696 }, { target := 72, numerator := 135722812363177937630727766016 }, { target := 73, numerator := 135326734116981893065657548800 }, { target := 74, numerator := 134402551542524455747160375296 }, { target := 75, numerator := 135326734116981893065657548800 }, { target := 76, numerator := 13846652788551495979659952128 }, { target := 77, numerator := 339466326429004417565856890880 }, { target := 78, numerator := 251026415069869056147383648256 }, { target := 79, numerator := 280059719303928644491831934976 }, { target := 80, numerator := 13846652788551495979659952128 }, { target := 81, numerator := 279613053084943112363455807488 }, { target := 82, numerator := 284526381493783965775593209856 }, { target := 83, numerator := 13846652788551495979659952128 }, { target := 84, numerator := 339466326429004417565856890880 }, { target := 85, numerator := 13846652788551495979659952128 }, { target := 301, numerator := 3468070803972007028242513920 }, { target := 302, numerator := 3457949974777536190611456000 }, { target := 303, numerator := 3434334706657104236138987520 }, { target := 304, numerator := 3457949974777536190611456000 }, { target := 669, numerator := 8621410966712458078584832 }, { target := 670, numerator := 1412883213919662701899939840 }, { target := 672, numerator := 14546179739564075729016586240 }, { target := 680, numerator := 1412883213919662701899939840 }, { target := 687, numerator := 8621410966712458078584832 }, { target := 704, numerator := 208860633419388903774748672 }, { target := 705, numerator := 34228235279150538358930800640 }, { target := 707, numerator := 352392934981052286209401815040 }, { target := 715, numerator := 34228235279150538358930800640 }, { target := 722, numerator := 208860633419388903774748672 }, { target := 739, numerator := 8621410966712458078584832 }, { target := 740, numerator := 1412883213919662701899939840 }, { target := 742, numerator := 14546179739564075729016586240 }, { target := 750, numerator := 1412883213919662701899939840 }, { target := 757, numerator := 8621410966712458078584832 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk8

namespace RouteChunk9

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot14.Left11.expected,
    Slot14.Left18.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 55, numerator := 245034152063140150848258048 }, { target := 56, numerator := 182472240898083091057213440 }, { target := 57, numerator := 192899226092259267689054208 }, { target := 58, numerator := 250247644660228239164178432 }, { target := 59, numerator := 3352275739927640787136806912 }, { target := 60, numerator := 6063291890413446711415406592 }, { target := 61, numerator := 182472240898083091057213440 }, { target := 62, numerator := 3352275739927640787136806912 }, { target := 63, numerator := 198112718689347356004974592 }, { target := 64, numerator := 198112718689347356004974592 }, { target := 65, numerator := 192899226092259267689054208 }, { target := 66, numerator := 192899226092259267689054208 }, { target := 67, numerator := 6063291890413446711415406592 }, { target := 68, numerator := 192899226092259267689054208 }, { target := 69, numerator := 245034152063140150848258048 }, { target := 70, numerator := 250247644660228239164178432 }, { target := 100, numerator := 183775614047355113136193536 }, { target := 101, numerator := 136854180673562318292910080 }, { target := 102, numerator := 144674419569194450766790656 }, { target := 103, numerator := 187685733495171179373133824 }, { target := 104, numerator := 2514206804945730590352605184 }, { target := 105, numerator := 4547468917810085033561554944 }, { target := 106, numerator := 136854180673562318292910080 }, { target := 107, numerator := 2514206804945730590352605184 }, { target := 108, numerator := 148584539017010517003730944 }, { target := 109, numerator := 148584539017010517003730944 }, { target := 110, numerator := 144674419569194450766790656 }, { target := 111, numerator := 144674419569194450766790656 }, { target := 112, numerator := 4547468917810085033561554944 }, { target := 113, numerator := 144674419569194450766790656 }, { target := 114, numerator := 183775614047355113136193536 }, { target := 115, numerator := 187685733495171179373133824 }, { target := 305, numerator := 1459109919853209502892425216 }, { target := 306, numerator := 35771727067369007167685263360 }, { target := 307, numerator := 26452250805080765826630418432 }, { target := 308, numerator := 29511674830579430913340342272 }, { target := 309, numerator := 1459109919853209502892425216 }, { target := 310, numerator := 29464606768648682219698651136 }, { target := 311, numerator := 29982355449886917849757253632 }, { target := 312, numerator := 1459109919853209502892425216 }, { target := 313, numerator := 35771727067369007167685263360 }, { target := 314, numerator := 1459109919853209502892425216 }, { target := 643, numerator := 12345077642960495808872448 }, { target := 644, numerator := 302653516408063768217518080 }, { target := 645, numerator := 223804310817541891760848896 }, { target := 646, numerator := 249689151036652608779452416 }, { target := 647, numerator := 12345077642960495808872448 }, { target := 648, numerator := 249290922725589366979166208 }, { target := 649, numerator := 253671434147285026782314496 }, { target := 650, numerator := 12345077642960495808872448 }, { target := 651, numerator := 302653516408063768217518080 }, { target := 652, numerator := 12345077642960495808872448 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk9

namespace RouteChunk10

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot15.Left2.expected,
    Slot15.Left3.expected,
    Slot15.Left4.expected,
    Slot15.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 126, numerator := 193985370383319286088204288 }, { target := 127, numerator := 144457190710982447086960640 }, { target := 128, numerator := 152711887323038586920501248 }, { target := 129, numerator := 198112718689347356004974592 }, { target := 130, numerator := 2653884960776048956483305472 }, { target := 131, numerator := 4800106079910645313203863552 }, { target := 132, numerator := 144457190710982447086960640 }, { target := 133, numerator := 2653884960776048956483305472 }, { target := 134, numerator := 156839235629066656837271552 }, { target := 135, numerator := 156839235629066656837271552 }, { target := 136, numerator := 152711887323038586920501248 }, { target := 137, numerator := 152711887323038586920501248 }, { target := 138, numerator := 4800106079910645313203863552 }, { target := 139, numerator := 152711887323038586920501248 }, { target := 140, numerator := 193985370383319286088204288 }, { target := 141, numerator := 198112718689347356004974592 }, { target := 195, numerator := 250139030231122237324263424 }, { target := 196, numerator := 186273745916793155454238720 }, { target := 197, numerator := 196917959969181335765909504 }, { target := 198, numerator := 255461137257316327480098816 }, { target := 199, numerator := 3422114817842799970202157056 }, { target := 200, numerator := 6189610471463726851236560896 }, { target := 201, numerator := 186273745916793155454238720 }, { target := 202, numerator := 3422114817842799970202157056 }, { target := 203, numerator := 202240066995375425921744896 }, { target := 204, numerator := 202240066995375425921744896 }, { target := 205, numerator := 196917959969181335765909504 }, { target := 206, numerator := 196917959969181335765909504 }, { target := 207, numerator := 6189610471463726851236560896 }, { target := 208, numerator := 196917959969181335765909504 }, { target := 209, numerator := 250139030231122237324263424 }, { target := 210, numerator := 255461137257316327480098816 }, { target := 240, numerator := 3348800078196248728259526656 }, { target := 241, numerator := 2493787292273802244448583680 }, { target := 242, numerator := 2636289423260876658417074176 }, { target := 243, numerator := 3420051143689785935243771904 }, { target := 244, numerator := 45814435112344424090869694464 }, { target := 245, numerator := 82864989168983771722677223424 }, { target := 246, numerator := 2493787292273802244448583680 }, { target := 247, numerator := 45814435112344424090869694464 }, { target := 248, numerator := 2707540488754413865401319424 }, { target := 249, numerator := 2707540488754413865401319424 }, { target := 250, numerator := 2636289423260876658417074176 }, { target := 251, numerator := 2636289423260876658417074176 }, { target := 252, numerator := 82864989168983771722677223424 }, { target := 253, numerator := 2636289423260876658417074176 }, { target := 254, numerator := 3348800078196248728259526656 }, { target := 255, numerator := 3420051143689785935243771904 }, { target := 266, numerator := 5855295258675453187978166272 }, { target := 267, numerator := 4360326256460443863387996160 }, { target := 268, numerator := 4609487756829612084153024512 }, { target := 269, numerator := 5979876008860037298360680448 }, { target := 270, numerator := 80105422368687582975956615168 }, { target := 271, numerator := 144887412464671320374863986688 }, { target := 272, numerator := 4360326256460443863387996160 }, { target := 273, numerator := 80105422368687582975956615168 }, { target := 274, numerator := 4734068507014196194535538688 }, { target := 275, numerator := 4734068507014196194535538688 }, { target := 276, numerator := 4609487756829612084153024512 }, { target := 277, numerator := 4609487756829612084153024512 }, { target := 278, numerator := 144887412464671320374863986688 }, { target := 279, numerator := 4609487756829612084153024512 }, { target := 280, numerator := 5855295258675453187978166272 }, { target := 281, numerator := 5979876008860037298360680448 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk10

namespace RouteChunk11

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot15.Left6.expected,
    Slot15.Left7.expected,
    Slot15.Left8.expected,
    Slot15.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 315, numerator := 178670735879373026660188160 }, { target := 316, numerator := 133052675654852253895884800 }, { target := 317, numerator := 140655685692272382689935360 }, { target := 318, numerator := 182472240898083091057213440 }, { target := 319, numerator := 2444367727030571407287255040 }, { target := 320, numerator := 4421150336759804893740400640 }, { target := 321, numerator := 133052675654852253895884800 }, { target := 322, numerator := 2444367727030571407287255040 }, { target := 323, numerator := 144457190710982447086960640 }, { target := 324, numerator := 144457190710982447086960640 }, { target := 325, numerator := 140655685692272382689935360 }, { target := 326, numerator := 140655685692272382689935360 }, { target := 327, numerator := 4421150336759804893740400640 }, { target := 328, numerator := 140655685692272382689935360 }, { target := 329, numerator := 178670735879373026660188160 }, { target := 330, numerator := 182472240898083091057213440 }, { target := 341, numerator := 3348800078196248728259526656 }, { target := 342, numerator := 2493787292273802244448583680 }, { target := 343, numerator := 2636289423260876658417074176 }, { target := 344, numerator := 3420051143689785935243771904 }, { target := 345, numerator := 45814435112344424090869694464 }, { target := 346, numerator := 82864989168983771722677223424 }, { target := 347, numerator := 2493787292273802244448583680 }, { target := 348, numerator := 45814435112344424090869694464 }, { target := 349, numerator := 2707540488754413865401319424 }, { target := 350, numerator := 2707540488754413865401319424 }, { target := 351, numerator := 2636289423260876658417074176 }, { target := 352, numerator := 2636289423260876658417074176 }, { target := 353, numerator := 82864989168983771722677223424 }, { target := 354, numerator := 2636289423260876658417074176 }, { target := 355, numerator := 3348800078196248728259526656 }, { target := 356, numerator := 3420051143689785935243771904 }, { target := 376, numerator := 188880492215337199612198912 }, { target := 377, numerator := 140655685692272382689935360 }, { target := 378, numerator := 148693153446116518843645952 }, { target := 379, numerator := 192899226092259267689054208 }, { target := 380, numerator := 2584045882860889773417955328 }, { target := 381, numerator := 4673787498860365173382709248 }, { target := 382, numerator := 140655685692272382689935360 }, { target := 383, numerator := 2584045882860889773417955328 }, { target := 384, numerator := 152711887323038586920501248 }, { target := 385, numerator := 152711887323038586920501248 }, { target := 386, numerator := 148693153446116518843645952 }, { target := 387, numerator := 148693153446116518843645952 }, { target := 388, numerator := 4673787498860365173382709248 }, { target := 389, numerator := 148693153446116518843645952 }, { target := 390, numerator := 188880492215337199612198912 }, { target := 391, numerator := 192899226092259267689054208 }, { target := 456, numerator := 193985370383319286088204288 }, { target := 457, numerator := 144457190710982447086960640 }, { target := 458, numerator := 152711887323038586920501248 }, { target := 459, numerator := 198112718689347356004974592 }, { target := 460, numerator := 2653884960776048956483305472 }, { target := 461, numerator := 4800106079910645313203863552 }, { target := 462, numerator := 144457190710982447086960640 }, { target := 463, numerator := 2653884960776048956483305472 }, { target := 464, numerator := 156839235629066656837271552 }, { target := 465, numerator := 156839235629066656837271552 }, { target := 466, numerator := 152711887323038586920501248 }, { target := 467, numerator := 152711887323038586920501248 }, { target := 468, numerator := 4800106079910645313203863552 }, { target := 469, numerator := 152711887323038586920501248 }, { target := 470, numerator := 193985370383319286088204288 }, { target := 471, numerator := 198112718689347356004974592 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk11

namespace RouteChunk12

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot15.Left10.expected,
    Slot15.Left11.expected,
    Slot15.Left12.expected,
    Slot15.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 482, numerator := 193985370383319286088204288 }, { target := 483, numerator := 144457190710982447086960640 }, { target := 484, numerator := 152711887323038586920501248 }, { target := 485, numerator := 198112718689347356004974592 }, { target := 486, numerator := 2653884960776048956483305472 }, { target := 487, numerator := 4800106079910645313203863552 }, { target := 488, numerator := 144457190710982447086960640 }, { target := 489, numerator := 2653884960776048956483305472 }, { target := 490, numerator := 156839235629066656837271552 }, { target := 491, numerator := 156839235629066656837271552 }, { target := 492, numerator := 152711887323038586920501248 }, { target := 493, numerator := 152711887323038586920501248 }, { target := 494, numerator := 4800106079910645313203863552 }, { target := 495, numerator := 152711887323038586920501248 }, { target := 496, numerator := 193985370383319286088204288 }, { target := 497, numerator := 198112718689347356004974592 }, { target := 531, numerator := 188880492215337199612198912 }, { target := 532, numerator := 140655685692272382689935360 }, { target := 533, numerator := 148693153446116518843645952 }, { target := 534, numerator := 192899226092259267689054208 }, { target := 535, numerator := 2584045882860889773417955328 }, { target := 536, numerator := 4673787498860365173382709248 }, { target := 537, numerator := 140655685692272382689935360 }, { target := 538, numerator := 2584045882860889773417955328 }, { target := 539, numerator := 152711887323038586920501248 }, { target := 540, numerator := 152711887323038586920501248 }, { target := 541, numerator := 148693153446116518843645952 }, { target := 542, numerator := 148693153446116518843645952 }, { target := 543, numerator := 4673787498860365173382709248 }, { target := 544, numerator := 148693153446116518843645952 }, { target := 545, numerator := 188880492215337199612198912 }, { target := 546, numerator := 192899226092259267689054208 }, { target := 557, numerator := 5855295258675453187978166272 }, { target := 558, numerator := 4360326256460443863387996160 }, { target := 559, numerator := 4609487756829612084153024512 }, { target := 560, numerator := 5979876008860037298360680448 }, { target := 561, numerator := 80105422368687582975956615168 }, { target := 562, numerator := 144887412464671320374863986688 }, { target := 563, numerator := 4360326256460443863387996160 }, { target := 564, numerator := 80105422368687582975956615168 }, { target := 565, numerator := 4734068507014196194535538688 }, { target := 566, numerator := 4734068507014196194535538688 }, { target := 567, numerator := 4609487756829612084153024512 }, { target := 568, numerator := 4609487756829612084153024512 }, { target := 569, numerator := 144887412464671320374863986688 }, { target := 570, numerator := 4609487756829612084153024512 }, { target := 571, numerator := 5855295258675453187978166272 }, { target := 572, numerator := 5979876008860037298360680448 }, { target := 592, numerator := 188880492215337199612198912 }, { target := 593, numerator := 140655685692272382689935360 }, { target := 594, numerator := 148693153446116518843645952 }, { target := 595, numerator := 192899226092259267689054208 }, { target := 596, numerator := 2584045882860889773417955328 }, { target := 597, numerator := 4673787498860365173382709248 }, { target := 598, numerator := 140655685692272382689935360 }, { target := 599, numerator := 2584045882860889773417955328 }, { target := 600, numerator := 152711887323038586920501248 }, { target := 601, numerator := 152711887323038586920501248 }, { target := 602, numerator := 148693153446116518843645952 }, { target := 603, numerator := 148693153446116518843645952 }, { target := 604, numerator := 4673787498860365173382709248 }, { target := 605, numerator := 148693153446116518843645952 }, { target := 606, numerator := 188880492215337199612198912 }, { target := 607, numerator := 192899226092259267689054208 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk12

namespace RouteChunk13

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot15.Left14.expected,
    Slot15.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 653, numerator := 245034152063140150848258048 }, { target := 654, numerator := 182472240898083091057213440 }, { target := 655, numerator := 192899226092259267689054208 }, { target := 656, numerator := 250247644660228239164178432 }, { target := 657, numerator := 3352275739927640787136806912 }, { target := 658, numerator := 6063291890413446711415406592 }, { target := 659, numerator := 182472240898083091057213440 }, { target := 660, numerator := 3352275739927640787136806912 }, { target := 661, numerator := 198112718689347356004974592 }, { target := 662, numerator := 198112718689347356004974592 }, { target := 663, numerator := 192899226092259267689054208 }, { target := 664, numerator := 192899226092259267689054208 }, { target := 665, numerator := 6063291890413446711415406592 }, { target := 666, numerator := 192899226092259267689054208 }, { target := 667, numerator := 245034152063140150848258048 }, { target := 668, numerator := 250247644660228239164178432 }, { target := 688, numerator := 250139030231122237324263424 }, { target := 689, numerator := 186273745916793155454238720 }, { target := 690, numerator := 196917959969181335765909504 }, { target := 691, numerator := 255461137257316327480098816 }, { target := 692, numerator := 3422114817842799970202157056 }, { target := 693, numerator := 6189610471463726851236560896 }, { target := 694, numerator := 186273745916793155454238720 }, { target := 695, numerator := 3422114817842799970202157056 }, { target := 696, numerator := 202240066995375425921744896 }, { target := 697, numerator := 202240066995375425921744896 }, { target := 698, numerator := 196917959969181335765909504 }, { target := 699, numerator := 196917959969181335765909504 }, { target := 700, numerator := 6189610471463726851236560896 }, { target := 701, numerator := 196917959969181335765909504 }, { target := 702, numerator := 250139030231122237324263424 }, { target := 703, numerator := 255461137257316327480098816 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk13

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent2
