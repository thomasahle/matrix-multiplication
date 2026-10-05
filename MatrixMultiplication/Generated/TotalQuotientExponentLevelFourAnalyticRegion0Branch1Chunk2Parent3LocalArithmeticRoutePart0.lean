import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk2Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 43; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk2.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 60339357665708935892434944 }, { target := 17, numerator := 3041500741817527303009206272 }, { target := 19, numerator := 33406840395105938851535781888 }, { target := 27, numerator := 3041521990564210848825344000 }, { target := 34, numerator := 60332274750147753953722368 }, { target := 35, numerator := 1219122724252953751888855040 }, { target := 37, numerator := 43915054832102616121433128960 }, { target := 40, numerator := 43932189197618261236834631680 }, { target := 47, numerator := 1236307124231285997284884480 }, { target := 86, numerator := 1620720769536950992581427200 }, { target := 89, numerator := 5350585045826721896112062464 }, { target := 91, numerator := 1621389455337378931372195840 }, { target := 122, numerator := 79747181084307550952751104 }, { target := 124, numerator := 79812137638892021527609344 }, { target := 126, numerator := 60350162536990586833993728 }, { target := 127, numerator := 3042045378440947316727742464 }, { target := 129, numerator := 33412822504037153239210131456 }, { target := 137, numerator := 3042066630992609597718528000 }, { target := 144, numerator := 60343078353103159837065216 }, { target := 145, numerator := 3980555914896207768864161792 }, { target := 147, numerator := 143324051225417654891309957120 }, { target := 150, numerator := 143379464488261698140323708928 }, { target := 157, numerator := 4036133540790244158142939136 }, { target := 161, numerator := 58153554221822382895697756160 }, { target := 164, numerator := 191898653390333795882930012160 }, { target := 166, numerator := 58177762480869038685935370240 }, { target := 197, numerator := 3400168862631367296325517312 }, { target := 199, numerator := 3402938405721403773557932032 }, { target := 216, numerator := 1219703295905070788001136640 }, { target := 218, numerator := 43936175417347845937524899840 }, { target := 221, numerator := 43953319695597300744653373440 }, { target := 228, numerator := 1236897629164886025002024960 }, { target := 232, numerator := 21345162299273298697330360320 }, { target := 235, numerator := 72854645646234030248332099584 }, { target := 237, numerator := 21348089355606898595353067520 }, { target := 242, numerator := 32638101046163779759609217024 }, { target := 244, numerator := 32664685792650270722400190464 }, { target := 406, numerator := 608590772407813079354572800 }, { target := 409, numerator := 2077223140573103326085775360 }, { target := 411, numerator := 608674228295848533216460800 }, { target := 416, numerator := 3400197185295419968594116608 }, { target := 418, numerator := 3402966751455145537031897088 }, { target := 498, numerator := 79740100418294382885601280 }, { target := 500, numerator := 79805051205456580659118080 }]

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
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 79747181084307550952751104 }, { target := 17, numerator := 3400168862631367296325517312 }, { target := 19, numerator := 32638101046163779759609217024 }, { target := 27, numerator := 3400197185295419968594116608 }, { target := 34, numerator := 79740100418294382885601280 }, { target := 35, numerator := 608467769263031780187832320 }, { target := 37, numerator := 21345232960654343273447424000 }, { target := 40, numerator := 21345162299273298697330360320 }, { target := 47, numerator := 608590772407813079354572800 }, { target := 86, numerator := 206869723979034539495260160 }, { target := 89, numerator := 706774179125455156582285312 }, { target := 91, numerator := 206865048851371111292600320 }, { target := 122, numerator := 60339357665708935892434944 }, { target := 124, numerator := 60350162536990586833993728 }, { target := 126, numerator := 79812137638892021527609344 }, { target := 127, numerator := 3402938405721403773557932032 }, { target := 129, numerator := 32664685792650270722400190464 }, { target := 137, numerator := 3402966751455145537031897088 }, { target := 144, numerator := 79805051205456580659118080 }, { target := 145, numerator := 2076803310055969283830185984 }, { target := 147, numerator := 72854886825467277464095948800 }, { target := 150, numerator := 72854645646234030248332099584 }, { target := 157, numerator := 2077223140573103326085775360 }, { target := 161, numerator := 7106733570934576499182796800 }, { target := 164, numerator := 24280284660551136472475893760 }, { target := 166, numerator := 7106572963156526496323993600 }, { target := 197, numerator := 3041500741817527303009206272 }, { target := 199, numerator := 3042045378440947316727742464 }, { target := 216, numerator := 608551208283679254663659520 }, { target := 218, numerator := 21348160026677719244734464000 }, { target := 221, numerator := 21348089355606898595353067520 }, { target := 228, numerator := 608674228295848533216460800 }, { target := 232, numerator := 43932189197618261236834631680 }, { target := 235, numerator := 143379464488261698140323708928 }, { target := 237, numerator := 43953319695597300744653373440 }, { target := 242, numerator := 33406840395105938851535781888 }, { target := 244, numerator := 33412822504037153239210131456 }, { target := 406, numerator := 1236307124231285997284884480 }, { target := 409, numerator := 4036133540790244158142939136 }, { target := 411, numerator := 1236897629164886025002024960 }, { target := 416, numerator := 3041521990564210848825344000 }, { target := 418, numerator := 3042066630992609597718528000 }, { target := 498, numerator := 60332274750147753953722368 }, { target := 500, numerator := 60343078353103159837065216 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk2.Parent3
