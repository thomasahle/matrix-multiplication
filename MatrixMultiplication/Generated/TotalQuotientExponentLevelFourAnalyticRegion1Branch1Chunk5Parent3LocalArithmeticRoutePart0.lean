import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk5Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 25; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot2.Left0.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left6.expected,
    Slot3.Left14.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left7.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 97280749547114691402137600 }, { target := 1, numerator := 31336207270378104744522547200 }, { target := 3, numerator := 49682837174650819881992192 }, { target := 4, numerator := 49682837174650819881992192 }, { target := 5, numerator := 49682837174650819881992192 }, { target := 6, numerator := 49682837174650819881992192 }, { target := 9, numerator := 9853837477108391379311001600 }, { target := 10, numerator := 9853837477108391379311001600 }, { target := 11, numerator := 9853837477108391379311001600 }, { target := 12, numerator := 9853837477108391379311001600 }, { target := 18, numerator := 35557469683752041577447424 }, { target := 20, numerator := 1607132942108285650100813824 }, { target := 25, numerator := 35747250648940219109212160 }, { target := 56, numerator := 9853837477108391379311001600 }, { target := 57, numerator := 9853837477108391379311001600 }, { target := 58, numerator := 9853837477108391379311001600 }, { target := 59, numerator := 9853837477108391379311001600 }, { target := 65, numerator := 1607132942108285650100813824 }, { target := 67, numerator := 72639485221578563858647220224 }, { target := 72, numerator := 1615710696477528546250588160 }, { target := 89, numerator := 106047550833087100525477888 }, { target := 90, numerator := 19739678703960665431451107328 }, { target := 95, numerator := 19739679889163972167289798656 }, { target := 103, numerator := 106046365629780364686786560 }, { target := 160, numerator := 105883062369103337060564992 }, { target := 161, numerator := 19710828972753898094723072000 }, { target := 166, numerator := 19710830154498440316741222400 }, { target := 174, numerator := 105881880624561115042414592 }, { target := 177, numerator := 49682837174650819881992192 }, { target := 178, numerator := 49682837174650819881992192 }, { target := 179, numerator := 49682837174650819881992192 }, { target := 180, numerator := 49682837174650819881992192 }, { target := 181, numerator := 35747250648940219109212160 }, { target := 183, numerator := 1615710696477528546250588160 }, { target := 188, numerator := 35938044532512862398054400 }, { target := 205, numerator := 105499255953141222309101568 }, { target := 206, numerator := 19643512933271440975690989568 }, { target := 211, numerator := 19643514106945532665461211136 }, { target := 219, numerator := 105498082279049532538880000 }, { target := 231, numerator := 105883062369103337060564992 }, { target := 232, numerator := 19710828972753898094723072000 }, { target := 237, numerator := 19710830154498440316741222400 }, { target := 245, numerator := 105881880624561115042414592 }, { target := 247, numerator := 97280749547114691402137600 }, { target := 248, numerator := 31336207270378104744522547200 }, { target := 250, numerator := 333273742084141591702966108160 }, { target := 258, numerator := 31336301717707762137426821120 }, { target := 265, numerator := 97280749547114691402137600 }]

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
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 3, numerator := 56364713658436280643485696 }, { target := 4, numerator := 56200225194452517178572800 }, { target := 5, numerator := 55816418778490402427109376 }, { target := 6, numerator := 56200225194452517178572800 }, { target := 7, numerator := 333273742084141591702966108160 }, { target := 9, numerator := 9885841226852274052140105728 }, { target := 10, numerator := 9856991495645506715412070400 }, { target := 11, numerator := 9789675456163049596379987968 }, { target := 12, numerator := 9856991495645506715412070400 }, { target := 55, numerator := 31336301717707762137426821120 }, { target := 56, numerator := 9885842412055580787978797056 }, { target := 57, numerator := 9856992677390048937430220800 }, { target := 58, numerator := 9789676629837141286150209536 }, { target := 59, numerator := 9856992677390048937430220800 }, { target := 176, numerator := 97280749547114691402137600 }, { target := 177, numerator := 56363528455129544804794368 }, { target := 178, numerator := 56199043449910295160422400 }, { target := 179, numerator := 55815245104398712656887808 }, { target := 180, numerator := 56199043449910295160422400 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent3
