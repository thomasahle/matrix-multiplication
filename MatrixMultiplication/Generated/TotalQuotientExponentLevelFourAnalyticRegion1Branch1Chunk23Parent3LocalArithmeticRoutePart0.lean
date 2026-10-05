import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk23Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 97; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left2.expected,
    Slot0.Left5.expected,
    Slot0.Left12.expected,
    Slot1.Left0.expected,
    Slot1.Left3.expected,
    Slot1.Left5.expected,
    Slot2.Left0.expected,
    Slot2.Left2.expected,
    Slot2.Left5.expected,
    Slot2.Left12.expected,
    Slot3.Left0.expected,
    Slot3.Left2.expected,
    Slot4.Left0.expected,
    Slot4.Left3.expected,
    Slot4.Left5.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected,
    Slot5.Left9.expected,
    Slot5.Left10.expected,
    Slot5.Left11.expected,
    Slot5.Left12.expected,
    Slot5.Left13.expected,
    Slot5.Left14.expected,
    Slot5.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 1895595459183123642997276672 }, { target := 17, numerator := 37911909183662472859945533440 }, { target := 18, numerator := 1963295297011092344532893696 }, { target := 19, numerator := 35271615508371693500056469504 }, { target := 20, numerator := 52805873505815587197781278720 }, { target := 21, numerator := 1895595459183123642997276672 }, { target := 22, numerator := 52873573343643555899316895744 }, { target := 23, numerator := 52873573343643555899316895744 }, { target := 24, numerator := 37844209345834504158409916416 }, { target := 25, numerator := 1963295297011092344532893696 }, { target := 26, numerator := 86422754351428627799543382016 }, { target := 27, numerator := 33342941102143313407842975744 }, { target := 28, numerator := 86422754351428627799543382016 }, { target := 29, numerator := 33342941102143313407842975744 }, { target := 44, numerator := 14933095626329289312620773376 }, { target := 49, numerator := 2379166013001590215821754368 }, { target := 50, numerator := 1895595911128353448881291264 }, { target := 51, numerator := 37911918222567068977625825280 }, { target := 52, numerator := 1963295765097223214912765952 }, { target := 53, numerator := 35271623917781148102398312448 }, { target := 54, numerator := 52805886095718417504550256640 }, { target := 55, numerator := 1895595911128353448881291264 }, { target := 56, numerator := 52873585949687287270581731328 }, { target := 57, numerator := 52873585949687287270581731328 }, { target := 58, numerator := 37844218368598199211594350592 }, { target := 59, numerator := 1963295765097223214912765952 }, { target := 60, numerator := 313974420508321972517030854656 }, { target := 61, numerator := 119933567594597773178497400832 }, { target := 62, numerator := 313974420508321972517030854656 }, { target := 63, numerator := 119933567594597773178497400832 }, { target := 64, numerator := 503995913481076986150236717056 }, { target := 69, numerator := 24894200477504443965549576192 }, { target := 70, numerator := 2205080694977083614664065024 }, { target := 71, numerator := 86422745589225192787506364416 }, { target := 72, numerator := 33342952225529989854702600192 }, { target := 73, numerator := 86422745589225192787506364416 }, { target := 74, numerator := 33342952225529989854702600192 }, { target := 75, numerator := 503995856812679191714494152704 }, { target := 76, numerator := 2205080694977083614664065024 }, { target := 91, numerator := 2147052255635581414278168576 }, { target := 96, numerator := 81123758199420076139483234304 }, { target := 97, numerator := 2147052255635581414278168576 }, { target := 102, numerator := 24894200477504443965549576192 }, { target := 103, numerator := 81123758199420076139483234304 }, { target := 104, numerator := 14933114515795220791201628160 }, { target := 109, numerator := 2147052255635581414278168576 }, { target := 110, numerator := 2147052255635581414278168576 }, { target := 111, numerator := 2379166013001590215821754368 }]

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
    Slot6.Left0.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot8.Left4.expected,
    Slot8.Left5.expected,
    Slot8.Left6.expected,
    Slot8.Left7.expected,
    Slot8.Left8.expected,
    Slot8.Left9.expected,
    Slot9.Left0.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected,
    Slot11.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 13946073807744704766506172416 }, { target := 1, numerator := 2379166013001590215821754368 }, { target := 2, numerator := 465368854042529401899579342848 }, { target := 3, numerator := 24894200477504443965549576192 }, { target := 4, numerator := 2205080694977083614664065024 }, { target := 5, numerator := 465368797374131607463836778496 }, { target := 6, numerator := 2205080694977083614664065024 }, { target := 7, numerator := 2147052255635581414278168576 }, { target := 8, numerator := 81123758199420076139483234304 }, { target := 9, numerator := 2147052255635581414278168576 }, { target := 10, numerator := 24894200477504443965549576192 }, { target := 11, numerator := 81123758199420076139483234304 }, { target := 12, numerator := 13946092697210636245087027200 }, { target := 13, numerator := 2147052255635581414278168576 }, { target := 14, numerator := 2147052255635581414278168576 }, { target := 15, numerator := 2379166013001590215821754368 }, { target := 16, numerator := 93430972885598359039638503424 }, { target := 19, numerator := 339572067058297920268435193856 }, { target := 21, numerator := 93430961762211682592778878976 }, { target := 26, numerator := 1895595459183123642997276672 }, { target := 28, numerator := 1895595911128353448881291264 }, { target := 30, numerator := 33342941102143313407842975744 }, { target := 33, numerator := 119933567594597773178497400832 }, { target := 35, numerator := 33342952225529989854702600192 }, { target := 40, numerator := 37911909183662472859945533440 }, { target := 42, numerator := 37911918222567068977625825280 }, { target := 45, numerator := 1963295297011092344532893696 }, { target := 47, numerator := 1963295765097223214912765952 }, { target := 50, numerator := 93430972885598359039638503424 }, { target := 53, numerator := 339572067058297920268435193856 }, { target := 55, numerator := 93430961762211682592778878976 }, { target := 60, numerator := 35271615508371693500056469504 }, { target := 62, numerator := 35271623917781148102398312448 }, { target := 65, numerator := 52805873505815587197781278720 }, { target := 67, numerator := 52805886095718417504550256640 }, { target := 71, numerator := 1895595459183123642997276672 }, { target := 73, numerator := 1895595911128353448881291264 }, { target := 77, numerator := 33342941102143313407842975744 }, { target := 80, numerator := 119933567594597773178497400832 }, { target := 82, numerator := 33342952225529989854702600192 }, { target := 87, numerator := 52873573343643555899316895744 }, { target := 89, numerator := 52873585949687287270581731328 }, { target := 92, numerator := 52873573343643555899316895744 }, { target := 94, numerator := 52873585949687287270581731328 }, { target := 98, numerator := 37844209345834504158409916416 }, { target := 100, numerator := 37844218368598199211594350592 }, { target := 105, numerator := 1963295297011092344532893696 }, { target := 107, numerator := 1963295765097223214912765952 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23.Parent3
