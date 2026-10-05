import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk9Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 73; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk9.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot15.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 178363378068211425985167360 }, { target := 17, numerator := 6061932285800549551498592256 }, { target := 19, numerator := 66747320901263664284105179136 }, { target := 27, numerator := 6062026732916285962102767616 }, { target := 34, numerator := 178339766289277323334123520 }, { target := 35, numerator := 889566574656259459551068160 }, { target := 37, numerator := 35729249986888108065633075200 }, { target := 40, numerator := 35736195189926066014608424960 }, { target := 47, numerator := 882682485912790141176381440 }, { target := 86, numerator := 2097713596989387985261690880 }, { target := 89, numerator := 7259810603599819525020712960 }, { target := 91, numerator := 2098152974016395417038618624 }, { target := 122, numerator := 239449702630193293755940864 }, { target := 124, numerator := 239450204764100297010184192 }, { target := 145, numerator := 3032508237934471210504028160 }, { target := 147, numerator := 121800040612278959535764275200 }, { target := 150, numerator := 121823716620378604466822184960 }, { target := 157, numerator := 3009040566801133651561021440 }, { target := 161, numerator := 70448020055203923606068264960 }, { target := 164, numerator := 243774526980856593701159305216 }, { target := 166, numerator := 70462630861953913559978082304 }, { target := 197, numerator := 9062682576788084799561531392 }, { target := 199, numerator := 9062695013029221720356028416 }, { target := 216, numerator := 889568008637565186405826560 }, { target := 218, numerator := 35729307582438580088419123200 }, { target := 221, numerator := 35736252796672205236060815360 }, { target := 228, numerator := 882683908796944911213527040 }, { target := 232, numerator := 70448027908419105703130562560 }, { target := 235, numerator := 243774553775742308257374404608 }, { target := 237, numerator := 70462638715151362733507608576 }, { target := 242, numerator := 100237832819371243930426277888 }, { target := 244, numerator := 100237967502737048278772219904 }, { target := 406, numerator := 2097690192684251841151631360 }, { target := 409, numerator := 7259729911889505062068682752 }, { target := 411, numerator := 2098129566136808543679938560 }, { target := 416, numerator := 9062781746282126028832768000 }, { target := 418, numerator := 9062794182927461016183767040 }, { target := 498, numerator := 239416646094649553770774528 }, { target := 500, numerator := 239417148168883861962358784 }]

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
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 61086324561981867770773504 }, { target := 17, numerator := 3000750290987535248062939136 }, { target := 19, numerator := 33490511918107579646321098752 }, { target := 27, numerator := 3000755013365840066730000384 }, { target := 34, numerator := 61076879805372230436651008 }, { target := 35, numerator := 2097713596989387985261690880 }, { target := 37, numerator := 70448020055203923606068264960 }, { target := 40, numerator := 70448027908419105703130562560 }, { target := 47, numerator := 2097690192684251841151631360 }, { target := 86, numerator := 889566574656259459551068160 }, { target := 89, numerator := 3032508237934471210504028160 }, { target := 91, numerator := 889568008637565186405826560 }, { target := 126, numerator := 239450204764100297010184192 }, { target := 127, numerator := 9062695013029221720356028416 }, { target := 129, numerator := 100237967502737048278772219904 }, { target := 137, numerator := 9062794182927461016183767040 }, { target := 144, numerator := 239417148168883861962358784 }, { target := 145, numerator := 7259810603599819525020712960 }, { target := 147, numerator := 243774526980856593701159305216 }, { target := 150, numerator := 243774553775742308257374404608 }, { target := 157, numerator := 7259729911889505062068682752 }, { target := 161, numerator := 35729249986888108065633075200 }, { target := 164, numerator := 121800040612278959535764275200 }, { target := 166, numerator := 35729307582438580088419123200 }, { target := 216, numerator := 2098152974016395417038618624 }, { target := 218, numerator := 70462630861953913559978082304 }, { target := 221, numerator := 70462638715151362733507608576 }, { target := 228, numerator := 2098129566136808543679938560 }, { target := 232, numerator := 35736195189926066014608424960 }, { target := 235, numerator := 121823716620378604466822184960 }, { target := 237, numerator := 35736252796672205236060815360 }, { target := 406, numerator := 882682485912790141176381440 }, { target := 409, numerator := 3009040566801133651561021440 }, { target := 411, numerator := 882683908796944911213527040 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk9.Parent0
