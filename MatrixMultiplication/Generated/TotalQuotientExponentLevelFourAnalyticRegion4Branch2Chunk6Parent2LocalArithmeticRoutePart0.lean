import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk6Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 61; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk6.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 9112439252613895532052480 }, { target := 30, numerator := 411642769945864345585975296 }, { target := 35, numerator := 411573056199586986816700416 }, { target := 43, numerator := 9112439252613895532052480 }, { target := 71, numerator := 650502209561755845132288 }, { target := 72, numerator := 22733399799690216502984704 }, { target := 74, numerator := 274286448731496521932996608 }, { target := 82, numerator := 22733935617707682721431552 }, { target := 89, numerator := 650521345919522495791104 }, { target := 104, numerator := 419891711001506802292490240 }, { target := 105, numerator := 18968070151401894711234920448 }, { target := 110, numerator := 18964857814573824402163499008 }, { target := 118, numerator := 419891711001506802292490240 }, { target := 146, numerator := 22733399799690216502984704 }, { target := 147, numerator := 794474574960673868409208832 }, { target := 149, numerator := 9585614632809907676998795264 }, { target := 157, numerator := 794493300439283915361878016 }, { target := 164, numerator := 22734068566783432465580032 }, { target := 200, numerator := 9112439252613895532052480 }, { target := 202, numerator := 419891711001506802292490240 }, { target := 205, numerator := 419891046166056061024337920 }, { target := 212, numerator := 9111569852409080027545600 }, { target := 226, numerator := 419891046166056061024337920 }, { target := 227, numerator := 18968040118312080385228406784 }, { target := 232, numerator := 18964827786570262905318539264 }, { target := 240, numerator := 419891046166056061024337920 }, { target := 242, numerator := 274286448731496521932996608 }, { target := 243, numerator := 9585614632809907676998795264 }, { target := 245, numerator := 115653805401246022194302025728 }, { target := 253, numerator := 9585840562282577988610424832 }, { target := 260, numerator := 274294517641234747347697664 }, { target := 296, numerator := 411642769945864345585975296 }, { target := 298, numerator := 18968070151401894711234920448 }, { target := 301, numerator := 18968040118312080385228406784 }, { target := 308, numerator := 411603495905337919269765120 }, { target := 624, numerator := 9111569852409080027545600 }, { target := 625, numerator := 411603495905337919269765120 }, { target := 630, numerator := 411533788810314260173291520 }, { target := 638, numerator := 9111569852409080027545600 }, { target := 640, numerator := 22733935617707682721431552 }, { target := 641, numerator := 794493300439283915361878016 }, { target := 643, numerator := 9585840562282577988610424832 }, { target := 651, numerator := 794512026359246725796855808 }, { target := 658, numerator := 22734604400563497379823616 }, { target := 659, numerator := 411573056199586986816700416 }, { target := 661, numerator := 18964857814573824402163499008 }, { target := 664, numerator := 18964827786570262905318539264 }, { target := 671, numerator := 411533788810314260173291520 }, { target := 1017, numerator := 650521345919522495791104 }, { target := 1018, numerator := 22734068566783432465580032 }, { target := 1020, numerator := 274294517641234747347697664 }, { target := 1028, numerator := 22734604400563497379823616 }, { target := 1035, numerator := 650540482840239099871232 }, { target := 1036, numerator := 9112439252613895532052480 }, { target := 1038, numerator := 419891711001506802292490240 }, { target := 1041, numerator := 419891046166056061024337920 }, { target := 1048, numerator := 9111569852409080027545600 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk6.Parent2
