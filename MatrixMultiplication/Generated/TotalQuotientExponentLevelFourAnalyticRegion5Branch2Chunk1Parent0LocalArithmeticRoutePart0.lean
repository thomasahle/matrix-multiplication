import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk1Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 32; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk1.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 2596919322559931796684800 }, { target := 57, numerator := 59916535213687647439421440 }, { target := 59, numerator := 676315775582354315778457600 }, { target := 67, numerator := 59810853300101308177448960 }, { target := 74, numerator := 2556614064960803763650560 }, { target := 110, numerator := 8894981814765754616119296 }, { target := 112, numerator := 341329795932056301537853440 }, { target := 115, numerator := 341329542791476646483329024 }, { target := 122, numerator := 8895410399824293329371136 }, { target := 152, numerator := 125804454945804224445808640 }, { target := 153, numerator := 2902580372565695319236411392 }, { target := 155, numerator := 32763257903027664589611335680 }, { target := 163, numerator := 2897460746622424544159203328 }, { target := 170, numerator := 123851917984159157041758208 }, { target := 206, numerator := 240786759029459276233965568 }, { target := 208, numerator := 9092121475150226927273377792 }, { target := 211, numerator := 9092119217991129685454487552 }, { target := 218, numerator := 240796647412024307791953920 }, { target := 283, numerator := 125803567162468679968358400 }, { target := 284, numerator := 2902559889487524896723435520 }, { target := 286, numerator := 32763026697587467863510220800 }, { target := 294, numerator := 2897440299672693282365767680 }, { target := 301, numerator := 123851043979586672504340480 }, { target := 302, numerator := 2551446463518686274146795520 }, { target := 304, numerator := 96931909994270840298594631680 }, { target := 307, numerator := 96931867741879127527160545280 }, { target := 314, numerator := 2551558079938091590195609600 }, { target := 660, numerator := 2597347907618470509936640 }, { target := 661, numerator := 59926423596252678997409792 }, { target := 663, numerator := 676427392001759631827271680 }, { target := 671, numerator := 59820724241350882836348928 }, { target := 678, numerator := 2557035998202692850679808 }, { target := 679, numerator := 240672630179611489612070912 }, { target := 681, numerator := 9086712787480386976694140928 }, { target := 684, numerator := 9086710565598548566021767168 }, { target := 691, numerator := 240682501120861064270970880 }, { target := 966, numerator := 8857358124233752729092096 }, { target := 968, numerator := 339469024597893512070955008 }, { target := 971, numerator := 339468785506292894598692864 }, { target := 978, numerator := 8857780057475641816121344 }]

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
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 6298062492205822819434496 }, { target := 57, numerator := 180870223815771628794544128 }, { target := 59, numerator := 1875130687936331958368337920 }, { target := 67, numerator := 180861776879510181434621952 }, { target := 74, numerator := 6300744059272948965441536 }, { target := 152, numerator := 215525340986252077092044800 }, { target := 153, numerator := 6189541102584531608036966400 }, { target := 155, numerator := 64168652091243175708983296000 }, { target := 163, numerator := 6189252040857962432534937600 }, { target := 170, numerator := 215617106613734355029196800 }, { target := 283, numerator := 215525975629007966514970624 }, { target := 284, numerator := 6189559328503604788731052032 }, { target := 286, numerator := 64168841044291659663650324480 }, { target := 294, numerator := 6189270265925855283655999488 }, { target := 301, numerator := 215617741526706222094352384 }, { target := 660, numerator := 6298062492205822819434496 }, { target := 661, numerator := 180870223815771628794544128 }, { target := 663, numerator := 1875130687936331958368337920 }, { target := 671, numerator := 180861776879510181434621952 }, { target := 678, numerator := 6300744059272948965441536 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk1.Parent0
