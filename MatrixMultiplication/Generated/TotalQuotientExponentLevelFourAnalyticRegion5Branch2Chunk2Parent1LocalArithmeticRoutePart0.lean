import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk2Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 44; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk2.Parent1

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
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 101675376938047965673553920 }, { target := 82, numerator := 3511343880643613735161692160 }, { target := 85, numerator := 3511353453506240672956416000 }, { target := 92, numerator := 101674421837156991075614720 }, { target := 131, numerator := 172047508826652990213455872 }, { target := 134, numerator := 613139630941342961667932160 }, { target := 136, numerator := 172064880508578350806073344 }, { target := 176, numerator := 3790069612773631951730900992 }, { target := 178, numerator := 131245968856193448628493221888 }, { target := 181, numerator := 131246318182913303806092509184 }, { target := 188, numerator := 3790023344125251736863506432 }, { target := 227, numerator := 4417703038400502538933633024 }, { target := 230, numerator := 15755609310725777013826650112 }, { target := 232, numerator := 4417494971319721186390179840 }, { target := 286, numerator := 3790070190756600929205616640 }, { target := 288, numerator := 131245977722636074715740897280 }, { target := 291, numerator := 131246327049644160269491896320 }, { target := 298, numerator := 3790023922434731687322583040 }, { target := 302, numerator := 47767301529223383346640322560 }, { target := 305, numerator := 170310705321844999553789460480 }, { target := 307, numerator := 47767803196737609190395084800 }, { target := 573, numerator := 101678981560642917862735872 }, { target := 575, numerator := 3511472502235251336951103488 }, { target := 578, numerator := 3511482075350079853878575104 }, { target := 585, numerator := 101678026302125956306829312 }, { target := 589, numerator := 4413825443493205880147542016 }, { target := 592, numerator := 15741873239036353281479671808 }, { target := 594, numerator := 4413612425686418952510504960 }, { target := 763, numerator := 170643062395246608996368384 }, { target := 766, numerator := 608168053035305962064314368 }, { target := 768, numerator := 170658444882252556314607616 }]

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
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 172047508826652990213455872 }, { target := 27, numerator := 4417703038400502538933633024 }, { target := 29, numerator := 47767301529223383346640322560 }, { target := 37, numerator := 4413825443493205880147542016 }, { target := 44, numerator := 170643062395246608996368384 }, { target := 80, numerator := 21841438194985300593213440 }, { target := 82, numerator := 1058080704888429630552276992 }, { target := 85, numerator := 1058073238170197229588971520 }, { target := 92, numerator := 21845042817580252782395392 }, { target := 157, numerator := 613139630941342961667932160 }, { target := 158, numerator := 15755609310725777013826650112 }, { target := 160, numerator := 170310705321844999553789460480 }, { target := 168, numerator := 15741873239036353281479671808 }, { target := 175, numerator := 608168053035305962064314368 }, { target := 176, numerator := 779354972758411413983068160 }, { target := 178, numerator := 37754860809662804139482021888 }, { target := 181, numerator := 37754594379222983392918241280 }, { target := 188, numerator := 779483594350049015772479488 }, { target := 267, numerator := 172064880508578350806073344 }, { target := 268, numerator := 4417494971319721186390179840 }, { target := 270, numerator := 47767803196737609190395084800 }, { target := 278, numerator := 4413612425686418952510504960 }, { target := 285, numerator := 170658444882252556314607616 }, { target := 286, numerator := 779356500919836973339770880 }, { target := 288, numerator := 37754934839500212483269853184 }, { target := 291, numerator := 37754668408537974179931095040 }, { target := 298, numerator := 779485122763676154261929984 }, { target := 573, numerator := 21840483094094325995274240 }, { target := 575, numerator := 1058034436240049415684882432 }, { target := 578, numerator := 1058026969848327987705937920 }, { target := 585, numerator := 21844087559063291226488832 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk2.Parent1
