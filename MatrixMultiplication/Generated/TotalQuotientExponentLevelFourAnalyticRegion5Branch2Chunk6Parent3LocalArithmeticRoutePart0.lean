import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk6Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 72; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk6.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 885007926385321933742800896 }, { target := 37, numerator := 34981610817858648734582177792 }, { target := 40, numerator := 34981571074465635517664854016 }, { target := 47, numerator := 884982069063762878121639936 }, { target := 86, numerator := 1086590574227575914295721984 }, { target := 89, numerator := 3832386633880089150806294528 }, { target := 91, numerator := 1086970986104295544483479552 }, { target := 122, numerator := 122746374190569210679132160 }, { target := 124, numerator := 122745847421409295754854400 }, { target := 145, numerator := 1054460744696100779867504640 }, { target := 147, numerator := 49841320203666009264215818240 }, { target := 150, numerator := 49841028976504593507596369920 }, { target := 157, numerator := 1054460744696100779867504640 }, { target := 161, numerator := 41879949627116295129181192192 }, { target := 164, numerator := 147909821401783127457266663424 }, { target := 166, numerator := 41888895823576667065019269120 }, { target := 197, numerator := 3106927133671733492860321792 }, { target := 199, numerator := 3106913800215597507967713280 }, { target := 216, numerator := 293298540308998761341779968 }, { target := 218, numerator := 13863376646630613757657612288 }, { target := 221, numerator := 13863295641717181734247727104 }, { target := 228, numerator := 293298540308998761341779968 }, { target := 232, numerator := 41879930196790566401540620288 }, { target := 235, numerator := 147909746760793738880420413440 }, { target := 237, numerator := 41888876558096195498020962304 }, { target := 242, numerator := 33158384638349311492438884352 }, { target := 244, numerator := 33158242338305540250853703680 }, { target := 406, numerator := 1086564716906016858674561024 }, { target := 409, numerator := 3832296711440826366792040448 }, { target := 411, numerator := 1086945094870631294762483712 }, { target := 416, numerator := 3109852645985326168671256576 }, { target := 418, numerator := 3109839299974280322576547840 }, { target := 498, numerator := 116255467531920085736226816 }, { target := 500, numerator := 116254968618649766005309440 }]

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
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 122746374190569210679132160 }, { target := 17, numerator := 3106927133671733492860321792 }, { target := 19, numerator := 33158384638349311492438884352 }, { target := 27, numerator := 3109852645985326168671256576 }, { target := 34, numerator := 116255467531920085736226816 }, { target := 35, numerator := 201582647842253980552921088 }, { target := 37, numerator := 6898338809257646394599014400 }, { target := 40, numerator := 6898359122324930883875766272 }, { target := 47, numerator := 201582647842253980552921088 }, { target := 126, numerator := 122745847421409295754854400 }, { target := 127, numerator := 3106913800215597507967713280 }, { target := 129, numerator := 33158242338305540250853703680 }, { target := 137, numerator := 3109839299974280322576547840 }, { target := 144, numerator := 116254968618649766005309440 }, { target := 145, numerator := 2777925889183988370938789888 }, { target := 147, numerator := 98068501198117118193050845184 }, { target := 150, numerator := 98068717784289145372824043520 }, { target := 157, numerator := 2777835966744725586924535808 }, { target := 216, numerator := 793672445795296783141699584 }, { target := 218, numerator := 28025519176946053307361656832 }, { target := 221, numerator := 28025580916379013763773235200 }, { target := 228, numerator := 793646554561632533420703744 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk6.Parent3
