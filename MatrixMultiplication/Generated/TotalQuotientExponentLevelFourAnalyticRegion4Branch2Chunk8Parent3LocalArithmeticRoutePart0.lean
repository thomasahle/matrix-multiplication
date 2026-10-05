import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk8Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 72; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk8.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
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
    Slot15.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 753098793368944187686256640 }, { target := 37, numerator := 34702008116010076692881080320 }, { target := 40, numerator := 34701953170592953772078530560 }, { target := 47, numerator := 753026941669629598944460800 }, { target := 86, numerator := 2702043007029234642903367680 }, { target := 89, numerator := 9631575567364062375523123200 }, { target := 91, numerator := 2701640728426394198747381760 }, { target := 122, numerator := 243521239847874118828425216 }, { target := 124, numerator := 243520027362886740286111744 }, { target := 145, numerator := 2701004682671149735508705280 }, { target := 147, numerator := 124459482932031278723775856640 }, { target := 150, numerator := 124459285869135617405873029120 }, { target := 157, numerator := 2700746985038361858251161600 }, { target := 161, numerator := 104062798057888591111876771840 }, { target := 164, numerator := 371065124682096045579646795776 }, { target := 166, numerator := 104048457104795179441306206208 }, { target := 197, numerator := 8378374696453403096054235136 }, { target := 199, numerator := 8378333582733242760513454080 }, { target := 216, numerator := 753100047213301694138941440 }, { target := 218, numerator := 34702065891852308173260062720 }, { target := 221, numerator := 34702010946343705885026549760 }, { target := 228, numerator := 753028195394360240295116800 }, { target := 232, numerator := 69360797222345599155448053760 }, { target := 235, numerator := 246605669690259213798816612352 }, { target := 237, numerator := 69346398493579685415455031296 }, { target := 242, numerator := 101591096777002425416325005312 }, { target := 244, numerator := 101590595927957759152095232000 }, { target := 406, numerator := 1948912637357457665228275712 }, { target := 409, numerator := 6930459302623869056803930112 }, { target := 411, numerator := 1948509112025102700934856704 }, { target := 416, numerator := 8378509284082812465665015808 }, { target := 418, numerator := 8378468169993356960679854080 }, { target := 498, numerator := 251034560731929211446493184 }, { target := 500, numerator := 251033276627322858738024448 }]

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
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 243521239847874118828425216 }, { target := 17, numerator := 8378374696453403096054235136 }, { target := 19, numerator := 101591096777002425416325005312 }, { target := 27, numerator := 8378509284082812465665015808 }, { target := 34, numerator := 251034560731929211446493184 }, { target := 35, numerator := 1948944213660290455217111040 }, { target := 37, numerator := 69360789941878514418995691520 }, { target := 40, numerator := 69360797222345599155448053760 }, { target := 47, numerator := 1948912637357457665228275712 }, { target := 126, numerator := 243520027362886740286111744 }, { target := 127, numerator := 8378333582733242760513454080 }, { target := 129, numerator := 101590595927957759152095232000 }, { target := 137, numerator := 8378468169993356960679854080 }, { target := 144, numerator := 251033276627322858738024448 }, { target := 145, numerator := 6930570884692912640014417920 }, { target := 147, numerator := 246605641750064766855870939136 }, { target := 150, numerator := 246605669690259213798816612352 }, { target := 157, numerator := 6930459302623869056803930112 }, { target := 216, numerator := 1948540681213092504608440320 }, { target := 218, numerator := 69346391212942871268046143488 }, { target := 221, numerator := 69346398493579685415455031296 }, { target := 228, numerator := 1948509112025102700934856704 }, { target := 232, numerator := 34701953170592953772078530560 }, { target := 235, numerator := 124459285869135617405873029120 }, { target := 237, numerator := 34702010946343705885026549760 }, { target := 406, numerator := 753026941669629598944460800 }, { target := 409, numerator := 2700746985038361858251161600 }, { target := 411, numerator := 753028195394360240295116800 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk8.Parent3
