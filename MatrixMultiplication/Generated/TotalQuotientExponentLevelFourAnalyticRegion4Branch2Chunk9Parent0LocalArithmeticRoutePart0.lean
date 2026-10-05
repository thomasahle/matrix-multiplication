import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk9Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 73; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk9.Parent0

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
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 3541987545614880726667231232 }, { target := 21, numerator := 135107473943037337428155170816 }, { target := 24, numerator := 135107412552346243616712163328 }, { target := 31, numerator := 3541860041753620243451740160 }, { target := 35, numerator := 48667078586309582801858461696 }, { target := 38, numerator := 173761133838621726069841985536 }, { target := 40, numerator := 48661818658666804316450324480 }, { target := 71, numerator := 4095038327479008853892268032 }, { target := 73, numerator := 4095027976892577015253696512 }, { target := 90, numerator := 841441707726165128628928512 }, { target := 92, numerator := 38772757608652517902286585856 }, { target := 95, numerator := 38772696217815057102954037248 }, { target := 102, numerator := 841361427400254852578672640 }, { target := 106, numerator := 172925563998582360655349678080 }, { target := 109, numerator := 617333815432264538100449935360 }, { target := 111, numerator := 172906691788182721245388734464 }, { target := 116, numerator := 154361548792290949356656263168 }, { target := 118, numerator := 154361204965588198455601266688 }, { target := 140, numerator := 48664958069304805890543583232 }, { target := 143, numerator := 173754329200732032083349733376 }, { target := 145, numerator := 48659698198357843114102620160 }, { target := 150, numerator := 154361508652350359450232553472 }, { target := 152, numerator := 154361164825298579578056343552 }, { target := 232, numerator := 4094908462423247936785743872 }, { target := 234, numerator := 4094898111791780101873467392 }]

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
    Slot17.Left2.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 553050781864128127225036800 }, { target := 21, numerator := 19254074849253611928501092352 }, { target := 24, numerator := 19254096100004115833520390144 }, { target := 31, numerator := 553048420669627693334003712 }, { target := 35, numerator := 2467438469562987735930634240 }, { target := 38, numerator := 8633700444829011849835970560 }, { target := 40, numerator := 2470635403553974231456808960 }, { target := 90, numerator := 3253586269166411886624768000 }, { target := 92, numerator := 115588447356935680553314680832 }, { target := 95, numerator := 115588468607483522475102306304 }, { target := 102, numerator := 3253536684391525249294794752 }, { target := 106, numerator := 9469270284868377264328278016 }, { target := 109, numerator := 33133488060253025550733410304 }, { target := 111, numerator := 9481539134696634877806116864 }, { target := 140, numerator := 2467495992915972657363550208 }, { target := 143, numerator := 8633901722147324039845117952 }, { target := 145, numerator := 2470693001437029386244063232 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk9.Parent0
