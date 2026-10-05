import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk2Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 46; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk2.Parent3

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
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 962790744660534142296915968 }, { target := 21, numerator := 38642792599157608954795655168 }, { target := 24, numerator := 38642712376577979000796741632 }, { target := 31, numerator := 962856829796919033594904576 }, { target := 35, numerator := 10272963808882682192818339840 }, { target := 38, numerator := 36509024363278985317467553792 }, { target := 40, numerator := 10276269309633861484327993344 }, { target := 71, numerator := 962790744660534142296915968 }, { target := 73, numerator := 963136700414676134849937408 }, { target := 90, numerator := 963136700414676134849937408 }, { target := 92, numerator := 38659456637130966970537082880 }, { target := 95, numerator := 38659376299250179356598730752 }, { target := 102, numerator := 963202841539811593617932288 }, { target := 106, numerator := 36509024363278985317467553792 }, { target := 109, numerator := 129748090072320354692819320832 }, { target := 111, numerator := 36520712043012866760167653376 }, { target := 116, numerator := 38642792599157608954795655168 }, { target := 118, numerator := 38659456637130966970537082880 }, { target := 140, numerator := 10276269309633861484327993344 }, { target := 143, numerator := 36520712043012866760167653376 }, { target := 145, numerator := 10279584744002886364611739648 }, { target := 150, numerator := 38642712376577979000796741632 }, { target := 152, numerator := 38659376299250179356598730752 }, { target := 232, numerator := 962856829796919033594904576 }, { target := 234, numerator := 963202841539811593617932288 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk2.Parent3
