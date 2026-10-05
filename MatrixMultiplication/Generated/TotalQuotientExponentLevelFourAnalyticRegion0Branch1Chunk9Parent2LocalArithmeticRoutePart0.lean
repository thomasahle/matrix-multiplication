import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk9Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 81; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk9.Parent2

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
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 494232129937031959339335680 }, { target := 37, numerator := 21171358979406701138966216704 }, { target := 40, numerator := 21166063214517943690585964544 }, { target := 47, numerator := 494178654607135927974232064 }, { target := 86, numerator := 494232129937031959339335680 }, { target := 89, numerator := 1723573611586516858089504768 }, { target := 91, numerator := 494612951807669391478226944 }, { target := 145, numerator := 1723573611586516858089504768 }, { target := 147, numerator := 73783080771462488588342525952 }, { target := 150, numerator := 73764674576108722220594888704 }, { target := 157, numerator := 1723387851547384512644120576 }, { target := 161, numerator := 21171358979406701138966216704 }, { target := 164, numerator := 73783080771462488588342525952 }, { target := 166, numerator := 21190034108025960093553000448 }, { target := 216, numerator := 494612951807669391478226944 }, { target := 218, numerator := 21190034108025960093553000448 }, { target := 221, numerator := 21184731293330698548778369024 }, { target := 228, numerator := 494559400454759850285465600 }, { target := 232, numerator := 21166063214517943690585964544 }, { target := 235, numerator := 73764674576108722220594888704 }, { target := 237, numerator := 21184731293330698548778369024 }, { target := 406, numerator := 494178654607135927974232064 }, { target := 409, numerator := 1723387851547384512644120576 }, { target := 411, numerator := 494559400454759850285465600 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk9.Parent2
