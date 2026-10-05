import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk4Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 53; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk4.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 2149219062547980581462867968 }, { target := 21, numerator := 77026047390500850116442718208 }, { target := 24, numerator := 77052932670354657211924348928 }, { target := 31, numerator := 2176198763279552658488164352 }, { target := 35, numerator := 30629756507811337181887201280 }, { target := 38, numerator := 102208688706915224059295825920 }, { target := 40, numerator := 30643318332809367250125455360 }, { target := 71, numerator := 2697922766160867725957660672 }, { target := 73, numerator := 2699850738188242755136782336 }, { target := 90, numerator := 2150613679266903126737682432 }, { target := 92, numerator := 77076557972276915840911147008 }, { target := 95, numerator := 77103465169029476874058727424 }, { target := 102, numerator := 2177615349801013964150145024 }, { target := 106, numerator := 102050929285989068175327625216 }, { target := 109, numerator := 340344987243757142820853383168 }, { target := 111, numerator := 102096886843503561166366441472 }, { target := 116, numerator := 96274738893382891420944171008 }, { target := 118, numerator := 96343959740327987863835639808 }, { target := 140, numerator := 30639695601549935878560808960 }, { target := 143, numerator := 102242265571845773547955814400 }, { target := 145, numerator := 30653259562726303448610897920 }, { target := 150, numerator := 77056516278618382684668297216 }, { target := 152, numerator := 77122312801559382216079835136 }, { target := 232, numerator := 2164799626171021791917506560 }, { target := 234, numerator := 2166649359246674190988738560 }]

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
  [{ target := 19, numerator := 548703703612887144494792704 }, { target := 21, numerator := 19248691502882041304501452800 }, { target := 24, numerator := 19248627781903806876880994304 }, { target := 31, numerator := 548814625315739666648924160 }, { target := 35, numerator := 2670696794030274435853844480 }, { target := 38, numerator := 9124484230882577161425780736 }, { target := 40, numerator := 2670636437936486321445928960 }, { target := 90, numerator := 549237058921339628399099904 }, { target := 92, numerator := 19267401768051072022924492800 }, { target := 95, numerator := 19267337985134268970124181504 }, { target := 102, numerator := 549348088443181979570012160 }, { target := 106, numerator := 9282243651808733045393981440 }, { target := 109, numerator := 31712954468457942102529015808 }, { target := 111, numerator := 9282033878849981237826682880 }, { target := 140, numerator := 2674259169195917693010575360 }, { target := 143, numerator := 9136655150507768856237309952 }, { target := 145, numerator := 2674198732594656739820830720 }, { target := 150, numerator := 19245044173640081404137046016 }, { target := 152, numerator := 19248490352604363628103073792 }, { target := 232, numerator := 560213762424270533219581952 }, { target := 234, numerator := 560314078997521752731418624 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk4.Parent1
