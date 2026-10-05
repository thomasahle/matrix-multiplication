import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk9Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 80; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk9.Parent1

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
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 931456140504483540278181888 }, { target := 21, numerator := 38673954816499699705756778496 }, { target := 24, numerator := 38685016992793982185110503424 }, { target := 31, numerator := 937588171105203203396861952 }, { target := 35, numerator := 12884428416026720146726846464 }, { target := 38, numerator := 45678494005136465460283310080 }, { target := 40, numerator := 12879205297904444352936017920 }, { target := 71, numerator := 931456140504483540278181888 }, { target := 73, numerator := 931460768589797060782325760 }, { target := 90, numerator := 931460768589797060782325760 }, { target := 92, numerator := 38674096652306228908503597056 }, { target := 95, numerator := 38685158762984190716976037888 }, { target := 102, numerator := 937592723745089866283614208 }, { target := 106, numerator := 45678494005136465460283310080 }, { target := 109, numerator := 161946640131372434249067003904 }, { target := 111, numerator := 45660177486191721608183283712 }, { target := 116, numerator := 38673954816499699705756778496 }, { target := 118, numerator := 38674096652306228908503597056 }, { target := 140, numerator := 12879205297904444352936017920 }, { target := 143, numerator := 45660177486191721608183283712 }, { target := 145, numerator := 12873990445457270729120677888 }, { target := 150, numerator := 38685016992793982185110503424 }, { target := 152, numerator := 38685158762984190716976037888 }, { target := 232, numerator := 937588171105203203396861952 }, { target := 234, numerator := 937592723745089866283614208 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk9.Parent1
