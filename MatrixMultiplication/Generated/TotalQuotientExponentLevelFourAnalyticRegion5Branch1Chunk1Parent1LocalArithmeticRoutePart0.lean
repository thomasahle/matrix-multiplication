import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk1Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 33; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk1.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 6654939039720924877160448 }, { target := 57, numerator := 229205413666471338236182528 }, { target := 59, numerator := 2539154168803074799346647040 }, { target := 67, numerator := 228997980986377395144491008 }, { target := 74, numerator := 6651968427689064418770944 }, { target := 110, numerator := 6654939039720924877160448 }, { target := 112, numerator := 254544401255359754390208512 }, { target := 115, numerator := 254542603157742679654137856 }, { target := 122, numerator := 6655681615182533907972096 }, { target := 152, numerator := 254544401255359754390208512 }, { target := 153, numerator := 8819094142957924835756343296 }, { target := 155, numerator := 97694164648922133151963152384 }, { target := 163, numerator := 8809582913111952921869680640 }, { target := 170, numerator := 254438757282911425864400896 }, { target := 206, numerator := 164902677756964813645283328 }, { target := 208, numerator := 5864439300308712040811200512 }, { target := 211, numerator := 5864415581474711195936096256 }, { target := 218, numerator := 164909146529874134974857216 }, { target := 283, numerator := 254542603157742679654137856 }, { target := 284, numerator := 8819029756939607358799085568 }, { target := 286, numerator := 97693451582885566050375565312 }, { target := 294, numerator := 8809518657334358968746639360 }, { target := 301, numerator := 254436959612573365775106048 }, { target := 302, numerator := 1827227335508713860329635840 }, { target := 304, numerator := 64981745249452678391906959360 }, { target := 307, numerator := 64981482429573448706220359680 }, { target := 314, numerator := 1827299013657594683698708480 }, { target := 660, numerator := 6655681615182533907972096 }, { target := 661, numerator := 229232395974832412031975424 }, { target := 663, numerator := 2539452962270258567019757568 }, { target := 671, numerator := 229024897662655199363203072 }, { target := 678, numerator := 6652710886620033091371008 }, { target := 679, numerator := 164900740401291861172420608 }, { target := 681, numerator := 5864370402065810956990021632 }, { target := 684, numerator := 5864346683510470339058466816 }, { target := 691, numerator := 164907209098202938790117376 }, { target := 966, numerator := 4930957658798633930194944 }, { target := 968, numerator := 175359807831838541664485376 }, { target := 971, numerator := 175359098585828924942450688 }, { target := 978, numerator := 4931151089528529399840768 }]

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
    Slot17.Left1.expected,
    Slot17.Left3.expected,
    Slot17.Left11.expected,
    Slot17.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 206, numerator := 64302735909506524590899200 }, { target := 208, numerator := 2954654842649212794945142784 }, { target := 211, numerator := 2954614175464896162862989312 }, { target := 218, numerator := 64323249444958277057118208 }, { target := 302, numerator := 711926833294360939017011200 }, { target := 304, numerator := 32712419399469454760056193024 }, { target := 307, numerator := 32711969153312117344155205632 }, { target := 314, numerator := 712153948612663883321049088 }, { target := 679, numerator := 64097240585085533972070400 }, { target := 681, numerator := 2945212511046141964879659008 }, { target := 684, numerator := 2945171973823888629688172544 }, { target := 691, numerator := 64117688564452260573085696 }, { target := 966, numerator := 1721010768890430488576000 }, { target := 968, numerator := 79078949451072884199915520 }, { target := 971, numerator := 79077861026744440832655360 }, { target := 978, numerator := 1721559797091503691530240 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk1.Parent1
