import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk11Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 48; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk11.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left1.expected,
    Slot0.Left2.expected,
    Slot0.Left3.expected,
    Slot0.Left4.expected,
    Slot0.Left5.expected,
    Slot0.Left6.expected,
    Slot0.Left7.expected,
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot2.Left0.expected,
    Slot3.Left0.expected,
    Slot3.Left3.expected,
    Slot3.Left5.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot5.Left0.expected,
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1637427068800432081899171610624 }, { target := 3, numerator := 5598700300115065790160839901184 }, { target := 5, numerator := 1637426832682107938416910925824 }, { target := 10, numerator := 3664721753837033762286680932352 }, { target := 11, numerator := 49227471111448616891737702400 }, { target := 12, numerator := 3664399230350294784035384197120 }, { target := 13, numerator := 49711041554586619022304870400 }, { target := 14, numerator := 1641624459246134074393751453696 }, { target := 15, numerator := 49227471111448616891737702400 }, { target := 17, numerator := 49227447637966783096333271040 }, { target := 19, numerator := 102903765765597235350989701120 }, { target := 20, numerator := 4197390445701992494579843072 }, { target := 21, numerator := 3664399230350294784035384197120 }, { target := 22, numerator := 49227447637966783096333271040 }, { target := 23, numerator := 3664076706863555805784087461888 }, { target := 24, numerator := 49711017850520484305531043840 }, { target := 25, numerator := 5684949903789651894001077321728 }, { target := 26, numerator := 84760207064820880696999411712 }, { target := 27, numerator := 1641624223127809930911490768896 }, { target := 28, numerator := 49711041554586619022304870400 }, { target := 30, numerator := 49711017850520484305531043840 }, { target := 32, numerator := 84895606756617719164566503424 }, { target := 33, numerator := 76094626789823218772705542144 }, { target := 34, numerator := 102903765765597235350989701120 }, { target := 35, numerator := 4197390445701992494579843072 }]

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
    Slot14.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 4197390445701992494579843072 }, { target := 1, numerator := 102903765765597235350989701120 }, { target := 2, numerator := 4197390445701992494579843072 }, { target := 3, numerator := 86249603674586103840237420544 }, { target := 4, numerator := 84760207064820880696999411712 }, { target := 5, numerator := 4197390445701992494579843072 }, { target := 6, numerator := 84895606756617719164566503424 }, { target := 7, numerator := 76094626789823218772705542144 }, { target := 8, numerator := 102903765765597235350989701120 }, { target := 9, numerator := 4197390445701992494579843072 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk11.Parent2
