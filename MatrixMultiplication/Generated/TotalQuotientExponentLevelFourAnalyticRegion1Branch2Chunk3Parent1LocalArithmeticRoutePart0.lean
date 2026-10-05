import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk3Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 15; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left7.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left6.expected,
    Slot5.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 3, numerator := 116884473409127306095493120 }, { target := 4, numerator := 116884473409127306095493120 }, { target := 5, numerator := 116884473409127306095493120 }, { target := 6, numerator := 116884473409127306095493120 }, { target := 9, numerator := 9786635840873914893097500672 }, { target := 10, numerator := 9786635840873914893097500672 }, { target := 11, numerator := 9786635840873914893097500672 }, { target := 12, numerator := 9786635840873914893097500672 }, { target := 18, numerator := 580152793223937127492878336 }, { target := 20, numerator := 5619402355982277722863828992 }, { target := 25, numerator := 580152793223937127492878336 }, { target := 56, numerator := 9786639382648777045331410944 }, { target := 57, numerator := 9786639382648777045331410944 }, { target := 58, numerator := 9786639382648777045331410944 }, { target := 59, numerator := 9786639382648777045331410944 }, { target := 65, numerator := 5619402355982277722863828992 }, { target := 67, numerator := 54429941917439478192117121024 }, { target := 72, numerator := 5619402355982277722863828992 }, { target := 89, numerator := 238502727224019865189744640 }, { target := 90, numerator := 20013422602960248069488115712 }, { target := 95, numerator := 20013423677483090363069497344 }, { target := 103, numerator := 238501652701177571608363008 }, { target := 160, numerator := 228045830634328168519958528 }, { target := 161, numerator := 19134110096313572693574156288 }, { target := 166, numerator := 19134111382973971834815381504 }, { target := 174, numerator := 228044543973929027278733312 }, { target := 177, numerator := 116880931634265153861582848 }, { target := 178, numerator := 116880931634265153861582848 }, { target := 179, numerator := 116880931634265153861582848 }, { target := 180, numerator := 116880931634265153861582848 }, { target := 181, numerator := 580152793223937127492878336 }, { target := 183, numerator := 5619402355982277722863828992 }, { target := 188, numerator := 580152793223937127492878336 }, { target := 205, numerator := 238502727224019865189744640 }, { target := 206, numerator := 20013422602960248069488115712 }, { target := 211, numerator := 20013423677483090363069497344 }, { target := 219, numerator := 238501652701177571608363008 }, { target := 231, numerator := 228045830634328168519958528 }, { target := 232, numerator := 19134110096313572693574156288 }, { target := 237, numerator := 19134111382973971834815381504 }, { target := 245, numerator := 228044543973929027278733312 }, { target := 247, numerator := 215670477272656696909496320 }, { target := 248, numerator := 31853400847581988288326533120 }, { target := 250, numerator := 332002669921612397997247692800 }, { target := 258, numerator := 31853400847581988288326533120 }, { target := 265, numerator := 215670477272656696909496320 }]

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
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 215670477272656696909496320 }, { target := 1, numerator := 31853400847581988288326533120 }, { target := 3, numerator := 121618253814892559094251520 }, { target := 4, numerator := 111161357225200862424465408 }, { target := 5, numerator := 121618253814892559094251520 }, { target := 6, numerator := 111161357225200862424465408 }, { target := 7, numerator := 332002669921612397997247692800 }, { target := 9, numerator := 10226786762086333176390615040 }, { target := 10, numerator := 9347474255439657800476655616 }, { target := 11, numerator := 10226786762086333176390615040 }, { target := 12, numerator := 9347474255439657800476655616 }, { target := 55, numerator := 31853400847581988288326533120 }, { target := 56, numerator := 10226784294834313317738086400 }, { target := 57, numerator := 9347472000325194789483970560 }, { target := 58, numerator := 10226784294834313317738086400 }, { target := 59, numerator := 9347472000325194789483970560 }, { target := 176, numerator := 215670477272656696909496320 }, { target := 177, numerator := 121620721066912417746780160 }, { target := 178, numerator := 111163612339663873417150464 }, { target := 179, numerator := 121620721066912417746780160 }, { target := 180, numerator := 111163612339663873417150464 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3.Parent1
