import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk1Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 31; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk1.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left6.expected,
    Slot8.Left14.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left3.expected,
    Slot14.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 2184991744851472401039360 }, { target := 72, numerator := 53721604935649926957760512 }, { target := 74, numerator := 723653036208654209477771264 }, { target := 82, numerator := 53610191890922483612647424 }, { target := 89, numerator := 2160137641767710111039488 }, { target := 146, numerator := 53721604935649926957760512 }, { target := 147, numerator := 1314529149341631294354751488 }, { target := 149, numerator := 17680625694847971562228809728 }, { target := 157, numerator := 1311977121824721697903738880 }, { target := 164, numerator := 53152821659345416257273856 }, { target := 200, numerator := 11161249231992122731659264 }, { target := 202, numerator := 389179635087795932545155072 }, { target := 205, numerator := 389361512638147291552677888 }, { target := 212, numerator := 10979562579095868797878272 }, { target := 242, numerator := 723653036208654209477771264 }, { target := 243, numerator := 17680625694847971562228809728 }, { target := 245, numerator := 237694070999465911720062484480 }, { target := 253, numerator := 17647040145160701003561959424 }, { target := 260, numerator := 716170035993175023492792320 }, { target := 296, numerator := 541044076097903241799401472 }, { target := 298, numerator := 18865570665570841746112249856 }, { target := 301, numerator := 18874387220881759863752884224 }, { target := 308, numerator := 532236774584215161542803456 }, { target := 640, numerator := 53610191890922483612647424 }, { target := 641, numerator := 1311977121824721697903738880 }, { target := 643, numerator := 17647040145160701003561959424 }, { target := 651, numerator := 1309425214153101785408995328 }, { target := 658, numerator := 53041419761027050654138368 }, { target := 659, numerator := 541119581125116852835450880 }, { target := 661, numerator := 18868203437075850280032010240 }, { target := 664, numerator := 18877021222774971669896232960 }, { target := 671, numerator := 532311050514632693503754240 }, { target := 1017, numerator := 1092518592522906331250688 }, { target := 1018, numerator := 28717167517548505555009536 }, { target := 1020, numerator := 394675759137846764586926080 }, { target := 1028, numerator := 28606342890630376302051328 }, { target := 1035, numerator := 1067641251990966716334080 }, { target := 1036, numerator := 11090220527228839115358208 }, { target := 1038, numerator := 386702947682474042310262784 }, { target := 1041, numerator := 386883667788299393707278336 }, { target := 1048, numerator := 10909690104012593308893184 }]

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
    Slot14.Left18.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 11161249231992122731659264 }, { target := 30, numerator := 541044076097903241799401472 }, { target := 35, numerator := 541119581125116852835450880 }, { target := 43, numerator := 11090220527228839115358208 }, { target := 104, numerator := 389179635087795932545155072 }, { target := 105, numerator := 18865570665570841746112249856 }, { target := 110, numerator := 18868203437075850280032010240 }, { target := 118, numerator := 386702947682474042310262784 }, { target := 226, numerator := 389361512638147291552677888 }, { target := 227, numerator := 18874387220881759863752884224 }, { target := 232, numerator := 18877021222774971669896232960 }, { target := 240, numerator := 386883667788299393707278336 }, { target := 624, numerator := 10979562579095868797878272 }, { target := 625, numerator := 532236774584215161542803456 }, { target := 630, numerator := 532311050514632693503754240 }, { target := 638, numerator := 10909690104012593308893184 }, { target := 1017, numerator := 1067619049244803779788800 }, { target := 1018, numerator := 24435654141796910702264320 }, { target := 1020, numerator := 321494276855328258905866240 }, { target := 1028, numerator := 24435076870396674352087040 }, { target := 1035, numerator := 1067641251990966716334080 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk1.Parent0
