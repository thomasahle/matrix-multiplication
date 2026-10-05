import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk2Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 34; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk2.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 92598633565391054790721536 }, { target := 17, numerator := 2870087764501941965159399424 }, { target := 19, numerator := 33688722628057544869067882496 }, { target := 27, numerator := 2870109015176447626466820096 }, { target := 34, numerator := 92610439495671977739288576 }, { target := 35, numerator := 632247651095930835019235328 }, { target := 37, numerator := 28111564409983299128156749824 }, { target := 40, numerator := 28111579794735897163019059200 }, { target := 47, numerator := 632275132634221577345433600 }, { target := 86, numerator := 632247651095930835019235328 }, { target := 89, numerator := 2222261624503498056539308032 }, { target := 91, numerator := 632991428565184186272448512 }, { target := 122, numerator := 92598633565391054790721536 }, { target := 124, numerator := 92598412793307821554794496 }, { target := 145, numerator := 2222261624503498056539308032 }, { target := 147, numerator := 98711779499547987151996059648 }, { target := 150, numerator := 98711833715603209770472833024 }, { target := 157, numerator := 2222357741226057948255485952 }, { target := 161, numerator := 28111564409983299128156749824 }, { target := 164, numerator := 98711779499547987151996059648 }, { target := 166, numerator := 28145362355670704087973756928 }, { target := 197, numerator := 2870087764501941965159399424 }, { target := 199, numerator := 2870080921687632142154072064 }, { target := 216, numerator := 632991428565184186272448512 }, { target := 218, numerator := 28145362355670704087973756928 }, { target := 221, numerator := 28145377757459575088248520704 }, { target := 228, numerator := 633018946031785380876910592 }, { target := 232, numerator := 28111579794735897163019059200 }, { target := 235, numerator := 98711833715603209770472833024 }, { target := 237, numerator := 28145377757459575088248520704 }, { target := 242, numerator := 33688722628057544869067882496 }, { target := 244, numerator := 33688642307979486582125101056 }, { target := 406, numerator := 632275132634221577345433600 }, { target := 409, numerator := 2222357741226057948255485952 }, { target := 411, numerator := 633018946031785380876910592 }, { target := 416, numerator := 2870109015176447626466820096 }, { target := 418, numerator := 2870102172311472307653574656 }, { target := 498, numerator := 92610439495671977739288576 }, { target := 500, numerator := 92610218695441246832295936 }]

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
    Slot16.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 126, numerator := 92598412793307821554794496 }, { target := 127, numerator := 2870080921687632142154072064 }, { target := 129, numerator := 33688642307979486582125101056 }, { target := 137, numerator := 2870102172311472307653574656 }, { target := 144, numerator := 92610218695441246832295936 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk2.Parent1
