import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk7Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 75; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk7.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 2980985071551189237104640 }, { target := 57, numerator := 81680167991183372141461504 }, { target := 59, numerator := 870009475734778479980314624 }, { target := 67, numerator := 81899962983574552927272960 }, { target := 74, numerator := 2760880334244011860557824 }, { target := 110, numerator := 2980985071551189237104640 }, { target := 112, numerator := 110639030605109560753520640 }, { target := 115, numerator := 110639328585778905722388480 }, { target := 122, numerator := 2980930893247671970037760 }, { target := 152, numerator := 110639030605109560753520640 }, { target := 153, numerator := 3031553123982776218213679104 }, { target := 155, numerator := 32290334470701344609454260224 }, { target := 163, numerator := 3039710798142936831712296960 }, { target := 170, numerator := 102469860286324143684583424 }, { target := 206, numerator := 81680167991183372141461504 }, { target := 208, numerator := 3031553123982776218213679104 }, { target := 211, numerator := 3031561288770772810625712128 }, { target := 218, numerator := 81678683484274900793819136 }, { target := 283, numerator := 110639328585778905722388480 }, { target := 284, numerator := 3031561288770772810625712128 }, { target := 286, numerator := 32290421437257598114325331968 }, { target := 294, numerator := 3039718984901744206251294720 }, { target := 301, numerator := 102470136265220459088314368 }, { target := 302, numerator := 870009475734778479980314624 }, { target := 304, numerator := 32290334470701344609454260224 }, { target := 307, numerator := 32290421437257598114325331968 }, { target := 314, numerator := 869993663633641479094665216 }, { target := 660, numerator := 2980930893247671970037760 }, { target := 661, numerator := 81678683484274900793819136 }, { target := 663, numerator := 869993663633641479094665216 }, { target := 671, numerator := 81898474481973212102000640 }, { target := 678, numerator := 2760830156262863605334016 }, { target := 679, numerator := 81899962983574552927272960 }, { target := 681, numerator := 3039710798142936831712296960 }, { target := 684, numerator := 3039718984901744206251294720 }, { target := 691, numerator := 81898474481973212102000640 }, { target := 966, numerator := 2760880334244011860557824 }, { target := 968, numerator := 102469860286324143684583424 }, { target := 971, numerator := 102470136265220459088314368 }, { target := 978, numerator := 2760830156262863605334016 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk7.Parent2
