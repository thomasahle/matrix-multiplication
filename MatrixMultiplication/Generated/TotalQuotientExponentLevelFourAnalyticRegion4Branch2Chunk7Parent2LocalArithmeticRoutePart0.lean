import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk7Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 65; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk7.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left5.expected,
    Slot4.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 3121261937373447666381357056 }, { target := 21, numerator := 115720946416288510950430998528 }, { target := 24, numerator := 115720915720869780550764724224 }, { target := 31, numerator := 3121174573601958827246223360 }, { target := 35, numerator := 51113479670576935252000768000 }, { target := 38, numerator := 182527284184374888253420994560 }, { target := 40, numerator := 51110520946709677537461534720 }, { target := 71, numerator := 6283408915420941874079203328 }, { target := 73, numerator := 6283403313672025614862778368 }, { target := 90, numerator := 3121267372897316429119881216 }, { target := 92, numerator := 115721129875395809475829956608 }, { target := 95, numerator := 115721099180050262570108452864 }, { target := 102, numerator := 3121180009108939091382108160 }, { target := 106, numerator := 182179500293876522380762808320 }, { target := 109, numerator := 650618359144317849204718305280 }, { target := 111, numerator := 182169153104581658786817638400 }, { target := 116, numerator := 231401203769957203212631015424 }, { target := 118, numerator := 231400949641802889120400277504 }, { target := 140, numerator := 51130430932302403942932807680 }, { target := 143, numerator := 182587053715615777189108121600 }, { target := 145, numerator := 51127468292931039323656028160 }, { target := 150, numerator := 231401286411507168795126923264 }, { target := 152, numerator := 231401032283079823975486849024 }, { target := 232, numerator := 5862655005157142083623976960 }, { target := 234, numerator := 5862650406154386106818232320 }]

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
    Slot18.Left12.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 3162146978047494207697846272 }, { target := 21, numerator := 115680257353668692262200016896 }, { target := 24, numerator := 115680370690637388244362199040 }, { target := 31, numerator := 3162161145255310682667089920 }, { target := 35, numerator := 13034289530241462683261992960 }, { target := 38, numerator := 45607682908180873518241546240 }, { target := 40, numerator := 13051177393408712619421859840 }, { target := 90, numerator := 3162135940774709185742897152 }, { target := 92, numerator := 115679819766407079644570320896 }, { target := 95, numerator := 115679933103029561405378396160 }, { target := 102, numerator := 3162150107765789928644935680 }, { target := 106, numerator := 45955466798679239390899732480 }, { target := 109, numerator := 160800659889344148357114757120 }, { target := 111, numerator := 46015008949655903729006673920 }, { target := 140, numerator := 13031267407815986213950586880 }, { target := 143, numerator := 45597108338621785326716190720 }, { target := 145, numerator := 13048151355373576129106411520 }, { target := 232, numerator := 420680713700127426289336320 }, { target := 234, numerator := 420679710720342913208811520 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk7.Parent2
