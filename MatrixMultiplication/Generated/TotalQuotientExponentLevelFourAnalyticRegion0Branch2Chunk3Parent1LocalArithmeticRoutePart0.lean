import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk3Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 45; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk3.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 1185246719410471135522848768 }, { target := 37, numerator := 41653399102499082761047900160 }, { target := 40, numerator := 41669615931664007774513135616 }, { target := 47, numerator := 1168325249614656549278449664 }, { target := 86, numerator := 1359726943775832564528316416 }, { target := 89, numerator := 4855290779743307875575922688 }, { target := 91, numerator := 1360168130583920404347224064 }, { target := 122, numerator := 208825333077639342147502080 }, { target := 124, numerator := 208839648133283559132626944 }, { target := 145, numerator := 4205858745960897039426387968 }, { target := 147, numerator := 147803424451287352339458949120 }, { target := 150, numerator := 147861008494785355816806383616 }, { target := 157, numerator := 4145783284431990364269707264 }, { target := 161, numerator := 55445808996923499999846727680 }, { target := 164, numerator := 198420739399316156686752808960 }, { target := 166, numerator := 55470840248850906928801382400 }, { target := 197, numerator := 5103332450825714311983267840 }, { target := 199, numerator := 5103670745478945636867899392 }, { target := 216, numerator := 190431232390622057185935360 }, { target := 218, numerator := 6965341919322617959730380800 }, { target := 221, numerator := 6965347890263965296828088320 }, { target := 228, numerator := 189703630537867979422433280 }, { target := 232, numerator := 55462107986598781297203609600 }, { target := 235, numerator := 198478621807669826745249300480 }, { target := 237, numerator := 55487139392633737975242424320 }, { target := 242, numerator := 68613140366066988573953884160 }, { target := 244, numerator := 68617639589771218185458024448 }, { target := 406, numerator := 1343455041097337479008092160 }, { target := 409, numerator := 4797505300977309027034726400 }, { target := 411, numerator := 1343896085944083764761067520 }, { target := 416, numerator := 5093604537918961684934819840 }, { target := 418, numerator := 5093942508476275325635919872 }, { target := 498, numerator := 206657802442972506011729920 }, { target := 500, numerator := 206672046336676060962226176 }]

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
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot19.Left5.expected,
    Slot19.Left12.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 208825333077639342147502080 }, { target := 17, numerator := 5103332450825714311983267840 }, { target := 19, numerator := 68613140366066988573953884160 }, { target := 27, numerator := 5093604537918961684934819840 }, { target := 34, numerator := 206657802442972506011729920 }, { target := 35, numerator := 364917929231696126149656576 }, { target := 37, numerator := 20757988555408773605606031360 }, { target := 40, numerator := 20758076687063420684803768320 }, { target := 47, numerator := 364839869766151570288803840 }, { target := 86, numerator := 190437704866334697144188928 }, { target := 89, numerator := 673404102410174409272721408 }, { target := 91, numerator := 190431232390622057185935360 }, { target := 126, numerator := 208839648133283559132626944 }, { target := 127, numerator := 5103670745478945636867899392 }, { target := 129, numerator := 68617639589771218185458024448 }, { target := 137, numerator := 5093942508476275325635919872 }, { target := 144, numerator := 206672046336676060962226176 }, { target := 145, numerator := 1322836136192585245422256128 }, { target := 147, numerator := 75248200146209121513850798080 }, { target := 150, numerator := 75248519625544530050112552960 }, { target := 157, numerator := 1322553168781223399018987520 }, { target := 161, numerator := 6965578660984356366807203840 }, { target := 164, numerator := 24630885198180317166556938240 }, { target := 166, numerator := 6965341919322617959730380800 }, { target := 216, numerator := 1360168130583920404347224064 }, { target := 218, numerator := 55470840248850906928801382400 }, { target := 221, numerator := 55487139392633737975242424320 }, { target := 228, numerator := 1343896085944083764761067520 }, { target := 232, numerator := 6965584632128647162113294336 }, { target := 235, numerator := 24630906312660059121669636096 }, { target := 237, numerator := 6965347890263965296828088320 }, { target := 406, numerator := 189710078283470640559161344 }, { target := 409, numerator := 670831152235904736253968384 }, { target := 411, numerator := 189703630537867979422433280 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk3.Parent1
