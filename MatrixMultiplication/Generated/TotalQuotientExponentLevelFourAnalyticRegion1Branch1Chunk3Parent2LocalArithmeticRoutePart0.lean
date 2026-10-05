import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk3Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 16; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk3.Parent2

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
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected,
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot3.Left10.expected,
    Slot3.Left11.expected,
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot4.Left0.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot6.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 12749633925110782933745008640 }, { target := 2, numerator := 502233313803178305422450753536 }, { target := 5, numerator := 502233403528141479945709813760 }, { target := 12, numerator := 12749761429005820414165778432 }, { target := 16, numerator := 90281806533927311314752897024 }, { target := 19, numerator := 327293370687969454934596780032 }, { target := 21, numerator := 90289723894930491528016035840 }, { target := 26, numerator := 64807820859572596036375412736 }, { target := 28, numerator := 64807822021717472680077164544 }, { target := 30, numerator := 29647951014809245671825080320 }, { target := 33, numerator := 106269962580747774009477693440 }, { target := 35, numerator := 29656566658862592086455091200 }, { target := 40, numerator := 33917610665220886156919439360 }, { target := 42, numerator := 33917634924995186094193508352 }, { target := 44, numerator := 1798881619586568211962789888 }, { target := 45, numerator := 1760195363863758563033743360 }, { target := 47, numerator := 1760196622854041593710641152 }, { target := 49, numerator := 2030995376952577013506375680 }, { target := 50, numerator := 90281806533927311314752897024 }, { target := 53, numerator := 327293370687969454934596780032 }, { target := 55, numerator := 90289723894930491528016035840 }, { target := 60, numerator := 36490203889329456364430295040 }, { target := 62, numerator := 36490229989166477654232137728 }, { target := 64, numerator := 1740853180245066011576893440 }, { target := 65, numerator := 54633756101463583091085803520 }, { target := 67, numerator := 54633795178585060235557208064 }, { target := 69, numerator := 22921233539893369152429096960 }, { target := 70, numerator := 2030995376952577013506375680 }, { target := 71, numerator := 1692495542176690925993984000 }, { target := 73, numerator := 1692496752744270763183308800 }, { target := 75, numerator := 1740853180245066011576893440 }, { target := 76, numerator := 2030995376952577013506375680 }, { target := 77, numerator := 29647951014809245671825080320 }, { target := 80, numerator := 106269962580747774009477693440 }, { target := 82, numerator := 29656566658862592086455091200 }, { target := 87, numerator := 54633756101463583091085803520 }, { target := 89, numerator := 54633795178585060235557208064 }, { target := 91, numerator := 2030995376952577013506375680 }, { target := 92, numerator := 56935550038823882750437621760 }, { target := 94, numerator := 56935590762317268473486508032 }, { target := 96, numerator := 84199265484519692759935746048 }, { target := 97, numerator := 2089023816294079213892272128 }, { target := 98, numerator := 33917610665220886156919439360 }, { target := 100, numerator := 33917634924995186094193508352 }, { target := 102, numerator := 22921233539893369152429096960 }, { target := 103, numerator := 84199265484519692759935746048 }, { target := 104, numerator := 1798881619586568211962789888 }, { target := 105, numerator := 1692495542176690925993984000 }, { target := 107, numerator := 1692496752744270763183308800 }, { target := 109, numerator := 2030995376952577013506375680 }, { target := 110, numerator := 2089023816294079213892272128 }, { target := 111, numerator := 2030995376952577013506375680 }]

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
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1798881619586568211962789888 }, { target := 1, numerator := 2030995376952577013506375680 }, { target := 2, numerator := 1740853180245066011576893440 }, { target := 3, numerator := 22921233539893369152429096960 }, { target := 4, numerator := 2030995376952577013506375680 }, { target := 5, numerator := 1740853180245066011576893440 }, { target := 6, numerator := 2030995376952577013506375680 }, { target := 7, numerator := 2030995376952577013506375680 }, { target := 8, numerator := 84199265484519692759935746048 }, { target := 9, numerator := 2089023816294079213892272128 }, { target := 10, numerator := 22921233539893369152429096960 }, { target := 11, numerator := 84199265484519692759935746048 }, { target := 12, numerator := 1798881619586568211962789888 }, { target := 13, numerator := 2030995376952577013506375680 }, { target := 14, numerator := 2089023816294079213892272128 }, { target := 15, numerator := 2030995376952577013506375680 }, { target := 16, numerator := 1624795720489623288954224640 }, { target := 17, numerator := 33917610665220886156919439360 }, { target := 18, numerator := 1760195363863758563033743360 }, { target := 19, numerator := 36490203889329456364430295040 }, { target := 20, numerator := 54633756101463583091085803520 }, { target := 21, numerator := 1692495542176690925993984000 }, { target := 22, numerator := 54633756101463583091085803520 }, { target := 23, numerator := 56935550038823882750437621760 }, { target := 24, numerator := 33917610665220886156919439360 }, { target := 25, numerator := 1692495542176690925993984000 }, { target := 26, numerator := 27098781394844338567331708928 }, { target := 27, numerator := 29647951014809245671825080320 }, { target := 28, numerator := 27098781394844338567331708928 }, { target := 29, numerator := 29647951014809245671825080320 }, { target := 44, numerator := 12749633925110782933745008640 }, { target := 50, numerator := 1624796882634499932655976448 }, { target := 51, numerator := 33917634924995186094193508352 }, { target := 52, numerator := 1760196622854041593710641152 }, { target := 53, numerator := 36490229989166477654232137728 }, { target := 54, numerator := 54633795178585060235557208064 }, { target := 55, numerator := 1692496752744270763183308800 }, { target := 56, numerator := 54633795178585060235557208064 }, { target := 57, numerator := 56935590762317268473486508032 }, { target := 58, numerator := 33917634924995186094193508352 }, { target := 59, numerator := 1692496752744270763183308800 }, { target := 60, numerator := 327293370687969454934596780032 }, { target := 61, numerator := 106269962580747774009477693440 }, { target := 62, numerator := 327293370687969454934596780032 }, { target := 63, numerator := 106269962580747774009477693440 }, { target := 64, numerator := 502233313803178305422450753536 }, { target := 71, numerator := 90289723894930491528016035840 }, { target := 72, numerator := 29656566658862592086455091200 }, { target := 73, numerator := 90289723894930491528016035840 }, { target := 74, numerator := 29656566658862592086455091200 }, { target := 75, numerator := 502233403528141479945709813760 }, { target := 104, numerator := 12749761429005820414165778432 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk3.Parent2
