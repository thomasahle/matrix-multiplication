import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk3Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 52; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk3.Parent0

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
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 1591428162009643456921600 }, { target := 72, numerator := 38499767942509917057843200 }, { target := 74, numerator := 422179963202496091243151360 }, { target := 82, numerator := 38486351160492151579607040 }, { target := 89, numerator := 1537000482922009817251840 }, { target := 146, numerator := 38499767942509917057843200 }, { target := 147, numerator := 929389300522186072209227776 }, { target := 149, numerator := 10204711516816784959888949248 }, { target := 157, numerator := 929007224272107202890694656 }, { target := 164, numerator := 37216345196903391177998336 }, { target := 200, numerator := 10344623164906541489848320 }, { target := 202, numerator := 369120999858553278148116480 }, { target := 205, numerator := 369121723632049392860528640 }, { target := 212, numerator := 10344170806471469794590720 }, { target := 242, numerator := 422179963202496091243151360 }, { target := 243, numerator := 10204711516816784959888949248 }, { target := 245, numerator := 111959974744245611612329738240 }, { target := 253, numerator := 10200903043462532483159949312 }, { target := 260, numerator := 407885477126672997398085632 }, { target := 296, numerator := 529619988631135252125843456 }, { target := 298, numerator := 18898113216129555714627600384 }, { target := 301, numerator := 18898150271603174530992832512 }, { target := 308, numerator := 529596828960123491897573376 }, { target := 640, numerator := 38486351160492151579607040 }, { target := 641, numerator := 929007224272107202890694656 }, { target := 643, numerator := 10200903043462532483159949312 }, { target := 651, numerator := 928623604465610398002839552 }, { target := 658, numerator := 37204346435434273153482752 }, { target := 659, numerator := 529617349532449662130192384 }, { target := 661, numerator := 18898019046749963899031781376 }, { target := 664, numerator := 18898056102038935130674823168 }, { target := 671, numerator := 529594189976842642353291264 }, { target := 1017, numerator := 783364270700149614837760 }, { target := 1018, numerator := 19828330769335755852480512 }, { target := 1020, numerator := 211615976203810819562012672 }, { target := 1028, numerator := 19847001315289347953524736 }, { target := 1035, numerator := 741939467773253177573376 }, { target := 1036, numerator := 10338250707104751012544512 }, { target := 1038, numerator := 368893615259051089270407168 }, { target := 1041, numerator := 368894338586690840873140224 }, { target := 1048, numerator := 10337798627329906260836352 }]

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
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 10344623164906541489848320 }, { target := 30, numerator := 529619988631135252125843456 }, { target := 35, numerator := 529617349532449662130192384 }, { target := 43, numerator := 10338250707104751012544512 }, { target := 104, numerator := 369120999858553278148116480 }, { target := 105, numerator := 18898113216129555714627600384 }, { target := 110, numerator := 18898019046749963899031781376 }, { target := 118, numerator := 368893615259051089270407168 }, { target := 226, numerator := 369121723632049392860528640 }, { target := 227, numerator := 18898150271603174530992832512 }, { target := 232, numerator := 18898056102038935130674823168 }, { target := 240, numerator := 368894338586690840873140224 }, { target := 624, numerator := 10344170806471469794590720 }, { target := 625, numerator := 529596828960123491897573376 }, { target := 630, numerator := 529594189976842642353291264 }, { target := 638, numerator := 10337798627329906260836352 }, { target := 1017, numerator := 753636212221860202414080 }, { target := 1018, numerator := 17388014427567635325517824 }, { target := 1020, numerator := 196269500922862177836072960 }, { target := 1028, numerator := 17357345120144925199958016 }, { target := 1035, numerator := 741939467773253177573376 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk3.Parent0
