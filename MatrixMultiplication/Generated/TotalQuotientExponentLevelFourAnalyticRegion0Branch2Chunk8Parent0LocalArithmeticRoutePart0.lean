import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk8Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 73; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk8.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 1985716301023690954358390784 }, { target := 21, numerator := 77235049107511633086523637760 }, { target := 24, numerator := 77246143763897314026064969728 }, { target := 31, numerator := 1987819696224827180058673152 }, { target := 35, numerator := 28092419994772230470281199616 }, { target := 38, numerator := 100281878870676125104415440896 }, { target := 40, numerator := 28094287663110828549042339840 }, { target := 71, numerator := 2537920178131617095312474112 }, { target := 73, numerator := 2537957937279166889435594752 }, { target := 90, numerator := 404341840871907150803238912 }, { target := 92, numerator := 19394077635243090599825375232 }, { target := 95, numerator := 19405123794260118354641551360 }, { target := 102, numerator := 412488324114477854975066112 }, { target := 106, numerator := 100297393812578679480368758784 }, { target := 109, numerator := 357963131928046462802103107584 }, { target := 111, numerator := 100302554401235289185347174400 }, { target := 116, numerator := 96489748910373313321635938304 }, { target := 118, numerator := 96491570800824160279813160960 }, { target := 140, numerator := 28094408476633055568391569408 }, { target := 143, numerator := 100287468408328848260315742208 }, { target := 145, numerator := 28096244101526194108718120960 }, { target := 150, numerator := 96509841976020838740450607104 }, { target := 152, numerator := 96511665073945855541767045120 }, { target := 232, numerator := 2531034608740824186246660096 }, { target := 234, numerator := 2531073086005911913058271232 }]

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
    Slot17.Left2.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 552203877107926140954083328 }, { target := 21, numerator := 19254699802861680235112300544 }, { target := 24, numerator := 19263698212123524714385637376 }, { target := 31, numerator := 543214912515997006187986944 }, { target := 35, numerator := 2574126015965255540624326656 }, { target := 38, numerator := 9140431243828221693975855104 }, { target := 40, numerator := 2574133681016386031450062848 }, { target := 90, numerator := 2133616096407259738632355840 }, { target := 92, numerator := 77097493165581069679987785728 }, { target := 95, numerator := 77106541279685737187125493760 }, { target := 102, numerator := 2118584761891434058083205120 }, { target := 106, numerator := 9124916301925667318022537216 }, { target := 109, numerator := 32401548932002487695933702144 }, { target := 111, numerator := 9124943473458677710300643328 }, { target := 140, numerator := 2574012867494159012100833280 }, { target := 143, numerator := 9140029466365118635332075520 }, { target := 145, numerator := 2574020532208363955803914240 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk8.Parent0
