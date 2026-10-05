import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk5Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 63; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk5.Parent0

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
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 111621456956218839983456256 }, { target := 82, numerator := 4252871985993905367225991168 }, { target := 85, numerator := 4252871729585964182514171904 }, { target := 92, numerator := 111617594860581391209332736 }, { target := 131, numerator := 181590761087681557598044160 }, { target := 134, numerator := 641403899519806893467893760 }, { target := 136, numerator := 181594361293371175243612160 }, { target := 176, numerator := 3948865251717290147495018496 }, { target := 178, numerator := 150142937999515433676669190144 }, { target := 181, numerator := 150142938256166569241259016192 }, { target := 188, numerator := 3948727442869107002720649216 }, { target := 227, numerator := 4386438661064724218751483904 }, { target := 230, numerator := 15504955202763814999045439488 }, { target := 232, numerator := 4386254445672443868652503040 }, { target := 286, numerator := 3948873779193112580981784576 }, { target := 288, numerator := 150143269482669572237515816960 }, { target := 291, numerator := 150143269739104535019991859200 }, { target := 298, numerator := 3948735970074713458565185536 }, { target := 302, numerator := 48144472212434875887741042688 }, { target := 305, numerator := 170102585963144064504797593600 }, { target := 307, numerator := 48144251314129255895501111296 }, { target := 573, numerator := 111617594860581391209332736 }, { target := 575, numerator := 4252734177145722222451621888 }, { target := 578, numerator := 4252733920467565060097572864 }, { target := 585, numerator := 111613732933828928461602816 }, { target := 589, numerator := 4384717627936587538275237888 }, { target := 592, numerator := 15499205946661956481881997312 }, { target := 594, numerator := 4384525564993808997415911424 }, { target := 763, numerator := 175490325991736120692441088 }, { target := 766, numerator := 619665441380372684872876032 }, { target := 768, numerator := 175498328982849550238613504 }]

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
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected,
    Slot18.Left12.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 181590761087681557598044160 }, { target := 27, numerator := 4386438661064724218751483904 }, { target := 29, numerator := 48144472212434875887741042688 }, { target := 37, numerator := 4384717627936587538275237888 }, { target := 44, numerator := 175490325991736120692441088 }, { target := 80, numerator := 23302281499912783571976192 }, { target := 82, numerator := 797424949695498818263449600 }, { target := 85, numerator := 797427297818301333711618048 }, { target := 92, numerator := 23302281499912783571976192 }, { target := 157, numerator := 641403899519806893467893760 }, { target := 158, numerator := 15504955202763814999045439488 }, { target := 160, numerator := 170102585963144064504797593600 }, { target := 168, numerator := 15499205946661956481881997312 }, { target := 175, numerator := 619665441380372684872876032 }, { target := 176, numerator := 1101431683972114037994422272 }, { target := 178, numerator := 37691979010200308006099353600 }, { target := 181, numerator := 37692089999197353535306989568 }, { target := 188, numerator := 1101431683972114037994422272 }, { target := 267, numerator := 181594361293371175243612160 }, { target := 268, numerator := 4386254445672443868652503040 }, { target := 270, numerator := 48144251314129255895501111296 }, { target := 278, numerator := 4384525564993808997415911424 }, { target := 285, numerator := 175498328982849550238613504 }, { target := 286, numerator := 1101425248211152935244005376 }, { target := 288, numerator := 37691758772694350539050188800 }, { target := 291, numerator := 37691869761042877721916473344 }, { target := 298, numerator := 1101425248211152935244005376 }, { target := 573, numerator := 23302281499912783571976192 }, { target := 575, numerator := 797424949695498818263449600 }, { target := 578, numerator := 797427297818301333711618048 }, { target := 585, numerator := 23302281499912783571976192 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk5.Parent0
