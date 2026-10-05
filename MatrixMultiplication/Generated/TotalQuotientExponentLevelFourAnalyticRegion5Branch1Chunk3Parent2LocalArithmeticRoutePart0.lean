import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk3Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 54; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk3.Parent2

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
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot16.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 80799497880425568833372160 }, { target := 17, numerator := 3018940304002549422722383872 }, { target := 19, numerator := 33424154977758929009132961792 }, { target := 27, numerator := 3009292532280181834345611264 }, { target := 34, numerator := 80799497880425568833372160 }, { target := 35, numerator := 647150418537599777982382080 }, { target := 37, numerator := 21333816704629542032360079360 }, { target := 40, numerator := 21333848148700215838286807040 }, { target := 47, numerator := 647181862608273583909109760 }, { target := 86, numerator := 1351844258957714805848276992 }, { target := 89, numerator := 4640966882220814220558073856 }, { target := 91, numerator := 1351644608938003822549139456 }, { target := 122, numerator := 170998865339216691409715200 }, { target := 124, numerator := 170999637716685884611362816 }, { target := 145, numerator := 2203939763990106767810887680 }, { target := 147, numerator := 72654587876585965305263554560 }, { target := 150, numerator := 72654694962721915458646179840 }, { target := 157, numerator := 2204046850126056921193512960 }, { target := 161, numerator := 49654307830387642185688285184 }, { target := 164, numerator := 170655167516492551923490095104 }, { target := 166, numerator := 49645109939576741583791325184 }, { target := 197, numerator := 6033600511747205647734669312 }, { target := 199, numerator := 6033627844756499204405198848 }, { target := 216, numerator := 647786702494139507357515776 }, { target := 218, numerator := 21354792299965769692313812992 }, { target := 221, numerator := 21354823774952529040232153088 }, { target := 228, numerator := 647818177480898855275855872 }, { target := 232, numerator := 49654039123375676528548380672 }, { target := 235, numerator := 170654236147139106819331325952 }, { target := 237, numerator := 49644841359965979885428539392 }, { target := 242, numerator := 66828521806658157096302804992 }, { target := 244, numerator := 66828824542126657651324485632 }, { target := 406, numerator := 1351939814879101248461602816 }, { target := 409, numerator := 4641300017399441842285576192 }, { target := 411, numerator := 1351740100517588288827031552 }, { target := 416, numerator := 6023917322352214780730671104 }, { target := 418, numerator := 6023944609205241656387829760 }, { target := 498, numerator := 170944558241194330847969280 }, { target := 500, numerator := 170945330385602243333193728 }]

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
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected,
    Slot18.Left12.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot23.Left0.expected,
    Slot23.Left3.expected,
    Slot23.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 90199367458791122576343040 }, { target := 17, numerator := 3014660207744656225012285440 }, { target := 19, numerator := 33404366828899228087169843200 }, { target := 27, numerator := 3014624790072032946385059840 }, { target := 34, numerator := 90145060360768762014597120 }, { target := 35, numerator := 1351844258957714805848276992 }, { target := 37, numerator := 49654307830387642185688285184 }, { target := 40, numerator := 49654039123375676528548380672 }, { target := 47, numerator := 1351939814879101248461602816 }, { target := 86, numerator := 647150418537599777982382080 }, { target := 89, numerator := 2203939763990106767810887680 }, { target := 91, numerator := 647786702494139507357515776 }, { target := 126, numerator := 170999637716685884611362816 }, { target := 127, numerator := 6033627844756499204405198848 }, { target := 129, numerator := 66828824542126657651324485632 }, { target := 137, numerator := 6023944609205241656387829760 }, { target := 144, numerator := 170945330385602243333193728 }, { target := 145, numerator := 4640966882220814220558073856 }, { target := 147, numerator := 170655167516492551923490095104 }, { target := 150, numerator := 170654236147139106819331325952 }, { target := 157, numerator := 4641300017399441842285576192 }, { target := 161, numerator := 21333816704629542032360079360 }, { target := 164, numerator := 72654587876585965305263554560 }, { target := 166, numerator := 21354792299965769692313812992 }, { target := 216, numerator := 1351644608938003822549139456 }, { target := 218, numerator := 49645109939576741583791325184 }, { target := 221, numerator := 49644841359965979885428539392 }, { target := 228, numerator := 1351740100517588288827031552 }, { target := 232, numerator := 21333848148700215838286807040 }, { target := 235, numerator := 72654694962721915458646179840 }, { target := 237, numerator := 21354823774952529040232153088 }, { target := 406, numerator := 647181862608273583909109760 }, { target := 409, numerator := 2204046850126056921193512960 }, { target := 411, numerator := 647818177480898855275855872 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk3.Parent2
