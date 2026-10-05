import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk5Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 64; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk5.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 113619866686326077506191360 }, { target := 17, numerator := 3113229209579961294149124096 }, { target := 19, numerator := 33160300463157996336999038976 }, { target := 27, numerator := 3121606667747107697370071040 }, { target := 34, numerator := 105230602631119997843275776 }, { target := 35, numerator := 1483829317788100471885398016 }, { target := 37, numerator := 49713194747284822259623002112 }, { target := 40, numerator := 49713276719780308674934734848 }, { target := 47, numerator := 1483888580676989138472271872 }, { target := 86, numerator := 1877102943492643976934064128 }, { target := 89, numerator := 6494666881899795226105479168 }, { target := 91, numerator := 1876327404046152398461206528 }, { target := 122, numerator := 80799517144572974910668800 }, { target := 124, numerator := 80799863899226284302008320 }, { target := 126, numerator := 113620408469361250176860160 }, { target := 127, numerator := 3113244054649046007625547776 }, { target := 129, numerator := 33160458584169366345855533056 }, { target := 137, numerator := 3121621552763121105622794240 }, { target := 144, numerator := 105231104410931480395513856 }, { target := 145, numerator := 5069235097643315514381959168 }, { target := 147, numerator := 169827614095635217436792324096 }, { target := 150, numerator := 169827894034078873776107290624 }, { target := 157, numerator := 5069437696099896742920585216 }, { target := 161, numerator := 63400871144790448189514711040 }, { target := 164, numerator := 219504308824442394816729317376 }, { target := 166, numerator := 63373284110324701255975305216 }, { target := 197, numerator := 3018941023775723168422952960 }, { target := 199, numerator := 3018953979692850591033196544 }, { target := 216, numerator := 1484020826727607726180925440 }, { target := 218, numerator := 49720292203161005727277907968 }, { target := 221, numerator := 49720374194671252719301296128 }, { target := 228, numerator := 1484080086302972966929956864 }, { target := 232, numerator := 20822349642668189642857119744 }, { target := 235, numerator := 73974572940015934943810027520 }, { target := 237, numerator := 20794680220229061520801136640 }, { target := 242, numerator := 33424162946717465954547138560 }, { target := 244, numerator := 33424306387971130972002320384 }, { target := 406, numerator := 585530793412078071692918784 }, { target := 409, numerator := 2080187449024933220025630720 }, { target := 411, numerator := 584752720852925683901399040 }, { target := 416, numerator := 3009293249753142070366699520 }, { target := 418, numerator := 3009306164266426318746288128 }, { target := 498, numerator := 80799517144572974910668800 }, { target := 500, numerator := 80799863899226284302008320 }]

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
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left3.expected,
    Slot16.Left11.expected,
    Slot16.Left18.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected,
    Slot21.Left5.expected,
    Slot21.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 80799517144572974910668800 }, { target := 17, numerator := 3018941023775723168422952960 }, { target := 19, numerator := 33424162946717465954547138560 }, { target := 27, numerator := 3009293249753142070366699520 }, { target := 34, numerator := 80799517144572974910668800 }, { target := 35, numerator := 585507825215263643818524672 }, { target := 37, numerator := 20822433859389842545063231488 }, { target := 40, numerator := 20822349642668189642857119744 }, { target := 47, numerator := 585530793412078071692918784 }, { target := 86, numerator := 192234199510720138769858560 }, { target := 89, numerator := 654674066746150208940277760 }, { target := 91, numerator := 192423205858461258436575232 }, { target := 122, numerator := 113619866686326077506191360 }, { target := 124, numerator := 113620408469361250176860160 }, { target := 126, numerator := 80799863899226284302008320 }, { target := 127, numerator := 3018953979692850591033196544 }, { target := 129, numerator := 33424306387971130972002320384 }, { target := 137, numerator := 3009306164266426318746288128 }, { target := 144, numerator := 80799863899226284302008320 }, { target := 145, numerator := 2080105851002629920663797760 }, { target := 147, numerator := 73974872132764380374803415040 }, { target := 150, numerator := 73974572940015934943810027520 }, { target := 157, numerator := 2080187449024933220025630720 }, { target := 161, numerator := 7134757461884216615171522560 }, { target := 164, numerator := 24298177403957202994866421760 }, { target := 166, numerator := 7141772417877071753780396032 }, { target := 197, numerator := 3113229209579961294149124096 }, { target := 199, numerator := 3113244054649046007625547776 }, { target := 216, numerator := 584729783177005930716856320 }, { target := 218, numerator := 20794764325040767282477793280 }, { target := 221, numerator := 20794680220229061520801136640 }, { target := 228, numerator := 584752720852925683901399040 }, { target := 232, numerator := 49713276719780308674934734848 }, { target := 235, numerator := 169827894034078873776107290624 }, { target := 237, numerator := 49720374194671252719301296128 }, { target := 242, numerator := 33160300463157996336999038976 }, { target := 244, numerator := 33160458584169366345855533056 }, { target := 406, numerator := 1483888580676989138472271872 }, { target := 409, numerator := 5069437696099896742920585216 }, { target := 411, numerator := 1484080086302972966929956864 }, { target := 416, numerator := 3121606667747107697370071040 }, { target := 418, numerator := 3121621552763121105622794240 }, { target := 498, numerator := 105230602631119997843275776 }, { target := 500, numerator := 105231104410931480395513856 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk5.Parent1
