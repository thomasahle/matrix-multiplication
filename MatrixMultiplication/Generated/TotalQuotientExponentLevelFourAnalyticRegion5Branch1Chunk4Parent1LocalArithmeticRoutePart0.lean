import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk4Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 57; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk4.Parent1

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
    Slot10.Left1.expected,
    Slot10.Left6.expected,
    Slot10.Left14.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 13156055398131795473989632 }, { target := 30, numerator := 570150883626483363285565440 }, { target := 35, numerator := 569835904646140140976078848 }, { target := 43, numerator := 13149451336526717981294592 }, { target := 71, numerator := 926990773180439514316800 }, { target := 72, numerator := 30017699162293934772715520 }, { target := 74, numerator := 327005667625949241823723520 }, { target := 82, numerator := 29996530622749427588136960 }, { target := 89, numerator := 892768015313543196835840 }, { target := 104, numerator := 433699594993600008074297344 }, { target := 105, numerator := 18795467169373791304789524480 }, { target := 110, numerator := 18785083642391550779579170816 }, { target := 118, numerator := 433481886968150250869489664 }, { target := 146, numerator := 17317742560321555692257280 }, { target := 147, numerator := 474512983997961210123255808 }, { target := 149, numerator := 5054235349784942592076546048 }, { target := 157, numerator := 475789861608186082932817920 }, { target := 164, numerator := 16039065517162318631272448 }, { target := 200, numerator := 13156055398131795473989632 }, { target := 202, numerator := 433699594993600008074297344 }, { target := 205, numerator := 433700234226649817694601216 }, { target := 212, numerator := 13156694631181605094293504 }, { target := 226, numerator := 433700234226649817694601216 }, { target := 227, numerator := 18795494872152258166621470720 }, { target := 232, numerator := 18785111329865660207699329024 }, { target := 240, numerator := 433482525880318587039645696 }, { target := 242, numerator := 191733142398906665093038080 }, { target := 243, numerator := 5253563806836143604983922688 }, { target := 245, numerator := 55957895358614838749930979328 }, { target := 253, numerator := 5267700739280684769733509120 }, { target := 260, numerator := 177576287558023136808009728 }, { target := 296, numerator := 570150883626483363285565440 }, { target := 298, numerator := 18795467169373791304789524480 }, { target := 301, numerator := 18795494872152258166621470720 }, { target := 308, numerator := 570178586404950225117511680 }, { target := 624, numerator := 13156694631181605094293504 }, { target := 625, numerator := 570178586404950225117511680 }, { target := 630, numerator := 569863592120249569096237056 }, { target := 638, numerator := 13150090248695054151450624 }, { target := 640, numerator := 17262399423278667383439360 }, { target := 641, numerator := 472996560190957728506576896 }, { target := 643, numerator := 5038083288473496187385675776 }, { target := 651, numerator := 474269357222416429917143040 }, { target := 658, numerator := 15987808709419375920152576 }, { target := 659, numerator := 569835904646140140976078848 }, { target := 661, numerator := 18785083642391550779579170816 }, { target := 664, numerator := 18785111329865660207699329024 }, { target := 671, numerator := 569863592120249569096237056 }, { target := 1017, numerator := 463495386590219757158400 }, { target := 1018, numerator := 12699956601972379080458240 }, { target := 1020, numerator := 135272525227042576730685440 }, { target := 1028, numerator := 12734131199470760204697600 }, { target := 1035, numerator := 429272628723323439677440 }, { target := 1036, numerator := 13149451336526717981294592 }, { target := 1038, numerator := 433481886968150250869489664 }, { target := 1041, numerator := 433482525880318587039645696 }, { target := 1048, numerator := 13150090248695054151450624 }]

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
    Slot14.Left1.expected,
    Slot14.Left3.expected,
    Slot14.Left11.expected,
    Slot14.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 146, numerator := 12699956601972379080458240 }, { target := 147, numerator := 474512983997961210123255808 }, { target := 149, numerator := 5253563806836143604983922688 }, { target := 157, numerator := 472996560190957728506576896 }, { target := 164, numerator := 12699956601972379080458240 }, { target := 242, numerator := 135272525227042576730685440 }, { target := 243, numerator := 5054235349784942592076546048 }, { target := 245, numerator := 55957895358614838749930979328 }, { target := 253, numerator := 5038083288473496187385675776 }, { target := 260, numerator := 135272525227042576730685440 }, { target := 640, numerator := 12734131199470760204697600 }, { target := 641, numerator := 475789861608186082932817920 }, { target := 643, numerator := 5267700739280684769733509120 }, { target := 651, numerator := 474269357222416429917143040 }, { target := 658, numerator := 12734131199470760204697600 }, { target := 1017, numerator := 429272628723323439677440 }, { target := 1018, numerator := 16039065517162318631272448 }, { target := 1020, numerator := 177576287558023136808009728 }, { target := 1028, numerator := 15987808709419375920152576 }, { target := 1035, numerator := 429272628723323439677440 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk4.Parent1
