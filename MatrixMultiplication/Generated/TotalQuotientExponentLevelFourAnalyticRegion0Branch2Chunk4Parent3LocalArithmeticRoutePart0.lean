import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk4Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 55; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk4.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left3.expected,
    Slot5.Left11.expected,
    Slot5.Left18.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 1139571849057342378876076032 }, { target := 37, numerator := 41681752886192963303988264960 }, { target := 40, numerator := 41681788617289099049837789184 }, { target := 47, numerator := 1135217759771086491784052736 }, { target := 86, numerator := 3350582550797344483949150208 }, { target := 89, numerator := 12035263201841327957948235776 }, { target := 91, numerator := 3352683901314428812566462464 }, { target := 122, numerator := 304118440014504570535280640 }, { target := 124, numerator := 304136530078554341924405248 }, { target := 145, numerator := 4046491146551320839809138688 }, { target := 147, numerator := 148007204781550114836200816640 }, { target := 150, numerator := 148007331658643726328404115456 }, { target := 157, numerator := 4031030266429806147035725824 }, { target := 161, numerator := 124237592298384393447942389760 }, { target := 164, numerator := 445784052694940943542533488640 }, { target := 166, numerator := 124305160010438534385023057920 }, { target := 197, numerator := 7608119216638626485011218432 }, { target := 199, numerator := 7608597018285330849498923008 }, { target := 216, numerator := 1139575242394123762931859456 }, { target := 218, numerator := 41681877003180670818378055680 }, { target := 221, numerator := 41681912734383204105424207872 }, { target := 228, numerator := 1135221140142567498593599488 }, { target := 232, numerator := 82587886908844310131302727680 }, { target := 235, numerator := 297893014521609969444574986240 }, { target := 237, numerator := 82655368854701805895312998400 }, { target := 242, numerator := 103037716929958916840944041984 }, { target := 244, numerator := 103044292708319386249791012864 }, { target := 406, numerator := 2179003625080677152461946880 }, { target := 409, numerator := 7872751247514929997063127040 }, { target := 411, numerator := 2181063264629921812033044480 }, { target := 416, numerator := 7588725409158688260986241024 }, { target := 418, numerator := 7589201307474977807738601472 }, { target := 498, numerator := 299781160072991647022972928 }, { target := 500, numerator := 299798822791035727179153408 }]

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
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left3.expected,
    Slot18.Left5.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot23.Left0.expected,
    Slot23.Left3.expected,
    Slot23.Left5.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 304118440014504570535280640 }, { target := 17, numerator := 7608119216638626485011218432 }, { target := 19, numerator := 103037716929958916840944041984 }, { target := 27, numerator := 7588725409158688260986241024 }, { target := 34, numerator := 299781160072991647022972928 }, { target := 35, numerator := 2211010701740002105073074176 }, { target := 37, numerator := 82555839412191430143954124800 }, { target := 40, numerator := 82587886908844310131302727680 }, { target := 47, numerator := 2179003625080677152461946880 }, { target := 126, numerator := 304136530078554341924405248 }, { target := 127, numerator := 7608597018285330849498923008 }, { target := 129, numerator := 103044292708319386249791012864 }, { target := 137, numerator := 7589201307474977807738601472 }, { target := 144, numerator := 299798822791035727179153408 }, { target := 145, numerator := 7988772055290007118139097088 }, { target := 147, numerator := 297776847913390828706332672000 }, { target := 150, numerator := 297893014521609969444574986240 }, { target := 157, numerator := 7872751247514929997063127040 }, { target := 216, numerator := 2213108658920305049634603008 }, { target := 218, numerator := 82623283007257863566645002240 }, { target := 221, numerator := 82655368854701805895312998400 }, { target := 228, numerator := 2181063264629921812033044480 }, { target := 232, numerator := 41681788617289099049837789184 }, { target := 235, numerator := 148007331658643726328404115456 }, { target := 237, numerator := 41681912734383204105424207872 }, { target := 406, numerator := 1135217759771086491784052736 }, { target := 409, numerator := 4031030266429806147035725824 }, { target := 411, numerator := 1135221140142567498593599488 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk4.Parent3
