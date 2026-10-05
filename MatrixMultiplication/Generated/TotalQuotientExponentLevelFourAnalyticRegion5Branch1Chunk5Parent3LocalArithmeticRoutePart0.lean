import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk5Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 66; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk5.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 6690261988133241020743680 }, { target := 57, numerator := 183315820099492834965454848 }, { target := 59, numerator := 1952573121003691365302796288 }, { target := 67, numerator := 183809108743173149577707520 }, { target := 74, numerator := 6196278180073444567154688 }, { target := 110, numerator := 8810156193213908013547520 }, { target := 112, numerator := 299229397725888618325606400 }, { target := 115, numerator := 299229934701331188778270720 }, { target := 122, numerator := 8810442734740199461355520 }, { target := 152, numerator := 220549688097732983059906560 }, { target := 153, numerator := 6043148537088063638723362816 }, { target := 155, numerator := 64368091053716849312237879296 }, { target := 163, numerator := 6059410180757447608463523840 }, { target := 170, numerator := 204265127794091144140292096 }, { target := 206, numerator := 262522179344577835539890176 }, { target := 208, numerator := 8982886440597983662224441344 }, { target := 211, numerator := 8982903265144345693016555520 }, { target := 218, numerator := 262529646839681172224606208 }, { target := 283, numerator := 220550013167554086662307840 }, { target := 284, numerator := 6043157444129514466809217024 }, { target := 286, numerator := 64368185926323671317551775744 }, { target := 294, numerator := 6059419111767055653415157760 }, { target := 301, numerator := 204265428861978033671634944 }, { target := 302, numerator := 2829505209764044050263965696 }, { target := 304, numerator := 96915357771987378836187643904 }, { target := 307, numerator := 96915540303138107241057484800 }, { target := 314, numerator := 2829584144453792164749508608 }, { target := 660, numerator := 6690587057954344623144960 }, { target := 661, numerator := 183324727140943663051309056 }, { target := 663, numerator := 1952667993610513370616692736 }, { target := 671, numerator := 183818039752781194529341440 }, { target := 678, numerator := 6196579247960334098497536 }, { target := 679, numerator := 262762344442905736203206656 }, { target := 681, numerator := 8989753423439178154299621376 }, { target := 684, numerator := 8989770246651348795483226112 }, { target := 691, numerator := 262769840506593309112664064 }, { target := 966, numerator := 8316172385154111559958528 }, { target := 968, numerator := 282944837422246779405991936 }, { target := 971, numerator := 282945350395755135787597824 }, { target := 978, numerator := 8316434924746188936708096 }]

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
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 2119894205080666992803840 }, { target := 57, numerator := 79206359245085000574435328 }, { target := 59, numerator := 876932088760352684961169408 }, { target := 67, numerator := 78953235699732586625499136 }, { target := 74, numerator := 2119894205080666992803840 }, { target := 152, numerator := 78679709628155635265699840 }, { target := 153, numerator := 2939737903509920023501078528 }, { target := 155, numerator := 32547266718270529523949764608 }, { target := 163, numerator := 2930343242681730545836097536 }, { target := 170, numerator := 78679709628155635265699840 }, { target := 283, numerator := 78679921533777102115962880 }, { target := 284, numerator := 2939745821014831226207338496 }, { target := 286, numerator := 32547354376814435923505709056 }, { target := 294, numerator := 2930351134884293142068068352 }, { target := 301, numerator := 78679921533777102115962880 }, { target := 660, numerator := 2119855676785854838210560 }, { target := 661, numerator := 79204919698737509173297152 }, { target := 663, numerator := 876916150843278794132815872 }, { target := 671, numerator := 78951800753812114583322624 }, { target := 678, numerator := 2119855676785854838210560 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk5.Parent3
