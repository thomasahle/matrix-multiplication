import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk8Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 73; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk8.Parent0

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
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot15.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 104438683326226869931474944 }, { target := 17, numerator := 3111691250194265799303102464 }, { target := 19, numerator := 33146189655086087231965757440 }, { target := 27, numerator := 3120383263632687907678978048 }, { target := 34, numerator := 112134761475207183646851072 }, { target := 35, numerator := 441110213891233501151232000 }, { target := 37, numerator := 21516670556509419114206330880 }, { target := 40, numerator := 21508649181216766306843361280 }, { target := 47, numerator := 441023849981067908119265280 }, { target := 86, numerator := 1215476822905121732034560000 }, { target := 89, numerator := 4230007747437696797978394624 }, { target := 91, numerator := 1216834786056159807114575872 }, { target := 122, numerator := 164783019001873823434801152 }, { target := 124, numerator := 164885385167256108933316608 }, { target := 145, numerator := 1505583694956230259140198400 }, { target := 147, numerator := 73440032308145994613817081856 }, { target := 150, numerator := 73412653998890338453957902336 }, { target := 157, numerator := 1505288920337816995428827136 }, { target := 161, numerator := 42142918563361512333015777280 }, { target := 164, numerator := 146671818960619340011937988608 }, { target := 166, numerator := 42189556505275520491416715264 }, { target := 197, numerator := 6153442916474780219152007168 }, { target := 199, numerator := 6156510354881941527326621696 }, { target := 216, numerator := 441170703215572342013952000 }, { target := 218, numerator := 21519621131723951801295175680 }, { target := 221, numerator := 21511598656462274380777390080 }, { target := 228, numerator := 441084327462347103881134080 }, { target := 232, numerator := 42146127939562594105462620160 }, { target := 235, numerator := 146683066760434294907325120512 }, { target := 237, numerator := 42192765702271899166327177216 }, { target := 242, numerator := 66555786121683637505785593856 }, { target := 244, numerator := 66588475108737390289373626368 }, { target := 406, numerator := 1218762041187598302529454080 }, { target := 409, numerator := 4241519339563749619678576640 }, { target := 411, numerator := 1220119916910538286442741760 }, { target := 416, numerator := 6162156180412912028297986048 }, { target := 418, numerator := 6165232067998564448309608448 }, { target := 498, numerator := 172472013650950903560142848 }, { target := 500, numerator := 172581860519368332914196480 }]

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
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 60344335675646953503326208 }, { target := 17, numerator := 3041751666280514419848904704 }, { target := 19, numerator := 33409596466597550273819836416 }, { target := 27, numerator := 3041772916780224120619008000 }, { target := 34, numerator := 60337252175743719913291776 }, { target := 35, numerator := 1215476822905121732034560000 }, { target := 37, numerator := 42142918563361512333015777280 }, { target := 40, numerator := 42146127939562594105462620160 }, { target := 47, numerator := 1218762041187598302529454080 }, { target := 86, numerator := 441110213891233501151232000 }, { target := 89, numerator := 1505583694956230259140198400 }, { target := 91, numerator := 441170703215572342013952000 }, { target := 126, numerator := 164885385167256108933316608 }, { target := 127, numerator := 6156510354881941527326621696 }, { target := 129, numerator := 66588475108737390289373626368 }, { target := 137, numerator := 6165232067998564448309608448 }, { target := 144, numerator := 172581860519368332914196480 }, { target := 145, numerator := 4230007747437696797978394624 }, { target := 147, numerator := 146671818960619340011937988608 }, { target := 150, numerator := 146683066760434294907325120512 }, { target := 157, numerator := 4241519339563749619678576640 }, { target := 161, numerator := 21516670556509419114206330880 }, { target := 164, numerator := 73440032308145994613817081856 }, { target := 166, numerator := 21519621131723951801295175680 }, { target := 216, numerator := 1216834786056159807114575872 }, { target := 218, numerator := 42189556505275520491416715264 }, { target := 221, numerator := 42192765702271899166327177216 }, { target := 228, numerator := 1220119916910538286442741760 }, { target := 232, numerator := 21508649181216766306843361280 }, { target := 235, numerator := 73412653998890338453957902336 }, { target := 237, numerator := 21511598656462274380777390080 }, { target := 406, numerator := 441023849981067908119265280 }, { target := 409, numerator := 1505288920337816995428827136 }, { target := 411, numerator := 441084327462347103881134080 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk8.Parent0
