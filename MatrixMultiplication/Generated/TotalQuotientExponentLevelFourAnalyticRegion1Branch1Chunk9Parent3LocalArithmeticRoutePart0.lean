import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk9Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 41; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk9.Parent3

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
  [{ target := 0, numerator := 14814918405095476441148030976 }, { target := 2, numerator := 579396314618986504119367237632 }, { target := 5, numerator := 579396272117688158292560314368 }, { target := 12, numerator := 14814932572194925050083672064 }, { target := 16, numerator := 720254838218782947088082665472 }, { target := 19, numerator := 2672382531182151544100582588416 }, { target := 21, numerator := 720108926114920127094950199296 }, { target := 26, numerator := 3811753026770164662730915577856 }, { target := 28, numerator := 3811753932353279676448008830976 }, { target := 30, numerator := 29582874775533453852729671680 }, { target := 33, numerator := 106408720834344624627688407040 }, { target := 35, numerator := 29582884644541533287339786240 }, { target := 40, numerator := 140515882616244118667327963136 }, { target := 42, numerator := 140515849114651037801568534528 }, { target := 44, numerator := 37176886804789076380564324352 }, { target := 45, numerator := 7292241413218257655390273536 }, { target := 47, numerator := 7292239674612628708265033728 }, { target := 49, numerator := 41973904457019924945798430720 }, { target := 50, numerator := 720254838218782947088082665472 }, { target := 53, numerator := 2672382531182151544100582588416 }, { target := 55, numerator := 720108926114920127094950199296 }, { target := 60, numerator := 151173773912486187548282978304 }, { target := 62, numerator := 151173737869854110529032814592 }, { target := 64, numerator := 35977632391731364239255797760 }, { target := 65, numerator := 226339954633351304919228874752 }, { target := 67, numerator := 226339900669707360291149316096 }, { target := 69, numerator := 473705493157796295816868003840 }, { target := 70, numerator := 41973904457019924945798430720 }, { target := 71, numerator := 7011770589632940053259878400 }, { target := 73, numerator := 7011768917896758373331763200 }, { target := 75, numerator := 35977632391731364239255797760 }, { target := 76, numerator := 41973904457019924945798430720 }, { target := 77, numerator := 29582874775533453852729671680 }, { target := 80, numerator := 106408720834344624627688407040 }, { target := 82, numerator := 29582884644541533287339786240 }, { target := 87, numerator := 226339954633351304919228874752 }, { target := 89, numerator := 226339900669707360291149316096 }, { target := 91, numerator := 41973904457019924945798430720 }, { target := 92, numerator := 235875962635252103391662309376 }, { target := 94, numerator := 235875906398046951678880514048 }, { target := 96, numerator := 1740118153346740317038672084992 }, { target := 97, numerator := 43173158870077637087106957312 }, { target := 98, numerator := 140515882616244118667327963136 }, { target := 100, numerator := 140515849114651037801568534528 }, { target := 102, numerator := 473705493157796295816868003840 }, { target := 103, numerator := 1740118153346740317038672084992 }, { target := 104, numerator := 37176886804789076380564324352 }, { target := 105, numerator := 7011770589632940053259878400 }, { target := 107, numerator := 7011768917896758373331763200 }, { target := 109, numerator := 41973904457019924945798430720 }, { target := 110, numerator := 43173158870077637087106957312 }, { target := 111, numerator := 41973904457019924945798430720 }]

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
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 350447369210634867056870162432 }, { target := 1, numerator := 42650902916004117283633889280 }, { target := 2, numerator := 12479621443611246016201719021568 }, { target := 3, numerator := 481345904337760752201011036160 }, { target := 4, numerator := 42650902916004117283633889280 }, { target := 5, numerator := 12479620031623667638177800126464 }, { target := 6, numerator := 42650902916004117283633889280 }, { target := 7, numerator := 42650902916004117283633889280 }, { target := 8, numerator := 1768184575174913547958650667008 }, { target := 9, numerator := 43869500142175663491737714688 }, { target := 10, numerator := 481345904337760752201011036160 }, { target := 11, numerator := 1768184575174913547958650667008 }, { target := 12, numerator := 350448346740496821073429397504 }, { target := 13, numerator := 42650902916004117283633889280 }, { target := 14, numerator := 43869500142175663491737714688 }, { target := 15, numerator := 42650902916004117283633889280 }, { target := 16, numerator := 9380678207245176254002142117888 }, { target := 19, numerator := 33844498785042824739843282567168 }, { target := 21, numerator := 9382309184541786983339476910080 }, { target := 26, numerator := 6318716927077666186061626212352 }, { target := 28, numerator := 6318720965626046151270370115584 }, { target := 44, numerator := 332289142839562719284846133248 }, { target := 50, numerator := 9380683115845104263923012468736 }, { target := 53, numerator := 33844516431961078272579994648576 }, { target := 55, numerator := 9382314094307069810538457333760 }, { target := 60, numerator := 36597213638718422067667588349952 }, { target := 62, numerator := 36597231419139082740665604374528 }, { target := 64, numerator := 13215726864328497221214849204224 }, { target := 71, numerator := 10125240474650662121298307579904 }, { target := 73, numerator := 10125245421561229351082675666944 }, { target := 75, numerator := 13215725424006719945973059026944 }, { target := 104, numerator := 332290148703623570519276650496 }]

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

namespace RouteChunk2

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot18.Left0.expected,
    Slot18.Left3.expected,
    Slot18.Left5.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot19.Left5.expected,
    Slot19.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 7195527336119872275345309696 }, { target := 17, numerator := 150206633141502333747833339904 }, { target := 18, numerator := 7795154614129861631624085504 }, { target := 19, numerator := 161599551423692131517130080256 }, { target := 20, numerator := 241949606677030705258486038528 }, { target := 21, numerator := 7495340975124866953484697600 }, { target := 22, numerator := 241949606677030705258486038528 }, { target := 23, numerator := 252143270403200524315225227264 }, { target := 24, numerator := 150206633141502333747833339904 }, { target := 25, numerator := 7495340975124866953484697600 }, { target := 26, numerator := 27039300495767960624270671872 }, { target := 27, numerator := 29582874775533453852729671680 }, { target := 28, numerator := 27039300495767960624270671872 }, { target := 29, numerator := 29582874775533453852729671680 }, { target := 44, numerator := 2970656582080461887772819456 }, { target := 50, numerator := 7195525620572673420357009408 }, { target := 51, numerator := 150206597329454557649952571392 }, { target := 52, numerator := 7795152755620396205386760192 }, { target := 53, numerator := 161599512895361290565517836288 }, { target := 54, numerator := 241949548991756143759504441344 }, { target := 55, numerator := 7495339188096534812871884800 }, { target := 56, numerator := 241949548991756143759504441344 }, { target := 57, numerator := 252143210287567431105010204672 }, { target := 58, numerator := 150206597329454557649952571392 }, { target := 59, numerator := 7495339188096534812871884800 }, { target := 60, numerator := 97259559790643965313905852416 }, { target := 61, numerator := 106408720834344624627688407040 }, { target := 62, numerator := 97259559790643965313905852416 }, { target := 63, numerator := 106408720834344624627688407040 }, { target := 64, numerator := 115871601356415493111478747136 }, { target := 71, numerator := 27039309516225812668241412096 }, { target := 72, numerator := 29582884644541533287339786240 }, { target := 73, numerator := 27039309516225812668241412096 }, { target := 74, numerator := 29582884644541533287339786240 }, { target := 75, numerator := 115871558855117147284671823872 }, { target := 104, numerator := 2970670749179910496708460544 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk9.Parent3
