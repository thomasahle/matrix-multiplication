import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk2Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 43; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk2.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot18.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 90199345953539951928803328 }, { target := 17, numerator := 3014659488992110744864555008 }, { target := 19, numerator := 33404358864660463551239946240 }, { target := 27, numerator := 3014624071327931715538649088 }, { target := 34, numerator := 90145038868465440295747584 }, { target := 35, numerator := 816877828315971749205245952 }, { target := 37, numerator := 28490435231268974814249877504 }, { target := 40, numerator := 28490359240421580900155785216 }, { target := 47, numerator := 816911891715936155854700544 }, { target := 86, numerator := 912655385876671403246223360 }, { target := 89, numerator := 3111978659568709041033052160 }, { target := 91, numerator := 913247076602986768034168832 }, { target := 122, numerator := 90199345953539951928803328 }, { target := 124, numerator := 90199776058563364879597568 }, { target := 145, numerator := 2782280181966800795650228224 }, { target := 147, numerator := 97037620253219937304736432128 }, { target := 150, numerator := 97037361473620982849760919552 }, { target := 157, numerator := 2782396203843671877513904128 }, { target := 161, numerator := 35691788489629501221991612416 }, { target := 164, numerator := 121728334057377802416352657408 }, { target := 166, numerator := 35712837074321597140561821696 }, { target := 197, numerator := 3014659488992110744864555008 }, { target := 199, numerator := 3014673864043020347819163648 }, { target := 216, numerator := 817477744119408968060633088 }, { target := 218, numerator := 28511747126433170426670612480 }, { target := 221, numerator := 28511671050995509136606625792 }, { target := 228, numerator := 817511831135405395710836736 }, { target := 232, numerator := 35691505032206796669308633088 }, { target := 235, numerator := 121727366288517194195920748544 }, { target := 237, numerator := 35712553531497977278982258688 }, { target := 242, numerator := 33404358864660463551239946240 }, { target := 244, numerator := 33404518149435754269837885440 }, { target := 406, numerator := 912778333664331982681669632 }, { target := 409, numerator := 3112398594287879461573492736 }, { target := 411, numerator := 913370047770240388033413120 }, { target := 416, numerator := 3014624071327931715538649088 }, { target := 418, numerator := 3014638446209956332466864128 }, { target := 498, numerator := 90145038868465440295747584 }, { target := 500, numerator := 90145468714531874672738304 }]

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
    Slot18.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 311473578324953072979148800 }, { target := 37, numerator := 14311940285872730130062770176 }, { target := 40, numerator := 14311743299644378543678291968 }, { target := 47, numerator := 311572943059608297969549312 }, { target := 86, numerator := 215696020764253418938171392 }, { target := 89, numerator := 734891424891155760455614464 }, { target := 91, numerator := 215704849351872838323142656 }, { target := 126, numerator := 90199776058563364879597568 }, { target := 127, numerator := 3014673864043020347819163648 }, { target := 129, numerator := 33404518149435754269837885440 }, { target := 137, numerator := 3014638446209956332466864128 }, { target := 144, numerator := 90145468714531874672738304 }, { target := 145, numerator := 1064589902493064005838438400 }, { target := 147, numerator := 48916981001605475071707578368 }, { target := 150, numerator := 48916307719618729773077889024 }, { target := 157, numerator := 1064929522610271811341910016 }, { target := 161, numerator := 7110587027512203722321035264 }, { target := 164, numerator := 24226267197447609960091353088 }, { target := 166, numerator := 7110878068767278660900093952 }, { target := 216, numerator := 311474181835450638296678400 }, { target := 218, numerator := 14311968016655705374791303168 }, { target := 221, numerator := 14311771030045673719987175424 }, { target := 228, numerator := 311573546762634747357167616 }, { target := 232, numerator := 7110597507859162774525444096 }, { target := 235, numerator := 24226302904722518426918060032 }, { target := 237, numerator := 7110888549543205577611542528 }, { target := 406, numerator := 215706501111212471142580224 }, { target := 409, numerator := 734927132166064227282321408 }, { target := 411, numerator := 215715330127799755034591232 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk2.Parent0
