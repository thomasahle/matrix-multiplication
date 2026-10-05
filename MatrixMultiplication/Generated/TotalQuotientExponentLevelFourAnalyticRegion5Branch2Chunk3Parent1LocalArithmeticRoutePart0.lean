import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk3Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 53; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk3.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left6.expected,
    Slot10.Left14.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 6970063199227635008798720 }, { target := 57, numerator := 176424587853536547636772864 }, { target := 59, numerator := 1882874651391132199114768384 }, { target := 67, numerator := 176590710933345012381908992 }, { target := 74, numerator := 6601481805851146240131072 }, { target := 110, numerator := 12798920796609844900528128 }, { target := 112, numerator := 483316553172879880474329088 }, { target := 115, numerator := 483316653247367200274120704 }, { target := 122, numerator := 12798461598332839136329728 }, { target := 152, numerator := 238521807233310928142336000 }, { target := 153, numerator := 6037407457063037129929523200 }, { target := 155, numerator := 64433657458567872049787699200 }, { target := 163, numerator := 6043092337685564248136089600 }, { target := 170, numerator := 225908621735871825680793600 }, { target := 206, numerator := 308273114527420434956156928 }, { target := 208, numerator := 11764417870998095265288683520 }, { target := 211, numerator := 11764416596591990710122577920 }, { target := 218, numerator := 308262519831815044001169408 }, { target := 257, numerator := 135791759662118926936965120 }, { target := 260, numerator := 487532469907565065745203200 }, { target := 262, numerator := 135607287892296689610915840 }, { target := 302, numerator := 3418937395560402218668523520 }, { target := 304, numerator := 129921601484408346759082803200 }, { target := 307, numerator := 129921603873793129060499456000 }, { target := 314, numerator := 3418817806539610808616222720 }, { target := 353, numerator := 6952213634270458235527888896 }, { target := 356, numerator := 24960497550621668339676610560 }, { target := 358, numerator := 6942769120431862414439350272 }, { target := 679, numerator := 307842691733958426573668352 }, { target := 681, numerator := 11749023648888008038919700480 }, { target := 684, numerator := 11749022345433685887213895680 }, { target := 691, numerator := 307832115725476739439132672 }, { target := 695, numerator := 6952178991359960152794988544 }, { target := 698, numerator := 24960373172354813693620387840 }, { target := 700, numerator := 6942734524583417487774711808 }, { target := 966, numerator := 12636918745210554735919104 }, { target := 968, numerator := 477547265194986808165793792 }, { target := 971, numerator := 477547353596143893821259776 }, { target := 978, numerator := 12636466673879959285530624 }, { target := 982, numerator := 135708109707501605216059392 }, { target := 985, numerator := 487232141897355066731397120 }, { target := 987, numerator := 135523751575319915469471744 }]

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
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 135791759662118926936965120 }, { target := 15, numerator := 6952213634270458235527888896 }, { target := 20, numerator := 6952178991359960152794988544 }, { target := 28, numerator := 135708109707501605216059392 }, { target := 56, numerator := 10501038038223216841850880 }, { target := 57, numerator := 242281618043201436845604864 }, { target := 59, numerator := 2734785645262123358025154560 }, { target := 67, numerator := 241854277160917729988837376 }, { target := 74, numerator := 10338057602322878573838336 }, { target := 110, numerator := 6970063199227635008798720 }, { target := 112, numerator := 238521807233310928142336000 }, { target := 115, numerator := 238522509592190814708039680 }, { target := 122, numerator := 6970063199227635008798720 }, { target := 136, numerator := 487532469907565065745203200 }, { target := 137, numerator := 24960497550621668339676610560 }, { target := 142, numerator := 24960373172354813693620387840 }, { target := 150, numerator := 487232141897355066731397120 }, { target := 152, numerator := 374702258209970641510072320 }, { target := 153, numerator := 8645190034842857759462916096 }, { target := 155, numerator := 97583720130330508820050083840 }, { target := 163, numerator := 8629941485791392790178955264 }, { target := 170, numerator := 368886724816641932031688704 }, { target := 206, numerator := 176424587853536547636772864 }, { target := 208, numerator := 6037407457063037129929523200 }, { target := 211, numerator := 6037425235004551776453001216 }, { target := 218, numerator := 176424587853536547636772864 }, { target := 267, numerator := 135607287892296689610915840 }, { target := 268, numerator := 6942769120431862414439350272 }, { target := 273, numerator := 6942734524583417487774711808 }, { target := 281, numerator := 135523751575319915469471744 }, { target := 283, numerator := 613225502519404665440829440 }, { target := 284, numerator := 14682632221360378161443897344 }, { target := 286, numerator := 162017758664723342114701705216 }, { target := 294, numerator := 14673068539771922199189913600 }, { target := 301, numerator := 594796735084336470074327040 }, { target := 302, numerator := 1882874651391132199114768384 }, { target := 304, numerator := 64433657458567872049787699200 }, { target := 307, numerator := 64433847191959567038567940096 }, { target := 314, numerator := 1882874651391132199114768384 }, { target := 660, numerator := 17470642039173846086451200 }, { target := 661, numerator := 418695611201132593527390208 }, { target := 663, numerator := 4617540707632464147087622144 }, { target := 671, numerator := 418434412085781055236210688 }, { target := 678, numerator := 16939087336843429363580928 }, { target := 679, numerator := 176590710933345012381908992 }, { target := 681, numerator := 6043092337685564248136089600 }, { target := 684, numerator := 6043110132366958709595701248 }, { target := 691, numerator := 176590710933345012381908992 }, { target := 966, numerator := 6601481805851146240131072 }, { target := 968, numerator := 225908621735871825680793600 }, { target := 971, numerator := 225909286953565585322016768 }, { target := 978, numerator := 6601481805851146240131072 }]

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
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 2297882758386628058677248 }, { target := 57, numerator := 65991496484218998110552064 }, { target := 59, numerator := 684151750298278860643368960 }, { target := 67, numerator := 65988414573040696584830976 }, { target := 74, numerator := 2298861142887676162080768 }, { target := 152, numerator := 108614294962909238964256768 }, { target := 153, numerator := 3119227836155237505825767424 }, { target := 155, numerator := 32337881354077837939032719360 }, { target := 163, numerator := 3119082163096615248740745216 }, { target := 170, numerator := 108660540378344876134105088 }, { target := 283, numerator := 108613660320153349541330944 }, { target := 284, numerator := 3119209610236164325131681792 }, { target := 286, numerator := 32337692401029353984365690880 }, { target := 294, numerator := 3119063938028722397619683328 }, { target := 301, numerator := 108659905465373009068949504 }, { target := 660, numerator := 2297882758386628058677248 }, { target := 661, numerator := 65991496484218998110552064 }, { target := 663, numerator := 684151750298278860643368960 }, { target := 671, numerator := 65988414573040696584830976 }, { target := 678, numerator := 2298861142887676162080768 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk3.Parent1
