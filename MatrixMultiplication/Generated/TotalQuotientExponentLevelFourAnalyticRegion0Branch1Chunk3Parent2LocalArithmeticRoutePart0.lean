import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk3Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 46; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk3.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 11616816949328255784058880 }, { target := 30, numerator := 518262206419531966040768512 }, { target := 35, numerator := 518279640646323051647991808 }, { target := 43, numerator := 11615932604491026803982336 }, { target := 71, numerator := 972411914761002408738816 }, { target := 72, numerator := 40340984428384606926929920 }, { target := 74, numerator := 438934916410292321757691904 }, { target := 82, numerator := 40376205742093807363555328 }, { target := 89, numerator := 1003360835766402202730496 }, { target := 104, numerator := 422419622552215337733980160 }, { target := 105, numerator := 18845448505709330893356662784 }, { target := 110, numerator := 18846082462457784776792211456 }, { target := 118, numerator := 422387465325844488574205952 }, { target := 146, numerator := 17944449540759037623140352 }, { target := 147, numerator := 534644681905046116485824512 }, { target := 149, numerator := 5695113235736824993305067520 }, { target := 157, numerator := 536138126590346899157417984 }, { target := 164, numerator := 19266774579794023311998976 }, { target := 200, numerator := 10602922390502967735222272 }, { target := 202, numerator := 364249263030089340745154560 }, { target := 205, numerator := 364248726799992508622307328 }, { target := 212, numerator := 10603101133868578442838016 }, { target := 226, numerator := 422616380008120427835555840 }, { target := 227, numerator := 18854226465599002935470063616 }, { target := 232, numerator := 18854860717636099486613766144 }, { target := 240, numerator := 422584207803340167994933248 }, { target := 242, numerator := 172248138545634637831471104 }, { target := 243, numerator := 5132035453764704100023271424 }, { target := 245, numerator := 54667191179873871799034839040 }, { target := 253, numerator := 5146370976650464892989472768 }, { target := 260, numerator := 184941089979375052130353152 }, { target := 296, numerator := 549648681723291330053931008 }, { target := 298, numerator := 18882447675227371105775779840 }, { target := 301, numerator := 18882419877403811808010043392 }, { target := 308, numerator := 549657947664477762642509824 }, { target := 624, numerator := 11813988522478081671168000 }, { target := 625, numerator := 527058641362904975356723200 }, { target := 630, numerator := 527076371499835477249228800 }, { target := 638, numerator := 11813089167706244618649600 }, { target := 640, numerator := 17944599014104770143059968 }, { target := 641, numerator := 534649135378483734441361408 }, { target := 643, numerator := 5695160674786305868751175680 }, { target := 651, numerator := 536142592503852587817107456 }, { target := 658, numerator := 19266935067818544473309184 }, { target := 659, numerator := 549750332356201868974620672 }, { target := 661, numerator := 18885939747201544025077186560 }, { target := 664, numerator := 18885911944237125752668028928 }, { target := 671, numerator := 549759600011007959777673216 }, { target := 1017, numerator := 420829748797765457018880 }, { target := 1018, numerator := 12538383340826885651169280 }, { target := 1020, numerator := 133560690559281412230348800 }, { target := 1028, numerator := 12573407315807613967400960 }, { target := 1035, numerator := 451840659037286238781440 }, { target := 1036, numerator := 10507015485864640606371840 }, { target := 1038, numerator := 360954509183234996384563200 }, { target := 1041, numerator := 360953977803514962939740160 }, { target := 1048, numerator := 10507192612437985087979520 }]

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
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left6.expected,
    Slot13.Left14.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 10602922390502967735222272 }, { target := 30, numerator := 549648681723291330053931008 }, { target := 35, numerator := 549750332356201868974620672 }, { target := 43, numerator := 10507015485864640606371840 }, { target := 71, numerator := 420867117134198586998784 }, { target := 72, numerator := 17944449540759037623140352 }, { target := 74, numerator := 172248138545634637831471104 }, { target := 82, numerator := 17944599014104770143059968 }, { target := 89, numerator := 420829748797765457018880 }, { target := 104, numerator := 364249263030089340745154560 }, { target := 105, numerator := 18882447675227371105775779840 }, { target := 110, numerator := 18885939747201544025077186560 }, { target := 118, numerator := 360954509183234996384563200 }, { target := 146, numerator := 40340984428384606926929920 }, { target := 147, numerator := 1936022634750362813118545920 }, { target := 149, numerator := 20524308406474199423575392256 }, { target := 157, numerator := 1936036878629148194303377408 }, { target := 164, numerator := 40336607591575948028280832 }, { target := 200, numerator := 11616816949328255784058880 }, { target := 202, numerator := 422419622552215337733980160 }, { target := 205, numerator := 422616380008120427835555840 }, { target := 212, numerator := 11813988522478081671168000 }, { target := 226, numerator := 364248726799992508622307328 }, { target := 227, numerator := 18882419877403811808010043392 }, { target := 232, numerator := 18885911944237125752668028928 }, { target := 240, numerator := 360953977803514962939740160 }, { target := 242, numerator := 305362366088640690665816064 }, { target := 243, numerator := 15392272952709495323552120832 }, { target := 245, numerator := 169063646370112124177904304128 }, { target := 253, numerator := 15392380487290815422398464000 }, { target := 260, numerator := 305326521228200657717035008 }, { target := 296, numerator := 518262206419531966040768512 }, { target := 298, numerator := 18845448505709330893356662784 }, { target := 301, numerator := 18854226465599002935470063616 }, { target := 308, numerator := 527058641362904975356723200 }, { target := 624, numerator := 10603101133868578442838016 }, { target := 625, numerator := 549657947664477762642509824 }, { target := 630, numerator := 549759600011007959777673216 }, { target := 638, numerator := 10507192612437985087979520 }, { target := 640, numerator := 27801681947909771231232000 }, { target := 641, numerator := 1401387743250664459862016000 }, { target := 643, numerator := 15392380487290815422398464000 }, { target := 651, numerator := 1401397533724410642432000000 }, { target := 658, numerator := 27798418456661043707904000 }, { target := 659, numerator := 518279640646323051647991808 }, { target := 661, numerator := 18846082462457784776792211456 }, { target := 664, numerator := 18854860717636099486613766144 }, { target := 671, numerator := 527076371499835477249228800 }, { target := 1017, numerator := 551480054722985673621504 }, { target := 1018, numerator := 27798224250749062377111552 }, { target := 1020, numerator := 305326521228200657717035008 }, { target := 1028, numerator := 27798418456661043707904000 }, { target := 1035, numerator := 551415319418991896690688 }, { target := 1036, numerator := 11615932604491026803982336 }, { target := 1038, numerator := 422387465325844488574205952 }, { target := 1041, numerator := 422584207803340167994933248 }, { target := 1048, numerator := 11813089167706244618649600 }]

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
    Slot18.Left3.expected,
    Slot18.Left11.expected,
    Slot18.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 242, numerator := 133572550321651631091875840 }, { target := 243, numerator := 5695113235736824993305067520 }, { target := 245, numerator := 54667191179873871799034839040 }, { target := 253, numerator := 5695160674786305868751175680 }, { target := 260, numerator := 133560690559281412230348800 }, { target := 640, numerator := 12574523794184036132323328 }, { target := 641, numerator := 536138126590346899157417984 }, { target := 643, numerator := 5146370976650464892989472768 }, { target := 651, numerator := 536142592503852587817107456 }, { target := 658, numerator := 12573407315807613967400960 }, { target := 1017, numerator := 451880781043416529108992 }, { target := 1018, numerator := 19266774579794023311998976 }, { target := 1020, numerator := 184941089979375052130353152 }, { target := 1028, numerator := 19266935067818544473309184 }, { target := 1035, numerator := 451840659037286238781440 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk3.Parent2
