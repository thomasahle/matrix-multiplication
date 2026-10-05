import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk7Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 71; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk7.Parent2

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
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 32281378357436753343676416 }, { target := 82, numerator := 1548362041105507503021490176 }, { target := 85, numerator := 1549243931631247203741204480 }, { target := 92, numerator := 32931767907202030702166016 }, { target := 131, numerator := 109786797936300107948359680 }, { target := 134, numerator := 387260028498980543876038656 }, { target := 136, numerator := 109706431116225713457332224 }, { target := 176, numerator := 1180745590226202309144084480 }, { target := 178, numerator := 56633940219835660570491617280 }, { target := 181, numerator := 56666196845863202365793894400 }, { target := 188, numerator := 1204534679536809233853972480 }, { target := 227, numerator := 2956978684421001014604201984 }, { target := 230, numerator := 10429827644943954100768210944 }, { target := 232, numerator := 2954791768878000317975756800 }, { target := 286, numerator := 1180746602403744636198715392 }, { target := 288, numerator := 56633988768483987962317504512 }, { target := 291, numerator := 56666245422163068519721205760 }, { target := 298, numerator := 1204535712107213623595630592 }, { target := 302, numerator := 36873770188242710589599645696 }, { target := 305, numerator := 130090092860814481815091806208 }, { target := 307, numerator := 36847651673723316745879420928 }, { target := 573, numerator := 32158037294064613686509568 }, { target := 575, numerator := 1542446041530755327666946048 }, { target := 578, numerator := 1543324562518985875170263040 }, { target := 585, numerator := 32805941827924252182970368 }, { target := 589, numerator := 2953503918381265445866962944 }, { target := 592, numerator := 10417509781036954630349651968 }, { target := 594, numerator := 2951317143574627204659675136 }, { target := 763, numerator := 108981861451532351328747520 }, { target := 766, numerator := 384407207473329538932408320 }, { target := 768, numerator := 108901552300332660293632000 }]

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
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 58445555965575416160190464 }, { target := 27, numerator := 498506212647555020189859840 }, { target := 28, numerator := 508820134288538917159305216 }, { target := 29, numerator := 61883529845903381816672256 }, { target := 30, numerator := 364425231314764359587069952 }, { target := 31, numerator := 61883529845903381816672256 }, { target := 32, numerator := 498506212647555020189859840 }, { target := 33, numerator := 508820134288538917159305216 }, { target := 34, numerator := 364425231314764359587069952 }, { target := 35, numerator := 8233947443385477747273891840 }, { target := 36, numerator := 364425231314764359587069952 }, { target := 37, numerator := 498506212647555020189859840 }, { target := 38, numerator := 498506212647555020189859840 }, { target := 39, numerator := 61883529845903381816672256 }, { target := 40, numerator := 364425231314764359587069952 }, { target := 41, numerator := 61883529845903381816672256 }, { target := 42, numerator := 508820134288538917159305216 }, { target := 43, numerator := 508820134288538917159305216 }, { target := 44, numerator := 55007582085247450503708672 }, { target := 131, numerator := 58445555965575416160190464 }, { target := 134, numerator := 211866524601592352176340992 }, { target := 136, numerator := 58515742368011367183548416 }, { target := 157, numerator := 211866524601592352176340992 }, { target := 158, numerator := 1807096827484170062680555520 }, { target := 159, numerator := 1844485037707980477770498048 }, { target := 160, numerator := 224329261342862490539655168 }, { target := 161, numerator := 1321050094574634666511302656 }, { target := 162, numerator := 224329261342862490539655168 }, { target := 163, numerator := 1807096827484170062680555520 }, { target := 164, numerator := 1844485037707980477770498048 }, { target := 165, numerator := 1321050094574634666511302656 }, { target := 166, numerator := 29848254495341981380137451520 }, { target := 167, numerator := 1321050094574634666511302656 }, { target := 168, numerator := 1807096827484170062680555520 }, { target := 169, numerator := 1807096827484170062680555520 }, { target := 170, numerator := 224329261342862490539655168 }, { target := 171, numerator := 1321050094574634666511302656 }, { target := 172, numerator := 224329261342862490539655168 }, { target := 173, numerator := 1844485037707980477770498048 }, { target := 174, numerator := 1844485037707980477770498048 }, { target := 175, numerator := 199403787860322213813026816 }, { target := 227, numerator := 498506212647555020189859840 }, { target := 230, numerator := 1807096827484170062680555520 }, { target := 232, numerator := 499104861374214602447912960 }, { target := 267, numerator := 58515742368011367183548416 }, { target := 268, numerator := 499104861374214602447912960 }, { target := 269, numerator := 509431168850922490774421504 }, { target := 270, numerator := 61957844860247329959051264 }, { target := 271, numerator := 364862864177012054203301888 }, { target := 272, numerator := 61957844860247329959051264 }, { target := 273, numerator := 499104861374214602447912960 }, { target := 274, numerator := 509431168850922490774421504 }, { target := 275, numerator := 364862864177012054203301888 }, { target := 276, numerator := 8243835468905130847329320960 }, { target := 277, numerator := 364862864177012054203301888 }, { target := 278, numerator := 499104861374214602447912960 }, { target := 279, numerator := 499104861374214602447912960 }, { target := 280, numerator := 61957844860247329959051264 }, { target := 281, numerator := 364862864177012054203301888 }, { target := 282, numerator := 61957844860247329959051264 }, { target := 283, numerator := 509431168850922490774421504 }, { target := 284, numerator := 509431168850922490774421504 }, { target := 285, numerator := 55073639875775404408045568 }]

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
    Slot13.Left2.expected,
    Slot13.Left3.expected,
    Slot13.Left4.expected,
    Slot13.Left5.expected,
    Slot13.Left6.expected,
    Slot13.Left7.expected,
    Slot13.Left8.expected,
    Slot13.Left9.expected,
    Slot13.Left10.expected,
    Slot13.Left11.expected,
    Slot13.Left12.expected,
    Slot13.Left13.expected,
    Slot13.Left14.expected,
    Slot13.Left15.expected,
    Slot13.Left16.expected,
    Slot13.Left17.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 32281378357436753343676416 }, { target := 82, numerator := 1180745590226202309144084480 }, { target := 85, numerator := 1180746602403744636198715392 }, { target := 92, numerator := 32158037294064613686509568 }, { target := 176, numerator := 1548362041105507503021490176 }, { target := 178, numerator := 56633940219835660570491617280 }, { target := 181, numerator := 56633988768483987962317504512 }, { target := 188, numerator := 1542446041530755327666946048 }, { target := 253, numerator := 508820134288538917159305216 }, { target := 256, numerator := 1844485037707980477770498048 }, { target := 258, numerator := 509431168850922490774421504 }, { target := 286, numerator := 1549243931631247203741204480 }, { target := 288, numerator := 56666196845863202365793894400 }, { target := 291, numerator := 56666245422163068519721205760 }, { target := 298, numerator := 1543324562518985875170263040 }, { target := 302, numerator := 61883529845903381816672256 }, { target := 305, numerator := 224329261342862490539655168 }, { target := 307, numerator := 61957844860247329959051264 }, { target := 328, numerator := 364425231314764359587069952 }, { target := 331, numerator := 1321050094574634666511302656 }, { target := 333, numerator := 364862864177012054203301888 }, { target := 342, numerator := 61883529845903381816672256 }, { target := 345, numerator := 224329261342862490539655168 }, { target := 347, numerator := 61957844860247329959051264 }, { target := 443, numerator := 498506212647555020189859840 }, { target := 446, numerator := 1807096827484170062680555520 }, { target := 448, numerator := 499104861374214602447912960 }, { target := 469, numerator := 508820134288538917159305216 }, { target := 472, numerator := 1844485037707980477770498048 }, { target := 474, numerator := 509431168850922490774421504 }, { target := 518, numerator := 364425231314764359587069952 }, { target := 521, numerator := 1321050094574634666511302656 }, { target := 523, numerator := 364862864177012054203301888 }, { target := 544, numerator := 8233947443385477747273891840 }, { target := 547, numerator := 29848254495341981380137451520 }, { target := 549, numerator := 8243835468905130847329320960 }, { target := 558, numerator := 364425231314764359587069952 }, { target := 561, numerator := 1321050094574634666511302656 }, { target := 563, numerator := 364862864177012054203301888 }, { target := 589, numerator := 498506212647555020189859840 }, { target := 592, numerator := 1807096827484170062680555520 }, { target := 594, numerator := 499104861374214602447912960 }, { target := 603, numerator := 498506212647555020189859840 }, { target := 606, numerator := 1807096827484170062680555520 }, { target := 608, numerator := 499104861374214602447912960 }, { target := 658, numerator := 61883529845903381816672256 }, { target := 661, numerator := 224329261342862490539655168 }, { target := 663, numerator := 61957844860247329959051264 }, { target := 684, numerator := 364425231314764359587069952 }, { target := 687, numerator := 1321050094574634666511302656 }, { target := 689, numerator := 364862864177012054203301888 }, { target := 698, numerator := 61883529845903381816672256 }, { target := 701, numerator := 224329261342862490539655168 }, { target := 703, numerator := 61957844860247329959051264 }, { target := 729, numerator := 508820134288538917159305216 }, { target := 732, numerator := 1844485037707980477770498048 }, { target := 734, numerator := 509431168850922490774421504 }, { target := 743, numerator := 508820134288538917159305216 }, { target := 746, numerator := 1844485037707980477770498048 }, { target := 748, numerator := 509431168850922490774421504 }, { target := 763, numerator := 55007582085247450503708672 }, { target := 766, numerator := 199403787860322213813026816 }, { target := 768, numerator := 55073639875775404408045568 }]

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

namespace RouteChunk3

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left3.expected,
    Slot18.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 109786797936300107948359680 }, { target := 27, numerator := 2956978684421001014604201984 }, { target := 29, numerator := 36873770188242710589599645696 }, { target := 37, numerator := 2953503918381265445866962944 }, { target := 44, numerator := 108981861451532351328747520 }, { target := 157, numerator := 387260028498980543876038656 }, { target := 158, numerator := 10429827644943954100768210944 }, { target := 160, numerator := 130090092860814481815091806208 }, { target := 168, numerator := 10417509781036954630349651968 }, { target := 175, numerator := 384407207473329538932408320 }, { target := 267, numerator := 109706431116225713457332224 }, { target := 268, numerator := 2954791768878000317975756800 }, { target := 270, numerator := 36847651673723316745879420928 }, { target := 278, numerator := 2951317143574627204659675136 }, { target := 285, numerator := 108901552300332660293632000 }, { target := 573, numerator := 32931767907202030702166016 }, { target := 575, numerator := 1204534679536809233853972480 }, { target := 578, numerator := 1204535712107213623595630592 }, { target := 585, numerator := 32805941827924252182970368 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk7.Parent2
