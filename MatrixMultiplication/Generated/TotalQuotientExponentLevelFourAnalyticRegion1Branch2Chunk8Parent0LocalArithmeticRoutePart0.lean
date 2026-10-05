import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk8Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 34; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left1.expected,
    Slot0.Left2.expected,
    Slot0.Left3.expected,
    Slot0.Left4.expected,
    Slot0.Left5.expected,
    Slot0.Left6.expected,
    Slot0.Left7.expected,
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected,
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected,
    Slot0.Left15.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot1.Left4.expected,
    Slot1.Left5.expected,
    Slot1.Left6.expected,
    Slot1.Left7.expected,
    Slot1.Left8.expected,
    Slot1.Left9.expected,
    Slot1.Left10.expected,
    Slot1.Left11.expected,
    Slot1.Left12.expected,
    Slot1.Left13.expected,
    Slot1.Left14.expected,
    Slot1.Left15.expected,
    Slot1.Left16.expected,
    Slot1.Left17.expected,
    Slot1.Left18.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 123387834663085935201846558720 }, { target := 89, numerator := 423568861946861548454182649856 }, { target := 91, numerator := 123387834663085935201846558720 }, { target := 112, numerator := 120817254774271644885141422080 }, { target := 115, numerator := 414744510656301932861387177984 }, { target := 117, numerator := 120817254774271644885141422080 }, { target := 122, numerator := 44449784535590685495596679168 }, { target := 124, numerator := 44449784535590685495596679168 }, { target := 161, numerator := 95111455886128741718090055680 }, { target := 164, numerator := 326500997750705776933432459264 }, { target := 166, numerator := 95111455886128741718090055680 }, { target := 197, numerator := 1185327587615751613215911444480 }, { target := 199, numerator := 1185327587615751613215911444480 }, { target := 211, numerator := 1133469505657562480137715318784 }, { target := 213, numerator := 1133469505657562480137715318784 }, { target := 215, numerator := 15570964556636423770215546880 }, { target := 242, numerator := 37041487112992237912997232640 }, { target := 244, numerator := 37041487112992237912997232640 }, { target := 256, numerator := 1163102695347956270468113104896 }, { target := 258, numerator := 1163102695347956270468113104896 }, { target := 260, numerator := 16015849258254607306507419648 }, { target := 261, numerator := 37041487112992237912997232640 }, { target := 263, numerator := 37041487112992237912997232640 }, { target := 265, numerator := 15570964556636423770215546880 }, { target := 337, numerator := 1133469505657562480137715318784 }, { target := 339, numerator := 1133469505657562480137715318784 }, { target := 351, numerator := 644521875766064939686151847936 }, { target := 353, numerator := 644521875766064939686151847936 }, { target := 355, numerator := 13791425750163689625048055808 }, { target := 382, numerator := 1163102695347956270468113104896 }, { target := 384, numerator := 1163102695347956270468113104896 }, { target := 396, numerator := 18157736982788795024951243440128 }, { target := 398, numerator := 18157736982788795024951243440128 }, { target := 400, numerator := 645527702047984311159507386368 }, { target := 401, numerator := 711196552569450967929546866688 }, { target := 403, numerator := 711196552569450967929546866688 }, { target := 405, numerator := 175729457139182496835289743360 }, { target := 416, numerator := 1185327587615751613215911444480 }, { target := 418, numerator := 1185327587615751613215911444480 }, { target := 420, numerator := 16015849258254607306507419648 }, { target := 421, numerator := 1133469505657562480137715318784 }, { target := 423, numerator := 1133469505657562480137715318784 }, { target := 425, numerator := 645527702047984311159507386368 }, { target := 426, numerator := 15570964556636423770215546880 }, { target := 453, numerator := 37041487112992237912997232640 }, { target := 455, numerator := 37041487112992237912997232640 }, { target := 467, numerator := 711196552569450967929546866688 }, { target := 469, numerator := 711196552569450967929546866688 }, { target := 471, numerator := 15570964556636423770215546880 }, { target := 472, numerator := 37041487112992237912997232640 }, { target := 474, numerator := 37041487112992237912997232640 }, { target := 476, numerator := 13346541048545506088756183040 }, { target := 487, numerator := 1140877803080160927720314765312 }, { target := 489, numerator := 1140877803080160927720314765312 }, { target := 491, numerator := 15570964556636423770215546880 }, { target := 492, numerator := 644521875766064939686151847936 }, { target := 494, numerator := 644521875766064939686151847936 }, { target := 496, numerator := 175729457139182496835289743360 }, { target := 497, numerator := 13346541048545506088756183040 }, { target := 498, numerator := 44449784535590685495596679168 }, { target := 500, numerator := 44449784535590685495596679168 }, { target := 502, numerator := 15570964556636423770215546880 }, { target := 503, numerator := 13791425750163689625048055808 }]

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
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot2.Left10.expected,
    Slot2.Left11.expected,
    Slot2.Left12.expected,
    Slot2.Left13.expected,
    Slot2.Left14.expected,
    Slot2.Left15.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 544090082984856676907089920 }, { target := 37, numerator := 20442862145525105795992125440 }, { target := 40, numerator := 20441316008612137737786490880 }, { target := 47, numerator := 545636219897824735112724480 }, { target := 70, numerator := 13338982679628744337077043200 }, { target := 72, numerator := 501179846148357432417871462400 }, { target := 75, numerator := 501141940856297570345733324800 }, { target := 82, numerator := 13376887971688606409215180800 }, { target := 96, numerator := 544090082984856676907089920 }, { target := 98, numerator := 20442862145525105795992125440 }, { target := 101, numerator := 20441316008612137737786490880 }, { target := 108, numerator := 545636219897824735112724480 }, { target := 145, numerator := 11180173640688829135155363840 }, { target := 147, numerator := 420067844732241690066031738880 }, { target := 150, numerator := 420036074112449410934515957760 }, { target := 157, numerator := 11211944260481108266671144960 }, { target := 171, numerator := 10987109417694202572381880320 }, { target := 173, numerator := 412813925906410200912615178240 }, { target := 176, numerator := 412782703915845103995301396480 }, { target := 183, numerator := 11018331408259299489695662080 }, { target := 187, numerator := 2989584410691019638328073912320 }, { target := 190, numerator := 10262720550920832934421133787136 }, { target := 192, numerator := 2989584410691019638328073912320 }, { target := 201, numerator := 95111455886128741718090055680 }, { target := 204, numerator := 326500997750705776933432459264 }, { target := 206, numerator := 95111455886128741718090055680 }, { target := 216, numerator := 544090082984856676907089920 }, { target := 218, numerator := 20442862145525105795992125440 }, { target := 221, numerator := 20441316008612137737786490880 }, { target := 228, numerator := 545636219897824735112724480 }, { target := 232, numerator := 95111455886128741718090055680 }, { target := 235, numerator := 326500997750705776933432459264 }, { target := 237, numerator := 95111455886128741718090055680 }, { target := 246, numerator := 97682035774943032034795192320 }, { target := 249, numerator := 335325349041265392526227931136 }, { target := 251, numerator := 97682035774943032034795192320 }, { target := 301, numerator := 97682035774943032034795192320 }, { target := 304, numerator := 335325349041265392526227931136 }, { target := 306, numerator := 97682035774943032034795192320 }, { target := 327, numerator := 1652882868507588673641402859520 }, { target := 330, numerator := 5674057879829832826167488413696 }, { target := 332, numerator := 1652882868507588673641402859520 }, { target := 341, numerator := 89970296108500161084679782400 }, { target := 344, numerator := 308852295169586545747841515520 }, { target := 346, numerator := 89970296108500161084679782400 }, { target := 372, numerator := 2989584410691019638328073912320 }, { target := 375, numerator := 10262720550920832934421133787136 }, { target := 377, numerator := 2989584410691019638328073912320 }, { target := 386, numerator := 1652882868507588673641402859520 }, { target := 389, numerator := 5674057879829832826167488413696 }, { target := 391, numerator := 1652882868507588673641402859520 }, { target := 406, numerator := 123387834663085935201846558720 }, { target := 409, numerator := 423568861946861548454182649856 }, { target := 411, numerator := 123387834663085935201846558720 }, { target := 443, numerator := 95111455886128741718090055680 }, { target := 446, numerator := 326500997750705776933432459264 }, { target := 448, numerator := 95111455886128741718090055680 }, { target := 457, numerator := 89970296108500161084679782400 }, { target := 460, numerator := 308852295169586545747841515520 }, { target := 462, numerator := 89970296108500161084679782400 }, { target := 477, numerator := 120817254774271644885141422080 }, { target := 480, numerator := 414744510656301932861387177984 }, { target := 482, numerator := 120817254774271644885141422080 }]

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
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left6.expected,
    Slot6.Left14.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 51784045840168835350528000 }, { target := 17, numerator := 8267177563804261255479296000 }, { target := 19, numerator := 82493999897833443254337536000 }, { target := 27, numerator := 8267177563804261255479296000 }, { target := 34, numerator := 51778137117457725259776000 }, { target := 51, numerator := 51430398697845731109109760 }, { target := 52, numerator := 8210718790197793129832120320 }, { target := 54, numerator := 81930626239994580715039621120 }, { target := 62, numerator := 8210718790197793129832120320 }, { target := 69, numerator := 51424530327387282258001920 }, { target := 86, numerator := 767302981690251834040315281408 }, { target := 89, numerator := 2600949881707924452246110076928 }, { target := 91, numerator := 767302981690251834040315281408 }, { target := 122, numerator := 13284843330446814174039244800 }, { target := 124, numerator := 13284843330446814174039244800 }, { target := 126, numerator := 51784045840168835350528000 }, { target := 127, numerator := 8267177563804261255479296000 }, { target := 129, numerator := 82493999897833443254337536000 }, { target := 137, numerator := 8267177563804261255479296000 }, { target := 144, numerator := 51778137117457725259776000 }, { target := 161, numerator := 26853691312369895727864767053824 }, { target := 164, numerator := 91026761147821228138086094864384 }, { target := 166, numerator := 26853691312369895727864767053824 }, { target := 197, numerator := 1392891863090406006285611827200 }, { target := 199, numerator := 1392891863090406006285611827200 }, { target := 215, numerator := 2805227361819055346291834880 }, { target := 232, numerator := 26853704483087891724171453923328 }, { target := 235, numerator := 91026805792998206641979573403648 }, { target := 237, numerator := 26853704483087891724171453923328 }, { target := 242, numerator := 15013982090335311671957913600000 }, { target := 244, numerator := 15013982090335311671957913600000 }, { target := 260, numerator := 234879260180973957434340016128 }, { target := 266, numerator := 51935608901164451453992960 }, { target := 267, numerator := 8291374181064176166470942720 }, { target := 269, numerator := 82735445751192955771179499520 }, { target := 277, numerator := 8291374181064176166470942720 }, { target := 284, numerator := 51929682884630772260536320 }, { target := 285, numerator := 11004660710693714078088560640 }, { target := 287, numerator := 413473373072394881744743956480 }, { target := 290, numerator := 413442101206445495535229992960 }, { target := 297, numerator := 11035932576643100287602524160 }, { target := 311, numerator := 9863826665725466207154339840 }, { target := 313, numerator := 370609307283390627656373370880 }, { target := 316, numerator := 370581277317420045439871221760 }, { target := 323, numerator := 9891856631696048423656488960 }, { target := 356, numerator := 13338982679628744337077043200 }, { target := 358, numerator := 501179846148357432417871462400 }, { target := 361, numerator := 501141940856297570345733324800 }, { target := 368, numerator := 13376887971688606409215180800 }, { target := 406, numerator := 767296396331253835886971846656 }, { target := 409, numerator := 2600927559119435200299370807296 }, { target := 411, numerator := 767296396331253835886971846656 }, { target := 416, numerator := 1392892925622864651955784908800 }, { target := 418, numerator := 1392892925622864651955784908800 }, { target := 420, numerator := 234879345183570649087953862656 }, { target := 427, numerator := 544090082984856676907089920 }, { target := 429, numerator := 20442862145525105795992125440 }, { target := 432, numerator := 20441316008612137737786490880 }, { target := 439, numerator := 545636219897824735112724480 }, { target := 498, numerator := 13284843330446814174039244800 }, { target := 500, numerator := 13284843330446814174039244800 }, { target := 502, numerator := 2805142359222363692677988352 }]

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
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left6.expected,
    Slot12.Left14.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 465559222080186843037433856 }, { target := 1, numerator := 39148522035051981953734541312 }, { target := 6, numerator := 39148512590319016214444113920 }, { target := 14, numerator := 465568666813152582327861248 }, { target := 16, numerator := 1078596244995959030808576000 }, { target := 17, numerator := 159303020881796425964322816000 }, { target := 19, numerator := 1660388745063923855696855040000 }, { target := 27, numerator := 159303020881796425964322816000 }, { target := 34, numerator := 1078596244995959030808576000 }, { target := 35, numerator := 993569235932388836671393628160 }, { target := 37, numerator := 35055685324837204997601723678720 }, { target := 40, numerator := 35055701502726524636037434572800 }, { target := 47, numerator := 993559629383208233114617774080 }, { target := 86, numerator := 228684866714254126185080422400 }, { target := 89, numerator := 781889053339123909593325895680 }, { target := 91, numerator := 228684792848678758850190376960 }, { target := 122, numerator := 1100168169895878211424747520 }, { target := 124, numerator := 1099670698285220097052114944 }, { target := 126, numerator := 1078108527730607938286387200 }, { target := 127, numerator := 159230987594023456918942515200 }, { target := 129, numerator := 1659637954152200124275621888000 }, { target := 137, numerator := 159230987594023456918942515200 }, { target := 144, numerator := 1078108527730607938286387200 }, { target := 145, numerator := 3374617456370985264058007027712 }, { target := 147, numerator := 119071611508325340573002423599104 }, { target := 150, numerator := 119071666436047384553127369768960 }, { target := 157, numerator := 3374584803717284736514293497856 }, { target := 161, numerator := 8287615264683470582365080780800 }, { target := 164, numerator := 28335918099202879593114039746560 }, { target := 166, numerator := 8287612587770569678131633848320 }, { target := 197, numerator := 162489081299432354483609272320 }, { target := 199, numerator := 162415607345903926057321365504 }, { target := 215, numerator := 465559222080186843037433856 }, { target := 216, numerator := 993569162320429178752245694464 }, { target := 218, numerator := 35055682657115421349691825061888 }, { target := 221, numerator := 35055698835003760610783652741120 }, { target := 228, numerator := 993559555772228952539353055232 }, { target := 232, numerator := 8287618310349735377808392192000 }, { target := 235, numerator := 28335928512542191386681042534400 }, { target := 237, numerator := 8287615633435850718531341516800 }, { target := 242, numerator := 1693596519965202332810792140800 }, { target := 244, numerator := 1692830713235244126761134325760 }, { target := 260, numerator := 39148522035051981953734541312 }, { target := 406, numerator := 228681821047989330741769011200 }, { target := 409, numerator := 781878639999812116026323107840 }, { target := 411, numerator := 228681747183397718450482708480 }, { target := 416, numerator := 162489081299432354483609272320 }, { target := 418, numerator := 162415607345903926057321365504 }, { target := 420, numerator := 39148512590319016214444113920 }, { target := 498, numerator := 1100168169895878211424747520 }, { target := 500, numerator := 1099670698285220097052114944 }, { target := 502, numerator := 465568666813152582327861248 }]

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

namespace RouteChunk4

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left3.expected,
    Slot19.Left11.expected,
    Slot19.Left18.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 2805227361819055346291834880 }, { target := 1, numerator := 234879260180973957434340016128 }, { target := 6, numerator := 234879345183570649087953862656 }, { target := 14, numerator := 2805142359222363692677988352 }, { target := 16, numerator := 13461974574852771696359768064 }, { target := 17, numerator := 1411463754598278086369419984896 }, { target := 19, numerator := 15214168518206449160917352448000 }, { target := 27, numerator := 1411464831297836180648528707584 }, { target := 34, numerator := 13461974574852771696359768064 }, { target := 86, numerator := 551862798456068915148619776 }, { target := 87, numerator := 13529539575052012113321000960 }, { target := 88, numerator := 551862798456068915148619776 }, { target := 89, numerator := 11339890406984383837086154752 }, { target := 90, numerator := 11144068123661262609130192896 }, { target := 91, numerator := 551862798456068915148619776 }, { target := 92, numerator := 11161870149417909993489825792 }, { target := 93, numerator := 10004738475235830010113687552 }, { target := 94, numerator := 13529539575052012113321000960 }, { target := 95, numerator := 551862798456068915148619776 }, { target := 122, numerator := 51784045840168835350528000 }, { target := 123, numerator := 51430398697845731109109760 }, { target := 124, numerator := 51784045840168835350528000 }, { target := 125, numerator := 51935608901164451453992960 }, { target := 126, numerator := 13461974574852771696359768064 }, { target := 127, numerator := 1411463754598278086369419984896 }, { target := 129, numerator := 15214168518206449160917352448000 }, { target := 137, numerator := 1411464831297836180648528707584 }, { target := 144, numerator := 13461974574852771696359768064 }, { target := 161, numerator := 20734903033318321593077727232 }, { target := 162, numerator := 508339558236191110023841054720 }, { target := 163, numerator := 20734903033318321593077727232 }, { target := 164, numerator := 426068813942702285638403620864 }, { target := 165, numerator := 418711267705073203782795395072 }, { target := 166, numerator := 20734903033318321593077727232 }, { target := 167, numerator := 419380135544857665769668870144 }, { target := 168, numerator := 375903725958867636622892990464 }, { target := 169, numerator := 508339558236191110023841054720 }, { target := 170, numerator := 20734903033318321593077727232 }, { target := 197, numerator := 8267177563804261255479296000 }, { target := 198, numerator := 8210718790197793129832120320 }, { target := 199, numerator := 8267177563804261255479296000 }, { target := 200, numerator := 8291374181064176166470942720 }, { target := 232, numerator := 20733334808735168276897726464 }, { target := 233, numerator := 508301111439958964207815229440 }, { target := 234, numerator := 20733334808735168276897726464 }, { target := 235, numerator := 426036589456912973947866185728 }, { target := 236, numerator := 418679599686071462623805702144 }, { target := 237, numerator := 20733334808735168276897726464 }, { target := 238, numerator := 419348416937966145471447564288 }, { target := 239, numerator := 375875295564811760374726524928 }, { target := 240, numerator := 508301111439958964207815229440 }, { target := 241, numerator := 20733334808735168276897726464 }, { target := 242, numerator := 82493999897833443254337536000 }, { target := 243, numerator := 81930626239994580715039621120 }, { target := 244, numerator := 82493999897833443254337536000 }, { target := 245, numerator := 82735445751192955771179499520 }, { target := 416, numerator := 8267177563804261255479296000 }, { target := 417, numerator := 8210718790197793129832120320 }, { target := 418, numerator := 8267177563804261255479296000 }, { target := 419, numerator := 8291374181064176166470942720 }, { target := 498, numerator := 51778137117457725259776000 }, { target := 499, numerator := 51424530327387282258001920 }, { target := 500, numerator := 51778137117457725259776000 }, { target := 501, numerator := 51929682884630772260536320 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk4

namespace RouteChunk5

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot20.Left12.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 124071423774792782488283381760 }, { target := 36, numerator := 121486602446151266186444144640 }, { target := 37, numerator := 95638389159736103168051773440 }, { target := 38, numerator := 3006147205210083459039032770560 }, { target := 39, numerator := 95638389159736103168051773440 }, { target := 40, numerator := 95638389159736103168051773440 }, { target := 41, numerator := 98223210488377619469891010560 }, { target := 42, numerator := 98223210488377619469891010560 }, { target := 43, numerator := 1662040114316494982082629468160 }, { target := 44, numerator := 90468746502453070564373299200 }, { target := 45, numerator := 3006147205210083459039032770560 }, { target := 46, numerator := 1662040114316494982082629468160 }, { target := 47, numerator := 124071423774792782488283381760 }, { target := 48, numerator := 95638389159736103168051773440 }, { target := 49, numerator := 90468746502453070564373299200 }, { target := 50, numerator := 121486602446151266186444144640 }, { target := 145, numerator := 425915503841303994706006376448 }, { target := 146, numerator := 417042264177943494816297910272 }, { target := 147, numerator := 328309867544338495919213248512 }, { target := 148, numerator := 10319577728488261371730946162688 }, { target := 149, numerator := 328309867544338495919213248512 }, { target := 150, numerator := 328309867544338495919213248512 }, { target := 151, numerator := 337183107207698995808921714688 }, { target := 152, numerator := 337183107207698995808921714688 }, { target := 153, numerator := 5705493103540801429082543751168 }, { target := 154, numerator := 310563388217617496139796316160 }, { target := 155, numerator := 10319577728488261371730946162688 }, { target := 156, numerator := 5705493103540801429082543751168 }, { target := 157, numerator := 425915503841303994706006376448 }, { target := 158, numerator := 328309867544338495919213248512 }, { target := 159, numerator := 310563388217617496139796316160 }, { target := 160, numerator := 417042264177943494816297910272 }, { target := 216, numerator := 124071423774792782488283381760 }, { target := 217, numerator := 121486602446151266186444144640 }, { target := 218, numerator := 95638389159736103168051773440 }, { target := 219, numerator := 3006147205210083459039032770560 }, { target := 220, numerator := 95638389159736103168051773440 }, { target := 221, numerator := 95638389159736103168051773440 }, { target := 222, numerator := 98223210488377619469891010560 }, { target := 223, numerator := 98223210488377619469891010560 }, { target := 224, numerator := 1662040114316494982082629468160 }, { target := 225, numerator := 90468746502453070564373299200 }, { target := 226, numerator := 3006147205210083459039032770560 }, { target := 227, numerator := 1662040114316494982082629468160 }, { target := 228, numerator := 124071423774792782488283381760 }, { target := 229, numerator := 95638389159736103168051773440 }, { target := 230, numerator := 90468746502453070564373299200 }, { target := 231, numerator := 121486602446151266186444144640 }, { target := 406, numerator := 553431023039222231328620544 }, { target := 407, numerator := 13567986371284157929346826240 }, { target := 408, numerator := 553431023039222231328620544 }, { target := 409, numerator := 11372114892773695527623589888 }, { target := 410, numerator := 11175736142663003768119885824 }, { target := 411, numerator := 553431023039222231328620544 }, { target := 412, numerator := 11193588756309430291711131648 }, { target := 413, numerator := 10033168869291706258280153088 }, { target := 414, numerator := 13567986371284157929346826240 }, { target := 415, numerator := 553431023039222231328620544 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk5

namespace RouteChunk6

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot23.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 14893966097652231432380088320 }, { target := 1, numerator := 15319507986156580901876662272 }, { target := 2, numerator := 14893966097652231432380088320 }, { target := 3, numerator := 13191798543634833554393792512 }, { target := 4, numerator := 617461280219811080239528804352 }, { target := 5, numerator := 168089045959218040451146711040 }, { target := 6, numerator := 15319507986156580901876662272 }, { target := 7, numerator := 617461280219811080239528804352 }, { target := 8, numerator := 14893966097652231432380088320 }, { target := 9, numerator := 14893966097652231432380088320 }, { target := 10, numerator := 12766256655130484084897218560 }, { target := 11, numerator := 14893966097652231432380088320 }, { target := 12, numerator := 168089045959218040451146711040 }, { target := 13, numerator := 12766256655130484084897218560 }, { target := 14, numerator := 14893966097652231432380088320 }, { target := 15, numerator := 13191798543634833554393792512 }, { target := 16, numerator := 44972040489664205299069747200 }, { target := 17, numerator := 1199254413057712141308526592000 }, { target := 18, numerator := 1146787032486437235126278553600 }, { target := 19, numerator := 37476700408053504415891456000 }, { target := 20, numerator := 1176768392812880038658991718400 }, { target := 21, numerator := 37476700408053504415891456000 }, { target := 22, numerator := 1146787032486437235126278553600 }, { target := 23, numerator := 652094587100130976836511334400 }, { target := 24, numerator := 1176768392812880038658991718400 }, { target := 25, numerator := 18371078540027827864669991731200 }, { target := 26, numerator := 719552647834627284785115955200 }, { target := 27, numerator := 1199254413057712141308526592000 }, { target := 28, numerator := 1146787032486437235126278553600 }, { target := 29, numerator := 37476700408053504415891456000 }, { target := 30, numerator := 719552647834627284785115955200 }, { target := 31, numerator := 37476700408053504415891456000 }, { target := 32, numerator := 1154282372568047936009456844800 }, { target := 33, numerator := 652094587100130976836511334400 }, { target := 34, numerator := 44972040489664205299069747200 }, { target := 126, numerator := 44972040489664205299069747200 }, { target := 127, numerator := 1199254413057712141308526592000 }, { target := 128, numerator := 1146787032486437235126278553600 }, { target := 129, numerator := 37476700408053504415891456000 }, { target := 130, numerator := 1176768392812880038658991718400 }, { target := 131, numerator := 37476700408053504415891456000 }, { target := 132, numerator := 1146787032486437235126278553600 }, { target := 133, numerator := 652094587100130976836511334400 }, { target := 134, numerator := 1176768392812880038658991718400 }, { target := 135, numerator := 18371078540027827864669991731200 }, { target := 136, numerator := 719552647834627284785115955200 }, { target := 137, numerator := 1199254413057712141308526592000 }, { target := 138, numerator := 1146787032486437235126278553600 }, { target := 139, numerator := 37476700408053504415891456000 }, { target := 140, numerator := 719552647834627284785115955200 }, { target := 141, numerator := 37476700408053504415891456000 }, { target := 142, numerator := 1154282372568047936009456844800 }, { target := 143, numerator := 652094587100130976836511334400 }, { target := 144, numerator := 44972040489664205299069747200 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk6

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8.Parent0
