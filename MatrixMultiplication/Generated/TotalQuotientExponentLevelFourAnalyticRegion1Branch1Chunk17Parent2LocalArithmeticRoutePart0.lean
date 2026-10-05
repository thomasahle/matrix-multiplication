import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk17Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 72; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17.Parent2

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
    Slot0.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 142879920305703985585586176 }, { target := 72, numerator := 156933682958724049741545472 }, { target := 73, numerator := 142879920305703985585586176 }, { target := 74, numerator := 156933682958724049741545472 }, { target := 85, numerator := 161316039054827080499855360 }, { target := 86, numerator := 177183190437269088417873920 }, { target := 87, numerator := 161316039054827080499855360 }, { target := 88, numerator := 177183190437269088417873920 }, { target := 116, numerator := 138270890618423211857018880 }, { target := 117, numerator := 151871306089087790072463360 }, { target := 118, numerator := 138270890618423211857018880 }, { target := 119, numerator := 151871306089087790072463360 }, { target := 130, numerator := 1820566726475905622784081920 }, { target := 131, numerator := 1999638863506322569287434240 }, { target := 132, numerator := 1820566726475905622784081920 }, { target := 133, numerator := 1999638863506322569287434240 }, { target := 135, numerator := 161316039054827080499855360 }, { target := 136, numerator := 177183190437269088417873920 }, { target := 137, numerator := 161316039054827080499855360 }, { target := 138, numerator := 177183190437269088417873920 }, { target := 150, numerator := 138270890618423211857018880 }, { target := 151, numerator := 151871306089087790072463360 }, { target := 152, numerator := 138270890618423211857018880 }, { target := 153, numerator := 151871306089087790072463360 }, { target := 155, numerator := 161316039054827080499855360 }, { target := 156, numerator := 177183190437269088417873920 }, { target := 157, numerator := 161316039054827080499855360 }, { target := 158, numerator := 177183190437269088417873920 }, { target := 187, numerator := 161316039054827080499855360 }, { target := 188, numerator := 177183190437269088417873920 }, { target := 189, numerator := 161316039054827080499855360 }, { target := 190, numerator := 177183190437269088417873920 }, { target := 201, numerator := 6687702076244402680151146496 }, { target := 202, numerator := 7345508837842212779838144512 }, { target := 203, numerator := 6687702076244402680151146496 }, { target := 204, numerator := 7345508837842212779838144512 }, { target := 206, numerator := 165925068742107854228422656 }, { target := 207, numerator := 182245567306905348086956032 }, { target := 208, numerator := 165925068742107854228422656 }, { target := 209, numerator := 182245567306905348086956032 }, { target := 221, numerator := 1820566726475905622784081920 }, { target := 222, numerator := 1999638863506322569287434240 }, { target := 223, numerator := 1820566726475905622784081920 }, { target := 224, numerator := 1999638863506322569287434240 }, { target := 226, numerator := 6687702076244402680151146496 }, { target := 227, numerator := 7345508837842212779838144512 }, { target := 228, numerator := 6687702076244402680151146496 }, { target := 229, numerator := 7345508837842212779838144512 }, { target := 232, numerator := 142879920305703985585586176 }, { target := 233, numerator := 156933682958724049741545472 }, { target := 234, numerator := 142879920305703985585586176 }, { target := 235, numerator := 156933682958724049741545472 }, { target := 248, numerator := 161316039054827080499855360 }, { target := 249, numerator := 177183190437269088417873920 }, { target := 250, numerator := 161316039054827080499855360 }, { target := 251, numerator := 177183190437269088417873920 }, { target := 253, numerator := 165925068742107854228422656 }, { target := 254, numerator := 182245567306905348086956032 }, { target := 255, numerator := 165925068742107854228422656 }, { target := 256, numerator := 182245567306905348086956032 }, { target := 259, numerator := 161316039054827080499855360 }, { target := 260, numerator := 177183190437269088417873920 }, { target := 261, numerator := 161316039054827080499855360 }, { target := 262, numerator := 177183190437269088417873920 }]

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
    Slot2.Left3.expected,
    Slot2.Left5.expected,
    Slot3.Left0.expected,
    Slot3.Left2.expected,
    Slot3.Left5.expected,
    Slot3.Left12.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left3.expected,
    Slot4.Left11.expected,
    Slot4.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 671868105862644458468671488 }, { target := 36, numerator := 13437362117252889169373429760 }, { target := 37, numerator := 695863395357738903413981184 }, { target := 38, numerator := 12501545826944205816506351616 }, { target := 39, numerator := 18716325806173667057341562880 }, { target := 40, numerator := 671868105862644458468671488 }, { target := 41, numerator := 18740321095668761502286872576 }, { target := 42, numerator := 18740321095668761502286872576 }, { target := 43, numerator := 13413366827757794724428120064 }, { target := 44, numerator := 695863395357738903413981184 }, { target := 71, numerator := 18850126257493035275331305472 }, { target := 73, numerator := 18850126257493035275331305472 }, { target := 89, numerator := 1333756855222805376285016064 }, { target := 106, numerator := 2447454706640958369057210368 }, { target := 107, numerator := 48949094132819167381144207360 }, { target := 108, numerator := 2534863803306706882237825024 }, { target := 109, numerator := 45540139362854975367100235776 }, { target := 110, numerator := 68179095399283840280879431680 }, { target := 111, numerator := 2447454706640958369057210368 }, { target := 112, numerator := 68266504495949588794060046336 }, { target := 113, numerator := 68266504495949588794060046336 }, { target := 114, numerator := 48861685036153418867963592704 }, { target := 115, numerator := 2534863803306706882237825024 }, { target := 116, numerator := 753624550342730672219803877376 }, { target := 118, numerator := 753624550342730672219803877376 }, { target := 134, numerator := 201240398679349716465748017152 }, { target := 139, numerator := 2978793219530446286476017664 }, { target := 140, numerator := 671868557807874264352686080 }, { target := 141, numerator := 13437371156157485287053721600 }, { target := 142, numerator := 695863863443869773793853440 }, { target := 143, numerator := 12501554236353660418848194560 }, { target := 144, numerator := 18716338396076497364110540800 }, { target := 145, numerator := 671868557807874264352686080 }, { target := 146, numerator := 18740333701712492873551708160 }, { target := 147, numerator := 18740333701712492873551708160 }, { target := 148, numerator := 13413375850521489777612554240 }, { target := 149, numerator := 695863863443869773793853440 }, { target := 150, numerator := 753624366170437840303640543232 }, { target := 152, numerator := 753624366170437840303640543232 }, { target := 154, numerator := 2054619204177791728473698467840 }, { target := 159, numerator := 1856910058928070412348686336 }, { target := 160, numerator := 96714065569170333976494080 }, { target := 205, numerator := 2959450406416612219680718848 }, { target := 210, numerator := 3094850098213450687247810560 }, { target := 225, numerator := 1856910058928070412348686336 }, { target := 230, numerator := 47409234942007297715277398016 }, { target := 231, numerator := 3036821658871948486861914112 }, { target := 232, numerator := 18850126257493035275331305472 }, { target := 234, numerator := 18850126257493035275331305472 }, { target := 236, numerator := 201240398679349716465748017152 }, { target := 237, numerator := 2959450406416612219680718848 }, { target := 252, numerator := 96714065569170333976494080 }, { target := 257, numerator := 3036821658871948486861914112 }, { target := 258, numerator := 96714065569170333976494080 }, { target := 263, numerator := 2959450406416612219680718848 }, { target := 264, numerator := 3094850098213450687247810560 }, { target := 265, numerator := 1333756855222805376285016064 }]

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
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 18801207622808498057898885120 }, { target := 20, numerator := 21412486459309678343718174720 }, { target := 21, numerator := 16712184553607553829243453440 }, { target := 22, numerator := 224047724171801268523295047680 }, { target := 23, numerator := 19845719157408970172226600960 }, { target := 24, numerator := 16712184553607553829243453440 }, { target := 25, numerator := 19845719157408970172226600960 }, { target := 26, numerator := 19323463390108734115062743040 }, { target := 27, numerator := 730113562685730007915073372160 }, { target := 28, numerator := 19323463390108734115062743040 }, { target := 29, numerator := 224047724171801268523295047680 }, { target := 30, numerator := 730113562685730007915073372160 }, { target := 31, numerator := 18801207622808498057898885120 }, { target := 32, numerator := 19323463390108734115062743040 }, { target := 33, numerator := 19323463390108734115062743040 }, { target := 34, numerator := 21412486459309678343718174720 }, { target := 35, numerator := 2713092553405379967569448927232 }, { target := 38, numerator := 9909620240983296821571669196800 }, { target := 40, numerator := 2713091639320204351491004170240 }, { target := 71, numerator := 791568680114970001227091279872 }, { target := 73, numerator := 791568868839672473275192049664 }, { target := 89, numerator := 10603601700635501362832998400 }, { target := 90, numerator := 18801221070484927792162013184 }, { target := 91, numerator := 21412501774718945541073403904 }, { target := 92, numerator := 16712196507097713593032900608 }, { target := 93, numerator := 224047884423278722856597323776 }, { target := 94, numerator := 19845733352178534891726569472 }, { target := 95, numerator := 16712196507097713593032900608 }, { target := 96, numerator := 19845733352178534891726569472 }, { target := 97, numerator := 19323477211331731341944291328 }, { target := 98, numerator := 730114084903831362595624845312 }, { target := 99, numerator := 19323477211331731341944291328 }, { target := 100, numerator := 224047884423278722856597323776 }, { target := 101, numerator := 730114084903831362595624845312 }, { target := 102, numerator := 18801221070484927792162013184 }, { target := 103, numerator := 19323477211331731341944291328 }, { target := 104, numerator := 19323477211331731341944291328 }, { target := 105, numerator := 21412501774718945541073403904 }, { target := 106, numerator := 9724794943990506574547196575744 }, { target := 109, numerator := 35519991640322510302001863065600 }, { target := 111, numerator := 9724791667548321419314153390080 }, { target := 116, numerator := 30978909338754706785550118944768 }, { target := 118, numerator := 30978916724703133921237077590016 }, { target := 134, numerator := 3415646592471213417152957644800 }, { target := 140, numerator := 2713880973479072398969006981120 }, { target := 143, numerator := 9912499959742191914962649088000 }, { target := 145, numerator := 2713880059128265188194018918400 }, { target := 150, numerator := 30978920700767110112328571420672 }, { target := 152, numerator := 30978928086718246163191393419264 }, { target := 154, numerator := 36326837887171433495623305789440 }, { target := 232, numerator := 791580042127373328005543755776 }, { target := 234, numerator := 791580230854784715229507878912 }, { target := 236, numerator := 3415656887230146072979523502080 }, { target := 265, numerator := 10603601700635501362832998400 }]

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
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 32831402946184291812082974720 }, { target := 1, numerator := 3233739505504334233756338487296 }, { target := 2, numerator := 165032881487232257897489498112 }, { target := 3, numerator := 29801711494017498545136315924480 }, { target := 4, numerator := 104451190814703960694613606400 }, { target := 5, numerator := 6267071448882237641676816384 }, { target := 6, numerator := 165032881487232257897489498112 }, { target := 7, numerator := 163988369579085218290543362048 }, { target := 8, numerator := 104451190814703960694613606400 }, { target := 9, numerator := 2530852353440276967630487683072 }, { target := 10, numerator := 161899345762791139076651089920 }, { target := 11, numerator := 3233741658903450422314555932672 }, { target := 12, numerator := 165032881487232257897489498112 }, { target := 13, numerator := 6267071448882237641676816384 }, { target := 14, numerator := 161899345762791139076651089920 }, { target := 15, numerator := 6267071448882237641676816384 }, { target := 16, numerator := 165032881487232257897489498112 }, { target := 17, numerator := 165032881487232257897489498112 }, { target := 18, numerator := 32831402946184291812082974720 }, { target := 19, numerator := 3357384662725018353501076455424 }, { target := 21, numerator := 131271082120826777970583216848896 }, { target := 24, numerator := 131271068867506823715968201523200 }, { target := 31, numerator := 3357389080498336438372748230656 }, { target := 35, numerator := 23544928719618308818393240698880 }, { target := 38, numerator := 84690408427192127737383501168640 }, { target := 40, numerator := 23544936574334712370993918115840 }, { target := 71, numerator := 2422151831549535078465216184320 }, { target := 73, numerator := 2422151254063605873865245327360 }, { target := 89, numerator := 26389566158504014340337696768 }, { target := 90, numerator := 3357384303980159851333762940928 }, { target := 92, numerator := 131271068052743084585347253796864 }, { target := 95, numerator := 131271054799419970492643684646912 }, { target := 102, numerator := 3357388721754531215568285990912 }, { target := 106, numerator := 87463542731338537875505204428800 }, { target := 109, numerator := 314603762220534493059614140006400 }, { target := 111, numerator := 87463571909652559792227903078400 }, { target := 116, numerator := 94790815162140156110922565287936 }, { target := 118, numerator := 94790792562251387391303827324928 }, { target := 134, numerator := 3119077292759448691044796858368 }, { target := 140, numerator := 23539972537473139457073621237760 }, { target := 143, numerator := 84672581187402516051715717857280 }, { target := 145, numerator := 23539980390536133663728001351680 }, { target := 150, numerator := 94790815162140156110922565287936 }, { target := 152, numerator := 94790792562251387391303827324928 }, { target := 154, numerator := 29599421761893822779155858587648 }, { target := 232, numerator := 2422151831549535078465216184320 }, { target := 234, numerator := 2422151254063605873865245327360 }, { target := 236, numerator := 3119079431991465430994078662656 }, { target := 265, numerator := 26389566158504014340337696768 }]

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
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left2.expected,
    Slot18.Left3.expected,
    Slot18.Left4.expected,
    Slot18.Left5.expected,
    Slot18.Left6.expected,
    Slot18.Left7.expected,
    Slot18.Left8.expected,
    Slot18.Left9.expected,
    Slot18.Left10.expected,
    Slot18.Left11.expected,
    Slot18.Left12.expected,
    Slot18.Left13.expected,
    Slot18.Left14.expected,
    Slot18.Left15.expected,
    Slot18.Left16.expected,
    Slot18.Left17.expected,
    Slot18.Left18.expected,
    Slot19.Left0.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected,
    Slot22.Left0.expected,
    Slot22.Left1.expected,
    Slot22.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 10681426300273193115954708480 }, { target := 1, numerator := 3440715558287515900948575682560 }, { target := 3, numerator := 36593456880838746768985678675968 }, { target := 11, numerator := 3440725928604312282689464958976 }, { target := 18, numerator := 10681426300273193115954708480 }, { target := 19, numerator := 788114203331425867805277290496 }, { target := 21, numerator := 30843714597251413177383753089024 }, { target := 24, numerator := 30843725909678974345005441744896 }, { target := 31, numerator := 788125515758987035426965946368 }, { target := 35, numerator := 26263008181677931869322042408960 }, { target := 38, numerator := 97206535630992401602691232432128 }, { target := 40, numerator := 26258840627520776436143884337152 }, { target := 71, numerator := 946636169486046284916736393216 }, { target := 73, numerator := 946636404146842333495412391936 }, { target := 85, numerator := 21412486459309678343718174720 }, { target := 87, numerator := 21412501774718945541073403904 }, { target := 89, numerator := 6034957691516228840133230592 }, { target := 90, numerator := 788114391232516795399302807552 }, { target := 92, numerator := 30843721950966898299386292338688 }, { target := 95, numerator := 30843733263397156560234822500352 }, { target := 102, numerator := 788125703662775056247832969216 }, { target := 106, numerator := 94618105844743026977310683168768 }, { target := 109, numerator := 350189711082602767750427186298880 }, { target := 111, numerator := 94603159112087540202499878158336 }, { target := 116, numerator := 36207271360622684445439390908416 }, { target := 118, numerator := 36207280001078898852286609489920 }, { target := 134, numerator := 90524365372743432601998458880 }, { target := 139, numerator := 158920552543260692790175072256 }, { target := 140, numerator := 26263015122289944916559122137088 }, { target := 143, numerator := 97206561532903087821941469347840 }, { target := 145, numerator := 26258847566213328863547847868416 }, { target := 150, numerator := 36190545901498475997356519063552 }, { target := 152, numerator := 36190554529998035339801813581824 }, { target := 154, numerator := 6034957691516228840133230592 }, { target := 159, numerator := 100582628191937147335553843200 }, { target := 160, numerator := 6034957691516228840133230592 }, { target := 205, numerator := 158920552543260692790175072256 }, { target := 210, numerator := 157914726261341321316819533824 }, { target := 225, numerator := 100582628191937147335553843200 }, { target := 230, numerator := 2437117081090637079940469620736 }, { target := 231, numerator := 155903073697502578370108456960 }, { target := 232, numerator := 927839386720104751610046971904 }, { target := 234, numerator := 927839607934279338667171381248 }, { target := 236, numerator := 90524365372743432601998458880 }, { target := 237, numerator := 158920552543260692790175072256 }, { target := 252, numerator := 6034957691516228840133230592 }, { target := 257, numerator := 155903073697502578370108456960 }, { target := 258, numerator := 6034957691516228840133230592 }, { target := 263, numerator := 158920552543260692790175072256 }, { target := 264, numerator := 158920552543260692790175072256 }, { target := 265, numerator := 6034957691516228840133230592 }]

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
    Slot22.Left3.expected,
    Slot22.Left4.expected,
    Slot22.Left5.expected,
    Slot22.Left6.expected,
    Slot22.Left7.expected,
    Slot22.Left8.expected,
    Slot22.Left9.expected,
    Slot22.Left10.expected,
    Slot22.Left11.expected,
    Slot22.Left12.expected,
    Slot22.Left13.expected,
    Slot22.Left14.expected,
    Slot22.Left15.expected,
    Slot23.Left0.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected,
    Slot25.Left0.expected,
    Slot25.Left1.expected,
    Slot25.Left2.expected,
    Slot25.Left3.expected,
    Slot25.Left4.expected,
    Slot25.Left5.expected,
    Slot25.Left6.expected,
    Slot25.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1178419332135291266625699840 }, { target := 1, numerator := 193120232843657567085055180800 }, { target := 3, numerator := 1988247571076344411102956748800 }, { target := 11, numerator := 193120232843657567085055180800 }, { target := 18, numerator := 1178419332135291266625699840 }, { target := 19, numerator := 18850126257493035275331305472 }, { target := 21, numerator := 753624550342730672219803877376 }, { target := 24, numerator := 753624366170437840303640543232 }, { target := 31, numerator := 18850126257493035275331305472 }, { target := 35, numerator := 671868105862644458468671488 }, { target := 38, numerator := 2447454706640958369057210368 }, { target := 40, numerator := 671868557807874264352686080 }, { target := 61, numerator := 13437362117252889169373429760 }, { target := 64, numerator := 48949094132819167381144207360 }, { target := 66, numerator := 13437371156157485287053721600 }, { target := 75, numerator := 695863395357738903413981184 }, { target := 78, numerator := 2534863803306706882237825024 }, { target := 80, numerator := 695863863443869773793853440 }, { target := 90, numerator := 18850126257493035275331305472 }, { target := 92, numerator := 753624550342730672219803877376 }, { target := 95, numerator := 753624366170437840303640543232 }, { target := 102, numerator := 18850126257493035275331305472 }, { target := 106, numerator := 12501545826944205816506351616 }, { target := 109, numerator := 45540139362854975367100235776 }, { target := 111, numerator := 12501554236353660418848194560 }, { target := 120, numerator := 18716325806173667057341562880 }, { target := 123, numerator := 68179095399283840280879431680 }, { target := 125, numerator := 18716338396076497364110540800 }, { target := 130, numerator := 224047724171801268523295047680 }, { target := 132, numerator := 224047884423278722856597323776 }, { target := 135, numerator := 19845719157408970172226600960 }, { target := 137, numerator := 19845733352178534891726569472 }, { target := 140, numerator := 671868105862644458468671488 }, { target := 143, numerator := 2447454706640958369057210368 }, { target := 145, numerator := 671868557807874264352686080 }, { target := 150, numerator := 16712184553607553829243453440 }, { target := 152, numerator := 16712196507097713593032900608 }, { target := 155, numerator := 19845719157408970172226600960 }, { target := 157, numerator := 19845733352178534891726569472 }, { target := 177, numerator := 18740321095668761502286872576 }, { target := 180, numerator := 68266504495949588794060046336 }, { target := 182, numerator := 18740333701712492873551708160 }, { target := 187, numerator := 19323463390108734115062743040 }, { target := 189, numerator := 19323477211331731341944291328 }, { target := 191, numerator := 18740321095668761502286872576 }, { target := 194, numerator := 68266504495949588794060046336 }, { target := 196, numerator := 18740333701712492873551708160 }, { target := 201, numerator := 730113562685730007915073372160 }, { target := 203, numerator := 730114084903831362595624845312 }, { target := 206, numerator := 19323463390108734115062743040 }, { target := 208, numerator := 19323477211331731341944291328 }, { target := 221, numerator := 224047724171801268523295047680 }, { target := 223, numerator := 224047884423278722856597323776 }, { target := 226, numerator := 730113562685730007915073372160 }, { target := 228, numerator := 730114084903831362595624845312 }, { target := 232, numerator := 18801207622808498057898885120 }, { target := 234, numerator := 18801221070484927792162013184 }, { target := 248, numerator := 19323463390108734115062743040 }, { target := 250, numerator := 19323477211331731341944291328 }, { target := 253, numerator := 19323463390108734115062743040 }, { target := 255, numerator := 19323477211331731341944291328 }, { target := 259, numerator := 21412486459309678343718174720 }, { target := 261, numerator := 21412501774718945541073403904 }]

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
    Slot25.Left8.expected,
    Slot25.Left9.expected,
    Slot26.Left0.expected,
    Slot27.Left0.expected,
    Slot27.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 116056878683004400771792896 }, { target := 1, numerator := 1682824740903563811190996992 }, { target := 2, numerator := 2978793219530446286476017664 }, { target := 3, numerator := 96714065569170333976494080 }, { target := 4, numerator := 1856910058928070412348686336 }, { target := 5, numerator := 96714065569170333976494080 }, { target := 6, numerator := 2959450406416612219680718848 }, { target := 7, numerator := 3094850098213450687247810560 }, { target := 8, numerator := 1856910058928070412348686336 }, { target := 9, numerator := 47409234942007297715277398016 }, { target := 10, numerator := 3036821658871948486861914112 }, { target := 11, numerator := 1682824740903563811190996992 }, { target := 12, numerator := 2959450406416612219680718848 }, { target := 13, numerator := 96714065569170333976494080 }, { target := 14, numerator := 3036821658871948486861914112 }, { target := 15, numerator := 96714065569170333976494080 }, { target := 16, numerator := 2959450406416612219680718848 }, { target := 17, numerator := 3094850098213450687247810560 }, { target := 18, numerator := 116056878683004400771792896 }, { target := 19, numerator := 142879920305703985585586176 }, { target := 20, numerator := 161316039054827080499855360 }, { target := 21, numerator := 138270890618423211857018880 }, { target := 22, numerator := 1820566726475905622784081920 }, { target := 23, numerator := 161316039054827080499855360 }, { target := 24, numerator := 138270890618423211857018880 }, { target := 25, numerator := 161316039054827080499855360 }, { target := 26, numerator := 161316039054827080499855360 }, { target := 27, numerator := 6687702076244402680151146496 }, { target := 28, numerator := 165925068742107854228422656 }, { target := 29, numerator := 1820566726475905622784081920 }, { target := 30, numerator := 6687702076244402680151146496 }, { target := 31, numerator := 142879920305703985585586176 }, { target := 32, numerator := 161316039054827080499855360 }, { target := 33, numerator := 165925068742107854228422656 }, { target := 34, numerator := 161316039054827080499855360 }, { target := 45, numerator := 156933682958724049741545472 }, { target := 46, numerator := 177183190437269088417873920 }, { target := 47, numerator := 151871306089087790072463360 }, { target := 48, numerator := 1999638863506322569287434240 }, { target := 49, numerator := 177183190437269088417873920 }, { target := 50, numerator := 151871306089087790072463360 }, { target := 51, numerator := 177183190437269088417873920 }, { target := 52, numerator := 177183190437269088417873920 }, { target := 53, numerator := 7345508837842212779838144512 }, { target := 54, numerator := 182245567306905348086956032 }, { target := 55, numerator := 1999638863506322569287434240 }, { target := 56, numerator := 7345508837842212779838144512 }, { target := 57, numerator := 156933682958724049741545472 }, { target := 58, numerator := 177183190437269088417873920 }, { target := 59, numerator := 182245567306905348086956032 }, { target := 60, numerator := 177183190437269088417873920 }, { target := 211, numerator := 13413366827757794724428120064 }, { target := 214, numerator := 48861685036153418867963592704 }, { target := 216, numerator := 13413375850521489777612554240 }, { target := 238, numerator := 695863395357738903413981184 }, { target := 241, numerator := 2534863803306706882237825024 }, { target := 243, numerator := 695863863443869773793853440 }]

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

namespace RouteChunk7

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot27.Left2.expected,
    Slot27.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 90, numerator := 142879920305703985585586176 }, { target := 91, numerator := 161316039054827080499855360 }, { target := 92, numerator := 138270890618423211857018880 }, { target := 93, numerator := 1820566726475905622784081920 }, { target := 94, numerator := 161316039054827080499855360 }, { target := 95, numerator := 138270890618423211857018880 }, { target := 96, numerator := 161316039054827080499855360 }, { target := 97, numerator := 161316039054827080499855360 }, { target := 98, numerator := 6687702076244402680151146496 }, { target := 99, numerator := 165925068742107854228422656 }, { target := 100, numerator := 1820566726475905622784081920 }, { target := 101, numerator := 6687702076244402680151146496 }, { target := 102, numerator := 142879920305703985585586176 }, { target := 103, numerator := 161316039054827080499855360 }, { target := 104, numerator := 165925068742107854228422656 }, { target := 105, numerator := 161316039054827080499855360 }, { target := 161, numerator := 156933682958724049741545472 }, { target := 162, numerator := 177183190437269088417873920 }, { target := 163, numerator := 151871306089087790072463360 }, { target := 164, numerator := 1999638863506322569287434240 }, { target := 165, numerator := 177183190437269088417873920 }, { target := 166, numerator := 151871306089087790072463360 }, { target := 167, numerator := 177183190437269088417873920 }, { target := 168, numerator := 177183190437269088417873920 }, { target := 169, numerator := 7345508837842212779838144512 }, { target := 170, numerator := 182245567306905348086956032 }, { target := 171, numerator := 1999638863506322569287434240 }, { target := 172, numerator := 7345508837842212779838144512 }, { target := 173, numerator := 156933682958724049741545472 }, { target := 174, numerator := 177183190437269088417873920 }, { target := 175, numerator := 182245567306905348086956032 }, { target := 176, numerator := 177183190437269088417873920 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17.Parent2
