import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk15Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 63; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

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
    Slot2.Left10.expected,
    Slot2.Left11.expected,
    Slot2.Left12.expected,
    Slot2.Left13.expected,
    Slot2.Left14.expected,
    Slot2.Left15.expected,
    Slot2.Left16.expected,
    Slot2.Left17.expected,
    Slot2.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 1199254413057712141308526592 }, { target := 73, numerator := 1199254413057712141308526592 }, { target := 85, numerator := 1353996917968384675670917120 }, { target := 87, numerator := 1353996917968384675670917120 }, { target := 89, numerator := 812398150781030805402550272 }, { target := 116, numerator := 1160568786830044007717928960 }, { target := 118, numerator := 1160568786830044007717928960 }, { target := 130, numerator := 15280822359928912768286064640 }, { target := 132, numerator := 15280822359928912768286064640 }, { target := 134, numerator := 11779773186324946678336978944 }, { target := 135, numerator := 1353996917968384675670917120 }, { target := 137, numerator := 1353996917968384675670917120 }, { target := 139, numerator := 20851552536713124005332123648 }, { target := 150, numerator := 1160568786830044007717928960 }, { target := 152, numerator := 1160568786830044007717928960 }, { target := 154, numerator := 676998458984192337835458560 }, { target := 155, numerator := 1353996917968384675670917120 }, { target := 157, numerator := 1353996917968384675670917120 }, { target := 159, numerator := 12998370412496492886440804352 }, { target := 160, numerator := 676998458984192337835458560 }, { target := 187, numerator := 1353996917968384675670917120 }, { target := 189, numerator := 1353996917968384675670917120 }, { target := 201, numerator := 56132843656346461839957164032 }, { target := 203, numerator := 56132843656346461839957164032 }, { target := 205, numerator := 20716152844916285537765031936 }, { target := 206, numerator := 1392682544196052809261514752 }, { target := 208, numerator := 1392682544196052809261514752 }, { target := 210, numerator := 21663950687494154810734673920 }, { target := 221, numerator := 15280822359928912768286064640 }, { target := 223, numerator := 15280822359928912768286064640 }, { target := 225, numerator := 12998370412496492886440804352 }, { target := 226, numerator := 56132843656346461839957164032 }, { target := 228, numerator := 56132843656346461839957164032 }, { target := 230, numerator := 331864644594051084006941786112 }, { target := 231, numerator := 21257751612103639408033398784 }, { target := 232, numerator := 1199254413057712141308526592 }, { target := 234, numerator := 1199254413057712141308526592 }, { target := 236, numerator := 11779773186324946678336978944 }, { target := 237, numerator := 20716152844916285537765031936 }, { target := 248, numerator := 1353996917968384675670917120 }, { target := 250, numerator := 1353996917968384675670917120 }, { target := 252, numerator := 676998458984192337835458560 }, { target := 253, numerator := 1392682544196052809261514752 }, { target := 255, numerator := 1392682544196052809261514752 }, { target := 257, numerator := 21257751612103639408033398784 }, { target := 258, numerator := 676998458984192337835458560 }, { target := 259, numerator := 1353996917968384675670917120 }, { target := 261, numerator := 1353996917968384675670917120 }, { target := 263, numerator := 20716152844916285537765031936 }, { target := 264, numerator := 21663950687494154810734673920 }, { target := 265, numerator := 812398150781030805402550272 }]

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
    Slot3.Left0.expected,
    Slot3.Left2.expected,
    Slot4.Left0.expected,
    Slot4.Left3.expected,
    Slot4.Left5.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 1044511908147039606946136064 }, { target := 20, numerator := 1189583006500795107910877184 }, { target := 21, numerator := 928455029464035206174343168 }, { target := 22, numerator := 12447100238752221982774788096 }, { target := 23, numerator := 1102540347488541807332032512 }, { target := 24, numerator := 928455029464035206174343168 }, { target := 25, numerator := 1102540347488541807332032512 }, { target := 26, numerator := 1073526127817790707139084288 }, { target := 27, numerator := 40561879099710038069741617152 }, { target := 28, numerator := 1073526127817790707139084288 }, { target := 29, numerator := 12447100238752221982774788096 }, { target := 30, numerator := 40561879099710038069741617152 }, { target := 31, numerator := 1044511908147039606946136064 }, { target := 32, numerator := 1073526127817790707139084288 }, { target := 33, numerator := 1073526127817790707139084288 }, { target := 34, numerator := 1189583006500795107910877184 }, { target := 35, numerator := 315463901774987579916923437056 }, { target := 38, numerator := 1152237678882416447638103654400 }, { target := 40, numerator := 315463795490048758872193105920 }, { target := 71, numerator := 320452108176508895010012266496 }, { target := 73, numerator := 320452184578254304351252119552 }, { target := 89, numerator := 14690961007286631123933724672 }, { target := 90, numerator := 1044511908147039606946136064 }, { target := 91, numerator := 1189583006500795107910877184 }, { target := 92, numerator := 928455029464035206174343168 }, { target := 93, numerator := 12447100238752221982774788096 }, { target := 94, numerator := 1102540347488541807332032512 }, { target := 95, numerator := 928455029464035206174343168 }, { target := 96, numerator := 1102540347488541807332032512 }, { target := 97, numerator := 1073526127817790707139084288 }, { target := 98, numerator := 40561879099710038069741617152 }, { target := 99, numerator := 1073526127817790707139084288 }, { target := 100, numerator := 12447100238752221982774788096 }, { target := 101, numerator := 40561879099710038069741617152 }, { target := 102, numerator := 1044511908147039606946136064 }, { target := 103, numerator := 1073526127817790707139084288 }, { target := 104, numerator := 1073526127817790707139084288 }, { target := 105, numerator := 1189583006500795107910877184 }, { target := 106, numerator := 1149159491926169446502541295616 }, { target := 109, numerator := 4197326090853833947342071398400 }, { target := 111, numerator := 1149159104755575258791144325120 }, { target := 116, numerator := 12811615828562618443210338336768 }, { target := 118, numerator := 12811618883090224412262993494016 }, { target := 134, numerator := 2407565569450931002993687920640 }, { target := 140, numerator := 315464113977954708564696104960 }, { target := 143, numerator := 1152238453957640333876527104000 }, { target := 145, numerator := 315464007692944392875881267200 }, { target := 150, numerator := 12811612697634013536454679986176 }, { target := 152, numerator := 12811615752160873033869098483712 }, { target := 154, numerator := 24786819719418426991750194135040 }, { target := 232, numerator := 320452108176508895010012266496 }, { target := 234, numerator := 320452184578254304351252119552 }, { target := 236, numerator := 2407565569450931002993687920640 }, { target := 265, numerator := 14690961007286631123933724672 }]

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
    Slot7.Left0.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected,
    Slot12.Left0.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 12463874084499374962573836288 }, { target := 1, numerator := 1401291947199370253886346493952 }, { target := 2, numerator := 18336986831914695321943277568 }, { target := 3, numerator := 13199555493374862267882519134208 }, { target := 4, numerator := 11605687868300440077179289600 }, { target := 5, numerator := 696341272098026404630757376 }, { target := 6, numerator := 18336986831914695321943277568 }, { target := 7, numerator := 18220929953231690921171484672 }, { target := 8, numerator := 11605687868300440077179289600 }, { target := 9, numerator := 281205817048919663070054187008 }, { target := 10, numerator := 17988816195865682119627898880 }, { target := 11, numerator := 1401292901117399793554679660544 }, { target := 12, numerator := 18336986831914695321943277568 }, { target := 13, numerator := 696341272098026404630757376 }, { target := 14, numerator := 17988816195865682119627898880 }, { target := 15, numerator := 696341272098026404630757376 }, { target := 16, numerator := 18336986831914695321943277568 }, { target := 17, numerator := 18336986831914695321943277568 }, { target := 18, numerator := 12463874084499374962573836288 }, { target := 19, numerator := 2437720616125691731379098746880 }, { target := 21, numerator := 95369433219564793781735066173440 }, { target := 24, numerator := 95369429833629236469549257195520 }, { target := 31, numerator := 2437721744770877502107701739520 }, { target := 35, numerator := 16067510566442723577999334047744 }, { target := 38, numerator := 57794357693104071179011287416832 }, { target := 40, numerator := 16067515926651722865993100296192 }, { target := 71, numerator := 2840567586684011693374068228096 }, { target := 73, numerator := 2840566909440004567994474692608 }, { target := 89, numerator := 15331446128625275364976885760 }, { target := 90, numerator := 2437721310173042271743824101376 }, { target := 92, numerator := 95369460359146300545292436504576 }, { target := 95, numerator := 95369456973208321422407009042432 }, { target := 102, numerator := 2437722438819035312705633255424 }, { target := 106, numerator := 57592301937113264824042282549248 }, { target := 109, numerator := 207157797392361825355111222738944 }, { target := 111, numerator := 57592321150218733555792755032064 }, { target := 116, numerator := 111168731089396034196159986663424 }, { target := 118, numerator := 111168704584708286943657409380352 }, { target := 134, numerator := 4938586265811589307736753438720 }, { target := 140, numerator := 16072179757638928190384677847040 }, { target := 143, numerator := 57811152634984771375818992517120 }, { target := 145, numerator := 16072185119405595081321448734720 }, { target := 150, numerator := 111168771862313107802574601322496 }, { target := 152, numerator := 111168745357615639530276344823808 }, { target := 154, numerator := 52523941752460714852387458646016 }, { target := 232, numerator := 2840608359601085299788682887168 }, { target := 234, numerator := 2840607682347357154613410136064 }, { target := 236, numerator := 4938601150710743312858467008512 }, { target := 265, numerator := 15331446128625275364976885760 }]

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
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left3.expected,
    Slot16.Left11.expected,
    Slot16.Left18.expected,
    Slot17.Left0.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected,
    Slot21.Left0.expected,
    Slot21.Left1.expected,
    Slot21.Left2.expected,
    Slot21.Left3.expected,
    Slot21.Left4.expected,
    Slot21.Left5.expected,
    Slot21.Left6.expected,
    Slot21.Left7.expected,
    Slot21.Left8.expected,
    Slot21.Left9.expected,
    Slot21.Left10.expected,
    Slot21.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 15526007627719504747781160960 }, { target := 1, numerator := 5001258680352345517225798533120 }, { target := 3, numerator := 53190489236628998035793390862336 }, { target := 11, numerator := 5001273754146158837133320650752 }, { target := 18, numerator := 15526007627719504747781160960 }, { target := 19, numerator := 2845502554694234090339624288256 }, { target := 21, numerator := 111361866480447799370232537022464 }, { target := 24, numerator := 111361907324200378663941131206656 }, { target := 31, numerator := 2845543398446813384048218472448 }, { target := 35, numerator := 54719136310000500279636572241920 }, { target := 38, numerator := 201178746108806767110744237408256 }, { target := 40, numerator := 54715649053435303626634956898304 }, { target := 71, numerator := 2440202556003383221726467850240 }, { target := 73, numerator := 2440203252767253828875315052544 }, { target := 89, numerator := 12696894536230094735998451712 }, { target := 90, numerator := 2845501876273639044311351820288 }, { target := 92, numerator := 111361839929712992098180789174272 }, { target := 95, numerator := 111361880773455833483595101503488 }, { target := 102, numerator := 2845542720016480429725664149504 }, { target := 106, numerator := 201380291864466945148679087980544 }, { target := 109, numerator := 740562776664915678024294631211008 }, { target := 111, numerator := 201366789023603347706999818158080 }, { target := 116, numerator := 95465986449773359733467739324416 }, { target := 118, numerator := 95466013695252790735891570098176 }, { target := 134, numerator := 1428833468548239558001532338176 }, { target := 139, numerator := 18336986831914695321943277568 }, { target := 140, numerator := 54710996994225317940228907859968 }, { target := 143, numerator := 201148509882070667925326699429888 }, { target := 145, numerator := 54707511453656534783272406745088 }, { target := 150, numerator := 95465983000085877702014833524736 }, { target := 152, numerator := 95466010245562841294792818688000 }, { target := 154, numerator := 13460919040941253639000893161472 }, { target := 159, numerator := 11605687868300440077179289600 }, { target := 160, numerator := 696341272098026404630757376 }, { target := 205, numerator := 18336986831914695321943277568 }, { target := 210, numerator := 18220929953231690921171484672 }, { target := 225, numerator := 11605687868300440077179289600 }, { target := 230, numerator := 281205817048919663070054187008 }, { target := 231, numerator := 17988816195865682119627898880 }, { target := 232, numerator := 2440203705899210565544103116800 }, { target := 234, numerator := 2440204402663903642574898855936 }, { target := 236, numerator := 1428834441355735029148446359552 }, { target := 265, numerator := 12000553264132068331367694336 }]

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
    Slot21.Left12.expected,
    Slot21.Left13.expected,
    Slot21.Left14.expected,
    Slot21.Left15.expected,
    Slot21.Left16.expected,
    Slot21.Left17.expected,
    Slot21.Left18.expected,
    Slot22.Left0.expected,
    Slot23.Left0.expected,
    Slot23.Left2.expected,
    Slot24.Left0.expected,
    Slot24.Left3.expected,
    Slot24.Left5.expected,
    Slot25.Left0.expected,
    Slot25.Left1.expected,
    Slot25.Left2.expected,
    Slot25.Left3.expected,
    Slot25.Left4.expected,
    Slot25.Left5.expected,
    Slot25.Left6.expected,
    Slot25.Left7.expected,
    Slot25.Left8.expected,
    Slot25.Left9.expected,
    Slot25.Left10.expected,
    Slot25.Left11.expected,
    Slot25.Left12.expected,
    Slot25.Left13.expected,
    Slot25.Left14.expected,
    Slot25.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 15240890028949767048359051264 }, { target := 1, numerator := 2497688344777971200966713671680 }, { target := 3, numerator := 25714668585920721050264907284480 }, { target := 11, numerator := 2497688344777971200966713671680 }, { target := 18, numerator := 15240890028949767048359051264 }, { target := 19, numerator := 312718723967121048373269889024 }, { target := 21, numerator := 12502436562714953443072532283392 }, { target := 24, numerator := 12502433507344203255031942610944 }, { target := 31, numerator := 312718723967121048373269889024 }, { target := 35, numerator := 330367708158057859283077300224 }, { target := 38, numerator := 1203450491544728632951480254464 }, { target := 40, numerator := 330367930386362017630744739840 }, { target := 71, numerator := 1392682544196052809261514752 }, { target := 73, numerator := 1392682544196052809261514752 }, { target := 85, numerator := 1586110675334393477214502912 }, { target := 87, numerator := 1586110675334393477214502912 }, { target := 90, numerator := 312718798525083763069773938688 }, { target := 92, numerator := 12502439543528469373656345083904 }, { target := 95, numerator := 12502436488156990728376028233728 }, { target := 102, numerator := 312718798525083763069773938688 }, { target := 106, numerator := 1206674104656388878235179417600 }, { target := 109, numerator := 4395624961287873346429098393600 }, { target := 111, numerator := 1206674916349339877209276416000 }, { target := 116, numerator := 1237940039285380274899124224 }, { target := 118, numerator := 1237940039285380274899124224 }, { target := 130, numerator := 16596133651669629310366384128 }, { target := 132, numerator := 16596133651669629310366384128 }, { target := 135, numerator := 1470053796651389076442710016 }, { target := 137, numerator := 1470053796651389076442710016 }, { target := 140, numerator := 330367596851783345905525063680 }, { target := 143, numerator := 1203450086082610310387576340480 }, { target := 145, numerator := 330367819080012631909387468800 }, { target := 150, numerator := 1237940039285380274899124224 }, { target := 152, numerator := 1237940039285380274899124224 }, { target := 155, numerator := 1470053796651389076442710016 }, { target := 157, numerator := 1470053796651389076442710016 }, { target := 187, numerator := 1431368170423720942852112384 }, { target := 189, numerator := 1431368170423720942852112384 }, { target := 201, numerator := 54082505466280050759655489536 }, { target := 203, numerator := 54082505466280050759655489536 }, { target := 206, numerator := 1431368170423720942852112384 }, { target := 208, numerator := 1431368170423720942852112384 }, { target := 221, numerator := 16596133651669629310366384128 }, { target := 223, numerator := 16596133651669629310366384128 }, { target := 226, numerator := 54082505466280050759655489536 }, { target := 228, numerator := 54082505466280050759655489536 }, { target := 232, numerator := 1392682544196052809261514752 }, { target := 234, numerator := 1392682544196052809261514752 }, { target := 237, numerator := 18336986831914695321943277568 }, { target := 248, numerator := 1431368170423720942852112384 }, { target := 250, numerator := 1431368170423720942852112384 }, { target := 252, numerator := 696341272098026404630757376 }, { target := 253, numerator := 1431368170423720942852112384 }, { target := 255, numerator := 1431368170423720942852112384 }, { target := 257, numerator := 17988816195865682119627898880 }, { target := 258, numerator := 696341272098026404630757376 }, { target := 259, numerator := 1586110675334393477214502912 }, { target := 261, numerator := 1586110675334393477214502912 }, { target := 263, numerator := 18336986831914695321943277568 }, { target := 264, numerator := 18336986831914695321943277568 }, { target := 265, numerator := 696341272098026404630757376 }]

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
    Slot26.Left0.expected,
    Slot27.Left0.expected,
    Slot27.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 812398150781030805402550272 }, { target := 1, numerator := 11779773186324946678336978944 }, { target := 2, numerator := 20851552536713124005332123648 }, { target := 3, numerator := 676998458984192337835458560 }, { target := 4, numerator := 12998370412496492886440804352 }, { target := 5, numerator := 676998458984192337835458560 }, { target := 6, numerator := 20716152844916285537765031936 }, { target := 7, numerator := 21663950687494154810734673920 }, { target := 8, numerator := 12998370412496492886440804352 }, { target := 9, numerator := 331864644594051084006941786112 }, { target := 10, numerator := 21257751612103639408033398784 }, { target := 11, numerator := 11779773186324946678336978944 }, { target := 12, numerator := 20716152844916285537765031936 }, { target := 13, numerator := 676998458984192337835458560 }, { target := 14, numerator := 21257751612103639408033398784 }, { target := 15, numerator := 676998458984192337835458560 }, { target := 16, numerator := 20716152844916285537765031936 }, { target := 17, numerator := 21663950687494154810734673920 }, { target := 18, numerator := 812398150781030805402550272 }, { target := 19, numerator := 1199254413057712141308526592 }, { target := 20, numerator := 1353996917968384675670917120 }, { target := 21, numerator := 1160568786830044007717928960 }, { target := 22, numerator := 15280822359928912768286064640 }, { target := 23, numerator := 1353996917968384675670917120 }, { target := 24, numerator := 1160568786830044007717928960 }, { target := 25, numerator := 1353996917968384675670917120 }, { target := 26, numerator := 1353996917968384675670917120 }, { target := 27, numerator := 56132843656346461839957164032 }, { target := 28, numerator := 1392682544196052809261514752 }, { target := 29, numerator := 15280822359928912768286064640 }, { target := 30, numerator := 56132843656346461839957164032 }, { target := 31, numerator := 1199254413057712141308526592 }, { target := 32, numerator := 1353996917968384675670917120 }, { target := 33, numerator := 1392682544196052809261514752 }, { target := 34, numerator := 1353996917968384675670917120 }, { target := 90, numerator := 1199254413057712141308526592 }, { target := 91, numerator := 1353996917968384675670917120 }, { target := 92, numerator := 1160568786830044007717928960 }, { target := 93, numerator := 15280822359928912768286064640 }, { target := 94, numerator := 1353996917968384675670917120 }, { target := 95, numerator := 1160568786830044007717928960 }, { target := 96, numerator := 1353996917968384675670917120 }, { target := 97, numerator := 1353996917968384675670917120 }, { target := 98, numerator := 56132843656346461839957164032 }, { target := 99, numerator := 1392682544196052809261514752 }, { target := 100, numerator := 15280822359928912768286064640 }, { target := 101, numerator := 56132843656346461839957164032 }, { target := 102, numerator := 1199254413057712141308526592 }, { target := 103, numerator := 1353996917968384675670917120 }, { target := 104, numerator := 1392682544196052809261514752 }, { target := 105, numerator := 1353996917968384675670917120 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15.Parent1
