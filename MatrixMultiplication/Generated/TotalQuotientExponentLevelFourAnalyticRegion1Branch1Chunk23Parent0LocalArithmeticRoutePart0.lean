import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk23Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 94; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23.Parent0

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
    Slot0.Left6.expected,
    Slot0.Left14.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left3.expected,
    Slot1.Left11.expected,
    Slot1.Left18.expected,
    Slot3.Left0.expected,
    Slot3.Left2.expected,
    Slot3.Left5.expected,
    Slot3.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 196303153047634688547487744 }, { target := 87, numerator := 3926063060952693770949754880 }, { target := 88, numerator := 203313979942193070281326592 }, { target := 89, numerator := 3652640812064916883330039808 }, { target := 90, numerator := 5468444977755537752394301440 }, { target := 91, numerator := 196303153047634688547487744 }, { target := 92, numerator := 5475455804650096134128140288 }, { target := 93, numerator := 5475455804650096134128140288 }, { target := 94, numerator := 3919052234058135389215916032 }, { target := 95, numerator := 203313979942193070281326592 }, { target := 122, numerator := 69405505642450713764167680 }, { target := 123, numerator := 76232276689249144626216960 }, { target := 124, numerator := 69405505642450713764167680 }, { target := 125, numerator := 76232276689249144626216960 }, { target := 161, numerator := 7656879907341258171103576064 }, { target := 162, numerator := 153137598146825163422071521280 }, { target := 163, numerator := 7930339904032017391500132352 }, { target := 164, numerator := 142472658275885553826605826048 }, { target := 165, numerator := 213298797418792191909313904640 }, { target := 166, numerator := 7656879907341258171103576064 }, { target := 167, numerator := 213572257415482951129710460928 }, { target := 168, numerator := 213572257415482951129710460928 }, { target := 169, numerator := 152864138150134404201674964992 }, { target := 170, numerator := 7930339904032017391500132352 }, { target := 197, numerator := 8203285167387829838995783680 }, { target := 198, numerator := 9010165675655485232995368960 }, { target := 199, numerator := 8203285167387829838995783680 }, { target := 200, numerator := 9010165675655485232995368960 }, { target := 215, numerator := 224581582825831717427740672 }, { target := 232, numerator := 7656877098824472948824342528 }, { target := 233, numerator := 153137541976489458976486850560 }, { target := 234, numerator := 7930336995211061268425211904 }, { target := 235, numerator := 142472606017412514512052944896 }, { target := 236, numerator := 213298719181538889288678113280 }, { target := 237, numerator := 7656877098824472948824342528 }, { target := 238, numerator := 213572179077925477608278982656 }, { target := 239, numerator := 213572179077925477608278982656 }, { target := 240, numerator := 152864082080102870656885981184 }, { target := 241, numerator := 7930336995211061268425211904 }, { target := 242, numerator := 77847541023192742374125076480 }, { target := 243, numerator := 85504676205801864574858690560 }, { target := 244, numerator := 77847541023192742374125076480 }, { target := 245, numerator := 85504676205801864574858690560 }, { target := 260, numerator := 39389499674306337079344234496 }, { target := 406, numerator := 196304089219896429307232256 }, { target := 407, numerator := 3926081784397928586144645120 }, { target := 408, numerator := 203314949549178444639633408 }, { target := 409, numerator := 3652658231555929988181000192 }, { target := 410, numerator := 5468471056839971959272898560 }, { target := 411, numerator := 196304089219896429307232256 }, { target := 412, numerator := 5475481917169253974605299712 }, { target := 413, numerator := 5475481917169253974605299712 }, { target := 414, numerator := 3919070924068646570812243968 }, { target := 415, numerator := 203314949549178444639633408 }, { target := 416, numerator := 8203290793644772320409026560 }, { target := 417, numerator := 9010171855314749925695160320 }, { target := 418, numerator := 8203290793644772320409026560 }, { target := 419, numerator := 9010171855314749925695160320 }, { target := 420, numerator := 39389504396672819948989448192 }, { target := 498, numerator := 69405505642450713764167680 }, { target := 499, numerator := 76232276689249144626216960 }, { target := 500, numerator := 69405505642450713764167680 }, { target := 501, numerator := 76232276689249144626216960 }, { target := 502, numerator := 224576860459348847782526976 }]

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
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot4.Left4.expected,
    Slot4.Left5.expected,
    Slot4.Left6.expected,
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot4.Left10.expected,
    Slot4.Left11.expected,
    Slot4.Left12.expected,
    Slot4.Left13.expected,
    Slot4.Left14.expected,
    Slot4.Left15.expected,
    Slot4.Left16.expected,
    Slot4.Left17.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 6282758412468567654694649856 }, { target := 36, numerator := 7155363747533646495624462336 }, { target := 37, numerator := 5584674144416504581950799872 }, { target := 38, numerator := 74869537748583764551777910784 }, { target := 39, numerator := 6631800546494599191066574848 }, { target := 40, numerator := 5584674144416504581950799872 }, { target := 41, numerator := 6631800546494599191066574848 }, { target := 42, numerator := 6457279479481583422880612352 }, { target := 43, numerator := 243980451684196043923975569408 }, { target := 44, numerator := 6457279479481583422880612352 }, { target := 45, numerator := 74869537748583764551777910784 }, { target := 46, numerator := 243980451684196043923975569408 }, { target := 47, numerator := 6282758412468567654694649856 }, { target := 48, numerator := 6457279479481583422880612352 }, { target := 49, numerator := 6457279479481583422880612352 }, { target := 50, numerator := 7155363747533646495624462336 }, { target := 122, numerator := 522255954073519803473068032 }, { target := 124, numerator := 522255954073519803473068032 }, { target := 197, numerator := 7833839311102797052096020480 }, { target := 199, numerator := 7833839311102797052096020480 }, { target := 211, numerator := 13752740123936021491457458176 }, { target := 213, numerator := 13752740123936021491457458176 }, { target := 242, numerator := 522255954073519803473068032 }, { target := 244, numerator := 522255954073519803473068032 }, { target := 256, numerator := 8704265901225330057884467200 }, { target := 258, numerator := 8704265901225330057884467200 }, { target := 261, numerator := 522255954073519803473068032 }, { target := 263, numerator := 522255954073519803473068032 }, { target := 337, numerator := 13752740123936021491457458176 }, { target := 339, numerator := 13752740123936021491457458176 }, { target := 351, numerator := 13665697464923768190878613504 }, { target := 353, numerator := 13665697464923768190878613504 }, { target := 382, numerator := 8704265901225330057884467200 }, { target := 384, numerator := 8704265901225330057884467200 }, { target := 396, numerator := 210904362786689747302540640256 }, { target := 398, numerator := 210904362786689747302540640256 }, { target := 401, numerator := 13491612146899261589720924160 }, { target := 403, numerator := 13491612146899261589720924160 }, { target := 416, numerator := 7833839311102797052096020480 }, { target := 418, numerator := 7833839311102797052096020480 }, { target := 421, numerator := 13752740123936021491457458176 }, { target := 423, numerator := 13752740123936021491457458176 }, { target := 453, numerator := 522255954073519803473068032 }, { target := 455, numerator := 522255954073519803473068032 }, { target := 467, numerator := 13491612146899261589720924160 }, { target := 469, numerator := 13491612146899261589720924160 }, { target := 472, numerator := 522255954073519803473068032 }, { target := 474, numerator := 522255954073519803473068032 }, { target := 487, numerator := 13752740123936021491457458176 }, { target := 489, numerator := 13752740123936021491457458176 }, { target := 492, numerator := 13752740123936021491457458176 }, { target := 494, numerator := 13752740123936021491457458176 }, { target := 498, numerator := 522255954073519803473068032 }, { target := 500, numerator := 522255954073519803473068032 }]

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
    Slot5.Left3.expected,
    Slot5.Left5.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot6.Left4.expected,
    Slot6.Left5.expected,
    Slot6.Left6.expected,
    Slot6.Left7.expected,
    Slot6.Left8.expected,
    Slot6.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 6159567071047615347739852800 }, { target := 89, numerator := 22497931538064797828382720000 }, { target := 91, numerator := 6159564995788907055415296000 }, { target := 112, numerator := 7015062497582006368259276800 }, { target := 115, numerator := 25622644251684908637880320000 }, { target := 117, numerator := 7015060134092921924222976000 }, { target := 145, numerator := 22947890168826093784950374400 }, { target := 146, numerator := 26135097136718606810637926400 }, { target := 147, numerator := 20398124594512083364400332800 }, { target := 148, numerator := 273462357845177617603991961600 }, { target := 149, numerator := 24222772955983098995225395200 }, { target := 150, numerator := 20398124594512083364400332800 }, { target := 151, numerator := 24222772955983098995225395200 }, { target := 152, numerator := 23585331562404596390087884800 }, { target := 153, numerator := 891143068222746641982239539200 }, { target := 154, numerator := 23585331562404596390087884800 }, { target := 155, numerator := 273462357845177617603991961600 }, { target := 156, numerator := 891143068222746641982239539200 }, { target := 157, numerator := 22947890168826093784950374400 }, { target := 158, numerator := 23585331562404596390087884800 }, { target := 159, numerator := 23585331562404596390087884800 }, { target := 160, numerator := 26135097136718606810637926400 }, { target := 161, numerator := 5475170729820102531324313600 }, { target := 164, numerator := 19998161367168709180784640000 }, { target := 166, numerator := 5475168885145695160369152000 }, { target := 187, numerator := 73401507596650749560566579200 }, { target := 190, numerator := 268100350828605507454894080000 }, { target := 192, numerator := 73401482866484475743698944000 }, { target := 201, numerator := 6501765241661371755947622400 }, { target := 204, numerator := 23747816623512842152181760000 }, { target := 206, numerator := 6501763051110513002938368000 }, { target := 216, numerator := 6282756295704685196523601920 }, { target := 217, numerator := 7155361336774780362707435520 }, { target := 218, numerator := 5584672262848609063576535040 }, { target := 219, numerator := 74869512523814165258572922880 }, { target := 220, numerator := 6631798312132723262997135360 }, { target := 221, numerator := 5584672262848609063576535040 }, { target := 222, numerator := 6631798312132723262997135360 }, { target := 223, numerator := 6457277303918704229760368640 }, { target := 224, numerator := 243980369483198608464999874560 }, { target := 225, numerator := 6457277303918704229760368640 }, { target := 226, numerator := 74869512523814165258572922880 }, { target := 227, numerator := 243980369483198608464999874560 }, { target := 228, numerator := 6282756295704685196523601920 }, { target := 229, numerator := 6457277303918704229760368640 }, { target := 230, numerator := 6457277303918704229760368640 }, { target := 231, numerator := 7155361336774780362707435520 }, { target := 232, numerator := 5475170729820102531324313600 }, { target := 235, numerator := 19998161367168709180784640000 }, { target := 237, numerator := 5475168885145695160369152000 }, { target := 246, numerator := 6501765241661371755947622400 }, { target := 249, numerator := 23747816623512842152181760000 }, { target := 251, numerator := 6501763051110513002938368000 }, { target := 301, numerator := 6330666156354493551843737600 }, { target := 304, numerator := 23122874080788819990282240000 }, { target := 306, numerator := 6330664023449710029176832000 }, { target := 327, numerator := 239196521259015729337230950400 }, { target := 330, numerator := 873669674728182982335528960000 }, { target := 332, numerator := 239196440669802557318627328000 }, { target := 341, numerator := 6330666156354493551843737600 }, { target := 344, numerator := 23122874080788819990282240000 }, { target := 346, numerator := 6330664023449710029176832000 }]

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
    Slot6.Left10.expected,
    Slot6.Left11.expected,
    Slot6.Left12.expected,
    Slot6.Left13.expected,
    Slot6.Left14.expected,
    Slot6.Left15.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 522255954073519803473068032 }, { target := 17, numerator := 7833839311102797052096020480 }, { target := 18, numerator := 13752740123936021491457458176 }, { target := 19, numerator := 522255954073519803473068032 }, { target := 20, numerator := 8704265901225330057884467200 }, { target := 21, numerator := 522255954073519803473068032 }, { target := 22, numerator := 13752740123936021491457458176 }, { target := 23, numerator := 13665697464923768190878613504 }, { target := 24, numerator := 8704265901225330057884467200 }, { target := 25, numerator := 210904362786689747302540640256 }, { target := 26, numerator := 13491612146899261589720924160 }, { target := 27, numerator := 7833839311102797052096020480 }, { target := 28, numerator := 13752740123936021491457458176 }, { target := 29, numerator := 522255954073519803473068032 }, { target := 30, numerator := 13491612146899261589720924160 }, { target := 31, numerator := 522255954073519803473068032 }, { target := 32, numerator := 13752740123936021491457458176 }, { target := 33, numerator := 13752740123936021491457458176 }, { target := 34, numerator := 522255954073519803473068032 }, { target := 35, numerator := 203072227290656574359470080 }, { target := 37, numerator := 7920910248973715349417492480 }, { target := 40, numerator := 7920907343611523740163112960 }, { target := 47, numerator := 203073195744720444110929920 }, { target := 70, numerator := 4061444545813131487189401600 }, { target := 72, numerator := 158418204979474306988349849600 }, { target := 75, numerator := 158418146872230474803262259200 }, { target := 82, numerator := 4061463914894408882218598400 }, { target := 126, numerator := 522255954073519803473068032 }, { target := 127, numerator := 7833839311102797052096020480 }, { target := 128, numerator := 13752740123936021491457458176 }, { target := 129, numerator := 522255954073519803473068032 }, { target := 130, numerator := 8704265901225330057884467200 }, { target := 131, numerator := 522255954073519803473068032 }, { target := 132, numerator := 13752740123936021491457458176 }, { target := 133, numerator := 13665697464923768190878613504 }, { target := 134, numerator := 8704265901225330057884467200 }, { target := 135, numerator := 210904362786689747302540640256 }, { target := 136, numerator := 13491612146899261589720924160 }, { target := 137, numerator := 7833839311102797052096020480 }, { target := 138, numerator := 13752740123936021491457458176 }, { target := 139, numerator := 522255954073519803473068032 }, { target := 140, numerator := 13491612146899261589720924160 }, { target := 141, numerator := 522255954073519803473068032 }, { target := 142, numerator := 13752740123936021491457458176 }, { target := 143, numerator := 13752740123936021491457458176 }, { target := 144, numerator := 522255954073519803473068032 }, { target := 372, numerator := 73401507596650749560566579200 }, { target := 375, numerator := 268100350828605507454894080000 }, { target := 377, numerator := 73401482866484475743698944000 }, { target := 386, numerator := 239196521259015729337230950400 }, { target := 389, numerator := 873669674728182982335528960000 }, { target := 391, numerator := 239196440669802557318627328000 }, { target := 406, numerator := 6159567071047615347739852800 }, { target := 409, numerator := 22497931538064797828382720000 }, { target := 411, numerator := 6159564995788907055415296000 }, { target := 443, numerator := 6330666156354493551843737600 }, { target := 446, numerator := 23122874080788819990282240000 }, { target := 448, numerator := 6330664023449710029176832000 }, { target := 457, numerator := 6330666156354493551843737600 }, { target := 460, numerator := 23122874080788819990282240000 }, { target := 462, numerator := 6330664023449710029176832000 }, { target := 477, numerator := 7015062497582006368259276800 }, { target := 480, numerator := 25622644251684908637880320000 }, { target := 482, numerator := 7015060134092921924222976000 }]

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
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot8.Left4.expected,
    Slot8.Left5.expected,
    Slot8.Left6.expected,
    Slot8.Left7.expected,
    Slot8.Left8.expected,
    Slot8.Left9.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected,
    Slot11.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 224581582825831717427740672 }, { target := 1, numerator := 39389499674306337079344234496 }, { target := 6, numerator := 39389504396672819948989448192 }, { target := 14, numerator := 224576860459348847782526976 }, { target := 16, numerator := 69405505642450713764167680 }, { target := 17, numerator := 8203285167387829838995783680 }, { target := 19, numerator := 77847541023192742374125076480 }, { target := 27, numerator := 8203290793644772320409026560 }, { target := 34, numerator := 69405505642450713764167680 }, { target := 51, numerator := 76232276689249144626216960 }, { target := 52, numerator := 9010165675655485232995368960 }, { target := 54, numerator := 85504676205801864574858690560 }, { target := 62, numerator := 9010171855314749925695160320 }, { target := 69, numerator := 76232276689249144626216960 }, { target := 96, numerator := 210324806836751452015165440 }, { target := 98, numerator := 8203799900722776611896688640 }, { target := 101, numerator := 8203796891597649588026081280 }, { target := 108, numerator := 210325809878460459972034560 }, { target := 126, numerator := 69405505642450713764167680 }, { target := 127, numerator := 8203285167387829838995783680 }, { target := 129, numerator := 77847541023192742374125076480 }, { target := 137, numerator := 8203290793644772320409026560 }, { target := 144, numerator := 69405505642450713764167680 }, { target := 145, numerator := 3778593943515431258617282560 }, { target := 147, numerator := 147385508561260917751661199360 }, { target := 150, numerator := 147385454500771566736606494720 }, { target := 157, numerator := 3778611963678548263635517440 }, { target := 171, numerator := 5657012045954004571442380800 }, { target := 173, numerator := 220653928364267784733773004800 }, { target := 176, numerator := 220653847429178161333115289600 }, { target := 183, numerator := 5657039024317212371661619200 }, { target := 216, numerator := 203072227290656574359470080 }, { target := 218, numerator := 7920910248973715349417492480 }, { target := 221, numerator := 7920907343611523740163112960 }, { target := 228, numerator := 203073195744720444110929920 }, { target := 266, numerator := 76232276689249144626216960 }, { target := 267, numerator := 9010165675655485232995368960 }, { target := 269, numerator := 85504676205801864574858690560 }, { target := 277, numerator := 9010171855314749925695160320 }, { target := 284, numerator := 76232276689249144626216960 }, { target := 285, numerator := 5664264625500099449098076160 }, { target := 287, numerator := 220936818016016845996252200960 }, { target := 290, numerator := 220936736977164287180978257920 }, { target := 297, numerator := 5664291638450952387522723840 }, { target := 311, numerator := 5664264625500099449098076160 }, { target := 313, numerator := 220936818016016845996252200960 }, { target := 316, numerator := 220936736977164287180978257920 }, { target := 323, numerator := 5664291638450952387522723840 }, { target := 356, numerator := 4054191966267036609533706240 }, { target := 358, numerator := 158135315327725245725870653440 }, { target := 361, numerator := 158135257324244348955399290880 }, { target := 368, numerator := 4054211300760668866357493760 }, { target := 427, numerator := 210324806836751452015165440 }, { target := 429, numerator := 8203799900722776611896688640 }, { target := 432, numerator := 8203796891597649588026081280 }, { target := 439, numerator := 210325809878460459972034560 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23.Parent0
