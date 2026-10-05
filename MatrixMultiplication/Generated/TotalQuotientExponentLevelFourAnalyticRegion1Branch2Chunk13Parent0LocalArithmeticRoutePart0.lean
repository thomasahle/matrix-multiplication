import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk13Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 54; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent0

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
    Slot2.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 3017202621906511684027023360 }, { target := 134, numerator := 10793843168264323751812792320 }, { target := 136, numerator := 3017201618864802676070154240 }, { target := 227, numerator := 80458736584173644907387289600 }, { target := 230, numerator := 287835817820381966715007795200 }, { target := 232, numerator := 80458709836394738028537446400 }, { target := 253, numerator := 76938666858616047942689095680 }, { target := 256, numerator := 275243000790740255671226204160 }, { target := 258, numerator := 76938641281052468239788933120 }, { target := 263, numerator := 20309953769525770135063756800 }, { target := 265, numerator := 20309953769525770135063756800 }, { target := 302, numerator := 2514335518255426403355852800 }, { target := 305, numerator := 8994869306886936459843993600 }, { target := 307, numerator := 2514334682387335563391795200 }, { target := 328, numerator := 78950135273220389065373777920 }, { target := 331, numerator := 282438896236249804839101399040 }, { target := 333, numerator := 78950109026962336690502369280 }, { target := 338, numerator := 20890238162940792138922721280 }, { target := 340, numerator := 20890238162940792138922721280 }, { target := 342, numerator := 2514335518255426403355852800 }, { target := 345, numerator := 8994869306886936459843993600 }, { target := 347, numerator := 2514334682387335563391795200 }, { target := 352, numerator := 20309953769525770135063756800 }, { target := 354, numerator := 20309953769525770135063756800 }, { target := 356, numerator := 1450710983537555009647411200 }, { target := 443, numerator := 76938666858616047942689095680 }, { target := 446, numerator := 275243000790740255671226204160 }, { target := 448, numerator := 76938641281052468239788933120 }, { target := 479, numerator := 17988816195865682119627898880 }, { target := 481, numerator := 17988816195865682119627898880 }, { target := 554, numerator := 841992654845196927599357460480 }, { target := 556, numerator := 841992654845196927599357460480 }, { target := 568, numerator := 229212335398933691524290969600 }, { target := 570, numerator := 229212335398933691524290969600 }, { target := 572, numerator := 29072248110092602393334120448 }, { target := 599, numerator := 20890238162940792138922721280 }, { target := 601, numerator := 20890238162940792138922721280 }, { target := 613, numerator := 841992654845196927599357460480 }, { target := 615, numerator := 841992654845196927599357460480 }, { target := 617, numerator := 48801917486203350524538912768 }, { target := 618, numerator := 20309953769525770135063756800 }, { target := 620, numerator := 20309953769525770135063756800 }, { target := 622, numerator := 46828950548592275711418433536 }, { target := 694, numerator := 20309953769525770135063756800 }, { target := 696, numerator := 20309953769525770135063756800 }, { target := 708, numerator := 17408531802450660115768934400 }, { target := 710, numerator := 17408531802450660115768934400 }, { target := 712, numerator := 1450710983537555009647411200 }, { target := 739, numerator := 20309953769525770135063756800 }, { target := 741, numerator := 20309953769525770135063756800 }, { target := 753, numerator := 229212335398933691524290969600 }, { target := 755, numerator := 229212335398933691524290969600 }, { target := 757, numerator := 46828950548592275711418433536 }, { target := 758, numerator := 17408531802450660115768934400 }, { target := 760, numerator := 17408531802450660115768934400 }, { target := 762, numerator := 31277328805069686007998185472 }, { target := 773, numerator := 20309953769525770135063756800 }, { target := 775, numerator := 20309953769525770135063756800 }, { target := 777, numerator := 1508739422879057210033307648 }, { target := 778, numerator := 17988816195865682119627898880 }, { target := 780, numerator := 17988816195865682119627898880 }, { target := 782, numerator := 29072248110092602393334120448 }, { target := 783, numerator := 1392682544196052809261514752 }]

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
    Slot2.Left18.expected,
    Slot3.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 188592427859882151254163456 }, { target := 81, numerator := 223953508083610054614319104 }, { target := 82, numerator := 170911887748018199574085632 }, { target := 83, numerator := 1762160497815773850781089792 }, { target := 84, numerator := 212166481342367420160933888 }, { target := 85, numerator := 170911887748018199574085632 }, { target := 86, numerator := 212166481342367420160933888 }, { target := 87, numerator := 212166481342367420160933888 }, { target := 88, numerator := 9087797617498071163560001536 }, { target := 89, numerator := 212166481342367420160933888 }, { target := 90, numerator := 1762160497815773850781089792 }, { target := 91, numerator := 9087797617498071163560001536 }, { target := 92, numerator := 188592427859882151254163456 }, { target := 93, numerator := 212166481342367420160933888 }, { target := 94, numerator := 212166481342367420160933888 }, { target := 95, numerator := 223953508083610054614319104 }, { target := 469, numerator := 43749438017644419418391838720 }, { target := 472, numerator := 156510725939832694401285488640 }, { target := 474, numerator := 43749423473539638803017236480 }, { target := 518, numerator := 78950135273220389065373777920 }, { target := 521, numerator := 282438896236249804839101399040 }, { target := 523, numerator := 78950109026962336690502369280 }, { target := 544, numerator := 1232527271048810022925039042560 }, { target := 547, numerator := 4409284934235976252615525662720 }, { target := 549, numerator := 1232526861306271893174658007040 }, { target := 558, numerator := 48275241950504186944432373760 }, { target := 561, numerator := 172701490692229180029004677120 }, { target := 563, numerator := 48275225901836842817122467840 }, { target := 589, numerator := 80458736584173644907387289600 }, { target := 592, numerator := 287835817820381966715007795200 }, { target := 594, numerator := 80458709836394738028537446400 }, { target := 603, numerator := 76938666858616047942689095680 }, { target := 606, numerator := 275243000790740255671226204160 }, { target := 608, numerator := 76938641281052468239788933120 }, { target := 658, numerator := 2514335518255426403355852800 }, { target := 661, numerator := 8994869306886936459843993600 }, { target := 663, numerator := 2514334682387335563391795200 }, { target := 684, numerator := 48275241950504186944432373760 }, { target := 687, numerator := 172701490692229180029004677120 }, { target := 689, numerator := 48275225901836842817122467840 }, { target := 698, numerator := 2514335518255426403355852800 }, { target := 701, numerator := 8994869306886936459843993600 }, { target := 703, numerator := 2514334682387335563391795200 }, { target := 729, numerator := 77441533962267133223360266240 }, { target := 732, numerator := 277041974652117642963195002880 }, { target := 734, numerator := 77441508217529935352467292160 }, { target := 743, numerator := 43749438017644419418391838720 }, { target := 746, numerator := 156510725939832694401285488640 }, { target := 748, numerator := 43749423473539638803017236480 }, { target := 763, numerator := 3017202621906511684027023360 }, { target := 766, numerator := 10793843168264323751812792320 }, { target := 768, numerator := 3017201618864802676070154240 }]

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
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 115, numerator := 184663418946134606436368384 }, { target := 116, numerator := 219287809998534845143187456 }, { target := 117, numerator := 167351223419934487082958848 }, { target := 118, numerator := 1725448820777945228889817088 }, { target := 119, numerator := 207746346314401432240914432 }, { target := 120, numerator := 167351223419934487082958848 }, { target := 121, numerator := 207746346314401432240914432 }, { target := 122, numerator := 207746346314401432240914432 }, { target := 123, numerator := 8898468500466861347652501504 }, { target := 124, numerator := 207746346314401432240914432 }, { target := 125, numerator := 1725448820777945228889817088 }, { target := 126, numerator := 8898468500466861347652501504 }, { target := 127, numerator := 184663418946134606436368384 }, { target := 128, numerator := 207746346314401432240914432 }, { target := 129, numerator := 207746346314401432240914432 }, { target := 130, numerator := 219287809998534845143187456 }, { target := 176, numerator := 145373329808659158258417664 }, { target := 177, numerator := 172630829147782750431870976 }, { target := 178, numerator := 131744580139097362171691008 }, { target := 179, numerator := 1358332050399659009977090048 }, { target := 180, numerator := 163544996034741553040719872 }, { target := 181, numerator := 131744580139097362171691008 }, { target := 182, numerator := 163544996034741553040719872 }, { target := 183, numerator := 163544996034741553040719872 }, { target := 184, numerator := 7005177330154763188577501184 }, { target := 185, numerator := 163544996034741553040719872 }, { target := 186, numerator := 1358332050399659009977090048 }, { target := 187, numerator := 7005177330154763188577501184 }, { target := 188, numerator := 145373329808659158258417664 }, { target := 189, numerator := 163544996034741553040719872 }, { target := 190, numerator := 163544996034741553040719872 }, { target := 191, numerator := 172630829147782750431870976 }, { target := 211, numerator := 4569437366688394623095668736 }, { target := 212, numerator := 5426206872942468614926106624 }, { target := 213, numerator := 4141052613561357627180449792 }, { target := 214, numerator := 42695680394994687259550154752 }, { target := 215, numerator := 5140617037524443950982627328 }, { target := 216, numerator := 4141052613561357627180449792 }, { target := 217, numerator := 5140617037524443950982627328 }, { target := 218, numerator := 5140617037524443950982627328 }, { target := 219, numerator := 220189763107297015900422537216 }, { target := 220, numerator := 5140617037524443950982627328 }, { target := 221, numerator := 42695680394994687259550154752 }, { target := 222, numerator := 220189763107297015900422537216 }, { target := 223, numerator := 4569437366688394623095668736 }, { target := 224, numerator := 5140617037524443950982627328 }, { target := 225, numerator := 5140617037524443950982627328 }, { target := 226, numerator := 5426206872942468614926106624 }, { target := 237, numerator := 145373329808659158258417664 }, { target := 238, numerator := 172630829147782750431870976 }, { target := 239, numerator := 131744580139097362171691008 }, { target := 240, numerator := 1358332050399659009977090048 }, { target := 241, numerator := 163544996034741553040719872 }, { target := 242, numerator := 131744580139097362171691008 }, { target := 243, numerator := 163544996034741553040719872 }, { target := 244, numerator := 163544996034741553040719872 }, { target := 245, numerator := 7005177330154763188577501184 }, { target := 246, numerator := 163544996034741553040719872 }, { target := 247, numerator := 1358332050399659009977090048 }, { target := 248, numerator := 7005177330154763188577501184 }, { target := 249, numerator := 145373329808659158258417664 }, { target := 250, numerator := 163544996034741553040719872 }, { target := 251, numerator := 163544996034741553040719872 }, { target := 252, numerator := 172630829147782750431870976 }]

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
    Slot3.Left5.expected,
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 286, numerator := 145373329808659158258417664 }, { target := 287, numerator := 172630829147782750431870976 }, { target := 288, numerator := 131744580139097362171691008 }, { target := 289, numerator := 1358332050399659009977090048 }, { target := 290, numerator := 163544996034741553040719872 }, { target := 291, numerator := 131744580139097362171691008 }, { target := 292, numerator := 163544996034741553040719872 }, { target := 293, numerator := 163544996034741553040719872 }, { target := 294, numerator := 7005177330154763188577501184 }, { target := 295, numerator := 163544996034741553040719872 }, { target := 296, numerator := 1358332050399659009977090048 }, { target := 297, numerator := 7005177330154763188577501184 }, { target := 298, numerator := 145373329808659158258417664 }, { target := 299, numerator := 163544996034741553040719872 }, { target := 300, numerator := 163544996034741553040719872 }, { target := 301, numerator := 172630829147782750431870976 }, { target := 312, numerator := 149302338722406703076212736 }, { target := 313, numerator := 177296527232857959903002624 }, { target := 314, numerator := 135305244467181074662817792 }, { target := 315, numerator := 1395043727437487631868362752 }, { target := 316, numerator := 167965131062707540960739328 }, { target := 317, numerator := 135305244467181074662817792 }, { target := 318, numerator := 167965131062707540960739328 }, { target := 319, numerator := 167965131062707540960739328 }, { target := 320, numerator := 7194506447185973004485001216 }, { target := 321, numerator := 167965131062707540960739328 }, { target := 322, numerator := 1395043727437487631868362752 }, { target := 323, numerator := 7194506447185973004485001216 }, { target := 324, numerator := 149302338722406703076212736 }, { target := 325, numerator := 167965131062707540960739328 }, { target := 326, numerator := 167965131062707540960739328 }, { target := 327, numerator := 177296527232857959903002624 }, { target := 392, numerator := 149302338722406703076212736 }, { target := 393, numerator := 177296527232857959903002624 }, { target := 394, numerator := 135305244467181074662817792 }, { target := 395, numerator := 1395043727437487631868362752 }, { target := 396, numerator := 167965131062707540960739328 }, { target := 397, numerator := 135305244467181074662817792 }, { target := 398, numerator := 167965131062707540960739328 }, { target := 399, numerator := 167965131062707540960739328 }, { target := 400, numerator := 7194506447185973004485001216 }, { target := 401, numerator := 167965131062707540960739328 }, { target := 402, numerator := 1395043727437487631868362752 }, { target := 403, numerator := 7194506447185973004485001216 }, { target := 404, numerator := 149302338722406703076212736 }, { target := 405, numerator := 167965131062707540960739328 }, { target := 406, numerator := 167965131062707540960739328 }, { target := 407, numerator := 177296527232857959903002624 }, { target := 427, numerator := 2526352731539671317842231296 }, { target := 428, numerator := 3000043868703359689937649664 }, { target := 429, numerator := 2289507162957827131794522112 }, { target := 430, numerator := 23605608335323803876088348672 }, { target := 431, numerator := 2842146822982130232572510208 }, { target := 432, numerator := 2289507162957827131794522112 }, { target := 433, numerator := 2842146822982130232572510208 }, { target := 434, numerator := 2842146822982130232572510208 }, { target := 435, numerator := 121738622251067911628522520576 }, { target := 436, numerator := 2842146822982130232572510208 }, { target := 437, numerator := 23605608335323803876088348672 }, { target := 438, numerator := 121738622251067911628522520576 }, { target := 439, numerator := 2526352731539671317842231296 }, { target := 440, numerator := 2842146822982130232572510208 }, { target := 441, numerator := 2842146822982130232572510208 }, { target := 442, numerator := 3000043868703359689937649664 }]

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
    Slot3.Left9.expected,
    Slot3.Left10.expected,
    Slot3.Left11.expected,
    Slot3.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 453, numerator := 137515311981164068622827520 }, { target := 454, numerator := 163299432977632331489607680 }, { target := 455, numerator := 124623251482929937189437440 }, { target := 456, numerator := 1284908696324001766194544640 }, { target := 457, numerator := 154704725978809577200680960 }, { target := 458, numerator := 124623251482929937189437440 }, { target := 459, numerator := 154704725978809577200680960 }, { target := 460, numerator := 154704725978809577200680960 }, { target := 461, numerator := 6626519096092343556762501120 }, { target := 462, numerator := 154704725978809577200680960 }, { target := 463, numerator := 1284908696324001766194544640 }, { target := 464, numerator := 6626519096092343556762501120 }, { target := 465, numerator := 137515311981164068622827520 }, { target := 466, numerator := 154704725978809577200680960 }, { target := 467, numerator := 154704725978809577200680960 }, { target := 468, numerator := 163299432977632331489607680 }, { target := 502, numerator := 4569437366688394623095668736 }, { target := 503, numerator := 5426206872942468614926106624 }, { target := 504, numerator := 4141052613561357627180449792 }, { target := 505, numerator := 42695680394994687259550154752 }, { target := 506, numerator := 5140617037524443950982627328 }, { target := 507, numerator := 4141052613561357627180449792 }, { target := 508, numerator := 5140617037524443950982627328 }, { target := 509, numerator := 5140617037524443950982627328 }, { target := 510, numerator := 220189763107297015900422537216 }, { target := 511, numerator := 5140617037524443950982627328 }, { target := 512, numerator := 42695680394994687259550154752 }, { target := 513, numerator := 220189763107297015900422537216 }, { target := 514, numerator := 4569437366688394623095668736 }, { target := 515, numerator := 5140617037524443950982627328 }, { target := 516, numerator := 5140617037524443950982627328 }, { target := 517, numerator := 5426206872942468614926106624 }, { target := 528, numerator := 2526352731539671317842231296 }, { target := 529, numerator := 3000043868703359689937649664 }, { target := 530, numerator := 2289507162957827131794522112 }, { target := 531, numerator := 23605608335323803876088348672 }, { target := 532, numerator := 2842146822982130232572510208 }, { target := 533, numerator := 2289507162957827131794522112 }, { target := 534, numerator := 2842146822982130232572510208 }, { target := 535, numerator := 2842146822982130232572510208 }, { target := 536, numerator := 121738622251067911628522520576 }, { target := 537, numerator := 2842146822982130232572510208 }, { target := 538, numerator := 23605608335323803876088348672 }, { target := 539, numerator := 121738622251067911628522520576 }, { target := 540, numerator := 2526352731539671317842231296 }, { target := 541, numerator := 2842146822982130232572510208 }, { target := 542, numerator := 2842146822982130232572510208 }, { target := 543, numerator := 3000043868703359689937649664 }, { target := 573, numerator := 188592427859882151254163456 }, { target := 574, numerator := 223953508083610054614319104 }, { target := 575, numerator := 170911887748018199574085632 }, { target := 576, numerator := 1762160497815773850781089792 }, { target := 577, numerator := 212166481342367420160933888 }, { target := 578, numerator := 170911887748018199574085632 }, { target := 579, numerator := 212166481342367420160933888 }, { target := 580, numerator := 212166481342367420160933888 }, { target := 581, numerator := 9087797617498071163560001536 }, { target := 582, numerator := 212166481342367420160933888 }, { target := 583, numerator := 1762160497815773850781089792 }, { target := 584, numerator := 9087797617498071163560001536 }, { target := 585, numerator := 188592427859882151254163456 }, { target := 586, numerator := 212166481342367420160933888 }, { target := 587, numerator := 212166481342367420160933888 }, { target := 588, numerator := 223953508083610054614319104 }]

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
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left7.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left6.expected,
    Slot5.Left14.expected,
    Slot6.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 51992541820268782705239392256 }, { target := 134, numerator := 189108082103186814855880376320 }, { target := 136, numerator := 51992541820268782705239392256 }, { target := 263, numerator := 133014562452722293130081075200 }, { target := 265, numerator := 133014499026451455543261265920 }, { target := 338, numerator := 11137194242227908482379672453120 }, { target := 340, numerator := 11137188931601121814310239076352 }, { target := 356, numerator := 61017371481871367800646270976 }, { target := 599, numerator := 11137198272768662567192352522240 }, { target := 601, numerator := 11137192962139953987981938786304 }, { target := 617, numerator := 591018719664636302740603011072 }, { target := 642, numerator := 145373329808659158258417664 }, { target := 643, numerator := 172630829147782750431870976 }, { target := 644, numerator := 131744580139097362171691008 }, { target := 645, numerator := 1358332050399659009977090048 }, { target := 646, numerator := 163544996034741553040719872 }, { target := 647, numerator := 131744580139097362171691008 }, { target := 648, numerator := 163544996034741553040719872 }, { target := 649, numerator := 163544996034741553040719872 }, { target := 650, numerator := 7005177330154763188577501184 }, { target := 651, numerator := 163544996034741553040719872 }, { target := 652, numerator := 1358332050399659009977090048 }, { target := 653, numerator := 7005177330154763188577501184 }, { target := 654, numerator := 145373329808659158258417664 }, { target := 655, numerator := 163544996034741553040719872 }, { target := 656, numerator := 163544996034741553040719872 }, { target := 657, numerator := 172630829147782750431870976 }, { target := 668, numerator := 137515311981164068622827520 }, { target := 669, numerator := 163299432977632331489607680 }, { target := 670, numerator := 124623251482929937189437440 }, { target := 671, numerator := 1284908696324001766194544640 }, { target := 672, numerator := 154704725978809577200680960 }, { target := 673, numerator := 124623251482929937189437440 }, { target := 674, numerator := 154704725978809577200680960 }, { target := 675, numerator := 154704725978809577200680960 }, { target := 676, numerator := 6626519096092343556762501120 }, { target := 677, numerator := 154704725978809577200680960 }, { target := 678, numerator := 1284908696324001766194544640 }, { target := 679, numerator := 6626519096092343556762501120 }, { target := 680, numerator := 137515311981164068622827520 }, { target := 681, numerator := 154704725978809577200680960 }, { target := 682, numerator := 154704725978809577200680960 }, { target := 683, numerator := 163299432977632331489607680 }, { target := 713, numerator := 184663418946134606436368384 }, { target := 714, numerator := 219287809998534845143187456 }, { target := 715, numerator := 167351223419934487082958848 }, { target := 716, numerator := 1725448820777945228889817088 }, { target := 717, numerator := 207746346314401432240914432 }, { target := 718, numerator := 167351223419934487082958848 }, { target := 719, numerator := 207746346314401432240914432 }, { target := 720, numerator := 207746346314401432240914432 }, { target := 721, numerator := 8898468500466861347652501504 }, { target := 722, numerator := 207746346314401432240914432 }, { target := 723, numerator := 1725448820777945228889817088 }, { target := 724, numerator := 8898468500466861347652501504 }, { target := 725, numerator := 184663418946134606436368384 }, { target := 726, numerator := 207746346314401432240914432 }, { target := 727, numerator := 207746346314401432240914432 }, { target := 728, numerator := 219287809998534845143187456 }, { target := 773, numerator := 133010531911968208317401006080 }, { target := 775, numerator := 133010468487619281871561555968 }, { target := 777, numerator := 61017371481871367800646270976 }]

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
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 2213027294069620657566515200 }, { target := 27, numerator := 37178858540369627047117455360 }, { target := 28, numerator := 80554193504134191935421153280 }, { target := 29, numerator := 2655632752883544789079818240 }, { target := 30, numerator := 42490124046136716625277091840 }, { target := 31, numerator := 3098238211697468920593121280 }, { target := 32, numerator := 80554193504134191935421153280 }, { target := 33, numerator := 80554193504134191935421153280 }, { target := 34, numerator := 42490124046136716625277091840 }, { target := 35, numerator := 994091860496073599378878627840 }, { target := 36, numerator := 79668982586506343672394547200 }, { target := 37, numerator := 37178858540369627047117455360 }, { target := 38, numerator := 80554193504134191935421153280 }, { target := 39, numerator := 3098238211697468920593121280 }, { target := 40, numerator := 79668982586506343672394547200 }, { target := 41, numerator := 3098238211697468920593121280 }, { target := 42, numerator := 80554193504134191935421153280 }, { target := 43, numerator := 80554193504134191935421153280 }, { target := 44, numerator := 2655632752883544789079818240 }, { target := 80, numerator := 30218213040854651270135283712 }, { target := 82, numerator := 1115918405548713706186038312960 }, { target := 85, numerator := 1115918132288449645791665979392 }, { target := 92, numerator := 30218486301118711664507617280 }, { target := 176, numerator := 1057562116105680876432875585536 }, { target := 178, numerator := 39054361976263212659213472890880 }, { target := 181, numerator := 39054352412835265526889841688576 }, { target := 188, numerator := 1057571679533628008756506787840 }, { target := 227, numerator := 5451324237815027738751044419584 }, { target := 230, numerator := 19827641339395613034505809428480 }, { target := 232, numerator := 5451324237815027738751044419584 }, { target := 286, numerator := 1057562634799823609087070830592 }, { target := 288, numerator := 39054381130947837561501237903360 }, { target := 291, numerator := 39054371567515199930165700329472 }, { target := 298, numerator := 1057572198232461240422608404480 }, { target := 302, numerator := 58759826691480484717151649792000 }, { target := 305, numerator := 213722155934481195630581514240000 }, { target := 307, numerator := 58759826691480484717151649792000 }, { target := 573, numerator := 30217953693783284943037661184 }, { target := 575, numerator := 1115908828206401255042155806720 }, { target := 578, numerator := 1115908554948482444153736658944 }, { target := 585, numerator := 30218226951702095831456808960 }, { target := 589, numerator := 5451328396220356081451412750336 }, { target := 592, numerator := 19827656464412177314023913553920 }, { target := 594, numerator := 5451328396220356081451412750336 }, { target := 763, numerator := 51992541820268782705239392256 }, { target := 766, numerator := 189108082103186814855880376320 }, { target := 768, numerator := 51992541820268782705239392256 }]

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
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left2.expected,
    Slot9.Left3.expected,
    Slot9.Left4.expected,
    Slot9.Left5.expected,
    Slot9.Left6.expected,
    Slot9.Left7.expected,
    Slot9.Left8.expected,
    Slot9.Left9.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left6.expected,
    Slot10.Left14.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 68621385148535608338693488640 }, { target := 134, numerator := 235565216716443149600368361472 }, { target := 136, numerator := 68621385148535608338693488640 }, { target := 157, numerator := 7566490257249212954197360640 }, { target := 158, numerator := 127117036321786777630515658752 }, { target := 159, numerator := 275420245363871351532783927296 }, { target := 160, numerator := 9079788308699055545036832768 }, { target := 161, numerator := 145276612939184888720589324288 }, { target := 162, numerator := 10593086360148898135876304896 }, { target := 163, numerator := 275420245363871351532783927296 }, { target := 164, numerator := 275420245363871351532783927296 }, { target := 165, numerator := 145276612939184888720589324288 }, { target := 166, numerator := 3398867423556346459025454399488 }, { target := 167, numerator := 272393649260971666351104983040 }, { target := 168, numerator := 127117036321786777630515658752 }, { target := 169, numerator := 275420245363871351532783927296 }, { target := 170, numerator := 10593086360148898135876304896 }, { target := 171, numerator := 272393649260971666351104983040 }, { target := 172, numerator := 10593086360148898135876304896 }, { target := 173, numerator := 275420245363871351532783927296 }, { target := 174, numerator := 275420245363871351532783927296 }, { target := 175, numerator := 9079788308699055545036832768 }, { target := 227, numerator := 10135019477372571843186382602240 }, { target := 230, numerator := 34791749750385081268828479946752 }, { target := 232, numerator := 10135019477372571843186382602240 }, { target := 263, numerator := 89154591028355780441668583424 }, { target := 265, numerator := 89154591028355780441668583424 }, { target := 267, numerator := 2213026579258287801321390080 }, { target := 268, numerator := 37178846531539235062199353344 }, { target := 269, numerator := 80554167485001675968098598912 }, { target := 270, numerator := 2655631895109945361585668096 }, { target := 271, numerator := 42490110321759125785370689536 }, { target := 272, numerator := 3098237210961602921849946112 }, { target := 273, numerator := 80554167485001675968098598912 }, { target := 274, numerator := 80554167485001675968098598912 }, { target := 275, numerator := 42490110321759125785370689536 }, { target := 276, numerator := 994091539402822880353568423936 }, { target := 277, numerator := 79668956853298360847570042880 }, { target := 278, numerator := 37178846531539235062199353344 }, { target := 279, numerator := 80554167485001675968098598912 }, { target := 280, numerator := 3098237210961602921849946112 }, { target := 281, numerator := 79668956853298360847570042880 }, { target := 282, numerator := 3098237210961602921849946112 }, { target := 283, numerator := 80554167485001675968098598912 }, { target := 284, numerator := 80554167485001675968098598912 }, { target := 285, numerator := 2655631895109945361585668096 }, { target := 338, numerator := 7496941969712454544140164661248 }, { target := 340, numerator := 7496941969712454544140164661248 }, { target := 356, numerator := 1798881619586568211962789888 }, { target := 572, numerator := 43057101991394632686335164416 }, { target := 599, numerator := 7496940161046091605066047815680 }, { target := 601, numerator := 7496940161046091605066047815680 }, { target := 617, numerator := 32205783834533721214172528640 }, { target := 622, numerator := 37370314935927417048517312512 }, { target := 712, numerator := 1798881619586568211962789888 }, { target := 757, numerator := 37312286496585914848131416064 }, { target := 762, numerator := 37486371814610421449289105408 }, { target := 773, numerator := 89156399694718719515785428992 }, { target := 775, numerator := 89156399694718719515785428992 }, { target := 777, numerator := 1798881619586568211962789888 }, { target := 782, numerator := 43057101991394632686335164416 }, { target := 783, numerator := 1798881619586568211962789888 }]

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

namespace RouteChunk8

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 21325451458002058641816944640 }, { target := 11, numerator := 16586462245112712276968734720 }, { target := 12, numerator := 18955956851557385459392839680 }, { target := 13, numerator := 22273249300579927914786586624 }, { target := 14, numerator := 263013901315358723249075650560 }, { target := 15, numerator := 591425853768590426333056598016 }, { target := 16, numerator := 16586462245112712276968734720 }, { target := 17, numerator := 263013901315358723249075650560 }, { target := 18, numerator := 18955956851557385459392839680 }, { target := 19, numerator := 18482057930268450822908018688 }, { target := 20, numerator := 18482057930268450822908018688 }, { target := 21, numerator := 18482057930268450822908018688 }, { target := 22, numerator := 591425853768590426333056598016 }, { target := 23, numerator := 18482057930268450822908018688 }, { target := 24, numerator := 21325451458002058641816944640 }, { target := 25, numerator := 22273249300579927914786586624 }, { target := 26, numerator := 15158010414341641909296955392 }, { target := 27, numerator := 2419933815062218118907920646144 }, { target := 29, numerator := 24147300375709322108736324501504 }, { target := 37, numerator := 2419933815062218118907920646144 }, { target := 44, numerator := 15156280837617047929161252864 }, { target := 80, numerator := 213961313983568300746695770112 }, { target := 82, numerator := 8039076217390343837558855696384 }, { target := 85, numerator := 8038468205048559708690100256768 }, { target := 92, numerator := 214569326325352429615451209728 }, { target := 157, numerator := 51381561566803248650095951872 }, { target := 158, numerator := 8202922079309633927691060117504 }, { target := 160, numerator := 81852826790031481980911578251264 }, { target := 168, numerator := 8202922079309633927691060117504 }, { target := 175, numerator := 51375698768815251930715521024 }, { target := 176, numerator := 7754028840210206409761073659904 }, { target := 178, numerator := 291338783061875813061688744214528 }, { target := 181, numerator := 291316748493356758510560195117056 }, { target := 188, numerator := 7776063408729260960889622757376 }, { target := 267, numerator := 15158010414341641909296955392 }, { target := 268, numerator := 2419933815062218118907920646144 }, { target := 270, numerator := 24147300375709322108736324501504 }, { target := 278, numerator := 2419933815062218118907920646144 }, { target := 285, numerator := 15156280837617047929161252864 }, { target := 286, numerator := 7754031689785542696940559400960 }, { target := 288, numerator := 291338890127741548806936429854720 }, { target := 291, numerator := 291316855551124876321757792829440 }, { target := 298, numerator := 7776066266402215182119196426240 }, { target := 302, numerator := 105635613047913115159317027225600 }, { target := 305, numerator := 362628589130672960859408307322880 }, { target := 307, numerator := 105635613047913115159317027225600 }, { target := 573, numerator := 213958464408232013567210029056 }, { target := 575, numerator := 8038969151524608092311170056192 }, { target := 578, numerator := 8038361147280441897492502544384 }, { target := 585, numerator := 214566468652398208385877540864 }, { target := 589, numerator := 10135019477372571843186382602240 }, { target := 592, numerator := 34791749750385081268828479946752 }, { target := 594, numerator := 10135019477372571843186382602240 }, { target := 763, numerator := 68621385148535608338693488640 }, { target := 766, numerator := 235565216716443149600368361472 }, { target := 768, numerator := 68621385148535608338693488640 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk8

namespace RouteChunk9

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot14.Left2.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left2.expected,
    Slot15.Left3.expected,
    Slot15.Left4.expected,
    Slot15.Left5.expected,
    Slot15.Left6.expected,
    Slot15.Left7.expected,
    Slot15.Left8.expected,
    Slot15.Left9.expected,
    Slot15.Left10.expected,
    Slot15.Left11.expected,
    Slot15.Left12.expected,
    Slot15.Left13.expected,
    Slot15.Left14.expected,
    Slot15.Left15.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left3.expected,
    Slot16.Left11.expected,
    Slot16.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 15119616264355974123305828352 }, { target := 134, numerator := 51251415767495236368814047232 }, { target := 136, numerator := 15119616264355974123305828352 }, { target := 141, numerator := 21325451458002058641816944640 }, { target := 142, numerator := 16586462245112712276968734720 }, { target := 143, numerator := 18955956851557385459392839680 }, { target := 144, numerator := 22273249300579927914786586624 }, { target := 145, numerator := 263013901315358723249075650560 }, { target := 146, numerator := 591425853768590426333056598016 }, { target := 147, numerator := 16586462245112712276968734720 }, { target := 148, numerator := 263013901315358723249075650560 }, { target := 149, numerator := 18955956851557385459392839680 }, { target := 150, numerator := 18482057930268450822908018688 }, { target := 151, numerator := 18482057930268450822908018688 }, { target := 152, numerator := 18482057930268450822908018688 }, { target := 153, numerator := 591425853768590426333056598016 }, { target := 154, numerator := 18482057930268450822908018688 }, { target := 155, numerator := 21325451458002058641816944640 }, { target := 156, numerator := 22273249300579927914786586624 }, { target := 227, numerator := 2413804296786984537046451748864 }, { target := 230, numerator := 8182144667761230599606736257024 }, { target := 232, numerator := 2413804296786984537046451748864 }, { target := 263, numerator := 21325451458002058641816944640 }, { target := 265, numerator := 21325451458002058641816944640 }, { target := 302, numerator := 24086137000897495051723314561024 }, { target := 305, numerator := 81645499467868281671942703939584 }, { target := 307, numerator := 24086137000897495051723314561024 }, { target := 338, numerator := 16586462245112712276968734720 }, { target := 340, numerator := 16586462245112712276968734720 }, { target := 352, numerator := 18955956851557385459392839680 }, { target := 354, numerator := 18955956851557385459392839680 }, { target := 479, numerator := 22273249300579927914786586624 }, { target := 481, numerator := 22273249300579927914786586624 }, { target := 554, numerator := 263013901315358723249075650560 }, { target := 556, numerator := 263013901315358723249075650560 }, { target := 568, numerator := 591425853768590426333056598016 }, { target := 570, numerator := 591425853768590426333056598016 }, { target := 589, numerator := 2413804296786984537046451748864 }, { target := 592, numerator := 8182144667761230599606736257024 }, { target := 594, numerator := 2413804296786984537046451748864 }, { target := 599, numerator := 16586462245112712276968734720 }, { target := 601, numerator := 16586462245112712276968734720 }, { target := 613, numerator := 263013901315358723249075650560 }, { target := 615, numerator := 263013901315358723249075650560 }, { target := 618, numerator := 18955956851557385459392839680 }, { target := 620, numerator := 18955956851557385459392839680 }, { target := 694, numerator := 18482057930268450822908018688 }, { target := 696, numerator := 18482057930268450822908018688 }, { target := 708, numerator := 18482057930268450822908018688 }, { target := 710, numerator := 18482057930268450822908018688 }, { target := 739, numerator := 18482057930268450822908018688 }, { target := 741, numerator := 18482057930268450822908018688 }, { target := 753, numerator := 591425853768590426333056598016 }, { target := 755, numerator := 591425853768590426333056598016 }, { target := 758, numerator := 18482057930268450822908018688 }, { target := 760, numerator := 18482057930268450822908018688 }, { target := 763, numerator := 15117891068524806166422749184 }, { target := 766, numerator := 51245567819552801951154438144 }, { target := 768, numerator := 15117891068524806166422749184 }, { target := 773, numerator := 21325451458002058641816944640 }, { target := 775, numerator := 21325451458002058641816944640 }, { target := 778, numerator := 22273249300579927914786586624 }, { target := 780, numerator := 22273249300579927914786586624 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk9

namespace RouteChunk10

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left3.expected,
    Slot18.Left5.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot20.Left0.expected,
    Slot21.Left0.expected,
    Slot21.Left1.expected,
    Slot21.Left2.expected,
    Slot21.Left3.expected,
    Slot21.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1199254413057712141308526592 }, { target := 1, numerator := 28704734660929755124223442944 }, { target := 2, numerator := 21470522556355814142781685760 }, { target := 3, numerator := 24913543290618278032344875008 }, { target := 4, numerator := 1199254413057712141308526592 }, { target := 5, numerator := 24874857664390609898754277376 }, { target := 6, numerator := 24990914543073614299526070272 }, { target := 7, numerator := 1199254413057712141308526592 }, { target := 8, numerator := 28704734660929755124223442944 }, { target := 9, numerator := 1199254413057712141308526592 }, { target := 10, numerator := 88223472584195406755593715712 }, { target := 11, numerator := 7418644925642350580232695578624 }, { target := 16, numerator := 7418643135865453572637159587840 }, { target := 24, numerator := 88225262361092414351129706496 }, { target := 26, numerator := 68121194559115529277564518400 }, { target := 27, numerator := 10061143944909946362899359334400 }, { target := 29, numerator := 104865620727883203525042241536000 }, { target := 37, numerator := 10061143944909946362899359334400 }, { target := 44, numerator := 68121194559115529277564518400 }, { target := 80, numerator := 216057216524362422143454019584 }, { target := 82, numerator := 7829985042034782769513840508928 }, { target := 85, numerator := 7829987919523726784711066910720 }, { target := 92, numerator := 216054339035418406946227617792 }, { target := 131, numerator := 2159486311148581448109260800 }, { target := 134, numerator := 7383430009089957802079682560 }, { target := 136, numerator := 2159485613631071160966840320 }, { target := 141, numerator := 88223472584195406755593715712 }, { target := 142, numerator := 7418644925642350580232695578624 }, { target := 147, numerator := 7418643135865453572637159587840 }, { target := 155, numerator := 88225262361092414351129706496 }, { target := 157, numerator := 233848149881647833341566648320 }, { target := 158, numerator := 34538147964630799176969612165120 }, { target := 160, numerator := 359985340129720467913192557772800 }, { target := 168, numerator := 34538147964630799176969612165120 }, { target := 175, numerator := 233848149881647833341566648320 }, { target := 176, numerator := 8117824660068911361133576716288 }, { target := 178, numerator := 294192652690373919885519168208896 }, { target := 181, numerator := 294192760805025605997028221911040 }, { target := 188, numerator := 8117716545417225249624523014144 }, { target := 227, numerator := 36279370027296168328235581440 }, { target := 230, numerator := 124041624152711291074938667008 }, { target := 232, numerator := 36279358309001995504242917376 }, { target := 253, numerator := 78605301725808364711177093120 }, { target := 256, numerator := 268756852330874463995700445184 }, { target := 258, numerator := 78605276336170990259192987648 }, { target := 267, numerator := 68121194559115529277564518400 }, { target := 268, numerator := 10061143944909946362899359334400 }, { target := 270, numerator := 104865620727883203525042241536000 }, { target := 278, numerator := 10061143944909946362899359334400 }, { target := 285, numerator := 68121194559115529277564518400 }, { target := 286, numerator := 8117210691815807312977069080576 }, { target := 288, numerator := 294170402277657217832181974433792 }, { target := 291, numerator := 294170510384131964109404063662080 }, { target := 298, numerator := 8117102585341061035754979852288 }, { target := 302, numerator := 2591383573378297737731112960 }, { target := 305, numerator := 8860116010907949362495619072 }, { target := 307, numerator := 2591382736357285393160208384 }, { target := 328, numerator := 41462137174052763803697807360 }, { target := 331, numerator := 141761856174527189799929905152 }, { target := 333, numerator := 41462123781716566290563334144 }, { target := 573, numerator := 216671184777466470299961655296 }, { target := 575, numerator := 7852235454751484822851034284032 }, { target := 578, numerator := 7852238340417368672335225159680 }, { target := 585, numerator := 216668299111582620815770779648 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk10

namespace RouteChunk11

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot21.Left5.expected,
    Slot21.Left6.expected,
    Slot21.Left7.expected,
    Slot21.Left8.expected,
    Slot21.Left9.expected,
    Slot21.Left10.expected,
    Slot21.Left11.expected,
    Slot21.Left12.expected,
    Slot21.Left13.expected,
    Slot21.Left14.expected,
    Slot21.Left15.expected,
    Slot21.Left16.expected,
    Slot21.Left17.expected,
    Slot21.Left18.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot22.Left5.expected,
    Slot22.Left12.expected,
    Slot23.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 52212494152707470142147133440 }, { target := 27, numerator := 5474385843172424109120458588160 }, { target := 29, numerator := 59008407747185780885374894080000 }, { target := 37, numerator := 5474390019169716975430155632640 }, { target := 44, numerator := 52212494152707470142147133440 }, { target := 80, numerator := 30319762484582919421307125760 }, { target := 82, numerator := 1061116093452171402661886689280 }, { target := 85, numerator := 1061116613889405349492068188160 }, { target := 92, numerator := 30319502265965946006216376320 }, { target := 176, numerator := 1119668491405094405150657740800 }, { target := 178, numerator := 39185605631488293066613614182400 }, { target := 181, numerator := 39185624850542957514900425932800 }, { target := 188, numerator := 1119658881877762181007251865600 }, { target := 286, numerator := 1119668217226528929286885212160 }, { target := 288, numerator := 39185596035922085910321540628480 }, { target := 291, numerator := 39185615254972044096997750210560 }, { target := 298, numerator := 1119658607701549835948780421120 }, { target := 342, numerator := 3023280835608014027352965120 }, { target := 345, numerator := 10336802012725940922911555584 }, { target := 347, numerator := 3023279859083499625353576448 }, { target := 443, numerator := 78605301725808364711177093120 }, { target := 446, numerator := 268756852330874463995700445184 }, { target := 448, numerator := 78605276336170990259192987648 }, { target := 469, numerator := 78605301725808364711177093120 }, { target := 472, numerator := 268756852330874463995700445184 }, { target := 474, numerator := 78605276336170990259192987648 }, { target := 518, numerator := 41462137174052763803697807360 }, { target := 521, numerator := 141761856174527189799929905152 }, { target := 523, numerator := 41462123781716566290563334144 }, { target := 544, numerator := 970041250967942786490679951360 }, { target := 547, numerator := 3316636760083209044694193405952 }, { target := 549, numerator := 970040937643077165506304671744 }, { target := 558, numerator := 77741507201348932131933388800 }, { target := 561, numerator := 265803480327238480874868572160 }, { target := 563, numerator := 77741482090718561794806251520 }, { target := 573, numerator := 30320036663148395285079654400 }, { target := 575, numerator := 1061125689018378558953960243200 }, { target := 578, numerator := 1061126209460318767394743910400 }, { target := 585, numerator := 30319776442178291064687820800 }, { target := 589, numerator := 36279370027296168328235581440 }, { target := 592, numerator := 124041624152711291074938667008 }, { target := 594, numerator := 36279358309001995504242917376 }, { target := 603, numerator := 78605301725808364711177093120 }, { target := 606, numerator := 268756852330874463995700445184 }, { target := 608, numerator := 78605276336170990259192987648 }, { target := 658, numerator := 3023280835608014027352965120 }, { target := 661, numerator := 10336802012725940922911555584 }, { target := 663, numerator := 3023279859083499625353576448 }, { target := 684, numerator := 77741507201348932131933388800 }, { target := 687, numerator := 265803480327238480874868572160 }, { target := 689, numerator := 77741482090718561794806251520 }, { target := 698, numerator := 3023280835608014027352965120 }, { target := 701, numerator := 10336802012725940922911555584 }, { target := 703, numerator := 3023279859083499625353576448 }, { target := 729, numerator := 78605301725808364711177093120 }, { target := 732, numerator := 268756852330874463995700445184 }, { target := 734, numerator := 78605276336170990259192987648 }, { target := 743, numerator := 78605301725808364711177093120 }, { target := 746, numerator := 268756852330874463995700445184 }, { target := 748, numerator := 78605276336170990259192987648 }, { target := 763, numerator := 2591383573378297737731112960 }, { target := 766, numerator := 8860116010907949362495619072 }, { target := 768, numerator := 2591382736357285393160208384 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk11

namespace RouteChunk12

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot23.Left3.expected,
    Slot23.Left5.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected,
    Slot25.Left0.expected,
    Slot26.Left0.expected,
    Slot26.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 61017371481871367800646270976 }, { target := 2, numerator := 591018719664636302740603011072 }, { target := 7, numerator := 61017371481871367800646270976 }, { target := 10, numerator := 131144410432297375124737228800 }, { target := 11, numerator := 10980608031440872862240766689280 }, { target := 16, numerator := 10980612005313215641818822082560 }, { target := 24, numerator := 131140436559954595546681835520 }, { target := 80, numerator := 181338872942194376205926400 }, { target := 81, numerator := 177560979755898660034969600 }, { target := 82, numerator := 139782047892941498325401600 }, { target := 83, numerator := 4393689775661917906822758400 }, { target := 84, numerator := 139782047892941498325401600 }, { target := 85, numerator := 139782047892941498325401600 }, { target := 86, numerator := 143559941079237214496358400 }, { target := 87, numerator := 143559941079237214496358400 }, { target := 88, numerator := 2429185318788145497925222400 }, { target := 89, numerator := 132226261520350065983488000 }, { target := 90, numerator := 4393689775661917906822758400 }, { target := 91, numerator := 2429185318788145497925222400 }, { target := 92, numerator := 181338872942194376205926400 }, { target := 93, numerator := 139782047892941498325401600 }, { target := 94, numerator := 132226261520350065983488000 }, { target := 95, numerator := 177560979755898660034969600 }, { target := 115, numerator := 215339911618855821744537600 }, { target := 116, numerator := 210853663460129658791526400 }, { target := 117, numerator := 165991181872868029261414400 }, { target := 118, numerator := 5217506608598527514352025600 }, { target := 119, numerator := 165991181872868029261414400 }, { target := 120, numerator := 165991181872868029261414400 }, { target := 121, numerator := 170477430031594192214425600 }, { target := 122, numerator := 170477430031594192214425600 }, { target := 123, numerator := 2884657566060922778786201600 }, { target := 124, numerator := 157018685555415703355392000 }, { target := 125, numerator := 5217506608598527514352025600 }, { target := 126, numerator := 2884657566060922778786201600 }, { target := 127, numerator := 215339911618855821744537600 }, { target := 128, numerator := 165991181872868029261414400 }, { target := 129, numerator := 157018685555415703355392000 }, { target := 130, numerator := 210853663460129658791526400 }, { target := 141, numerator := 131144347897784299753549332480 }, { target := 142, numerator := 10980602795480192157870024818688 }, { target := 147, numerator := 10980606769350640047904864075776 }, { target := 155, numerator := 131140374027336409718710075392 }, { target := 157, numerator := 189908096149151142638308556800 }, { target := 158, numerator := 19911521369235924854353638195200 }, { target := 160, numerator := 214626298818168565716851097600000 }, { target := 168, numerator := 19911536558238256226915634380800 }, { target := 175, numerator := 189908096149151142638308556800 }, { target := 267, numerator := 52212494152707470142147133440 }, { target := 268, numerator := 5474385843172424109120458588160 }, { target := 270, numerator := 59008407747185780885374894080000 }, { target := 278, numerator := 5474390019169716975430155632640 }, { target := 285, numerator := 52212494152707470142147133440 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk12

namespace RouteChunk13

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot26.Left2.expected,
    Slot26.Left3.expected,
    Slot26.Left4.expected,
    Slot26.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 176, numerator := 164338353603863653436620800 }, { target := 177, numerator := 160914637903783160656691200 }, { target := 178, numerator := 126677480902978232857395200 }, { target := 179, numerator := 3981781359193613103058124800 }, { target := 180, numerator := 126677480902978232857395200 }, { target := 181, numerator := 126677480902978232857395200 }, { target := 182, numerator := 130101196603058725637324800 }, { target := 183, numerator := 130101196603058725637324800 }, { target := 184, numerator := 2201449195151756857494732800 }, { target := 185, numerator := 119830049502817247297536000 }, { target := 186, numerator := 3981781359193613103058124800 }, { target := 187, numerator := 2201449195151756857494732800 }, { target := 188, numerator := 164338353603863653436620800 }, { target := 189, numerator := 126677480902978232857395200 }, { target := 190, numerator := 119830049502817247297536000 }, { target := 191, numerator := 160914637903783160656691200 }, { target := 211, numerator := 1694385094053628702674124800 }, { target := 212, numerator := 1659085404594178104701747200 }, { target := 213, numerator := 1306088509999672124977971200 }, { target := 214, numerator := 41053538841341045441875148800 }, { target := 215, numerator := 1306088509999672124977971200 }, { target := 216, numerator := 1306088509999672124977971200 }, { target := 217, numerator := 1341388199459122722950348800 }, { target := 218, numerator := 1341388199459122722950348800 }, { target := 219, numerator := 22697700322426734496238796800 }, { target := 220, numerator := 1235489131080770929033216000 }, { target := 221, numerator := 41053538841341045441875148800 }, { target := 222, numerator := 22697700322426734496238796800 }, { target := 223, numerator := 1694385094053628702674124800 }, { target := 224, numerator := 1306088509999672124977971200 }, { target := 225, numerator := 1235489131080770929033216000 }, { target := 226, numerator := 1659085404594178104701747200 }, { target := 237, numerator := 204006232059968673231667200 }, { target := 238, numerator := 199756102225385992539340800 }, { target := 239, numerator := 157254803879559185616076800 }, { target := 240, numerator := 4942900997619657645175603200 }, { target := 241, numerator := 157254803879559185616076800 }, { target := 242, numerator := 157254803879559185616076800 }, { target := 243, numerator := 161504933714141866308403200 }, { target := 244, numerator := 161504933714141866308403200 }, { target := 245, numerator := 2732833483636663685165875200 }, { target := 246, numerator := 148754544210393824231424000 }, { target := 247, numerator := 4942900997619657645175603200 }, { target := 248, numerator := 2732833483636663685165875200 }, { target := 249, numerator := 204006232059968673231667200 }, { target := 250, numerator := 157254803879559185616076800 }, { target := 251, numerator := 148754544210393824231424000 }, { target := 252, numerator := 199756102225385992539340800 }, { target := 286, numerator := 164338353603863653436620800 }, { target := 287, numerator := 160914637903783160656691200 }, { target := 288, numerator := 126677480902978232857395200 }, { target := 289, numerator := 3981781359193613103058124800 }, { target := 290, numerator := 126677480902978232857395200 }, { target := 291, numerator := 126677480902978232857395200 }, { target := 292, numerator := 130101196603058725637324800 }, { target := 293, numerator := 130101196603058725637324800 }, { target := 294, numerator := 2201449195151756857494732800 }, { target := 295, numerator := 119830049502817247297536000 }, { target := 296, numerator := 3981781359193613103058124800 }, { target := 297, numerator := 2201449195151756857494732800 }, { target := 298, numerator := 164338353603863653436620800 }, { target := 299, numerator := 126677480902978232857395200 }, { target := 300, numerator := 119830049502817247297536000 }, { target := 301, numerator := 160914637903783160656691200 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk13

namespace RouteChunk14

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot26.Left6.expected,
    Slot26.Left7.expected,
    Slot26.Left8.expected,
    Slot26.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 312, numerator := 204006232059968673231667200 }, { target := 313, numerator := 199756102225385992539340800 }, { target := 314, numerator := 157254803879559185616076800 }, { target := 315, numerator := 4942900997619657645175603200 }, { target := 316, numerator := 157254803879559185616076800 }, { target := 317, numerator := 157254803879559185616076800 }, { target := 318, numerator := 161504933714141866308403200 }, { target := 319, numerator := 161504933714141866308403200 }, { target := 320, numerator := 2732833483636663685165875200 }, { target := 321, numerator := 148754544210393824231424000 }, { target := 322, numerator := 4942900997619657645175603200 }, { target := 323, numerator := 2732833483636663685165875200 }, { target := 324, numerator := 204006232059968673231667200 }, { target := 325, numerator := 157254803879559185616076800 }, { target := 326, numerator := 148754544210393824231424000 }, { target := 327, numerator := 199756102225385992539340800 }, { target := 392, numerator := 204006232059968673231667200 }, { target := 393, numerator := 199756102225385992539340800 }, { target := 394, numerator := 157254803879559185616076800 }, { target := 395, numerator := 4942900997619657645175603200 }, { target := 396, numerator := 157254803879559185616076800 }, { target := 397, numerator := 157254803879559185616076800 }, { target := 398, numerator := 161504933714141866308403200 }, { target := 399, numerator := 161504933714141866308403200 }, { target := 400, numerator := 2732833483636663685165875200 }, { target := 401, numerator := 148754544210393824231424000 }, { target := 402, numerator := 4942900997619657645175603200 }, { target := 403, numerator := 2732833483636663685165875200 }, { target := 404, numerator := 204006232059968673231667200 }, { target := 405, numerator := 157254803879559185616076800 }, { target := 406, numerator := 148754544210393824231424000 }, { target := 407, numerator := 199756102225385992539340800 }, { target := 427, numerator := 8738266939901991503423078400 }, { target := 428, numerator := 8556219711987366680435097600 }, { target := 429, numerator := 6735747432841118450555289600 }, { target := 430, numerator := 211720926064708669135021670400 }, { target := 431, numerator := 6735747432841118450555289600 }, { target := 432, numerator := 6735747432841118450555289600 }, { target := 433, numerator := 6917794660755743273543270400 }, { target := 434, numerator := 6917794660755743273543270400 }, { target := 435, numerator := 117056367549103761181271654400 }, { target := 436, numerator := 6371652977011868804579328000 }, { target := 437, numerator := 211720926064708669135021670400 }, { target := 438, numerator := 117056367549103761181271654400 }, { target := 439, numerator := 8738266939901991503423078400 }, { target := 440, numerator := 6735747432841118450555289600 }, { target := 441, numerator := 6371652977011868804579328000 }, { target := 442, numerator := 8556219711987366680435097600 }, { target := 453, numerator := 204006232059968673231667200 }, { target := 454, numerator := 199756102225385992539340800 }, { target := 455, numerator := 157254803879559185616076800 }, { target := 456, numerator := 4942900997619657645175603200 }, { target := 457, numerator := 157254803879559185616076800 }, { target := 458, numerator := 157254803879559185616076800 }, { target := 459, numerator := 161504933714141866308403200 }, { target := 460, numerator := 161504933714141866308403200 }, { target := 461, numerator := 2732833483636663685165875200 }, { target := 462, numerator := 148754544210393824231424000 }, { target := 463, numerator := 4942900997619657645175603200 }, { target := 464, numerator := 2732833483636663685165875200 }, { target := 465, numerator := 204006232059968673231667200 }, { target := 466, numerator := 157254803879559185616076800 }, { target := 467, numerator := 148754544210393824231424000 }, { target := 468, numerator := 199756102225385992539340800 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk14

namespace RouteChunk15

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot26.Left10.expected,
    Slot26.Left11.expected,
    Slot26.Left12.expected,
    Slot26.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 502, numerator := 1694385094053628702674124800 }, { target := 503, numerator := 1659085404594178104701747200 }, { target := 504, numerator := 1306088509999672124977971200 }, { target := 505, numerator := 41053538841341045441875148800 }, { target := 506, numerator := 1306088509999672124977971200 }, { target := 507, numerator := 1306088509999672124977971200 }, { target := 508, numerator := 1341388199459122722950348800 }, { target := 509, numerator := 1341388199459122722950348800 }, { target := 510, numerator := 22697700322426734496238796800 }, { target := 511, numerator := 1235489131080770929033216000 }, { target := 512, numerator := 41053538841341045441875148800 }, { target := 513, numerator := 22697700322426734496238796800 }, { target := 514, numerator := 1694385094053628702674124800 }, { target := 515, numerator := 1306088509999672124977971200 }, { target := 516, numerator := 1235489131080770929033216000 }, { target := 517, numerator := 1659085404594178104701747200 }, { target := 528, numerator := 8738266939901991503423078400 }, { target := 529, numerator := 8556219711987366680435097600 }, { target := 530, numerator := 6735747432841118450555289600 }, { target := 531, numerator := 211720926064708669135021670400 }, { target := 532, numerator := 6735747432841118450555289600 }, { target := 533, numerator := 6735747432841118450555289600 }, { target := 534, numerator := 6917794660755743273543270400 }, { target := 535, numerator := 6917794660755743273543270400 }, { target := 536, numerator := 117056367549103761181271654400 }, { target := 537, numerator := 6371652977011868804579328000 }, { target := 538, numerator := 211720926064708669135021670400 }, { target := 539, numerator := 117056367549103761181271654400 }, { target := 540, numerator := 8738266939901991503423078400 }, { target := 541, numerator := 6735747432841118450555289600 }, { target := 542, numerator := 6371652977011868804579328000 }, { target := 543, numerator := 8556219711987366680435097600 }, { target := 573, numerator := 181338872942194376205926400 }, { target := 574, numerator := 177560979755898660034969600 }, { target := 575, numerator := 139782047892941498325401600 }, { target := 576, numerator := 4393689775661917906822758400 }, { target := 577, numerator := 139782047892941498325401600 }, { target := 578, numerator := 139782047892941498325401600 }, { target := 579, numerator := 143559941079237214496358400 }, { target := 580, numerator := 143559941079237214496358400 }, { target := 581, numerator := 2429185318788145497925222400 }, { target := 582, numerator := 132226261520350065983488000 }, { target := 583, numerator := 4393689775661917906822758400 }, { target := 584, numerator := 2429185318788145497925222400 }, { target := 585, numerator := 181338872942194376205926400 }, { target := 586, numerator := 139782047892941498325401600 }, { target := 587, numerator := 132226261520350065983488000 }, { target := 588, numerator := 177560979755898660034969600 }, { target := 642, numerator := 204006232059968673231667200 }, { target := 643, numerator := 199756102225385992539340800 }, { target := 644, numerator := 157254803879559185616076800 }, { target := 645, numerator := 4942900997619657645175603200 }, { target := 646, numerator := 157254803879559185616076800 }, { target := 647, numerator := 157254803879559185616076800 }, { target := 648, numerator := 161504933714141866308403200 }, { target := 649, numerator := 161504933714141866308403200 }, { target := 650, numerator := 2732833483636663685165875200 }, { target := 651, numerator := 148754544210393824231424000 }, { target := 652, numerator := 4942900997619657645175603200 }, { target := 653, numerator := 2732833483636663685165875200 }, { target := 654, numerator := 204006232059968673231667200 }, { target := 655, numerator := 157254803879559185616076800 }, { target := 656, numerator := 148754544210393824231424000 }, { target := 657, numerator := 199756102225385992539340800 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk15

namespace RouteChunk16

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot26.Left14.expected,
    Slot26.Left15.expected,
    Slot27.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 3017202621906511684027023360 }, { target := 27, numerator := 80458736584173644907387289600 }, { target := 28, numerator := 76938666858616047942689095680 }, { target := 29, numerator := 2514335518255426403355852800 }, { target := 30, numerator := 78950135273220389065373777920 }, { target := 31, numerator := 2514335518255426403355852800 }, { target := 32, numerator := 76938666858616047942689095680 }, { target := 33, numerator := 43749438017644419418391838720 }, { target := 34, numerator := 78950135273220389065373777920 }, { target := 35, numerator := 1232527271048810022925039042560 }, { target := 36, numerator := 48275241950504186944432373760 }, { target := 37, numerator := 80458736584173644907387289600 }, { target := 38, numerator := 76938666858616047942689095680 }, { target := 39, numerator := 2514335518255426403355852800 }, { target := 40, numerator := 48275241950504186944432373760 }, { target := 41, numerator := 2514335518255426403355852800 }, { target := 42, numerator := 77441533962267133223360266240 }, { target := 43, numerator := 43749438017644419418391838720 }, { target := 44, numerator := 3017202621906511684027023360 }, { target := 668, numerator := 204006232059968673231667200 }, { target := 669, numerator := 199756102225385992539340800 }, { target := 670, numerator := 157254803879559185616076800 }, { target := 671, numerator := 4942900997619657645175603200 }, { target := 672, numerator := 157254803879559185616076800 }, { target := 673, numerator := 157254803879559185616076800 }, { target := 674, numerator := 161504933714141866308403200 }, { target := 675, numerator := 161504933714141866308403200 }, { target := 676, numerator := 2732833483636663685165875200 }, { target := 677, numerator := 148754544210393824231424000 }, { target := 678, numerator := 4942900997619657645175603200 }, { target := 679, numerator := 2732833483636663685165875200 }, { target := 680, numerator := 204006232059968673231667200 }, { target := 681, numerator := 157254803879559185616076800 }, { target := 682, numerator := 148754544210393824231424000 }, { target := 683, numerator := 199756102225385992539340800 }, { target := 713, numerator := 215339911618855821744537600 }, { target := 714, numerator := 210853663460129658791526400 }, { target := 715, numerator := 165991181872868029261414400 }, { target := 716, numerator := 5217506608598527514352025600 }, { target := 717, numerator := 165991181872868029261414400 }, { target := 718, numerator := 165991181872868029261414400 }, { target := 719, numerator := 170477430031594192214425600 }, { target := 720, numerator := 170477430031594192214425600 }, { target := 721, numerator := 2884657566060922778786201600 }, { target := 722, numerator := 157018685555415703355392000 }, { target := 723, numerator := 5217506608598527514352025600 }, { target := 724, numerator := 2884657566060922778786201600 }, { target := 725, numerator := 215339911618855821744537600 }, { target := 726, numerator := 165991181872868029261414400 }, { target := 727, numerator := 157018685555415703355392000 }, { target := 728, numerator := 210853663460129658791526400 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk16

namespace RouteChunk17

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot27.Left3.expected,
    Slot27.Left5.expected,
    Slot28.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 21325451458002058641816944640 }, { target := 11, numerator := 21934750071087831745868857344 }, { target := 12, numerator := 21325451458002058641816944640 }, { target := 13, numerator := 18888257005658966225609293824 }, { target := 14, numerator := 884092287587456773979325333504 }, { target := 15, numerator := 240672952168880376100505518080 }, { target := 16, numerator := 21934750071087831745868857344 }, { target := 17, numerator := 884092287587456773979325333504 }, { target := 18, numerator := 21325451458002058641816944640 }, { target := 19, numerator := 21325451458002058641816944640 }, { target := 20, numerator := 18278958392573193121557381120 }, { target := 21, numerator := 21325451458002058641816944640 }, { target := 22, numerator := 240672952168880376100505518080 }, { target := 23, numerator := 18278958392573193121557381120 }, { target := 24, numerator := 21325451458002058641816944640 }, { target := 25, numerator := 18888257005658966225609293824 }, { target := 157, numerator := 10793843168264323751812792320 }, { target := 158, numerator := 287835817820381966715007795200 }, { target := 159, numerator := 275243000790740255671226204160 }, { target := 160, numerator := 8994869306886936459843993600 }, { target := 161, numerator := 282438896236249804839101399040 }, { target := 162, numerator := 8994869306886936459843993600 }, { target := 163, numerator := 275243000790740255671226204160 }, { target := 164, numerator := 156510725939832694401285488640 }, { target := 165, numerator := 282438896236249804839101399040 }, { target := 166, numerator := 4409284934235976252615525662720 }, { target := 167, numerator := 172701490692229180029004677120 }, { target := 168, numerator := 287835817820381966715007795200 }, { target := 169, numerator := 275243000790740255671226204160 }, { target := 170, numerator := 8994869306886936459843993600 }, { target := 171, numerator := 172701490692229180029004677120 }, { target := 172, numerator := 8994869306886936459843993600 }, { target := 173, numerator := 277041974652117642963195002880 }, { target := 174, numerator := 156510725939832694401285488640 }, { target := 175, numerator := 10793843168264323751812792320 }, { target := 267, numerator := 3017201618864802676070154240 }, { target := 268, numerator := 80458709836394738028537446400 }, { target := 269, numerator := 76938641281052468239788933120 }, { target := 270, numerator := 2514334682387335563391795200 }, { target := 271, numerator := 78950109026962336690502369280 }, { target := 272, numerator := 2514334682387335563391795200 }, { target := 273, numerator := 76938641281052468239788933120 }, { target := 274, numerator := 43749423473539638803017236480 }, { target := 275, numerator := 78950109026962336690502369280 }, { target := 276, numerator := 1232526861306271893174658007040 }, { target := 277, numerator := 48275225901836842817122467840 }, { target := 278, numerator := 80458709836394738028537446400 }, { target := 279, numerator := 76938641281052468239788933120 }, { target := 280, numerator := 2514334682387335563391795200 }, { target := 281, numerator := 48275225901836842817122467840 }, { target := 282, numerator := 2514334682387335563391795200 }, { target := 283, numerator := 77441508217529935352467292160 }, { target := 284, numerator := 43749423473539638803017236480 }, { target := 285, numerator := 3017201618864802676070154240 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent0
