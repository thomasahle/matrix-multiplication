import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk3Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 17; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3.Parent3

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
    Slot2.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 142, numerator := 12110402776540781320601600 }, { target := 143, numerator := 1788643113999965162674585600 }, { target := 145, numerator := 18642728047356164926603264000 }, { target := 153, numerator := 1788643113999965162674585600 }, { target := 160, numerator := 12110402776540781320601600 }, { target := 282, numerator := 242692471641877257664856064 }, { target := 283, numerator := 35844408004559301859998695424 }, { target := 285, numerator := 373600270069017545129129410560 }, { target := 293, numerator := 35844408004559301859998695424 }, { target := 300, numerator := 242692471641877257664856064 }, { target := 357, numerator := 407393949402831883625037824 }, { target := 358, numerator := 60169954354958828072373059584 }, { target := 360, numerator := 627141371513061388130933800960 }, { target := 368, numerator := 60169954354958828072373059584 }, { target := 375, numerator := 407393949402831883625037824 }, { target := 392, numerator := 390923801626736421029019648 }, { target := 393, numerator := 57737399719918875451135623168 }, { target := 395, numerator := 601787261368657003830753361920 }, { target := 403, numerator := 57737399719918875451135623168 }, { target := 410, numerator := 390923801626736421029019648 }, { target := 411, numerator := 3612461586404324120943656960 }, { target := 413, numerator := 130916803620311610440359608320 }, { target := 416, numerator := 130916851731725997684083916800 }, { target := 423, numerator := 3612413474989936877219348480 }, { target := 498, numerator := 12110402776540781320601600 }, { target := 499, numerator := 1788643113999965162674585600 }, { target := 501, numerator := 18642728047356164926603264000 }, { target := 509, numerator := 1788643113999965162674585600 }, { target := 516, numerator := 12110402776540781320601600 }, { target := 573, numerator := 390923801626736421029019648 }, { target := 574, numerator := 57737399719918875451135623168 }, { target := 576, numerator := 601787261368657003830753361920 }, { target := 584, numerator := 57737399719918875451135623168 }, { target := 591, numerator := 390923801626736421029019648 }, { target := 608, numerator := 261100283862219245272170496 }, { target := 609, numerator := 38563145537839248907264065536 }, { target := 611, numerator := 401937216700998915817566371840 }, { target := 619, numerator := 38563145537839248907264065536 }, { target := 626, numerator := 261100283862219245272170496 }, { target := 627, numerator := 3301857412620027093722333184 }, { target := 629, numerator := 119660405552023135523992240128 }, { target := 632, numerator := 119660449526755164238349598720 }, { target := 639, numerator := 3301813437887998379364974592 }, { target := 669, numerator := 12594818887602412573425664 }, { target := 670, numerator := 1860188838559963769181569024 }, { target := 672, numerator := 19388437169250411523667394560 }, { target := 680, numerator := 1860188838559963769181569024 }, { target := 687, numerator := 12594818887602412573425664 }, { target := 704, numerator := 242692471641877257664856064 }, { target := 705, numerator := 35844408004559301859998695424 }, { target := 707, numerator := 373600270069017545129129410560 }, { target := 715, numerator := 35844408004559301859998695424 }, { target := 722, numerator := 242692471641877257664856064 }, { target := 723, numerator := 3612461586404324120943656960 }, { target := 725, numerator := 130916803620311610440359608320 }, { target := 728, numerator := 130916851731725997684083916800 }, { target := 735, numerator := 3612413474989936877219348480 }, { target := 758, numerator := 3301857412620027093722333184 }, { target := 760, numerator := 119660405552023135523992240128 }, { target := 763, numerator := 119660449526755164238349598720 }, { target := 770, numerator := 3301813437887998379364974592 }, { target := 774, numerator := 73499195281372130284677365760 }, { target := 777, numerator := 249142422008577427398365020160 }, { target := 779, numerator := 73499195281372130284677365760 }]

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
    Slot3.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 55, numerator := 202886526223909549517045760 }, { target := 56, numerator := 17060574177872995065287147520 }, { target := 61, numerator := 17060570061943223618843443200 }, { target := 69, numerator := 202890642153680995960750080 }, { target := 100, numerator := 208683284116021250931818496 }, { target := 101, numerator := 17548019154383652067152494592 }, { target := 106, numerator := 17548014920855887150810398720 }, { target := 114, numerator := 208687517643786167273914368 }, { target := 126, numerator := 202886526223909549517045760 }, { target := 127, numerator := 17060574177872995065287147520 }, { target := 132, numerator := 17060570061943223618843443200 }, { target := 140, numerator := 202890642153680995960750080 }, { target := 195, numerator := 179699494655462743857954816 }, { target := 196, numerator := 15110794271830367057825759232 }, { target := 201, numerator := 15110790626292569490975621120 }, { target := 209, numerator := 179703140193260310708092928 }, { target := 240, numerator := 8411095701454078752835239936 }, { target := 241, numerator := 707282660916963309706618601472 }, { target := 246, numerator := 707282490282274784884052459520 }, { target := 254, numerator := 8411266336142603575401381888 }, { target := 266, numerator := 2289719367384122058835230720 }, { target := 267, numerator := 192540765721709515736812093440 }, { target := 272, numerator := 192540719270502095126947430400 }, { target := 280, numerator := 2289765818591542668699893760 }, { target := 315, numerator := 208683284116021250931818496 }, { target := 316, numerator := 17548019154383652067152494592 }, { target := 321, numerator := 17548014920855887150810398720 }, { target := 329, numerator := 208687517643786167273914368 }, { target := 341, numerator := 8411095701454078752835239936 }, { target := 342, numerator := 707282660916963309706618601472 }, { target := 347, numerator := 707282490282274784884052459520 }, { target := 355, numerator := 8411266336142603575401381888 }, { target := 376, numerator := 202886526223909549517045760 }, { target := 377, numerator := 17060574177872995065287147520 }, { target := 382, numerator := 17060570061943223618843443200 }, { target := 390, numerator := 202890642153680995960750080 }, { target := 456, numerator := 202886526223909549517045760 }, { target := 457, numerator := 17060574177872995065287147520 }, { target := 462, numerator := 17060570061943223618843443200 }, { target := 470, numerator := 202890642153680995960750080 }, { target := 482, numerator := 173902736763351042443182080 }, { target := 483, numerator := 14623349295319710055960412160 }, { target := 488, numerator := 14623345767379905959008665600 }, { target := 496, numerator := 173906264703155139394928640 }, { target := 531, numerator := 202886526223909549517045760 }, { target := 532, numerator := 17060574177872995065287147520 }, { target := 537, numerator := 17060570061943223618843443200 }, { target := 545, numerator := 202890642153680995960750080 }, { target := 557, numerator := 2289719367384122058835230720 }, { target := 558, numerator := 192540765721709515736812093440 }, { target := 563, numerator := 192540719270502095126947430400 }, { target := 571, numerator := 2289765818591542668699893760 }, { target := 592, numerator := 173902736763351042443182080 }, { target := 593, numerator := 14623349295319710055960412160 }, { target := 598, numerator := 14623345767379905959008665600 }, { target := 606, numerator := 173906264703155139394928640 }, { target := 739, numerator := 11625986665479150067777536 }, { target := 740, numerator := 1717097389439966556167602176 }, { target := 742, numerator := 17897018925461918329539133440 }, { target := 750, numerator := 1717097389439966556167602176 }, { target := 757, numerator := 11625986665479150067777536 }]

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
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot4.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 11, numerator := 5270160994882524058484736 }, { target := 12, numerator := 126143853490413962948247552 }, { target := 13, numerator := 94352882327735511369646080 }, { target := 14, numerator := 109483344538849854634328064 }, { target := 15, numerator := 5270160994882524058484736 }, { target := 16, numerator := 109313339345466547406635008 }, { target := 17, numerator := 109823354925616469089714176 }, { target := 18, numerator := 5270160994882524058484736 }, { target := 19, numerator := 126143853490413962948247552 }, { target := 20, numerator := 5270160994882524058484736 }, { target := 31, numerator := 140537626530200641559592960 }, { target := 32, numerator := 3363836093077705678619934720 }, { target := 33, numerator := 2516076862072946969857228800 }, { target := 34, numerator := 2919555854369329456915415040 }, { target := 35, numerator := 140537626530200641559592960 }, { target := 36, numerator := 2915022382545774597510266880 }, { target := 37, numerator := 2928622798016439175725711360 }, { target := 38, numerator := 140537626530200641559592960 }, { target := 39, numerator := 3363836093077705678619934720 }, { target := 40, numerator := 140537626530200641559592960 }, { target := 45, numerator := 134389105369504363491360768 }, { target := 46, numerator := 3216668264005556055180312576 }, { target := 47, numerator := 2405998499357255539925975040 }, { target := 48, numerator := 2791825285740671293175365632 }, { target := 49, numerator := 134389105369504363491360768 }, { target := 50, numerator := 2787490153309396958869192704 }, { target := 51, numerator := 2800495550603219961787711488 }, { target := 52, numerator := 134389105369504363491360768 }, { target := 53, numerator := 3216668264005556055180312576 }, { target := 54, numerator := 134389105369504363491360768 }, { target := 76, numerator := 4391800829068770048737280 }, { target := 77, numerator := 105119877908678302456872960 }, { target := 78, numerator := 78627401939779592808038400 }, { target := 79, numerator := 91236120449041545528606720 }, { target := 80, numerator := 4391800829068770048737280 }, { target := 81, numerator := 91094449454555456172195840 }, { target := 82, numerator := 91519462438013724241428480 }, { target := 83, numerator := 4391800829068770048737280 }, { target := 84, numerator := 105119877908678302456872960 }, { target := 85, numerator := 4391800829068770048737280 }, { target := 90, numerator := 137902546032759379530350592 }, { target := 91, numerator := 3300764166332498697145810944 }, { target := 92, numerator := 2468900420909079214172405760 }, { target := 93, numerator := 2864814182099904529598251008 }, { target := 94, numerator := 137902546032759379530350592 }, { target := 95, numerator := 2860365712873041323806949376 }, { target := 96, numerator := 2873711120553630941180854272 }, { target := 97, numerator := 137902546032759379530350592 }, { target := 98, numerator := 3300764166332498697145810944 }, { target := 99, numerator := 137902546032759379530350592 }, { target := 653, numerator := 202886526223909549517045760 }, { target := 654, numerator := 17060574177872995065287147520 }, { target := 659, numerator := 17060570061943223618843443200 }, { target := 667, numerator := 202890642153680995960750080 }, { target := 688, numerator := 179699494655462743857954816 }, { target := 689, numerator := 15110794271830367057825759232 }, { target := 694, numerator := 15110790626292569490975621120 }, { target := 702, numerator := 179703140193260310708092928 }]

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
    Slot4.Left5.expected,
    Slot4.Left6.expected,
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot4.Left10.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 116, numerator := 4391800829068770048737280 }, { target := 117, numerator := 105119877908678302456872960 }, { target := 118, numerator := 78627401939779592808038400 }, { target := 119, numerator := 91236120449041545528606720 }, { target := 120, numerator := 4391800829068770048737280 }, { target := 121, numerator := 91094449454555456172195840 }, { target := 122, numerator := 91519462438013724241428480 }, { target := 123, numerator := 4391800829068770048737280 }, { target := 124, numerator := 105119877908678302456872960 }, { target := 125, numerator := 4391800829068770048737280 }, { target := 171, numerator := 134389105369504363491360768 }, { target := 172, numerator := 3216668264005556055180312576 }, { target := 173, numerator := 2405998499357255539925975040 }, { target := 174, numerator := 2791825285740671293175365632 }, { target := 175, numerator := 134389105369504363491360768 }, { target := 176, numerator := 2787490153309396958869192704 }, { target := 177, numerator := 2800495550603219961787711488 }, { target := 178, numerator := 134389105369504363491360768 }, { target := 179, numerator := 3216668264005556055180312576 }, { target := 180, numerator := 134389105369504363491360768 }, { target := 185, numerator := 76417334425796598848028672 }, { target := 186, numerator := 1829085875611002462749589504 }, { target := 187, numerator := 1368116793752164914859868160 }, { target := 188, numerator := 1587508495813322892197756928 }, { target := 189, numerator := 76417334425796598848028672 }, { target := 190, numerator := 1585043420509264937396207616 }, { target := 191, numerator := 1592438646421438801800855552 }, { target := 192, numerator := 76417334425796598848028672 }, { target := 193, numerator := 1829085875611002462749589504 }, { target := 194, numerator := 76417334425796598848028672 }, { target := 216, numerator := 137902546032759379530350592 }, { target := 217, numerator := 3300764166332498697145810944 }, { target := 218, numerator := 2468900420909079214172405760 }, { target := 219, numerator := 2864814182099904529598251008 }, { target := 220, numerator := 137902546032759379530350592 }, { target := 221, numerator := 2860365712873041323806949376 }, { target := 222, numerator := 2873711120553630941180854272 }, { target := 223, numerator := 137902546032759379530350592 }, { target := 224, numerator := 3300764166332498697145810944 }, { target := 225, numerator := 137902546032759379530350592 }, { target := 230, numerator := 2152860766409511077891014656 }, { target := 231, numerator := 51529764150834103864359124992 }, { target := 232, numerator := 38543152430879956394500423680 }, { target := 233, numerator := 44723946244120165618123014144 }, { target := 234, numerator := 2152860766409511077891014656 }, { target := 235, numerator := 44654499122623084615610400768 }, { target := 236, numerator := 44862840487114327623148240896 }, { target := 237, numerator := 2152860766409511077891014656 }, { target := 238, numerator := 51529764150834103864359124992 }, { target := 239, numerator := 2152860766409511077891014656 }, { target := 256, numerator := 84322575918120384935755776 }, { target := 257, numerator := 2018301655846623407171960832 }, { target := 258, numerator := 1509646117243768181914337280 }, { target := 259, numerator := 1751733512621597674149249024 }, { target := 260, numerator := 84322575918120384935755776 }, { target := 261, numerator := 1749013429527464758506160128 }, { target := 262, numerator := 1757173678809863505435426816 }, { target := 263, numerator := 84322575918120384935755776 }, { target := 264, numerator := 2018301655846623407171960832 }, { target := 265, numerator := 84322575918120384935755776 }]

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
    Slot4.Left11.expected,
    Slot4.Left12.expected,
    Slot4.Left13.expected,
    Slot4.Left14.expected,
    Slot4.Left15.expected,
    Slot4.Left16.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 305, numerator := 140537626530200641559592960 }, { target := 306, numerator := 3363836093077705678619934720 }, { target := 307, numerator := 2516076862072946969857228800 }, { target := 308, numerator := 2919555854369329456915415040 }, { target := 309, numerator := 140537626530200641559592960 }, { target := 310, numerator := 2915022382545774597510266880 }, { target := 311, numerator := 2928622798016439175725711360 }, { target := 312, numerator := 140537626530200641559592960 }, { target := 313, numerator := 3363836093077705678619934720 }, { target := 314, numerator := 140537626530200641559592960 }, { target := 331, numerator := 134389105369504363491360768 }, { target := 332, numerator := 3216668264005556055180312576 }, { target := 333, numerator := 2405998499357255539925975040 }, { target := 334, numerator := 2791825285740671293175365632 }, { target := 335, numerator := 134389105369504363491360768 }, { target := 336, numerator := 2787490153309396958869192704 }, { target := 337, numerator := 2800495550603219961787711488 }, { target := 338, numerator := 134389105369504363491360768 }, { target := 339, numerator := 3216668264005556055180312576 }, { target := 340, numerator := 134389105369504363491360768 }, { target := 432, numerator := 4391800829068770048737280 }, { target := 433, numerator := 105119877908678302456872960 }, { target := 434, numerator := 78627401939779592808038400 }, { target := 435, numerator := 91236120449041545528606720 }, { target := 436, numerator := 4391800829068770048737280 }, { target := 437, numerator := 91094449454555456172195840 }, { target := 438, numerator := 91519462438013724241428480 }, { target := 439, numerator := 4391800829068770048737280 }, { target := 440, numerator := 105119877908678302456872960 }, { target := 441, numerator := 4391800829068770048737280 }, { target := 446, numerator := 84322575918120384935755776 }, { target := 447, numerator := 2018301655846623407171960832 }, { target := 448, numerator := 1509646117243768181914337280 }, { target := 449, numerator := 1751733512621597674149249024 }, { target := 450, numerator := 84322575918120384935755776 }, { target := 451, numerator := 1749013429527464758506160128 }, { target := 452, numerator := 1757173678809863505435426816 }, { target := 453, numerator := 84322575918120384935755776 }, { target := 454, numerator := 2018301655846623407171960832 }, { target := 455, numerator := 84322575918120384935755776 }, { target := 472, numerator := 4391800829068770048737280 }, { target := 473, numerator := 105119877908678302456872960 }, { target := 474, numerator := 78627401939779592808038400 }, { target := 475, numerator := 91236120449041545528606720 }, { target := 476, numerator := 4391800829068770048737280 }, { target := 477, numerator := 91094449454555456172195840 }, { target := 478, numerator := 91519462438013724241428480 }, { target := 479, numerator := 4391800829068770048737280 }, { target := 480, numerator := 105119877908678302456872960 }, { target := 481, numerator := 4391800829068770048737280 }, { target := 521, numerator := 135267465535318117501108224 }, { target := 522, numerator := 3237692239587291715671687168 }, { target := 523, numerator := 2421723979745211458487582720 }, { target := 524, numerator := 2810072509830479602281086976 }, { target := 525, numerator := 135267465535318117501108224 }, { target := 526, numerator := 2805709043200308050103631872 }, { target := 527, numerator := 2818799443090822706635997184 }, { target := 528, numerator := 135267465535318117501108224 }, { target := 529, numerator := 3237692239587291715671687168 }, { target := 530, numerator := 135267465535318117501108224 }]

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
    Slot4.Left17.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left7.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 55, numerator := 322804744938580018515148800 }, { target := 56, numerator := 27028162032797209607830241280 }, { target := 61, numerator := 27028171814265163910542786560 }, { target := 69, numerator := 322794963470625715802603520 }, { target := 100, numerator := 27028162032797209607830241280 }, { target := 101, numerator := 2263044624731698875376984915968 }, { target := 106, numerator := 2263045443725548664697007374336 }, { target := 114, numerator := 27027343038947420287807782912 }, { target := 142, numerator := 191994557342514945674182656 }, { target := 143, numerator := 20130283062287264259646685184 }, { target := 145, numerator := 216984331217207040348782592000 }, { target := 153, numerator := 20130298418166440658506612736 }, { target := 160, numerator := 191994557342514945674182656 }, { target := 315, numerator := 27028171814265163910542786560 }, { target := 316, numerator := 2263045443725548664697007374336 }, { target := 321, numerator := 2263046262719694847167506153472 }, { target := 329, numerator := 27027352820118981440044007424 }, { target := 357, numerator := 1859673314457098724711596032 }, { target := 358, numerator := 194983392975138485875609960448 }, { target := 360, numerator := 2101726090599994112788660224000 }, { target := 368, numerator := 194983541713306482124408225792 }, { target := 375, numerator := 1859673314457098724711596032 }, { target := 411, numerator := 1100467228602562033083219968 }, { target := 413, numerator := 38513609306163123894043541504 }, { target := 416, numerator := 38513628195629055372624396288 }, { target := 423, numerator := 1100457783869596293792792576 }, { target := 547, numerator := 76417334425796598848028672 }, { target := 548, numerator := 1829085875611002462749589504 }, { target := 549, numerator := 1368116793752164914859868160 }, { target := 550, numerator := 1587508495813322892197756928 }, { target := 551, numerator := 76417334425796598848028672 }, { target := 552, numerator := 1585043420509264937396207616 }, { target := 553, numerator := 1592438646421438801800855552 }, { target := 554, numerator := 76417334425796598848028672 }, { target := 555, numerator := 1829085875611002462749589504 }, { target := 556, numerator := 76417334425796598848028672 }, { target := 627, numerator := 1100467228602562033083219968 }, { target := 629, numerator := 38513609306163123894043541504 }, { target := 632, numerator := 38513628195629055372624396288 }, { target := 639, numerator := 1100457783869596293792792576 }, { target := 643, numerator := 5270160994882524058484736 }, { target := 644, numerator := 126143853490413962948247552 }, { target := 645, numerator := 94352882327735511369646080 }, { target := 646, numerator := 109483344538849854634328064 }, { target := 647, numerator := 5270160994882524058484736 }, { target := 648, numerator := 109313339345466547406635008 }, { target := 649, numerator := 109823354925616469089714176 }, { target := 650, numerator := 5270160994882524058484736 }, { target := 651, numerator := 126143853490413962948247552 }, { target := 652, numerator := 5270160994882524058484736 }, { target := 669, numerator := 191994557342514945674182656 }, { target := 670, numerator := 20130283062287264259646685184 }, { target := 672, numerator := 216984331217207040348782592000 }, { target := 680, numerator := 20130298418166440658506612736 }, { target := 687, numerator := 191994557342514945674182656 }, { target := 723, numerator := 1100467228602562033083219968 }, { target := 725, numerator := 38513609306163123894043541504 }, { target := 728, numerator := 38513628195629055372624396288 }, { target := 735, numerator := 1100457783869596293792792576 }, { target := 758, numerator := 1100467228602562033083219968 }, { target := 760, numerator := 38513609306163123894043541504 }, { target := 763, numerator := 38513628195629055372624396288 }, { target := 770, numerator := 1100457783869596293792792576 }]

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
    Slot7.Left14.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 1100467228602562033083219968 }, { target := 3, numerator := 1100467228602562033083219968 }, { target := 4, numerator := 1100467228602562033083219968 }, { target := 5, numerator := 1100467228602562033083219968 }, { target := 11, numerator := 191994557342514945674182656 }, { target := 13, numerator := 1859673314457098724711596032 }, { target := 18, numerator := 191994557342514945674182656 }, { target := 22, numerator := 38513609306163123894043541504 }, { target := 23, numerator := 38513609306163123894043541504 }, { target := 24, numerator := 38513609306163123894043541504 }, { target := 25, numerator := 38513609306163123894043541504 }, { target := 31, numerator := 20130283062287264259646685184 }, { target := 33, numerator := 194983392975138485875609960448 }, { target := 38, numerator := 20130283062287264259646685184 }, { target := 72, numerator := 38513628195629055372624396288 }, { target := 73, numerator := 38513628195629055372624396288 }, { target := 74, numerator := 38513628195629055372624396288 }, { target := 75, numerator := 38513628195629055372624396288 }, { target := 76, numerator := 216984331217207040348782592000 }, { target := 78, numerator := 2101726090599994112788660224000 }, { target := 83, numerator := 216984331217207040348782592000 }, { target := 142, numerator := 5270160994882524058484736 }, { target := 143, numerator := 140537626530200641559592960 }, { target := 144, numerator := 134389105369504363491360768 }, { target := 145, numerator := 4391800829068770048737280 }, { target := 146, numerator := 137902546032759379530350592 }, { target := 147, numerator := 4391800829068770048737280 }, { target := 148, numerator := 134389105369504363491360768 }, { target := 149, numerator := 76417334425796598848028672 }, { target := 150, numerator := 137902546032759379530350592 }, { target := 151, numerator := 2152860766409511077891014656 }, { target := 152, numerator := 84322575918120384935755776 }, { target := 153, numerator := 140537626530200641559592960 }, { target := 154, numerator := 134389105369504363491360768 }, { target := 155, numerator := 4391800829068770048737280 }, { target := 156, numerator := 84322575918120384935755776 }, { target := 157, numerator := 4391800829068770048737280 }, { target := 158, numerator := 135267465535318117501108224 }, { target := 159, numerator := 76417334425796598848028672 }, { target := 160, numerator := 5270160994882524058484736 }, { target := 301, numerator := 1100457783869596293792792576 }, { target := 302, numerator := 1100457783869596293792792576 }, { target := 303, numerator := 1100457783869596293792792576 }, { target := 304, numerator := 1100457783869596293792792576 }, { target := 305, numerator := 20130298418166440658506612736 }, { target := 307, numerator := 194983541713306482124408225792 }, { target := 312, numerator := 20130298418166440658506612736 }, { target := 643, numerator := 191994557342514945674182656 }, { target := 645, numerator := 1859673314457098724711596032 }, { target := 650, numerator := 191994557342514945674182656 }, { target := 653, numerator := 322794963470625715802603520 }, { target := 654, numerator := 27027343038947420287807782912 }, { target := 659, numerator := 27027352820118981440044007424 }, { target := 667, numerator := 322785182299064563566379008 }]

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
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 282, numerator := 126143853490413962948247552 }, { target := 283, numerator := 3363836093077705678619934720 }, { target := 284, numerator := 3216668264005556055180312576 }, { target := 285, numerator := 105119877908678302456872960 }, { target := 286, numerator := 3300764166332498697145810944 }, { target := 287, numerator := 105119877908678302456872960 }, { target := 288, numerator := 3216668264005556055180312576 }, { target := 289, numerator := 1829085875611002462749589504 }, { target := 290, numerator := 3300764166332498697145810944 }, { target := 291, numerator := 51529764150834103864359124992 }, { target := 292, numerator := 2018301655846623407171960832 }, { target := 293, numerator := 3363836093077705678619934720 }, { target := 294, numerator := 3216668264005556055180312576 }, { target := 295, numerator := 105119877908678302456872960 }, { target := 296, numerator := 2018301655846623407171960832 }, { target := 297, numerator := 105119877908678302456872960 }, { target := 298, numerator := 3237692239587291715671687168 }, { target := 299, numerator := 1829085875611002462749589504 }, { target := 300, numerator := 126143853490413962948247552 }, { target := 357, numerator := 94352882327735511369646080 }, { target := 358, numerator := 2516076862072946969857228800 }, { target := 359, numerator := 2405998499357255539925975040 }, { target := 360, numerator := 78627401939779592808038400 }, { target := 361, numerator := 2468900420909079214172405760 }, { target := 362, numerator := 78627401939779592808038400 }, { target := 363, numerator := 2405998499357255539925975040 }, { target := 364, numerator := 1368116793752164914859868160 }, { target := 365, numerator := 2468900420909079214172405760 }, { target := 366, numerator := 38543152430879956394500423680 }, { target := 367, numerator := 1509646117243768181914337280 }, { target := 368, numerator := 2516076862072946969857228800 }, { target := 369, numerator := 2405998499357255539925975040 }, { target := 370, numerator := 78627401939779592808038400 }, { target := 371, numerator := 1509646117243768181914337280 }, { target := 372, numerator := 78627401939779592808038400 }, { target := 373, numerator := 2421723979745211458487582720 }, { target := 374, numerator := 1368116793752164914859868160 }, { target := 375, numerator := 94352882327735511369646080 }, { target := 392, numerator := 109483344538849854634328064 }, { target := 393, numerator := 2919555854369329456915415040 }, { target := 394, numerator := 2791825285740671293175365632 }, { target := 395, numerator := 91236120449041545528606720 }, { target := 396, numerator := 2864814182099904529598251008 }, { target := 397, numerator := 91236120449041545528606720 }, { target := 398, numerator := 2791825285740671293175365632 }, { target := 399, numerator := 1587508495813322892197756928 }, { target := 400, numerator := 2864814182099904529598251008 }, { target := 401, numerator := 44723946244120165618123014144 }, { target := 402, numerator := 1751733512621597674149249024 }, { target := 403, numerator := 2919555854369329456915415040 }, { target := 404, numerator := 2791825285740671293175365632 }, { target := 405, numerator := 91236120449041545528606720 }, { target := 406, numerator := 1751733512621597674149249024 }, { target := 407, numerator := 91236120449041545528606720 }, { target := 408, numerator := 2810072509830479602281086976 }, { target := 409, numerator := 1587508495813322892197756928 }, { target := 410, numerator := 109483344538849854634328064 }]

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
    Slot10.Left4.expected,
    Slot10.Left5.expected,
    Slot10.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 498, numerator := 5270160994882524058484736 }, { target := 499, numerator := 140537626530200641559592960 }, { target := 500, numerator := 134389105369504363491360768 }, { target := 501, numerator := 4391800829068770048737280 }, { target := 502, numerator := 137902546032759379530350592 }, { target := 503, numerator := 4391800829068770048737280 }, { target := 504, numerator := 134389105369504363491360768 }, { target := 505, numerator := 76417334425796598848028672 }, { target := 506, numerator := 137902546032759379530350592 }, { target := 507, numerator := 2152860766409511077891014656 }, { target := 508, numerator := 84322575918120384935755776 }, { target := 509, numerator := 140537626530200641559592960 }, { target := 510, numerator := 134389105369504363491360768 }, { target := 511, numerator := 4391800829068770048737280 }, { target := 512, numerator := 84322575918120384935755776 }, { target := 513, numerator := 4391800829068770048737280 }, { target := 514, numerator := 135267465535318117501108224 }, { target := 515, numerator := 76417334425796598848028672 }, { target := 516, numerator := 5270160994882524058484736 }, { target := 573, numerator := 109313339345466547406635008 }, { target := 574, numerator := 2915022382545774597510266880 }, { target := 575, numerator := 2787490153309396958869192704 }, { target := 576, numerator := 91094449454555456172195840 }, { target := 577, numerator := 2860365712873041323806949376 }, { target := 578, numerator := 91094449454555456172195840 }, { target := 579, numerator := 2787490153309396958869192704 }, { target := 580, numerator := 1585043420509264937396207616 }, { target := 581, numerator := 2860365712873041323806949376 }, { target := 582, numerator := 44654499122623084615610400768 }, { target := 583, numerator := 1749013429527464758506160128 }, { target := 584, numerator := 2915022382545774597510266880 }, { target := 585, numerator := 2787490153309396958869192704 }, { target := 586, numerator := 91094449454555456172195840 }, { target := 587, numerator := 1749013429527464758506160128 }, { target := 588, numerator := 91094449454555456172195840 }, { target := 589, numerator := 2805709043200308050103631872 }, { target := 590, numerator := 1585043420509264937396207616 }, { target := 591, numerator := 109313339345466547406635008 }, { target := 608, numerator := 109823354925616469089714176 }, { target := 609, numerator := 2928622798016439175725711360 }, { target := 610, numerator := 2800495550603219961787711488 }, { target := 611, numerator := 91519462438013724241428480 }, { target := 612, numerator := 2873711120553630941180854272 }, { target := 613, numerator := 91519462438013724241428480 }, { target := 614, numerator := 2800495550603219961787711488 }, { target := 615, numerator := 1592438646421438801800855552 }, { target := 616, numerator := 2873711120553630941180854272 }, { target := 617, numerator := 44862840487114327623148240896 }, { target := 618, numerator := 1757173678809863505435426816 }, { target := 619, numerator := 2928622798016439175725711360 }, { target := 620, numerator := 2800495550603219961787711488 }, { target := 621, numerator := 91519462438013724241428480 }, { target := 622, numerator := 1757173678809863505435426816 }, { target := 623, numerator := 91519462438013724241428480 }, { target := 624, numerator := 2818799443090822706635997184 }, { target := 625, numerator := 1592438646421438801800855552 }, { target := 626, numerator := 109823354925616469089714176 }]

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
    Slot10.Left7.expected,
    Slot10.Left8.expected,
    Slot10.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 669, numerator := 5270160994882524058484736 }, { target := 670, numerator := 140537626530200641559592960 }, { target := 671, numerator := 134389105369504363491360768 }, { target := 672, numerator := 4391800829068770048737280 }, { target := 673, numerator := 137902546032759379530350592 }, { target := 674, numerator := 4391800829068770048737280 }, { target := 675, numerator := 134389105369504363491360768 }, { target := 676, numerator := 76417334425796598848028672 }, { target := 677, numerator := 137902546032759379530350592 }, { target := 678, numerator := 2152860766409511077891014656 }, { target := 679, numerator := 84322575918120384935755776 }, { target := 680, numerator := 140537626530200641559592960 }, { target := 681, numerator := 134389105369504363491360768 }, { target := 682, numerator := 4391800829068770048737280 }, { target := 683, numerator := 84322575918120384935755776 }, { target := 684, numerator := 4391800829068770048737280 }, { target := 685, numerator := 135267465535318117501108224 }, { target := 686, numerator := 76417334425796598848028672 }, { target := 687, numerator := 5270160994882524058484736 }, { target := 704, numerator := 126143853490413962948247552 }, { target := 705, numerator := 3363836093077705678619934720 }, { target := 706, numerator := 3216668264005556055180312576 }, { target := 707, numerator := 105119877908678302456872960 }, { target := 708, numerator := 3300764166332498697145810944 }, { target := 709, numerator := 105119877908678302456872960 }, { target := 710, numerator := 3216668264005556055180312576 }, { target := 711, numerator := 1829085875611002462749589504 }, { target := 712, numerator := 3300764166332498697145810944 }, { target := 713, numerator := 51529764150834103864359124992 }, { target := 714, numerator := 2018301655846623407171960832 }, { target := 715, numerator := 3363836093077705678619934720 }, { target := 716, numerator := 3216668264005556055180312576 }, { target := 717, numerator := 105119877908678302456872960 }, { target := 718, numerator := 2018301655846623407171960832 }, { target := 719, numerator := 105119877908678302456872960 }, { target := 720, numerator := 3237692239587291715671687168 }, { target := 721, numerator := 1829085875611002462749589504 }, { target := 722, numerator := 126143853490413962948247552 }, { target := 739, numerator := 5270160994882524058484736 }, { target := 740, numerator := 140537626530200641559592960 }, { target := 741, numerator := 134389105369504363491360768 }, { target := 742, numerator := 4391800829068770048737280 }, { target := 743, numerator := 137902546032759379530350592 }, { target := 744, numerator := 4391800829068770048737280 }, { target := 745, numerator := 134389105369504363491360768 }, { target := 746, numerator := 76417334425796598848028672 }, { target := 747, numerator := 137902546032759379530350592 }, { target := 748, numerator := 2152860766409511077891014656 }, { target := 749, numerator := 84322575918120384935755776 }, { target := 750, numerator := 140537626530200641559592960 }, { target := 751, numerator := 134389105369504363491360768 }, { target := 752, numerator := 4391800829068770048737280 }, { target := 753, numerator := 84322575918120384935755776 }, { target := 754, numerator := 4391800829068770048737280 }, { target := 755, numerator := 135267465535318117501108224 }, { target := 756, numerator := 76417334425796598848028672 }, { target := 757, numerator := 5270160994882524058484736 }]

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
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left6.expected,
    Slot11.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 55, numerator := 198908359043048577957888000 }, { target := 56, numerator := 204591455015707108756684800 }, { target := 57, numerator := 198908359043048577957888000 }, { target := 58, numerator := 176175975152414454762700800 }, { target := 59, numerator := 8246172256327528189054156800 }, { target := 60, numerator := 2244822909200119665524736000 }, { target := 61, numerator := 204591455015707108756684800 }, { target := 62, numerator := 8246172256327528189054156800 }, { target := 63, numerator := 198908359043048577957888000 }, { target := 64, numerator := 198908359043048577957888000 }, { target := 65, numerator := 170492879179755923963904000 }, { target := 66, numerator := 198908359043048577957888000 }, { target := 67, numerator := 2244822909200119665524736000 }, { target := 68, numerator := 170492879179755923963904000 }, { target := 69, numerator := 198908359043048577957888000 }, { target := 70, numerator := 176175975152414454762700800 }, { target := 100, numerator := 16726053115561759867928576000 }, { target := 101, numerator := 17203940347434953007012249600 }, { target := 102, numerator := 16726053115561759867928576000 }, { target := 103, numerator := 14814504188068987311593881600 }, { target := 104, numerator := 693414373448003244810410393600 }, { target := 105, numerator := 188765456589911289938051072000 }, { target := 106, numerator := 17203940347434953007012249600 }, { target := 107, numerator := 693414373448003244810410393600 }, { target := 108, numerator := 16726053115561759867928576000 }, { target := 109, numerator := 16726053115561759867928576000 }, { target := 110, numerator := 14336616956195794172510208000 }, { target := 111, numerator := 16726053115561759867928576000 }, { target := 112, numerator := 188765456589911289938051072000 }, { target := 113, numerator := 14336616956195794172510208000 }, { target := 114, numerator := 16726053115561759867928576000 }, { target := 115, numerator := 14814504188068987311593881600 }, { target := 315, numerator := 16726049080336493743964160000 }, { target := 316, numerator := 17203936196917536422363136000 }, { target := 317, numerator := 16726049080336493743964160000 }, { target := 318, numerator := 14814500614012323030368256000 }, { target := 319, numerator := 693414206159092926356914176000 }, { target := 320, numerator := 188765411049511857967595520000 }, { target := 321, numerator := 17203936196917536422363136000 }, { target := 322, numerator := 693414206159092926356914176000 }, { target := 323, numerator := 16726049080336493743964160000 }, { target := 324, numerator := 16726049080336493743964160000 }, { target := 325, numerator := 14336613497431280351969280000 }, { target := 326, numerator := 16726049080336493743964160000 }, { target := 327, numerator := 188765411049511857967595520000 }, { target := 328, numerator := 14336613497431280351969280000 }, { target := 329, numerator := 16726049080336493743964160000 }, { target := 330, numerator := 14814500614012323030368256000 }, { target := 653, numerator := 198912394268314701922304000 }, { target := 654, numerator := 204595605533123693405798400 }, { target := 655, numerator := 198912394268314701922304000 }, { target := 656, numerator := 176179549209078735988326400 }, { target := 657, numerator := 8246339545237846642550374400 }, { target := 658, numerator := 2244868449599551635980288000 }, { target := 659, numerator := 204595605533123693405798400 }, { target := 660, numerator := 8246339545237846642550374400 }, { target := 661, numerator := 198912394268314701922304000 }, { target := 662, numerator := 198912394268314701922304000 }, { target := 663, numerator := 170496337944269744504832000 }, { target := 664, numerator := 198912394268314701922304000 }, { target := 665, numerator := 2244868449599551635980288000 }, { target := 666, numerator := 170496337944269744504832000 }, { target := 667, numerator := 198912394268314701922304000 }, { target := 668, numerator := 176179549209078735988326400 }]

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
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 3612461586404324120943656960 }, { target := 3, numerator := 3301857412620027093722333184 }, { target := 4, numerator := 3612461586404324120943656960 }, { target := 5, numerator := 3301857412620027093722333184 }, { target := 11, numerator := 11847133150963807813632000 }, { target := 12, numerator := 237416548345314708585185280 }, { target := 13, numerator := 398537559198422494850580480 }, { target := 14, numerator := 382425458113111716224040960 }, { target := 15, numerator := 11847133150963807813632000 }, { target := 16, numerator := 382425458113111716224040960 }, { target := 17, numerator := 255424190734779696461905920 }, { target := 18, numerator := 12321018477002360126177280 }, { target := 19, numerator := 237416548345314708585185280 }, { target := 20, numerator := 11373247824925255501086720 }, { target := 22, numerator := 130916803620311610440359608320 }, { target := 23, numerator := 119660405552023135523992240128 }, { target := 24, numerator := 130916803620311610440359608320 }, { target := 25, numerator := 119660405552023135523992240128 }, { target := 31, numerator := 1749759568043444180877312000 }, { target := 32, numerator := 35065181743590621384781332480 }, { target := 33, numerator := 58861911868981462244712775680 }, { target := 34, numerator := 56482238856442378158719631360 }, { target := 35, numerator := 1749759568043444180877312000 }, { target := 36, numerator := 56482238856442378158719631360 }, { target := 37, numerator := 37724816287016656539714846720 }, { target := 38, numerator := 1819749950765181948112404480 }, { target := 39, numerator := 35065181743590621384781332480 }, { target := 40, numerator := 1679769185321706413642219520 }, { target := 72, numerator := 130916851731725997684083916800 }, { target := 73, numerator := 119660449526755164238349598720 }, { target := 74, numerator := 130916851731725997684083916800 }, { target := 75, numerator := 119660449526755164238349598720 }, { target := 76, numerator := 18237451350674509167329280000 }, { target := 77, numerator := 365478525067517163713278771200 }, { target := 78, numerator := 613507863436690488388956979200 }, { target := 79, numerator := 588704929599773155921389158400 }, { target := 80, numerator := 18237451350674509167329280000 }, { target := 81, numerator := 588704929599773155921389158400 }, { target := 82, numerator := 393199451120542417647619276800 }, { target := 83, numerator := 18966949404701489534022451200 }, { target := 84, numerator := 365478525067517163713278771200 }, { target := 85, numerator := 17507953296647528800636108800 }, { target := 305, numerator := 1749759568043444180877312000 }, { target := 306, numerator := 35065181743590621384781332480 }, { target := 307, numerator := 58861911868981462244712775680 }, { target := 308, numerator := 56482238856442378158719631360 }, { target := 309, numerator := 1749759568043444180877312000 }, { target := 310, numerator := 56482238856442378158719631360 }, { target := 311, numerator := 37724816287016656539714846720 }, { target := 312, numerator := 1819749950765181948112404480 }, { target := 313, numerator := 35065181743590621384781332480 }, { target := 314, numerator := 1679769185321706413642219520 }, { target := 643, numerator := 11847133150963807813632000 }, { target := 644, numerator := 237416548345314708585185280 }, { target := 645, numerator := 398537559198422494850580480 }, { target := 646, numerator := 382425458113111716224040960 }, { target := 647, numerator := 11847133150963807813632000 }, { target := 648, numerator := 382425458113111716224040960 }, { target := 649, numerator := 255424190734779696461905920 }, { target := 650, numerator := 12321018477002360126177280 }, { target := 651, numerator := 237416548345314708585185280 }, { target := 652, numerator := 11373247824925255501086720 }]

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
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 73499195281372130284677365760 }, { target := 21, numerator := 249142422008577427398365020160 }, { target := 71, numerator := 73499195281372130284677365760 }, { target := 301, numerator := 3612413474989936877219348480 }, { target := 302, numerator := 3301813437887998379364974592 }, { target := 303, numerator := 3612413474989936877219348480 }, { target := 304, numerator := 3301813437887998379364974592 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3.Parent3
