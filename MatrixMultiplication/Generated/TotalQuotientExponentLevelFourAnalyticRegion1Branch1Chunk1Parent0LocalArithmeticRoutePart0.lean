import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 5; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent0

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
  [{ target := 10, numerator := 47450990973445802582605824 }, { target := 11, numerator := 9411184621691412860318515200 }, { target := 16, numerator := 9411184621691412860318515200 }, { target := 24, numerator := 47450990973445802582605824 }, { target := 26, numerator := 6674640748422548189872128 }, { target := 27, numerator := 1093845068841029188567695360 }, { target := 29, numerator := 11261558508049607016012840960 }, { target := 37, numerator := 1093845068841029188567695360 }, { target := 44, numerator := 6674640748422548189872128 }, { target := 45, numerator := 51914683375855837181378560 }, { target := 46, numerator := 10296490332525369898303488000 }, { target := 51, numerator := 10296490332525369898303488000 }, { target := 59, numerator := 51914683375855837181378560 }, { target := 61, numerator := 139333125623320693463580672 }, { target := 62, numerator := 22834015812056484311350640640 }, { target := 64, numerator := 235085033855535546459268055040 }, { target := 72, numerator := 22834015812056484311350640640 }, { target := 79, numerator := 139333125623320693463580672 }, { target := 96, numerator := 7230860810791093872361472 }, { target := 97, numerator := 1184998824577781620948336640 }, { target := 99, numerator := 12200021717053740934013911040 }, { target := 107, numerator := 1184998824577781620948336640 }, { target := 114, numerator := 7230860810791093872361472 }, { target := 141, numerator := 47450990973445802582605824 }, { target := 142, numerator := 9411184621691412860318515200 }, { target := 147, numerator := 9411184621691412860318515200 }, { target := 155, numerator := 47450990973445802582605824 }, { target := 157, numerator := 149901306808323061430878208 }, { target := 158, numerator := 24565937171054780526582824960 }, { target := 160, numerator := 252915834826614090901288386560 }, { target := 168, numerator := 24565937171054780526582824960 }, { target := 175, numerator := 149901306808323061430878208 }, { target := 192, numerator := 224434795165708182884450304 }, { target := 193, numerator := 36780540439779606465588756480 }, { target := 195, numerator := 378669904833168035913431777280 }, { target := 203, numerator := 36780540439779606465588756480 }, { target := 210, numerator := 224434795165708182884450304 }, { target := 267, numerator := 6952750779606821031116800 }, { target := 268, numerator := 1139421946709405404758016000 }, { target := 270, numerator := 11730790112551673975013376000 }, { target := 278, numerator := 1139421946709405404758016000 }, { target := 285, numerator := 6952750779606821031116800 }, { target := 357, numerator := 51914683375855837181378560 }, { target := 358, numerator := 10296490332525369898303488000 }, { target := 363, numerator := 10296490332525369898303488000 }, { target := 371, numerator := 51914683375855837181378560 }, { target := 373, numerator := 224434795165708182884450304 }, { target := 374, numerator := 36780540439779606465588756480 }, { target := 376, numerator := 378669904833168035913431777280 }, { target := 384, numerator := 36780540439779606465588756480 }, { target := 391, numerator := 224434795165708182884450304 }, { target := 408, numerator := 233890536225973459486769152 }, { target := 409, numerator := 38330154287304397816059658240 }, { target := 411, numerator := 394623779386238312519449968640 }, { target := 419, numerator := 38330154287304397816059658240 }, { target := 426, numerator := 233890536225973459486769152 }, { target := 483, numerator := 139333125623320693463580672 }, { target := 484, numerator := 22834015812056484311350640640 }, { target := 486, numerator := 235085033855535546459268055040 }, { target := 494, numerator := 22834015812056484311350640640 }, { target := 501, numerator := 139333125623320693463580672 }]

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
  [{ target := 80, numerator := 1726606616834673553614831616 }, { target := 82, numerator := 69029412188344070487280713728 }, { target := 85, numerator := 69029395318796615079895760896 }, { target := 92, numerator := 1726606616834673553614831616 }, { target := 115, numerator := 1949394567393986270210293760 }, { target := 117, numerator := 77936433115872337646929838080 }, { target := 120, numerator := 77936414069609081541817794560 }, { target := 127, numerator := 1949394567393986270210293760 }, { target := 176, numerator := 1670909629194845374465966080 }, { target := 178, numerator := 66802656956462003697368432640 }, { target := 181, numerator := 66802640631093498464415252480 }, { target := 188, numerator := 1670909629194845374465966080 }, { target := 211, numerator := 22000310117732130763801886720 }, { target := 213, numerator := 879568316593416382015351029760 }, { target := 216, numerator := 879568101642731063114800824320 }, { target := 223, numerator := 22000310117732130763801886720 }, { target := 237, numerator := 1949394567393986270210293760 }, { target := 239, numerator := 77936433115872337646929838080 }, { target := 242, numerator := 77936414069609081541817794560 }, { target := 249, numerator := 1949394567393986270210293760 }, { target := 286, numerator := 1670909629194845374465966080 }, { target := 288, numerator := 66802656956462003697368432640 }, { target := 291, numerator := 66802640631093498464415252480 }, { target := 298, numerator := 1670909629194845374465966080 }, { target := 312, numerator := 1949394567393986270210293760 }, { target := 314, numerator := 77936433115872337646929838080 }, { target := 317, numerator := 77936414069609081541817794560 }, { target := 324, numerator := 1949394567393986270210293760 }, { target := 392, numerator := 1949394567393986270210293760 }, { target := 394, numerator := 77936433115872337646929838080 }, { target := 397, numerator := 77936414069609081541817794560 }, { target := 404, numerator := 1949394567393986270210293760 }, { target := 427, numerator := 80816329065390687945003892736 }, { target := 429, numerator := 3231021841460878912162719858688 }, { target := 432, numerator := 3231021051857222209062217711616 }, { target := 439, numerator := 80816329065390687945003892736 }, { target := 453, numerator := 2005091555033814449359159296 }, { target := 455, numerator := 80163188347754404436842119168 }, { target := 458, numerator := 80163168757312198157298302976 }, { target := 465, numerator := 2005091555033814449359159296 }, { target := 502, numerator := 22000310117732130763801886720 }, { target := 504, numerator := 879568316593416382015351029760 }, { target := 507, numerator := 879568101642731063114800824320 }, { target := 514, numerator := 22000310117732130763801886720 }, { target := 528, numerator := 80816329065390687945003892736 }, { target := 530, numerator := 3231021841460878912162719858688 }, { target := 533, numerator := 3231021051857222209062217711616 }, { target := 540, numerator := 80816329065390687945003892736 }, { target := 573, numerator := 1726606616834673553614831616 }, { target := 575, numerator := 69029412188344070487280713728 }, { target := 578, numerator := 69029395318796615079895760896 }, { target := 585, numerator := 1726606616834673553614831616 }, { target := 623, numerator := 6952750779606821031116800 }, { target := 624, numerator := 1139421946709405404758016000 }, { target := 626, numerator := 11730790112551673975013376000 }, { target := 634, numerator := 1139421946709405404758016000 }, { target := 641, numerator := 6952750779606821031116800 }, { target := 642, numerator := 1949394567393986270210293760 }, { target := 644, numerator := 77936433115872337646929838080 }, { target := 647, numerator := 77936414069609081541817794560 }, { target := 654, numerator := 1949394567393986270210293760 }]

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
    Slot4.Left17.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 2529789092482814338519793664 }, { target := 134, numerator := 9215416191331771818184802304 }, { target := 136, numerator := 2529790794194955138225930240 }, { target := 227, numerator := 36681941841000807908537008128 }, { target := 230, numerator := 133623534774310691363679633408 }, { target := 232, numerator := 36681966515826849504275988480 }, { target := 253, numerator := 64931253373725568022008037376 }, { target := 256, numerator := 236529015577515476666743259136 }, { target := 258, numerator := 64931297051003848547798876160 }, { target := 302, numerator := 2108157577069011948766494720 }, { target := 305, numerator := 7679513492776476515154001920 }, { target := 307, numerator := 2108158995162462615188275200 }, { target := 328, numerator := 40476625479725029416316698624 }, { target := 331, numerator := 147446659061308349090956836864 }, { target := 333, numerator := 40476652707119282211614883840 }, { target := 342, numerator := 2108157577069011948766494720 }, { target := 345, numerator := 7679513492776476515154001920 }, { target := 347, numerator := 2108158995162462615188275200 }, { target := 443, numerator := 64509621858311765632254738432 }, { target := 446, numerator := 234993112878960181363712458752 }, { target := 448, numerator := 64509665251971356024761221120 }, { target := 469, numerator := 67461042466208382360527831040 }, { target := 472, numerator := 245744431768847248484928061440 }, { target := 474, numerator := 67461087845198803686024806400 }, { target := 518, numerator := 40476625479725029416316698624 }, { target := 521, numerator := 147446659061308349090956836864 }, { target := 523, numerator := 40476652707119282211614883840 }, { target := 544, numerator := 1033418844279229657285335711744 }, { target := 547, numerator := 3764497514159028787728491741184 }, { target := 549, numerator := 1033419539428639173965292503040 }, { target := 558, numerator := 66196147919966975191267934208 }, { target := 561, numerator := 241136723673181362575835660288 }, { target := 563, numerator := 66196192448101326116911841280 }, { target := 589, numerator := 36681941841000807908537008128 }, { target := 592, numerator := 133623534774310691363679633408 }, { target := 594, numerator := 36681966515826849504275988480 }, { target := 603, numerator := 64509621858311765632254738432 }, { target := 606, numerator := 234993112878960181363712458752 }, { target := 608, numerator := 64509665251971356024761221120 }, { target := 658, numerator := 2108157577069011948766494720 }, { target := 661, numerator := 7679513492776476515154001920 }, { target := 663, numerator := 2108158995162462615188275200 }, { target := 668, numerator := 2005091555033814449359159296 }, { target := 670, numerator := 80163188347754404436842119168 }, { target := 673, numerator := 80163168757312198157298302976 }, { target := 680, numerator := 2005091555033814449359159296 }, { target := 684, numerator := 66196147919966975191267934208 }, { target := 687, numerator := 241136723673181362575835660288 }, { target := 689, numerator := 66196192448101326116911841280 }, { target := 698, numerator := 2108157577069011948766494720 }, { target := 701, numerator := 7679513492776476515154001920 }, { target := 703, numerator := 2108158995162462615188275200 }, { target := 713, numerator := 1949394567393986270210293760 }, { target := 715, numerator := 77936433115872337646929838080 }, { target := 718, numerator := 77936414069609081541817794560 }, { target := 725, numerator := 1949394567393986270210293760 }, { target := 729, numerator := 64509621858311765632254738432 }, { target := 732, numerator := 234993112878960181363712458752 }, { target := 734, numerator := 64509665251971356024761221120 }, { target := 743, numerator := 67461042466208382360527831040 }, { target := 746, numerator := 245744431768847248484928061440 }, { target := 748, numerator := 67461087845198803686024806400 }]

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
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected,
    Slot5.Left9.expected,
    Slot5.Left10.expected,
    Slot5.Left11.expected,
    Slot5.Left12.expected,
    Slot5.Left13.expected,
    Slot5.Left14.expected,
    Slot5.Left15.expected,
    Slot8.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 1818224432700402278758088704 }, { target := 11, numerator := 1353996917968384675670917120 }, { target := 12, numerator := 1431368170423720942852112384 }, { target := 13, numerator := 1856910058928070412348686336 }, { target := 14, numerator := 24874857664390609898754277376 }, { target := 15, numerator := 44991383302778039365865046016 }, { target := 16, numerator := 1353996917968384675670917120 }, { target := 17, numerator := 24874857664390609898754277376 }, { target := 18, numerator := 1470053796651389076442710016 }, { target := 19, numerator := 1470053796651389076442710016 }, { target := 20, numerator := 1431368170423720942852112384 }, { target := 21, numerator := 1431368170423720942852112384 }, { target := 22, numerator := 44991383302778039365865046016 }, { target := 23, numerator := 1431368170423720942852112384 }, { target := 24, numerator := 1818224432700402278758088704 }, { target := 25, numerator := 1856910058928070412348686336 }, { target := 263, numerator := 1363668324525301709068566528 }, { target := 265, numerator := 1363668324525301709068566528 }, { target := 338, numerator := 1015497688476288506753187840 }, { target := 340, numerator := 1015497688476288506753187840 }, { target := 352, numerator := 1073526127817790707139084288 }, { target := 354, numerator := 1073526127817790707139084288 }, { target := 479, numerator := 1392682544196052809261514752 }, { target := 481, numerator := 1392682544196052809261514752 }, { target := 554, numerator := 18656143248292957424065708032 }, { target := 556, numerator := 18656143248292957424065708032 }, { target := 568, numerator := 33743537477083529524398784512 }, { target := 570, numerator := 33743537477083529524398784512 }, { target := 599, numerator := 1015497688476288506753187840 }, { target := 601, numerator := 1015497688476288506753187840 }, { target := 613, numerator := 18656143248292957424065708032 }, { target := 615, numerator := 18656143248292957424065708032 }, { target := 618, numerator := 1102540347488541807332032512 }, { target := 620, numerator := 1102540347488541807332032512 }, { target := 694, numerator := 1102540347488541807332032512 }, { target := 696, numerator := 1102540347488541807332032512 }, { target := 708, numerator := 1073526127817790707139084288 }, { target := 710, numerator := 1073526127817790707139084288 }, { target := 739, numerator := 1073526127817790707139084288 }, { target := 741, numerator := 1073526127817790707139084288 }, { target := 753, numerator := 33743537477083529524398784512 }, { target := 755, numerator := 33743537477083529524398784512 }, { target := 758, numerator := 1073526127817790707139084288 }, { target := 760, numerator := 1073526127817790707139084288 }, { target := 763, numerator := 2529789092482814338519793664 }, { target := 766, numerator := 9215416191331771818184802304 }, { target := 768, numerator := 2529790794194955138225930240 }, { target := 773, numerator := 1363668324525301709068566528 }, { target := 775, numerator := 1363668324525301709068566528 }, { target := 778, numerator := 1392682544196052809261514752 }, { target := 780, numerator := 1392682544196052809261514752 }]

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
    Slot9.Left0.expected,
    Slot9.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 2591491265470200054093447168 }, { target := 27, numerator := 37576623349317900784354983936 }, { target := 28, numerator := 66514942480401801388398477312 }, { target := 29, numerator := 2159576054558500045077872640 }, { target := 30, numerator := 41463860247523200865495154688 }, { target := 31, numerator := 2159576054558500045077872640 }, { target := 32, numerator := 66083027269490101379382902784 }, { target := 33, numerator := 69106433745872001442491924480 }, { target := 34, numerator := 41463860247523200865495154688 }, { target := 35, numerator := 1058624181944576722097173168128 }, { target := 36, numerator := 67810688113136901415445200896 }, { target := 37, numerator := 37576623349317900784354983936 }, { target := 38, numerator := 66083027269490101379382902784 }, { target := 39, numerator := 2159576054558500045077872640 }, { target := 40, numerator := 67810688113136901415445200896 }, { target := 41, numerator := 2159576054558500045077872640 }, { target := 42, numerator := 66083027269490101379382902784 }, { target := 43, numerator := 69106433745872001442491924480 }, { target := 44, numerator := 2591491265470200054093447168 }, { target := 141, numerator := 1818224432700402278758088704 }, { target := 142, numerator := 1353996917968384675670917120 }, { target := 143, numerator := 1431368170423720942852112384 }, { target := 144, numerator := 1856910058928070412348686336 }, { target := 145, numerator := 24874857664390609898754277376 }, { target := 146, numerator := 44991383302778039365865046016 }, { target := 147, numerator := 1353996917968384675670917120 }, { target := 148, numerator := 24874857664390609898754277376 }, { target := 149, numerator := 1470053796651389076442710016 }, { target := 150, numerator := 1470053796651389076442710016 }, { target := 151, numerator := 1431368170423720942852112384 }, { target := 152, numerator := 1431368170423720942852112384 }, { target := 153, numerator := 44991383302778039365865046016 }, { target := 154, numerator := 1431368170423720942852112384 }, { target := 155, numerator := 1818224432700402278758088704 }, { target := 156, numerator := 1856910058928070412348686336 }, { target := 157, numerator := 9440182439900839423506382848 }, { target := 158, numerator := 136882645378562171640842551296 }, { target := 159, numerator := 242298015957454878536663826432 }, { target := 160, numerator := 7866818699917366186255319040 }, { target := 161, numerator := 151042919038413430776102125568 }, { target := 162, numerator := 7866818699917366186255319040 }, { target := 163, numerator := 240724652217471405299412762624 }, { target := 164, numerator := 251738198397355717960170209280 }, { target := 165, numerator := 151042919038413430776102125568 }, { target := 166, numerator := 3856314526699492904502357393408 }, { target := 167, numerator := 247018107177405298248417017856 }, { target := 168, numerator := 136882645378562171640842551296 }, { target := 169, numerator := 240724652217471405299412762624 }, { target := 170, numerator := 7866818699917366186255319040 }, { target := 171, numerator := 247018107177405298248417017856 }, { target := 172, numerator := 7866818699917366186255319040 }, { target := 173, numerator := 240724652217471405299412762624 }, { target := 174, numerator := 251738198397355717960170209280 }, { target := 175, numerator := 9440182439900839423506382848 }]

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
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 1755871135764074800286269440 }, { target := 81, numerator := 1982435153282019935807078400 }, { target := 82, numerator := 1699230131384588516406067200 }, { target := 83, numerator := 22373196729897082132679884800 }, { target := 84, numerator := 1982435153282019935807078400 }, { target := 85, numerator := 1699230131384588516406067200 }, { target := 86, numerator := 1982435153282019935807078400 }, { target := 87, numerator := 1982435153282019935807078400 }, { target := 88, numerator := 82186097354634597910173450240 }, { target := 89, numerator := 2039076157661506219687280640 }, { target := 90, numerator := 22373196729897082132679884800 }, { target := 91, numerator := 82186097354634597910173450240 }, { target := 92, numerator := 1755871135764074800286269440 }, { target := 93, numerator := 1982435153282019935807078400 }, { target := 94, numerator := 2039076157661506219687280640 }, { target := 95, numerator := 1982435153282019935807078400 }, { target := 176, numerator := 70199402225434647953166827520 }, { target := 177, numerator := 79257389609361699301962547200 }, { target := 178, numerator := 67934905379452885115967897600 }, { target := 179, numerator := 894476254162796320693577318400 }, { target := 180, numerator := 79257389609361699301962547200 }, { target := 181, numerator := 67934905379452885115967897600 }, { target := 182, numerator := 79257389609361699301962547200 }, { target := 183, numerator := 79257389609361699301962547200 }, { target := 184, numerator := 3285784923519537876775647313920 }, { target := 185, numerator := 81521886455343462139161477120 }, { target := 186, numerator := 894476254162796320693577318400 }, { target := 187, numerator := 3285784923519537876775647313920 }, { target := 188, numerator := 70199402225434647953166827520 }, { target := 189, numerator := 79257389609361699301962547200 }, { target := 190, numerator := 81521886455343462139161477120 }, { target := 191, numerator := 79257389609361699301962547200 }, { target := 267, numerator := 2591493008687515019646074880 }, { target := 268, numerator := 37576648625968967784868085760 }, { target := 269, numerator := 66514987222979552170915921920 }, { target := 270, numerator := 2159577507239595849705062400 }, { target := 271, numerator := 41463888139000240314337198080 }, { target := 272, numerator := 2159577507239595849705062400 }, { target := 273, numerator := 66083071721531633000974909440 }, { target := 274, numerator := 69106480231667067190561996800 }, { target := 275, numerator := 41463888139000240314337198080 }, { target := 276, numerator := 1058624894048849885525421588480 }, { target := 277, numerator := 67810733727323309680738959360 }, { target := 278, numerator := 37576648625968967784868085760 }, { target := 279, numerator := 66083071721531633000974909440 }, { target := 280, numerator := 2159577507239595849705062400 }, { target := 281, numerator := 67810733727323309680738959360 }, { target := 282, numerator := 2159577507239595849705062400 }, { target := 283, numerator := 66083071721531633000974909440 }, { target := 284, numerator := 69106480231667067190561996800 }, { target := 285, numerator := 2591493008687515019646074880 }]

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
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 6674640748422548189872128 }, { target := 132, numerator := 139333125623320693463580672 }, { target := 133, numerator := 7230860810791093872361472 }, { target := 134, numerator := 149901306808323061430878208 }, { target := 135, numerator := 224434795165708182884450304 }, { target := 136, numerator := 6952750779606821031116800 }, { target := 137, numerator := 224434795165708182884450304 }, { target := 138, numerator := 233890536225973459486769152 }, { target := 139, numerator := 139333125623320693463580672 }, { target := 140, numerator := 6952750779606821031116800 }, { target := 227, numerator := 1093845068841029188567695360 }, { target := 228, numerator := 22834015812056484311350640640 }, { target := 229, numerator := 1184998824577781620948336640 }, { target := 230, numerator := 24565937171054780526582824960 }, { target := 231, numerator := 36780540439779606465588756480 }, { target := 232, numerator := 1139421946709405404758016000 }, { target := 233, numerator := 36780540439779606465588756480 }, { target := 234, numerator := 38330154287304397816059658240 }, { target := 235, numerator := 22834015812056484311350640640 }, { target := 236, numerator := 1139421946709405404758016000 }, { target := 286, numerator := 70199385069962659403283824640 }, { target := 287, numerator := 79257370240280421906933350400 }, { target := 288, numerator := 67934888777383218777371443200 }, { target := 289, numerator := 894476035568879047235390668800 }, { target := 290, numerator := 79257370240280421906933350400 }, { target := 291, numerator := 67934888777383218777371443200 }, { target := 292, numerator := 79257370240280421906933350400 }, { target := 293, numerator := 79257370240280421906933350400 }, { target := 294, numerator := 3285784120532768348198865469440 }, { target := 295, numerator := 81521866532859862532845731840 }, { target := 296, numerator := 894476035568879047235390668800 }, { target := 297, numerator := 3285784120532768348198865469440 }, { target := 298, numerator := 70199385069962659403283824640 }, { target := 299, numerator := 79257370240280421906933350400 }, { target := 300, numerator := 81521866532859862532845731840 }, { target := 301, numerator := 79257370240280421906933350400 }, { target := 302, numerator := 11261558508049607016012840960 }, { target := 303, numerator := 235085033855535546459268055040 }, { target := 304, numerator := 12200021717053740934013911040 }, { target := 305, numerator := 252915834826614090901288386560 }, { target := 306, numerator := 378669904833168035913431777280 }, { target := 307, numerator := 11730790112551673975013376000 }, { target := 308, numerator := 378669904833168035913431777280 }, { target := 309, numerator := 394623779386238312519449968640 }, { target := 310, numerator := 235085033855535546459268055040 }, { target := 311, numerator := 11730790112551673975013376000 }, { target := 573, numerator := 1755871135764074800286269440 }, { target := 574, numerator := 1982435153282019935807078400 }, { target := 575, numerator := 1699230131384588516406067200 }, { target := 576, numerator := 22373196729897082132679884800 }, { target := 577, numerator := 1982435153282019935807078400 }, { target := 578, numerator := 1699230131384588516406067200 }, { target := 579, numerator := 1982435153282019935807078400 }, { target := 580, numerator := 1982435153282019935807078400 }, { target := 581, numerator := 82186097354634597910173450240 }, { target := 582, numerator := 2039076157661506219687280640 }, { target := 583, numerator := 22373196729897082132679884800 }, { target := 584, numerator := 82186097354634597910173450240 }, { target := 585, numerator := 1755871135764074800286269440 }, { target := 586, numerator := 1982435153282019935807078400 }, { target := 587, numerator := 2039076157661506219687280640 }, { target := 588, numerator := 1982435153282019935807078400 }]

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
    Slot11.Left11.expected,
    Slot11.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left6.expected,
    Slot12.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 263, numerator := 47450990973445802582605824 }, { target := 264, numerator := 51914683375855837181378560 }, { target := 265, numerator := 47450990973445802582605824 }, { target := 266, numerator := 51914683375855837181378560 }, { target := 338, numerator := 9411184621691412860318515200 }, { target := 339, numerator := 10296490332525369898303488000 }, { target := 340, numerator := 9411184621691412860318515200 }, { target := 341, numerator := 10296490332525369898303488000 }, { target := 589, numerator := 1093845068841029188567695360 }, { target := 590, numerator := 22834015812056484311350640640 }, { target := 591, numerator := 1184998824577781620948336640 }, { target := 592, numerator := 24565937171054780526582824960 }, { target := 593, numerator := 36780540439779606465588756480 }, { target := 594, numerator := 1139421946709405404758016000 }, { target := 595, numerator := 36780540439779606465588756480 }, { target := 596, numerator := 38330154287304397816059658240 }, { target := 597, numerator := 22834015812056484311350640640 }, { target := 598, numerator := 1139421946709405404758016000 }, { target := 599, numerator := 9411184621691412860318515200 }, { target := 600, numerator := 10296490332525369898303488000 }, { target := 601, numerator := 9411184621691412860318515200 }, { target := 602, numerator := 10296490332525369898303488000 }, { target := 763, numerator := 6674640748422548189872128 }, { target := 764, numerator := 139333125623320693463580672 }, { target := 765, numerator := 7230860810791093872361472 }, { target := 766, numerator := 149901306808323061430878208 }, { target := 767, numerator := 224434795165708182884450304 }, { target := 768, numerator := 6952750779606821031116800 }, { target := 769, numerator := 224434795165708182884450304 }, { target := 770, numerator := 233890536225973459486769152 }, { target := 771, numerator := 139333125623320693463580672 }, { target := 772, numerator := 6952750779606821031116800 }, { target := 773, numerator := 47450990973445802582605824 }, { target := 774, numerator := 51914683375855837181378560 }, { target := 775, numerator := 47450990973445802582605824 }, { target := 776, numerator := 51914683375855837181378560 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent0
