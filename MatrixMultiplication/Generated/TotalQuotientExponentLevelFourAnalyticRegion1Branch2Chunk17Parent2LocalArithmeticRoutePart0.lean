import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk17Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 72; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17.Parent2

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
    Slot1.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 122, numerator := 27370836134712463658582016 }, { target := 123, numerator := 30657603206789736727314432 }, { target := 124, numerator := 27370836134712463658582016 }, { target := 125, numerator := 30657603206789736727314432 }, { target := 197, numerator := 729888963592332364228853760 }, { target := 198, numerator := 817536085514392979395051520 }, { target := 199, numerator := 729888963592332364228853760 }, { target := 200, numerator := 817536085514392979395051520 }, { target := 211, numerator := 697956321435167823293841408 }, { target := 212, numerator := 781768881773138286546518016 }, { target := 213, numerator := 697956321435167823293841408 }, { target := 214, numerator := 781768881773138286546518016 }, { target := 215, numerator := 676998458984192337835458560 }, { target := 242, numerator := 22809030112260386382151680 }, { target := 243, numerator := 25548002672324780606095360 }, { target := 244, numerator := 22809030112260386382151680 }, { target := 245, numerator := 25548002672324780606095360 }, { target := 256, numerator := 716203545524976132399562752 }, { target := 257, numerator := 802207283910998111031394304 }, { target := 258, numerator := 716203545524976132399562752 }, { target := 259, numerator := 802207283910998111031394304 }, { target := 260, numerator := 696341272098026404630757376 }, { target := 261, numerator := 22809030112260386382151680 }, { target := 262, numerator := 25548002672324780606095360 }, { target := 263, numerator := 22809030112260386382151680 }, { target := 264, numerator := 25548002672324780606095360 }, { target := 265, numerator := 676998458984192337835458560 }, { target := 337, numerator := 697956321435167823293841408 }, { target := 338, numerator := 781768881773138286546518016 }, { target := 339, numerator := 697956321435167823293841408 }, { target := 340, numerator := 781768881773138286546518016 }, { target := 351, numerator := 396877123953330723049439232 }, { target := 352, numerator := 444535246498451182546059264 }, { target := 353, numerator := 396877123953330723049439232 }, { target := 354, numerator := 444535246498451182546059264 }, { target := 355, numerator := 599627206528856070654263296 }, { target := 382, numerator := 716203545524976132399562752 }, { target := 383, numerator := 802207283910998111031394304 }, { target := 384, numerator := 716203545524976132399562752 }, { target := 385, numerator := 802207283910998111031394304 }, { target := 396, numerator := 11180986561030041404530753536 }, { target := 397, numerator := 12523630909973607453107945472 }, { target := 398, numerator := 11180986561030041404530753536 }, { target := 399, numerator := 12523630909973607453107945472 }, { target := 400, numerator := 28066421828173230919978582016 }, { target := 401, numerator := 437933378155399418537312256 }, { target := 402, numerator := 490521651308635787637030912 }, { target := 403, numerator := 437933378155399418537312256 }, { target := 404, numerator := 490521651308635787637030912 }, { target := 405, numerator := 7640411179964456384143032320 }, { target := 416, numerator := 729888963592332364228853760 }, { target := 417, numerator := 817536085514392979395051520 }, { target := 418, numerator := 729888963592332364228853760 }, { target := 419, numerator := 817536085514392979395051520 }, { target := 420, numerator := 696341272098026404630757376 }, { target := 425, numerator := 28066421828173230919978582016 }, { target := 426, numerator := 676998458984192337835458560 }, { target := 471, numerator := 676998458984192337835458560 }, { target := 476, numerator := 580284393415022003858964480 }, { target := 491, numerator := 676998458984192337835458560 }, { target := 496, numerator := 7640411179964456384143032320 }, { target := 497, numerator := 580284393415022003858964480 }, { target := 502, numerator := 676998458984192337835458560 }, { target := 503, numerator := 599627206528856070654263296 }]

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
    Slot1.Left12.expected,
    Slot1.Left13.expected,
    Slot1.Left14.expected,
    Slot1.Left15.expected,
    Slot1.Left16.expected,
    Slot1.Left17.expected,
    Slot1.Left18.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left6.expected,
    Slot2.Left14.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left3.expected,
    Slot3.Left11.expected,
    Slot3.Left18.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 249861943994234055363133440 }, { target := 87, numerator := 4447542603097366185463775232 }, { target := 88, numerator := 249861943994234055363133440 }, { target := 89, numerator := 3956147446575372543249612800 }, { target := 90, numerator := 6754601219310793963316707328 }, { target := 91, numerator := 249861943994234055363133440 }, { target := 92, numerator := 6754601219310793963316707328 }, { target := 93, numerator := 6754601219310793963316707328 }, { target := 94, numerator := 4447542603097366185463775232 }, { target := 95, numerator := 249861943994234055363133440 }, { target := 122, numerator := 1151353088638723895083401216 }, { target := 124, numerator := 1151353088638723895083401216 }, { target := 161, numerator := 8744545081721607720083128320 }, { target := 162, numerator := 155652902454644617417479684096 }, { target := 163, numerator := 8744545081721607720083128320 }, { target := 164, numerator := 138455297127258788901316198400 }, { target := 165, numerator := 236394202042540795366247235584 }, { target := 166, numerator := 8744545081721607720083128320 }, { target := 167, numerator := 236394202042540795366247235584 }, { target := 168, numerator := 236394202042540795366247235584 }, { target := 169, numerator := 155652902454644617417479684096 }, { target := 170, numerator := 8744545081721607720083128320 }, { target := 197, numerator := 120717294801168520544753025024 }, { target := 199, numerator := 120717294801168520544753025024 }, { target := 215, numerator := 3272765255455564570673807360 }, { target := 242, numerator := 1301211781162393678236352512000 }, { target := 244, numerator := 1301211781162393678236352512000 }, { target := 260, numerator := 274025803544469617006730018816 }, { target := 416, numerator := 120717386887314936502834692096 }, { target := 418, numerator := 120717386887314936502834692096 }, { target := 420, numerator := 274025902714165757269279506432 }, { target := 421, numerator := 697956321435167823293841408 }, { target := 422, numerator := 781768881773138286546518016 }, { target := 423, numerator := 697956321435167823293841408 }, { target := 424, numerator := 781768881773138286546518016 }, { target := 453, numerator := 22809030112260386382151680 }, { target := 454, numerator := 25548002672324780606095360 }, { target := 455, numerator := 22809030112260386382151680 }, { target := 456, numerator := 25548002672324780606095360 }, { target := 467, numerator := 437933378155399418537312256 }, { target := 468, numerator := 490521651308635787637030912 }, { target := 469, numerator := 437933378155399418537312256 }, { target := 470, numerator := 490521651308635787637030912 }, { target := 472, numerator := 22809030112260386382151680 }, { target := 473, numerator := 25548002672324780606095360 }, { target := 474, numerator := 22809030112260386382151680 }, { target := 475, numerator := 25548002672324780606095360 }, { target := 487, numerator := 702518127457619900570271744 }, { target := 488, numerator := 786878482307603242667737088 }, { target := 489, numerator := 702518127457619900570271744 }, { target := 490, numerator := 786878482307603242667737088 }, { target := 492, numerator := 396877123953330723049439232 }, { target := 493, numerator := 444535246498451182546059264 }, { target := 494, numerator := 396877123953330723049439232 }, { target := 495, numerator := 444535246498451182546059264 }, { target := 498, numerator := 1178723924773436358741983232 }, { target := 499, numerator := 30657603206789736727314432 }, { target := 500, numerator := 1178723924773436358741983232 }, { target := 501, numerator := 30657603206789736727314432 }, { target := 502, numerator := 3272666085759424308124319744 }]

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
    Slot4.Left5.expected,
    Slot4.Left12.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left6.expected,
    Slot5.Left14.expected,
    Slot6.Left0.expected,
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
  [{ target := 35, numerator := 62589158481793454695545569280 }, { target := 36, numerator := 74324625697129727450960363520 }, { target := 37, numerator := 56721424874125318317838172160 }, { target := 38, numerator := 584817449564257592311503912960 }, { target := 39, numerator := 70412803292017636532488765440 }, { target := 40, numerator := 56721424874125318317838172160 }, { target := 41, numerator := 70412803292017636532488765440 }, { target := 42, numerator := 70412803292017636532488765440 }, { target := 43, numerator := 3016015074341422098141602119680 }, { target := 44, numerator := 70412803292017636532488765440 }, { target := 45, numerator := 584817449564257592311503912960 }, { target := 46, numerator := 3016015074341422098141602119680 }, { target := 47, numerator := 62589158481793454695545569280 }, { target := 48, numerator := 70412803292017636532488765440 }, { target := 49, numerator := 70412803292017636532488765440 }, { target := 50, numerator := 74324625697129727450960363520 }, { target := 86, numerator := 305918687717615673889607647232 }, { target := 89, numerator := 1094403906946984950752486621184 }, { target := 91, numerator := 305918586017716198177020837888 }, { target := 122, numerator := 23313978593174188935916552192 }, { target := 124, numerator := 23313978593174188935916552192 }, { target := 161, numerator := 11086594502330563211093495250944 }, { target := 164, numerator := 39661559836734575290759017136128 }, { target := 166, numerator := 11086590816692543425350620676096 }, { target := 197, numerator := 3443352631623612933968098230272 }, { target := 199, numerator := 3443352631623612933968098230272 }, { target := 215, numerator := 25140197992330089524021428224 }, { target := 232, numerator := 11095343125981363566594857369600 }, { target := 233, numerator := 155652978796494966464459046912 }, { target := 234, numerator := 8744549370589604857553879040 }, { target := 235, numerator := 39800029777237359226036703723520 }, { target := 236, numerator := 236394317984938984649206530048 }, { target := 237, numerator := 11095339440341989323264051118080 }, { target := 238, numerator := 236394317984938984649206530048 }, { target := 239, numerator := 236394317984938984649206530048 }, { target := 240, numerator := 155652978796494966464459046912 }, { target := 241, numerator := 8744549370589604857553879040 }, { target := 242, numerator := 35889488618526300223502475591680 }, { target := 244, numerator := 35889488618526300223502475591680 }, { target := 260, numerator := 2114020189892807025501665230848 }, { target := 406, numerator := 306164473236965158732427165696 }, { target := 407, numerator := 4447504432172191661974093824 }, { target := 408, numerator := 249859799560235486627758080 }, { target := 409, numerator := 1098345444971573487591009288192 }, { target := 410, numerator := 6754543248111699321837060096 }, { target := 411, numerator := 306164371538420140607772033024 }, { target := 412, numerator := 6754543248111699321837060096 }, { target := 413, numerator := 6754543248111699321837060096 }, { target := 414, numerator := 4447504432172191661974093824 }, { target := 415, numerator := 249859799560235486627758080 }, { target := 416, numerator := 3443352631623612933968098230272 }, { target := 418, numerator := 3443352631623612933968098230272 }, { target := 420, numerator := 2114019679877226875579982151680 }, { target := 498, numerator := 23313978593174188935916552192 }, { target := 500, numerator := 23313978593174188935916552192 }, { target := 502, numerator := 25140708007910239445704507392 }]

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
    Slot9.Left10.expected,
    Slot9.Left11.expected,
    Slot9.Left12.expected,
    Slot9.Left13.expected,
    Slot9.Left14.expected,
    Slot9.Left15.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 1731643565684765468554784931840 }, { target := 89, numerator := 6298360921167922001393536204800 }, { target := 91, numerator := 1731643565684765468554784931840 }, { target := 122, numerator := 38717379206106319374296023040 }, { target := 124, numerator := 38717360744225647317152169984 }, { target := 145, numerator := 212160343741679215518920212480 }, { target := 146, numerator := 251940408193244068428717752320 }, { target := 147, numerator := 192270311515896789064021442560 }, { target := 148, numerator := 1982373211836315170004910735360 }, { target := 149, numerator := 238680386709389117458785239040 }, { target := 150, numerator := 192270311515896789064021442560 }, { target := 151, numerator := 238680386709389117458785239040 }, { target := 152, numerator := 238680386709389117458785239040 }, { target := 153, numerator := 10223476564052167197817967738880 }, { target := 154, numerator := 238680386709389117458785239040 }, { target := 155, numerator := 1982373211836315170004910735360 }, { target := 156, numerator := 10223476564052167197817967738880 }, { target := 157, numerator := 212160343741679215518920212480 }, { target := 158, numerator := 238680386709389117458785239040 }, { target := 159, numerator := 238680386709389117458785239040 }, { target := 160, numerator := 251940408193244068428717752320 }, { target := 161, numerator := 65062297228939694644940117114880 }, { target := 164, numerator := 236645599838624422184934283673600 }, { target := 166, numerator := 65062297228939694644940117114880 }, { target := 197, numerator := 6181120912992382991774022369280 }, { target := 199, numerator := 6181117965604955042503288946688 }, { target := 215, numerator := 47003035866616782312576122880 }, { target := 216, numerator := 62589158481793454695545569280 }, { target := 217, numerator := 74324625697129727450960363520 }, { target := 218, numerator := 56721424874125318317838172160 }, { target := 219, numerator := 584817449564257592311503912960 }, { target := 220, numerator := 70412803292017636532488765440 }, { target := 221, numerator := 56721424874125318317838172160 }, { target := 222, numerator := 70412803292017636532488765440 }, { target := 223, numerator := 70412803292017636532488765440 }, { target := 224, numerator := 3016015074341422098141602119680 }, { target := 225, numerator := 70412803292017636532488765440 }, { target := 226, numerator := 584817449564257592311503912960 }, { target := 227, numerator := 3016015074341422098141602119680 }, { target := 228, numerator := 62589158481793454695545569280 }, { target := 229, numerator := 70412803292017636532488765440 }, { target := 230, numerator := 70412803292017636532488765440 }, { target := 231, numerator := 74324625697129727450960363520 }, { target := 242, numerator := 61678291536567586098592067092480 }, { target := 244, numerator := 61678262126073338986097339793408 }, { target := 260, numerator := 36557916785146386243114762240 }, { target := 265, numerator := 41780476325881584277845442560 }, { target := 355, numerator := 49092059682910861526468395008 }, { target := 400, numerator := 579704109021606981855105515520 }, { target := 405, numerator := 1303550861367505429468777807872 }, { target := 416, numerator := 6181120912992382991774022369280 }, { target := 418, numerator := 6181117965604955042503288946688 }, { target := 420, numerator := 36557916785146386243114762240 }, { target := 425, numerator := 579704109021606981855105515520 }, { target := 426, numerator := 41780476325881584277845442560 }, { target := 471, numerator := 40735964417734544670899306496 }, { target := 476, numerator := 40735964417734544670899306496 }, { target := 491, numerator := 40735964417734544670899306496 }, { target := 496, numerator := 1303550861367505429468777807872 }, { target := 497, numerator := 40735964417734544670899306496 }, { target := 498, numerator := 38712961431208315458347335680 }, { target := 500, numerator := 38712942971434202126906032128 }, { target := 502, numerator := 47003035866616782312576122880 }, { target := 503, numerator := 49092059682910861526468395008 }]

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
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left2.expected,
    Slot14.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 21905735851417080645675909120 }, { target := 17, numerator := 368016362303806954847355273216 }, { target := 18, numerator := 797368784991581735502603091968 }, { target := 19, numerator := 26286883021700496774811090944 }, { target := 20, numerator := 420590128347207948396977455104 }, { target := 21, numerator := 30668030191983912903946272768 }, { target := 22, numerator := 797368784991581735502603091968 }, { target := 23, numerator := 797368784991581735502603091968 }, { target := 24, numerator := 420590128347207948396977455104 }, { target := 25, numerator := 9840056544456552626037618376704 }, { target := 26, numerator := 788606490651014903244332728320 }, { target := 27, numerator := 368016362303806954847355273216 }, { target := 28, numerator := 797368784991581735502603091968 }, { target := 29, numerator := 30668030191983912903946272768 }, { target := 30, numerator := 788606490651014903244332728320 }, { target := 31, numerator := 30668030191983912903946272768 }, { target := 32, numerator := 797368784991581735502603091968 }, { target := 33, numerator := 797368784991581735502603091968 }, { target := 34, numerator := 26286883021700496774811090944 }, { target := 35, numerator := 943541061296292423469293895680 }, { target := 37, numerator := 34843716114780576716071265894400 }, { target := 40, numerator := 34843707582433570853628023930880 }, { target := 47, numerator := 943549593643298285912535859200 }, { target := 122, numerator := 22050806949770836146640650240 }, { target := 124, numerator := 22050806949770836146640650240 }, { target := 126, numerator := 21905735851417080645675909120 }, { target := 127, numerator := 368016362303806954847355273216 }, { target := 128, numerator := 797368784991581735502603091968 }, { target := 129, numerator := 26286883021700496774811090944 }, { target := 130, numerator := 420590128347207948396977455104 }, { target := 131, numerator := 30668030191983912903946272768 }, { target := 132, numerator := 797368784991581735502603091968 }, { target := 133, numerator := 797368784991581735502603091968 }, { target := 134, numerator := 420590128347207948396977455104 }, { target := 135, numerator := 9840056544456552626037618376704 }, { target := 136, numerator := 788606490651014903244332728320 }, { target := 137, numerator := 368016362303806954847355273216 }, { target := 138, numerator := 797368784991581735502603091968 }, { target := 139, numerator := 30668030191983912903946272768 }, { target := 140, numerator := 788606490651014903244332728320 }, { target := 141, numerator := 30668030191983912903946272768 }, { target := 142, numerator := 797368784991581735502603091968 }, { target := 143, numerator := 797368784991581735502603091968 }, { target := 144, numerator := 26286883021700496774811090944 }, { target := 145, numerator := 3239011484597918756453706891264 }, { target := 147, numerator := 119612384973253027419022027653120 }, { target := 150, numerator := 119612355683197643295471093940224 }, { target := 157, numerator := 3239040774653302880004640604160 }, { target := 197, numerator := 370453556756150047263562924032 }, { target := 199, numerator := 370453556756150047263562924032 }, { target := 211, numerator := 802649372971658435737719668736 }, { target := 213, numerator := 802649372971658435737719668736 }, { target := 216, numerator := 943541061296292423469293895680 }, { target := 218, numerator := 34843716114780576716071265894400 }, { target := 221, numerator := 34843707582433570853628023930880 }, { target := 228, numerator := 943549593643298285912535859200 }, { target := 232, numerator := 65057376429754528534382782709760 }, { target := 235, numerator := 236627701831261394651795632947200 }, { target := 237, numerator := 65057376429754528534382782709760 }, { target := 242, numerator := 26460968339725003375968780288 }, { target := 244, numerator := 26460968339725003375968780288 }, { target := 406, numerator := 1736564364869931579112119336960 }, { target := 409, numerator := 6316258928530949534532186931200 }, { target := 411, numerator := 1736564364869931579112119336960 }]

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
    Slot14.Left4.expected,
    Slot14.Left5.expected,
    Slot14.Left6.expected,
    Slot14.Left7.expected,
    Slot14.Left8.expected,
    Slot14.Left9.expected,
    Slot14.Left10.expected,
    Slot14.Left11.expected,
    Slot14.Left12.expected,
    Slot14.Left13.expected,
    Slot14.Left14.expected,
    Slot14.Left15.expected,
    Slot14.Left16.expected,
    Slot14.Left17.expected,
    Slot14.Left18.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 38779459450691203905628405760 }, { target := 17, numerator := 6191031849784995043604766392320 }, { target := 19, numerator := 61777187781682339042630429573120 }, { target := 27, numerator := 6191031849784995043604766392320 }, { target := 34, numerator := 38775034592241786835351633920 }, { target := 35, numerator := 1731825748069371966762944299008 }, { target := 37, numerator := 65069142289142634118337796243456 }, { target := 40, numerator := 65064220972251083455848788262912 }, { target := 47, numerator := 1736747064960922629251952279552 }, { target := 86, numerator := 947001480836498874900110376960 }, { target := 89, numerator := 3250890499822605500059282833408 }, { target := 91, numerator := 947001480836498874900110376960 }, { target := 126, numerator := 38779440959208371497778282496 }, { target := 127, numerator := 6191028897671665285756901916672 }, { target := 129, numerator := 61777158324030698695855913828352 }, { target := 137, numerator := 6191028897671665285756901916672 }, { target := 144, numerator := 38775016102868890852924588032 }, { target := 145, numerator := 6299023557771937563939711221760 }, { target := 147, numerator := 236670496798102446847973203640320 }, { target := 150, numerator := 236652596907729702005257158000640 }, { target := 157, numerator := 6316923448144682406655756861440 }, { target := 161, numerator := 34971504804688084943636319436800 }, { target := 164, numerator := 120051061201761290355766607216640 }, { target := 166, numerator := 34971504804688084943636319436800 }, { target := 216, numerator := 1731825748069371966762944299008 }, { target := 218, numerator := 65069142289142634118337796243456 }, { target := 221, numerator := 65064220972251083455848788262912 }, { target := 228, numerator := 1736747064960922629251952279552 }, { target := 232, numerator := 34971496241048852898323481231360 }, { target := 235, numerator := 120051031804285165214647638294528 }, { target := 237, numerator := 34971496241048852898323481231360 }, { target := 256, numerator := 423375493435600054015500484608 }, { target := 258, numerator := 423375493435600054015500484608 }, { target := 261, numerator := 30871129729679170605296910336 }, { target := 263, numerator := 30871129729679170605296910336 }, { target := 337, numerator := 802649372971658435737719668736 }, { target := 339, numerator := 802649372971658435737719668736 }, { target := 351, numerator := 802649372971658435737719668736 }, { target := 353, numerator := 802649372971658435737719668736 }, { target := 382, numerator := 423375493435600054015500484608 }, { target := 384, numerator := 423375493435600054015500484608 }, { target := 396, numerator := 9905222481837059597070980087808 }, { target := 398, numerator := 9905222481837059597070980087808 }, { target := 401, numerator := 793829050191750101279063408640 }, { target := 403, numerator := 793829050191750101279063408640 }, { target := 406, numerator := 947010044475730920212948582400 }, { target := 409, numerator := 3250919897298730641178251755520 }, { target := 411, numerator := 947010044475730920212948582400 }, { target := 416, numerator := 370453556756150047263562924032 }, { target := 418, numerator := 370453556756150047263562924032 }, { target := 421, numerator := 802649372971658435737719668736 }, { target := 423, numerator := 802649372971658435737719668736 }, { target := 453, numerator := 30871129729679170605296910336 }, { target := 455, numerator := 30871129729679170605296910336 }, { target := 467, numerator := 793829050191750101279063408640 }, { target := 469, numerator := 793829050191750101279063408640 }, { target := 472, numerator := 30871129729679170605296910336 }, { target := 474, numerator := 30871129729679170605296910336 }, { target := 487, numerator := 802649372971658435737719668736 }, { target := 489, numerator := 802649372971658435737719668736 }, { target := 492, numerator := 802649372971658435737719668736 }, { target := 494, numerator := 802649372971658435737719668736 }, { target := 498, numerator := 26460968339725003375968780288 }, { target := 500, numerator := 26460968339725003375968780288 }]

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
    Slot18.Left0.expected,
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left2.expected,
    Slot19.Left3.expected,
    Slot19.Left4.expected,
    Slot19.Left5.expected,
    Slot19.Left6.expected,
    Slot19.Left7.expected,
    Slot19.Left8.expected,
    Slot19.Left9.expected,
    Slot19.Left10.expected,
    Slot19.Left11.expected,
    Slot19.Left12.expected,
    Slot19.Left13.expected,
    Slot19.Left14.expected,
    Slot19.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 45262182686371716300999229440 }, { target := 1, numerator := 35203919867178001567443845120 }, { target := 2, numerator := 40233051276774858934221537280 }, { target := 3, numerator := 47273835250210459247710306304 }, { target := 4, numerator := 558233586465251167712323829760 }, { target := 5, numerator := 1255271199835375598747711963136 }, { target := 6, numerator := 35203919867178001567443845120 }, { target := 7, numerator := 558233586465251167712323829760 }, { target := 8, numerator := 40233051276774858934221537280 }, { target := 9, numerator := 39227224994855487460865998848 }, { target := 10, numerator := 39227224994855487460865998848 }, { target := 11, numerator := 39227224994855487460865998848 }, { target := 12, numerator := 1255271199835375598747711963136 }, { target := 13, numerator := 39227224994855487460865998848 }, { target := 14, numerator := 45262182686371716300999229440 }, { target := 15, numerator := 47273835250210459247710306304 }, { target := 86, numerator := 63048528452302030509824802816 }, { target := 89, numerator := 213717483879232824440159993856 }, { target := 91, numerator := 63048528452302030509824802816 }, { target := 112, numerator := 74870127537108661230416953344 }, { target := 115, numerator := 253789512106588979022689992704 }, { target := 117, numerator := 74870127537108661230416953344 }, { target := 161, numerator := 57137728909898715149528727552 }, { target := 164, numerator := 193681469765554747148894994432 }, { target := 166, numerator := 57137728909898715149528727552 }, { target := 187, numerator := 589109687726197097576175501312 }, { target := 190, numerator := 1996922739996581703362744942592 }, { target := 192, numerator := 589109687726197097576175501312 }, { target := 201, numerator := 70929594508839784323552903168 }, { target := 204, numerator := 240432169364136927495179993088 }, { target := 206, numerator := 70929594508839784323552903168 }, { target := 232, numerator := 57137728909898715149528727552 }, { target := 235, numerator := 193681469765554747148894994432 }, { target := 237, numerator := 57137728909898715149528727552 }, { target := 246, numerator := 70929594508839784323552903168 }, { target := 249, numerator := 240432169364136927495179993088 }, { target := 251, numerator := 70929594508839784323552903168 }, { target := 301, numerator := 70929594508839784323552903168 }, { target := 304, numerator := 240432169364136927495179993088 }, { target := 306, numerator := 70929594508839784323552903168 }, { target := 327, numerator := 3038150964795304095192182685696 }, { target := 330, numerator := 10298511254430531727710209703936 }, { target := 332, numerator := 3038150964795304095192182685696 }, { target := 341, numerator := 70929594508839784323552903168 }, { target := 344, numerator := 240432169364136927495179993088 }, { target := 346, numerator := 70929594508839784323552903168 }, { target := 372, numerator := 589109687726197097576175501312 }, { target := 375, numerator := 1996922739996581703362744942592 }, { target := 377, numerator := 589109687726197097576175501312 }, { target := 386, numerator := 3038150964795304095192182685696 }, { target := 389, numerator := 10298511254430531727710209703936 }, { target := 391, numerator := 3038150964795304095192182685696 }, { target := 406, numerator := 63048528452302030509824802816 }, { target := 409, numerator := 213717483879232824440159993856 }, { target := 411, numerator := 63048528452302030509824802816 }, { target := 443, numerator := 70929594508839784323552903168 }, { target := 446, numerator := 240432169364136927495179993088 }, { target := 448, numerator := 70929594508839784323552903168 }, { target := 457, numerator := 70929594508839784323552903168 }, { target := 460, numerator := 240432169364136927495179993088 }, { target := 462, numerator := 70929594508839784323552903168 }, { target := 477, numerator := 74870127537108661230416953344 }, { target := 480, numerator := 253789512106588979022689992704 }, { target := 482, numerator := 74870127537108661230416953344 }]

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
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected,
    Slot22.Left0.expected,
    Slot23.Left0.expected,
    Slot23.Left1.expected,
    Slot23.Left2.expected,
    Slot23.Left3.expected,
    Slot23.Left4.expected,
    Slot23.Left5.expected,
    Slot23.Left6.expected,
    Slot23.Left7.expected,
    Slot23.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 25140197992330089524021428224 }, { target := 1, numerator := 2114020189892807025501665230848 }, { target := 6, numerator := 2114019679877226875579982151680 }, { target := 14, numerator := 25140708007910239445704507392 }, { target := 16, numerator := 23335545640901454605607501824 }, { target := 17, numerator := 3446537971708371132796930883584 }, { target := 19, numerator := 35922688885518461463302200360960 }, { target := 27, numerator := 3446537971708371132796930883584 }, { target := 34, numerator := 23335545640901454605607501824 }, { target := 35, numerator := 304825432981678901737528754176 }, { target := 37, numerator := 11046674071599461762028317704192 }, { target := 40, numerator := 11046678132249665318748977889280 }, { target := 47, numerator := 304821374406734053309193125888 }, { target := 70, numerator := 4304073486868418889158492160 }, { target := 72, numerator := 150631841085139952339496468480 }, { target := 75, numerator := 150631914964349967546250690560 }, { target := 82, numerator := 4304036547263411285781381120 }, { target := 96, numerator := 241801881284742634222387200 }, { target := 98, numerator := 8462462982311233277499801600 }, { target := 101, numerator := 8462467132828649862148915200 }, { target := 108, numerator := 241799806026034341897830400 }, { target := 126, numerator := 23335545640901454605607501824 }, { target := 127, numerator := 3446537971708371132796930883584 }, { target := 129, numerator := 35922688885518461463302200360960 }, { target := 137, numerator := 3446537971708371132796930883584 }, { target := 144, numerator := 23335545640901454605607501824 }, { target := 145, numerator := 1093456359833351920273600806912 }, { target := 147, numerator := 39622462226188205129143632789504 }, { target := 150, numerator := 39622476803764526586545527848960 }, { target := 157, numerator := 1093441815115293344166844563456 }, { target := 171, numerator := 6536710857397542545145200640 }, { target := 173, numerator := 228768582621813672935077969920 }, { target := 176, numerator := 228768694824134501273425674240 }, { target := 183, numerator := 6536654756237128375971348480 }, { target := 216, numerator := 304825331725606917502490640384 }, { target := 218, numerator := 11046670402045897174851652681728 }, { target := 221, numerator := 11046674462694752184958892113920 }, { target := 228, numerator := 304821273152010615687575764992 }, { target := 285, numerator := 6536710857397542545145200640 }, { target := 287, numerator := 228768582621813672935077969920 }, { target := 290, numerator := 228768694824134501273425674240 }, { target := 297, numerator := 6536654756237128375971348480 }, { target := 311, numerator := 6536710857397542545145200640 }, { target := 313, numerator := 228768582621813672935077969920 }, { target := 316, numerator := 228768694824134501273425674240 }, { target := 323, numerator := 6536654756237128375971348480 }, { target := 356, numerator := 4304073486868418889158492160 }, { target := 358, numerator := 150631841085139952339496468480 }, { target := 361, numerator := 150631914964349967546250690560 }, { target := 368, numerator := 4304036547263411285781381120 }]

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
    Slot23.Left9.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected,
    Slot25.Left0.expected,
    Slot26.Left0.expected,
    Slot26.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 3272765255455564570673807360 }, { target := 1, numerator := 274025803544469617006730018816 }, { target := 6, numerator := 274025902714165757269279506432 }, { target := 14, numerator := 3272666085759424308124319744 }, { target := 16, numerator := 1178723924773436358741983232 }, { target := 17, numerator := 121447183764760852908981878784 }, { target := 18, numerator := 697956321435167823293841408 }, { target := 19, numerator := 1301234590192505938622734663680 }, { target := 20, numerator := 716203545524976132399562752 }, { target := 21, numerator := 22809030112260386382151680 }, { target := 22, numerator := 697956321435167823293841408 }, { target := 23, numerator := 396877123953330723049439232 }, { target := 24, numerator := 716203545524976132399562752 }, { target := 25, numerator := 11180986561030041404530753536 }, { target := 26, numerator := 437933378155399418537312256 }, { target := 27, numerator := 121447275850907268867063545856 }, { target := 28, numerator := 697956321435167823293841408 }, { target := 29, numerator := 22809030112260386382151680 }, { target := 30, numerator := 437933378155399418537312256 }, { target := 31, numerator := 22809030112260386382151680 }, { target := 32, numerator := 702518127457619900570271744 }, { target := 33, numerator := 396877123953330723049439232 }, { target := 34, numerator := 1178723924773436358741983232 }, { target := 51, numerator := 30657603206789736727314432 }, { target := 52, numerator := 817536085514392979395051520 }, { target := 53, numerator := 781768881773138286546518016 }, { target := 54, numerator := 25548002672324780606095360 }, { target := 55, numerator := 802207283910998111031394304 }, { target := 56, numerator := 25548002672324780606095360 }, { target := 57, numerator := 781768881773138286546518016 }, { target := 58, numerator := 444535246498451182546059264 }, { target := 59, numerator := 802207283910998111031394304 }, { target := 60, numerator := 12523630909973607453107945472 }, { target := 61, numerator := 490521651308635787637030912 }, { target := 62, numerator := 817536085514392979395051520 }, { target := 63, numerator := 781768881773138286546518016 }, { target := 64, numerator := 25548002672324780606095360 }, { target := 65, numerator := 490521651308635787637030912 }, { target := 66, numerator := 25548002672324780606095360 }, { target := 67, numerator := 786878482307603242667737088 }, { target := 68, numerator := 444535246498451182546059264 }, { target := 69, numerator := 30657603206789736727314432 }, { target := 126, numerator := 1151353088638723895083401216 }, { target := 127, numerator := 120717294801168520544753025024 }, { target := 129, numerator := 1301211781162393678236352512000 }, { target := 137, numerator := 120717386887314936502834692096 }, { target := 144, numerator := 1151353088638723895083401216 }, { target := 427, numerator := 241801881284742634222387200 }, { target := 429, numerator := 8462462982311233277499801600 }, { target := 432, numerator := 8462467132828649862148915200 }, { target := 439, numerator := 241799806026034341897830400 }]

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
    Slot26.Left2.expected,
    Slot26.Left3.expected,
    Slot27.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 676998458984192337835458560 }, { target := 1, numerator := 696341272098026404630757376 }, { target := 2, numerator := 676998458984192337835458560 }, { target := 3, numerator := 599627206528856070654263296 }, { target := 4, numerator := 28066421828173230919978582016 }, { target := 5, numerator := 7640411179964456384143032320 }, { target := 6, numerator := 696341272098026404630757376 }, { target := 7, numerator := 28066421828173230919978582016 }, { target := 8, numerator := 676998458984192337835458560 }, { target := 9, numerator := 676998458984192337835458560 }, { target := 10, numerator := 580284393415022003858964480 }, { target := 11, numerator := 676998458984192337835458560 }, { target := 12, numerator := 7640411179964456384143032320 }, { target := 13, numerator := 580284393415022003858964480 }, { target := 14, numerator := 676998458984192337835458560 }, { target := 15, numerator := 599627206528856070654263296 }, { target := 126, numerator := 27370836134712463658582016 }, { target := 127, numerator := 729888963592332364228853760 }, { target := 128, numerator := 697956321435167823293841408 }, { target := 129, numerator := 22809030112260386382151680 }, { target := 130, numerator := 716203545524976132399562752 }, { target := 131, numerator := 22809030112260386382151680 }, { target := 132, numerator := 697956321435167823293841408 }, { target := 133, numerator := 396877123953330723049439232 }, { target := 134, numerator := 716203545524976132399562752 }, { target := 135, numerator := 11180986561030041404530753536 }, { target := 136, numerator := 437933378155399418537312256 }, { target := 137, numerator := 729888963592332364228853760 }, { target := 138, numerator := 697956321435167823293841408 }, { target := 139, numerator := 22809030112260386382151680 }, { target := 140, numerator := 437933378155399418537312256 }, { target := 141, numerator := 22809030112260386382151680 }, { target := 142, numerator := 702518127457619900570271744 }, { target := 143, numerator := 396877123953330723049439232 }, { target := 144, numerator := 27370836134712463658582016 }, { target := 266, numerator := 30657603206789736727314432 }, { target := 267, numerator := 817536085514392979395051520 }, { target := 268, numerator := 781768881773138286546518016 }, { target := 269, numerator := 25548002672324780606095360 }, { target := 270, numerator := 802207283910998111031394304 }, { target := 271, numerator := 25548002672324780606095360 }, { target := 272, numerator := 781768881773138286546518016 }, { target := 273, numerator := 444535246498451182546059264 }, { target := 274, numerator := 802207283910998111031394304 }, { target := 275, numerator := 12523630909973607453107945472 }, { target := 276, numerator := 490521651308635787637030912 }, { target := 277, numerator := 817536085514392979395051520 }, { target := 278, numerator := 781768881773138286546518016 }, { target := 279, numerator := 25548002672324780606095360 }, { target := 280, numerator := 490521651308635787637030912 }, { target := 281, numerator := 25548002672324780606095360 }, { target := 282, numerator := 786878482307603242667737088 }, { target := 283, numerator := 444535246498451182546059264 }, { target := 284, numerator := 30657603206789736727314432 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17.Parent2
