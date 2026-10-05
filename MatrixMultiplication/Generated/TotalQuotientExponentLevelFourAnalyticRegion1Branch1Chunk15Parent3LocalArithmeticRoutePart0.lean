import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk15Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 65; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15.Parent3

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
    Slot0.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 6346860552976803167207424 }, { target := 132, numerator := 126937211059536063344148480 }, { target := 133, numerator := 6573534144154546137464832 }, { target := 134, numerator := 118096941003604087504109568 }, { target := 135, numerator := 176805401118639516800778240 }, { target := 136, numerator := 6346860552976803167207424 }, { target := 137, numerator := 177032074709817259771035648 }, { target := 138, numerator := 177032074709817259771035648 }, { target := 139, numerator := 126710537468358320373891072 }, { target := 140, numerator := 6573534144154546137464832 }, { target := 227, numerator := 92029478018163645924507648 }, { target := 228, numerator := 1840589560363272918490152960 }, { target := 229, numerator := 95316245090240918993240064 }, { target := 230, numerator := 1712405644552259268809588736 }, { target := 231, numerator := 2563678316220272993611284480 }, { target := 232, numerator := 92029478018163645924507648 }, { target := 233, numerator := 2566965083292350266680016896 }, { target := 234, numerator := 2566965083292350266680016896 }, { target := 235, numerator := 1837302793291195645421420544 }, { target := 236, numerator := 95316245090240918993240064 }, { target := 253, numerator := 162902754193071281291657216 }, { target := 254, numerator := 3258055083861425625833144320 }, { target := 255, numerator := 168720709699966684194930688 }, { target := 256, numerator := 3031154819092504912605478912 }, { target := 257, numerator := 4538005295378414264553308160 }, { target := 258, numerator := 162902754193071281291657216 }, { target := 259, numerator := 4543823250885309667456581632 }, { target := 260, numerator := 4543823250885309667456581632 }, { target := 261, numerator := 3252237128354530222929870848 }, { target := 262, numerator := 168720709699966684194930688 }, { target := 302, numerator := 5289050460814002639339520 }, { target := 303, numerator := 105781009216280052786790400 }, { target := 304, numerator := 5477945120128788447887360 }, { target := 305, numerator := 98414117503003406253424640 }, { target := 306, numerator := 147337834265532930667315200 }, { target := 307, numerator := 5289050460814002639339520 }, { target := 308, numerator := 147526728924847716475863040 }, { target := 309, numerator := 147526728924847716475863040 }, { target := 310, numerator := 105592114556965266978242560 }, { target := 311, numerator := 5477945120128788447887360 }, { target := 328, numerator := 101549768847628850675318784 }, { target := 329, numerator := 2030995376952577013506375680 }, { target := 330, numerator := 105176546306472738199437312 }, { target := 331, numerator := 1889551056057665400065753088 }, { target := 332, numerator := 2828886417898232268812451840 }, { target := 333, numerator := 101549768847628850675318784 }, { target := 334, numerator := 2832513195357076156336570368 }, { target := 335, numerator := 2832513195357076156336570368 }, { target := 336, numerator := 2027368599493733125982257152 }, { target := 337, numerator := 105176546306472738199437312 }, { target := 342, numerator := 5289050460814002639339520 }, { target := 343, numerator := 105781009216280052786790400 }, { target := 344, numerator := 5477945120128788447887360 }, { target := 345, numerator := 98414117503003406253424640 }, { target := 346, numerator := 147337834265532930667315200 }, { target := 347, numerator := 5289050460814002639339520 }, { target := 348, numerator := 147526728924847716475863040 }, { target := 349, numerator := 147526728924847716475863040 }, { target := 350, numerator := 105592114556965266978242560 }, { target := 351, numerator := 5477945120128788447887360 }]

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
    Slot0.Left6.expected,
    Slot0.Left7.expected,
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 443, numerator := 161844944100908480763789312 }, { target := 444, numerator := 3236898882018169615275786240 }, { target := 445, numerator := 167625120675940926505353216 }, { target := 446, numerator := 3011471995591904231354793984 }, { target := 447, numerator := 4508537728525307678419845120 }, { target := 448, numerator := 161844944100908480763789312 }, { target := 449, numerator := 4514317905100340124161409024 }, { target := 450, numerator := 4514317905100340124161409024 }, { target := 451, numerator := 3231118705443137169534222336 }, { target := 452, numerator := 167625120675940926505353216 }, { target := 469, numerator := 169249614746048084458864640 }, { target := 470, numerator := 3384992294920961689177292800 }, { target := 471, numerator := 175294243844121230332395520 }, { target := 472, numerator := 3149251760096109000109588480 }, { target := 473, numerator := 4714810696497053781354086400 }, { target := 474, numerator := 169249614746048084458864640 }, { target := 475, numerator := 4720855325595126927227617280 }, { target := 476, numerator := 4720855325595126927227617280 }, { target := 477, numerator := 3378947665822888543303761920 }, { target := 478, numerator := 175294243844121230332395520 }, { target := 518, numerator := 101549768847628850675318784 }, { target := 519, numerator := 2030995376952577013506375680 }, { target := 520, numerator := 105176546306472738199437312 }, { target := 521, numerator := 1889551056057665400065753088 }, { target := 522, numerator := 2828886417898232268812451840 }, { target := 523, numerator := 101549768847628850675318784 }, { target := 524, numerator := 2832513195357076156336570368 }, { target := 525, numerator := 2832513195357076156336570368 }, { target := 526, numerator := 2027368599493733125982257152 }, { target := 527, numerator := 105176546306472738199437312 }, { target := 544, numerator := 2592692535891024093804232704 }, { target := 545, numerator := 51853850717820481876084654080 }, { target := 546, numerator := 2685288697887132097154383872 }, { target := 547, numerator := 48242600399972269745428758528 }, { target := 548, numerator := 72225006356964242613117911040 }, { target := 549, numerator := 2592692535891024093804232704 }, { target := 550, numerator := 72317602518960350616468062208 }, { target := 551, numerator := 72317602518960350616468062208 }, { target := 552, numerator := 51761254555824373872734502912 }, { target := 553, numerator := 2685288697887132097154383872 }, { target := 558, numerator := 166076184469559682875260928 }, { target := 559, numerator := 3321523689391193657505218560 }, { target := 560, numerator := 172007476772043957263663104 }, { target := 561, numerator := 3090203289594306956357533696 }, { target := 562, numerator := 4626407995937734022953697280 }, { target := 563, numerator := 166076184469559682875260928 }, { target := 564, numerator := 4632339288240218297342099456 }, { target := 565, numerator := 4632339288240218297342099456 }, { target := 566, numerator := 3315592397088709383116816384 }, { target := 567, numerator := 172007476772043957263663104 }, { target := 589, numerator := 92029478018163645924507648 }, { target := 590, numerator := 1840589560363272918490152960 }, { target := 591, numerator := 95316245090240918993240064 }, { target := 592, numerator := 1712405644552259268809588736 }, { target := 593, numerator := 2563678316220272993611284480 }, { target := 594, numerator := 92029478018163645924507648 }, { target := 595, numerator := 2566965083292350266680016896 }, { target := 596, numerator := 2566965083292350266680016896 }, { target := 597, numerator := 1837302793291195645421420544 }, { target := 598, numerator := 95316245090240918993240064 }]

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
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected,
    Slot0.Left15.expected,
    Slot0.Left16.expected,
    Slot0.Left17.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 603, numerator := 161844944100908480763789312 }, { target := 604, numerator := 3236898882018169615275786240 }, { target := 605, numerator := 167625120675940926505353216 }, { target := 606, numerator := 3011471995591904231354793984 }, { target := 607, numerator := 4508537728525307678419845120 }, { target := 608, numerator := 161844944100908480763789312 }, { target := 609, numerator := 4514317905100340124161409024 }, { target := 610, numerator := 4514317905100340124161409024 }, { target := 611, numerator := 3231118705443137169534222336 }, { target := 612, numerator := 167625120675940926505353216 }, { target := 658, numerator := 5289050460814002639339520 }, { target := 659, numerator := 105781009216280052786790400 }, { target := 660, numerator := 5477945120128788447887360 }, { target := 661, numerator := 98414117503003406253424640 }, { target := 662, numerator := 147337834265532930667315200 }, { target := 663, numerator := 5289050460814002639339520 }, { target := 664, numerator := 147526728924847716475863040 }, { target := 665, numerator := 147526728924847716475863040 }, { target := 666, numerator := 105592114556965266978242560 }, { target := 667, numerator := 5477945120128788447887360 }, { target := 684, numerator := 166076184469559682875260928 }, { target := 685, numerator := 3321523689391193657505218560 }, { target := 686, numerator := 172007476772043957263663104 }, { target := 687, numerator := 3090203289594306956357533696 }, { target := 688, numerator := 4626407995937734022953697280 }, { target := 689, numerator := 166076184469559682875260928 }, { target := 690, numerator := 4632339288240218297342099456 }, { target := 691, numerator := 4632339288240218297342099456 }, { target := 692, numerator := 3315592397088709383116816384 }, { target := 693, numerator := 172007476772043957263663104 }, { target := 698, numerator := 5289050460814002639339520 }, { target := 699, numerator := 105781009216280052786790400 }, { target := 700, numerator := 5477945120128788447887360 }, { target := 701, numerator := 98414117503003406253424640 }, { target := 702, numerator := 147337834265532930667315200 }, { target := 703, numerator := 5289050460814002639339520 }, { target := 704, numerator := 147526728924847716475863040 }, { target := 705, numerator := 147526728924847716475863040 }, { target := 706, numerator := 105592114556965266978242560 }, { target := 707, numerator := 5477945120128788447887360 }, { target := 729, numerator := 161844944100908480763789312 }, { target := 730, numerator := 3236898882018169615275786240 }, { target := 731, numerator := 167625120675940926505353216 }, { target := 732, numerator := 3011471995591904231354793984 }, { target := 733, numerator := 4508537728525307678419845120 }, { target := 734, numerator := 161844944100908480763789312 }, { target := 735, numerator := 4514317905100340124161409024 }, { target := 736, numerator := 4514317905100340124161409024 }, { target := 737, numerator := 3231118705443137169534222336 }, { target := 738, numerator := 167625120675940926505353216 }, { target := 743, numerator := 169249614746048084458864640 }, { target := 744, numerator := 3384992294920961689177292800 }, { target := 745, numerator := 175294243844121230332395520 }, { target := 746, numerator := 3149251760096109000109588480 }, { target := 747, numerator := 4714810696497053781354086400 }, { target := 748, numerator := 169249614746048084458864640 }, { target := 749, numerator := 4720855325595126927227617280 }, { target := 750, numerator := 4720855325595126927227617280 }, { target := 751, numerator := 3378947665822888543303761920 }, { target := 752, numerator := 175294243844121230332395520 }]

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
    Slot0.Left18.expected,
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
    Slot3.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 3406956413426099975394164736 }, { target := 81, numerator := 3880144804179724971976687616 }, { target := 82, numerator := 3028405700823199978128146432 }, { target := 83, numerator := 40599563926661024706780463104 }, { target := 84, numerator := 3596231769727549974027173888 }, { target := 85, numerator := 3028405700823199978128146432 }, { target := 86, numerator := 3596231769727549974027173888 }, { target := 87, numerator := 3501594091576824974710669312 }, { target := 88, numerator := 132303474054713549044473397248 }, { target := 89, numerator := 3501594091576824974710669312 }, { target := 90, numerator := 40599563926661024706780463104 }, { target := 91, numerator := 132303474054713549044473397248 }, { target := 92, numerator := 3406956413426099975394164736 }, { target := 93, numerator := 3501594091576824974710669312 }, { target := 94, numerator := 3501594091576824974710669312 }, { target := 95, numerator := 3880144804179724971976687616 }, { target := 263, numerator := 1363668324525301709068566528 }, { target := 265, numerator := 1363668324525301709068566528 }, { target := 338, numerator := 1015497688476288506753187840 }, { target := 340, numerator := 1015497688476288506753187840 }, { target := 352, numerator := 1073526127817790707139084288 }, { target := 354, numerator := 1073526127817790707139084288 }, { target := 479, numerator := 1392682544196052809261514752 }, { target := 481, numerator := 1392682544196052809261514752 }, { target := 554, numerator := 18656143248292957424065708032 }, { target := 556, numerator := 18656143248292957424065708032 }, { target := 568, numerator := 33743537477083529524398784512 }, { target := 570, numerator := 33743537477083529524398784512 }, { target := 599, numerator := 1015497688476288506753187840 }, { target := 601, numerator := 1015497688476288506753187840 }, { target := 613, numerator := 18656143248292957424065708032 }, { target := 615, numerator := 18656143248292957424065708032 }, { target := 618, numerator := 1102540347488541807332032512 }, { target := 620, numerator := 1102540347488541807332032512 }, { target := 694, numerator := 1102540347488541807332032512 }, { target := 696, numerator := 1102540347488541807332032512 }, { target := 708, numerator := 1073526127817790707139084288 }, { target := 710, numerator := 1073526127817790707139084288 }, { target := 739, numerator := 1073526127817790707139084288 }, { target := 741, numerator := 1073526127817790707139084288 }, { target := 753, numerator := 33743537477083529524398784512 }, { target := 755, numerator := 33743537477083529524398784512 }, { target := 758, numerator := 1073526127817790707139084288 }, { target := 760, numerator := 1073526127817790707139084288 }, { target := 763, numerator := 6346860552976803167207424 }, { target := 764, numerator := 126937211059536063344148480 }, { target := 765, numerator := 6573534144154546137464832 }, { target := 766, numerator := 118096941003604087504109568 }, { target := 767, numerator := 176805401118639516800778240 }, { target := 768, numerator := 6346860552976803167207424 }, { target := 769, numerator := 177032074709817259771035648 }, { target := 770, numerator := 177032074709817259771035648 }, { target := 771, numerator := 126710537468358320373891072 }, { target := 772, numerator := 6573534144154546137464832 }, { target := 773, numerator := 1363668324525301709068566528 }, { target := 775, numerator := 1363668324525301709068566528 }, { target := 778, numerator := 1392682544196052809261514752 }, { target := 780, numerator := 1392682544196052809261514752 }]

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
  [{ target := 131, numerator := 4628186814423926721466073088 }, { target := 134, numerator := 16904537103867310958129971200 }, { target := 136, numerator := 4628185255112228439494492160 }, { target := 176, numerator := 136209485285803034657515634688 }, { target := 177, numerator := 155127469353275678359948361728 }, { target := 178, numerator := 121075098031824919695569453056 }, { target := 179, numerator := 1623163032989152829668727980032 }, { target := 180, numerator := 143776678912792092138488725504 }, { target := 181, numerator := 121075098031824919695569453056 }, { target := 182, numerator := 143776678912792092138488725504 }, { target := 183, numerator := 139993082099297563398002180096 }, { target := 184, numerator := 5289468345265351179200190480384 }, { target := 185, numerator := 139993082099297563398002180096 }, { target := 186, numerator := 1623163032989152829668727980032 }, { target := 187, numerator := 5289468345265351179200190480384 }, { target := 188, numerator := 136209485285803034657515634688 }, { target := 189, numerator := 139993082099297563398002180096 }, { target := 190, numerator := 139993082099297563398002180096 }, { target := 191, numerator := 155127469353275678359948361728 }, { target := 227, numerator := 758470682610016824913884610560 }, { target := 230, numerator := 2770328059450320221890412544000 }, { target := 232, numerator := 758470427068860942483927859200 }, { target := 286, numerator := 136209451998653353648629743616 }, { target := 287, numerator := 155127431442910763877606096896 }, { target := 288, numerator := 121075068443247425465448660992 }, { target := 289, numerator := 1623162636317285797646171111424 }, { target := 290, numerator := 143776643776356317740220284928 }, { target := 291, numerator := 121075068443247425465448660992 }, { target := 292, numerator := 143776643776356317740220284928 }, { target := 293, numerator := 139993047887504835694425014272 }, { target := 294, numerator := 5289467052614371900021788377088 }, { target := 295, numerator := 139993047887504835694425014272 }, { target := 296, numerator := 1623162636317285797646171111424 }, { target := 297, numerator := 5289467052614371900021788377088 }, { target := 298, numerator := 136209451998653353648629743616 }, { target := 299, numerator := 139993047887504835694425014272 }, { target := 300, numerator := 139993047887504835694425014272 }, { target := 301, numerator := 155127431442910763877606096896 }, { target := 302, numerator := 7808749348665200508536000348160 }, { target := 305, numerator := 28521600011459587339173494784000 }, { target := 307, numerator := 7808746717770058078776144691200 }, { target := 573, numerator := 3406956413426099975394164736 }, { target := 574, numerator := 3880144804179724971976687616 }, { target := 575, numerator := 3028405700823199978128146432 }, { target := 576, numerator := 40599563926661024706780463104 }, { target := 577, numerator := 3596231769727549974027173888 }, { target := 578, numerator := 3028405700823199978128146432 }, { target := 579, numerator := 3596231769727549974027173888 }, { target := 580, numerator := 3501594091576824974710669312 }, { target := 581, numerator := 132303474054713549044473397248 }, { target := 582, numerator := 3501594091576824974710669312 }, { target := 583, numerator := 40599563926661024706780463104 }, { target := 584, numerator := 132303474054713549044473397248 }, { target := 585, numerator := 3406956413426099975394164736 }, { target := 586, numerator := 3501594091576824974710669312 }, { target := 587, numerator := 3501594091576824974710669312 }, { target := 588, numerator := 3880144804179724971976687616 }, { target := 589, numerator := 758470682610016824913884610560 }, { target := 592, numerator := 2770328059450320221890412544000 }, { target := 594, numerator := 758470427068860942483927859200 }, { target := 763, numerator := 4628186814423926721466073088 }, { target := 766, numerator := 16904537103867310958129971200 }, { target := 768, numerator := 4628185255112228439494492160 }]

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
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left6.expected,
    Slot5.Left14.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left7.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 18869396860827192806086803456 }, { target := 27, numerator := 283040952912407892091302051840 }, { target := 28, numerator := 496894117335116077226952491008 }, { target := 29, numerator := 18869396860827192806086803456 }, { target := 30, numerator := 314489947680453213434780057600 }, { target := 31, numerator := 18869396860827192806086803456 }, { target := 32, numerator := 496894117335116077226952491008 }, { target := 33, numerator := 493749217858311545092604690432 }, { target := 34, numerator := 314489947680453213434780057600 }, { target := 35, numerator := 7620091432297381361524720795648 }, { target := 36, numerator := 487459418904702480823909089280 }, { target := 37, numerator := 283040952912407892091302051840 }, { target := 38, numerator := 496894117335116077226952491008 }, { target := 39, numerator := 18869396860827192806086803456 }, { target := 40, numerator := 487459418904702480823909089280 }, { target := 41, numerator := 18869396860827192806086803456 }, { target := 42, numerator := 496894117335116077226952491008 }, { target := 43, numerator := 496894117335116077226952491008 }, { target := 44, numerator := 18869396860827192806086803456 }, { target := 157, numerator := 67635368707933863645284401152 }, { target := 158, numerator := 1014530530619007954679266017280 }, { target := 159, numerator := 1781064709308925075992489230336 }, { target := 160, numerator := 67635368707933863645284401152 }, { target := 161, numerator := 1127256145132231060754740019200 }, { target := 162, numerator := 67635368707933863645284401152 }, { target := 163, numerator := 1781064709308925075992489230336 }, { target := 164, numerator := 1769792147857602765384941830144 }, { target := 165, numerator := 1127256145132231060754740019200 }, { target := 166, numerator := 27313416396553958602087350665216 }, { target := 167, numerator := 1747247024954958144169847029760 }, { target := 168, numerator := 1014530530619007954679266017280 }, { target := 169, numerator := 1781064709308925075992489230336 }, { target := 170, numerator := 67635368707933863645284401152 }, { target := 171, numerator := 1747247024954958144169847029760 }, { target := 172, numerator := 67635368707933863645284401152 }, { target := 173, numerator := 1781064709308925075992489230336 }, { target := 174, numerator := 1781064709308925075992489230336 }, { target := 175, numerator := 67635368707933863645284401152 }, { target := 263, numerator := 11128954200446901823138168832 }, { target := 265, numerator := 11128956853796665483994333184 }, { target := 338, numerator := 2207259331746431510095960473600 }, { target := 340, numerator := 2207259857998127827835368243200 }, { target := 356, numerator := 5035312987322933732362420224 }, { target := 599, numerator := 2207259331746431510095960473600 }, { target := 601, numerator := 2207259857998127827835368243200 }, { target := 617, numerator := 227586986580493134164995866624 }, { target := 773, numerator := 11128954200446901823138168832 }, { target := 775, numerator := 11128956853796665483994333184 }, { target := 777, numerator := 5062187974976944883273564160 }]

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
    Slot7.Left5.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left6.expected,
    Slot10.Left14.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left2.expected,
    Slot11.Left3.expected,
    Slot11.Left4.expected,
    Slot11.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 86720389747946428069199216640 }, { target := 82, numerator := 3382562121438398638716711075840 }, { target := 85, numerator := 3382560880726436314684776775680 }, { target := 92, numerator := 86720803318600536079843983360 }, { target := 131, numerator := 17909346247176959157411512320 }, { target := 134, numerator := 64419385864337650051144744960 }, { target := 136, numerator := 17909352221832368812206325760 }, { target := 176, numerator := 3393897660823201235293343580160 }, { target := 178, numerator := 132380282248567716137709558824960 }, { target := 181, numerator := 132380233691942925523109197905920 }, { target := 188, numerator := 3393913846364798106826797219840 }, { target := 227, numerator := 5768982955941366401982309335040 }, { target := 230, numerator := 20750860134950744875940834181120 }, { target := 232, numerator := 5768984880505487850832889118720 }, { target := 263, numerator := 42558215018829082608021798912 }, { target := 265, numerator := 42558204872161138297091915776 }, { target := 267, numerator := 18874880275406939449416744960 }, { target := 268, numerator := 283123204131104091741251174400 }, { target := 269, numerator := 497038513919049405501307617280 }, { target := 270, numerator := 18874880275406939449416744960 }, { target := 271, numerator := 314581337923448990823612416000 }, { target := 272, numerator := 18874880275406939449416744960 }, { target := 273, numerator := 497038513919049405501307617280 }, { target := 274, numerator := 493892700539814915593071493120 }, { target := 275, numerator := 314581337923448990823612416000 }, { target := 276, numerator := 7622305817885169047656128839680 }, { target := 277, numerator := 487601073781345935776599244800 }, { target := 278, numerator := 283123204131104091741251174400 }, { target := 279, numerator := 497038513919049405501307617280 }, { target := 280, numerator := 18874880275406939449416744960 }, { target := 281, numerator := 487601073781345935776599244800 }, { target := 282, numerator := 18874880275406939449416744960 }, { target := 283, numerator := 497038513919049405501307617280 }, { target := 284, numerator := 497038513919049405501307617280 }, { target := 285, numerator := 18874880275406939449416744960 }, { target := 286, numerator := 3393898905589661417104620912640 }, { target := 288, numerator := 132380330801161754123565887651840 }, { target := 291, numerator := 132380282244519154587189043527680 }, { target := 298, numerator := 3393915091137194595896902287360 }, { target := 302, numerator := 61355559757344332039670634381312 }, { target := 305, numerator := 220694123860262066620313670516736 }, { target := 307, numerator := 61355580225893097430751972950016 }, { target := 338, numerator := 7464311078096165408178035490816 }, { target := 340, numerator := 7464309298465936344893429383168 }, { target := 356, numerator := 4797017652230848565234106368 }, { target := 572, numerator := 116211621187915073306155286528 }, { target := 573, numerator := 86721634514406609880476549120 }, { target := 575, numerator := 3382610674032436624573039902720 }, { target := 578, numerator := 3382609433302665378764622397440 }, { target := 585, numerator := 86722048090997025149949050880 }, { target := 589, numerator := 5769000343656169486408675753984 }, { target := 592, numerator := 20750922678043817048416611991552 }, { target := 594, numerator := 5769002268226091571579308736512 }, { target := 599, numerator := 7464311972984720590991976824832 }, { target := 601, numerator := 7464310193354278169675024039936 }, { target := 617, numerator := 88048485294172672052200210432 }, { target := 622, numerator := 98106748113366386785755594752 }, { target := 712, numerator := 4797017652230848565234106368 }, { target := 757, numerator := 98106748113366386785755594752 }, { target := 763, numerator := 17909346247176959157411512320 }, { target := 766, numerator := 64419385864337650051144744960 }, { target := 768, numerator := 17909352221832368812206325760 }, { target := 773, numerator := 42557320130273899794080464896 }, { target := 775, numerator := 42557309983819313515497259008 }]

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
    Slot11.Left6.expected,
    Slot11.Left7.expected,
    Slot11.Left8.expected,
    Slot11.Left9.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 85417852528088510280367079424 }, { target := 11, numerator := 64063389396066382710275309568 }, { target := 12, numerator := 67622466584736737305290604544 }, { target := 13, numerator := 87197391122423687577874726912 }, { target := 14, numerator := 1167377317883876307165016752128 }, { target := 15, numerator := 2041130767702448360241271668736 }, { target := 16, numerator := 62283850801731205412767662080 }, { target := 17, numerator := 1167377317883876307165016752128 }, { target := 18, numerator := 65842927990401560007782957056 }, { target := 19, numerator := 67622466584736737305290604544 }, { target := 20, numerator := 67622466584736737305290604544 }, { target := 21, numerator := 65842927990401560007782957056 }, { target := 22, numerator := 2041130767702448360241271668736 }, { target := 23, numerator := 65842927990401560007782957056 }, { target := 24, numerator := 85417852528088510280367079424 }, { target := 25, numerator := 87197391122423687577874726912 }, { target := 26, numerator := 44528224495408130919147503616 }, { target := 27, numerator := 5262950253760286119717100322816 }, { target := 29, numerator := 49944348809355077547583315378176 }, { target := 37, numerator := 5262953863376409288339905052672 }, { target := 44, numerator := 44528224495408130919147503616 }, { target := 80, numerator := 194084563248903371589314150400 }, { target := 82, numerator := 7595491629020637866347116625920 }, { target := 85, numerator := 7595491629020637866347116625920 }, { target := 92, numerator := 194084563248903371589314150400 }, { target := 141, numerator := 85417872893293967655712063488 }, { target := 142, numerator := 64063404669970475741784047616 }, { target := 143, numerator := 67622482707191057727438716928 }, { target := 144, numerator := 87197411911904258648539398144 }, { target := 145, numerator := 1167377596208350891294731534336 }, { target := 146, numerator := 2041131254346003768772952850432 }, { target := 147, numerator := 62283865651360184748956712960 }, { target := 148, numerator := 1167377596208350891294731534336 }, { target := 149, numerator := 65842943688580766734611382272 }, { target := 150, numerator := 67622482707191057727438716928 }, { target := 151, numerator := 67622482707191057727438716928 }, { target := 152, numerator := 65842943688580766734611382272 }, { target := 153, numerator := 2041131254346003768772952850432 }, { target := 154, numerator := 65842943688580766734611382272 }, { target := 155, numerator := 85417872893293967655712063488 }, { target := 156, numerator := 87197411911904258648539398144 }, { target := 157, numerator := 165411257442443447786180444160 }, { target := 158, numerator := 19550548650806620852494438236160 }, { target := 160, numerator := 185530809555439602337345972469760 }, { target := 168, numerator := 19550562059630991997391308062720 }, { target := 175, numerator := 165411257442443447786180444160 }, { target := 176, numerator := 7595491629020637866347116625920 }, { target := 178, numerator := 297249261459996897039840880623616 }, { target := 181, numerator := 297249261459996897039840880623616 }, { target := 188, numerator := 7595491629020637866347116625920 }, { target := 267, numerator := 44518851352094413874352095232 }, { target := 268, numerator := 5261842408398373121571403333632 }, { target := 270, numerator := 49933835577704697376335149924352 }, { target := 278, numerator := 5261846017254675982662022201344 }, { target := 285, numerator := 44518851352094413874352095232 }, { target := 286, numerator := 7595491629020637866347116625920 }, { target := 288, numerator := 297249261459996897039840880623616 }, { target := 291, numerator := 297249261459996897039840880623616 }, { target := 298, numerator := 7595491629020637866347116625920 }, { target := 762, numerator := 97952005608455714251393204224 }, { target := 777, numerator := 4797017652230848565234106368 }, { target := 782, numerator := 116211621187915073306155286528 }, { target := 783, numerator := 4797017652230848565234106368 }]

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
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left2.expected,
    Slot16.Left3.expected,
    Slot16.Left4.expected,
    Slot16.Left5.expected,
    Slot16.Left6.expected,
    Slot16.Left7.expected,
    Slot16.Left8.expected,
    Slot16.Left9.expected,
    Slot16.Left10.expected,
    Slot16.Left11.expected,
    Slot16.Left12.expected,
    Slot16.Left13.expected,
    Slot16.Left14.expected,
    Slot16.Left15.expected,
    Slot17.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 4797017652230848565234106368 }, { target := 1, numerator := 116211621187915073306155286528 }, { target := 2, numerator := 88048485294172672052200210432 }, { target := 3, numerator := 98106748113366386785755594752 }, { target := 4, numerator := 4797017652230848565234106368 }, { target := 5, numerator := 98106748113366386785755594752 }, { target := 6, numerator := 97952005608455714251393204224 }, { target := 7, numerator := 4797017652230848565234106368 }, { target := 8, numerator := 116211621187915073306155286528 }, { target := 9, numerator := 4797017652230848565234106368 }, { target := 131, numerator := 44487447733049698564825939968 }, { target := 134, numerator := 165259781931965019720442183680 }, { target := 136, numerator := 44478083173200554520987303936 }, { target := 227, numerator := 5258130702245853623270472941568 }, { target := 230, numerator := 19532645217976211859039772999680 }, { target := 232, numerator := 5257023871394345307357510107136 }, { target := 263, numerator := 87274762365655651808201146368 }, { target := 265, numerator := 87274783173582966952575369216 }, { target := 302, numerator := 49898612226196327476569044942848 }, { target := 305, numerator := 185360909546689199771102981652480 }, { target := 307, numerator := 49888108622047458642474037149696 }, { target := 338, numerator := 65456071774241738856150859776 }, { target := 340, numerator := 65456087380187225214431526912 }, { target := 352, numerator := 69092520206144057681492574208 }, { target := 354, numerator := 69092536679086515504122167296 }, { target := 479, numerator := 89092986581606811220872003584 }, { target := 481, numerator := 89093007823032612097420689408 }, { target := 554, numerator := 1192755085663960574712082333696 }, { target := 556, numerator := 1192755370038967215018530045952 }, { target := 568, numerator := 2085503175695979846333473226752 }, { target := 570, numerator := 2085503672918742981137582260224 }, { target := 573, numerator := 194084563248903371589314150400 }, { target := 575, numerator := 7595491629020637866347116625920 }, { target := 578, numerator := 7595491629020637866347116625920 }, { target := 585, numerator := 194084563248903371589314150400 }, { target := 589, numerator := 5258134308556467521592341037056 }, { target := 592, numerator := 19532658614521439806917506498560 }, { target := 594, numerator := 5257027476945834704289621082112 }, { target := 599, numerator := 63637847558290579443480002560 }, { target := 601, numerator := 63637862730737580069586206720 }, { target := 613, numerator := 1192755085663960574712082333696 }, { target := 615, numerator := 1192755370038967215018530045952 }, { target := 618, numerator := 67274295990192898268821716992 }, { target := 620, numerator := 67274312029636870359276847104 }, { target := 694, numerator := 69092520206144057681492574208 }, { target := 696, numerator := 69092536679086515504122167296 }, { target := 708, numerator := 69092520206144057681492574208 }, { target := 710, numerator := 69092536679086515504122167296 }, { target := 739, numerator := 67274295990192898268821716992 }, { target := 741, numerator := 67274312029636870359276847104 }, { target := 753, numerator := 2085503175695979846333473226752 }, { target := 755, numerator := 2085503672918742981137582260224 }, { target := 758, numerator := 67274295990192898268821716992 }, { target := 760, numerator := 67274312029636870359276847104 }, { target := 763, numerator := 44487447733049698564825939968 }, { target := 766, numerator := 165259781931965019720442183680 }, { target := 768, numerator := 44478083173200554520987303936 }, { target := 773, numerator := 87274762365655651808201146368 }, { target := 775, numerator := 87274783173582966952575369216 }, { target := 778, numerator := 89092986581606811220872003584 }, { target := 780, numerator := 89093007823032612097420689408 }]

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
    Slot21.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 43344250652422231891019563008 }, { target := 11, numerator := 7602174343390817539727497887744 }, { target := 16, numerator := 7602175254807657382910034444288 }, { target := 24, numerator := 43343339235582388708483006464 }, { target := 26, numerator := 17926727212090756672121733120 }, { target := 27, numerator := 5774581735984011361611562352640 }, { target := 29, numerator := 61415105137543618076199817838592 }, { target := 37, numerator := 5774599140573537663317069266944 }, { target := 44, numerator := 17926727212090756672121733120 }, { target := 80, numerator := 86671046709683016161336229888 }, { target := 82, numerator := 3391966566848337393907685916672 }, { target := 85, numerator := 3391967810906537854420635353088 }, { target := 92, numerator := 86672290767883476674285666304 }, { target := 131, numerator := 18869396860827192806086803456 }, { target := 134, numerator := 67635368707933863645284401152 }, { target := 136, numerator := 18874880275406939449416744960 }, { target := 141, numerator := 43344240318348811036088336384 }, { target := 142, numerator := 7602172530891428572899376627712 }, { target := 147, numerator := 7602173442308051117399892557824 }, { target := 155, numerator := 43343328901726266535572406272 }, { target := 157, numerator := 64481904678258785192886927360 }, { target := 158, numerator := 20770998780268049558467950673920 }, { target := 160, numerator := 220908306822082973129067856920576 }, { target := 168, numerator := 20771061384058999324278817554432 }, { target := 175, numerator := 64481904678258785192886927360 }, { target := 176, numerator := 3380637477272573091838351638528 }, { target := 178, numerator := 132304959186121873909466196344832 }, { target := 181, numerator := 132305007711089969341703261257728 }, { target := 188, numerator := 3380686002240668524075416551424 }, { target := 227, numerator := 283040952912407892091302051840 }, { target := 230, numerator := 1014530530619007954679266017280 }, { target := 232, numerator := 283123204131104091741251174400 }, { target := 253, numerator := 496894117335116077226952491008 }, { target := 256, numerator := 1781064709308925075992489230336 }, { target := 258, numerator := 497038513919049405501307617280 }, { target := 267, numerator := 17926733192544550847156060160 }, { target := 268, numerator := 5774583662415916313421042155520 }, { target := 270, numerator := 61415125625957046477171569197056 }, { target := 278, numerator := 5774601067011248880946136481792 }, { target := 285, numerator := 17926733192544550847156060160 }, { target := 286, numerator := 3380636237266563520195624697856 }, { target := 288, numerator := 132304910657125319306595337764864 }, { target := 291, numerator := 132304959182075615950155081056256 }, { target := 298, numerator := 3380684762216860163755367989248 }, { target := 302, numerator := 18869396860827192806086803456 }, { target := 305, numerator := 67635368707933863645284401152 }, { target := 307, numerator := 18874880275406939449416744960 }, { target := 328, numerator := 314489947680453213434780057600 }, { target := 331, numerator := 1127256145132231060754740019200 }, { target := 333, numerator := 314581337923448990823612416000 }, { target := 342, numerator := 18869396860827192806086803456 }, { target := 345, numerator := 67635368707933863645284401152 }, { target := 347, numerator := 18874880275406939449416744960 }, { target := 443, numerator := 496894117335116077226952491008 }, { target := 446, numerator := 1781064709308925075992489230336 }, { target := 448, numerator := 497038513919049405501307617280 }, { target := 469, numerator := 493749217858311545092604690432 }, { target := 472, numerator := 1769792147857602765384941830144 }, { target := 474, numerator := 493892700539814915593071493120 }, { target := 573, numerator := 86671460045019540042245210112 }, { target := 575, numerator := 3391982743180522261531305443328 }, { target := 578, numerator := 3391983987244655651603362086912 }, { target := 585, numerator := 86672704109152930114301853696 }]

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
    Slot23.Left0.expected,
    Slot23.Left2.expected,
    Slot24.Left0.expected,
    Slot24.Left3.expected,
    Slot24.Left5.expected,
    Slot25.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 5035312987322933732362420224 }, { target := 2, numerator := 227586986580493134164995866624 }, { target := 7, numerator := 5062187974976944883273564160 }, { target := 10, numerator := 11526416850462862602535960576 }, { target := 11, numerator := 2286090022165946921170816204800 }, { target := 16, numerator := 2286090022165946921170816204800 }, { target := 24, numerator := 11526416850462862602535960576 }, { target := 26, numerator := 4537846831559796019695714304 }, { target := 27, numerator := 743665699315827307310460436480 }, { target := 29, numerator := 7656326313330894792903916257280 }, { target := 37, numerator := 743665699315827307310460436480 }, { target := 44, numerator := 4537846831559796019695714304 }, { target := 80, numerator := 3279514153572255836663709696 }, { target := 82, numerator := 131114367382344068273818042368 }, { target := 85, numerator := 131114335340349612240326885376 }, { target := 92, numerator := 3279514153572255836663709696 }, { target := 141, numerator := 11526419598575117822708416512 }, { target := 142, numerator := 2286090567212346678829488537600 }, { target := 147, numerator := 2286090567212346678829488537600 }, { target := 155, numerator := 11526419598575117822708416512 }, { target := 157, numerator := 16574568661899931014502809600 }, { target := 158, numerator := 2716252586818407064406065152000 }, { target := 160, numerator := 27964872083307973772492931072000 }, { target := 168, numerator := 2716252586818407064406065152000 }, { target := 175, numerator := 16574568661899931014502809600 }, { target := 267, numerator := 4537845302685112869354209280 }, { target := 268, numerator := 743665448762712005168175513600 }, { target := 270, numerator := 7656323733789561449610844569600 }, { target := 278, numerator := 743665448762712005168175513600 }, { target := 285, numerator := 4537845302685112869354209280 }, { target := 518, numerator := 314489947680453213434780057600 }, { target := 521, numerator := 1127256145132231060754740019200 }, { target := 523, numerator := 314581337923448990823612416000 }, { target := 544, numerator := 7620091432297381361524720795648 }, { target := 547, numerator := 27313416396553958602087350665216 }, { target := 549, numerator := 7622305817885169047656128839680 }, { target := 558, numerator := 487459418904702480823909089280 }, { target := 561, numerator := 1747247024954958144169847029760 }, { target := 563, numerator := 487601073781345935776599244800 }, { target := 589, numerator := 283040952912407892091302051840 }, { target := 592, numerator := 1014530530619007954679266017280 }, { target := 594, numerator := 283123204131104091741251174400 }, { target := 603, numerator := 496894117335116077226952491008 }, { target := 606, numerator := 1781064709308925075992489230336 }, { target := 608, numerator := 497038513919049405501307617280 }, { target := 658, numerator := 18869396860827192806086803456 }, { target := 661, numerator := 67635368707933863645284401152 }, { target := 663, numerator := 18874880275406939449416744960 }, { target := 684, numerator := 487459418904702480823909089280 }, { target := 687, numerator := 1747247024954958144169847029760 }, { target := 689, numerator := 487601073781345935776599244800 }, { target := 698, numerator := 18869396860827192806086803456 }, { target := 701, numerator := 67635368707933863645284401152 }, { target := 703, numerator := 18874880275406939449416744960 }, { target := 729, numerator := 496894117335116077226952491008 }, { target := 732, numerator := 1781064709308925075992489230336 }, { target := 734, numerator := 497038513919049405501307617280 }, { target := 743, numerator := 496894117335116077226952491008 }, { target := 746, numerator := 1781064709308925075992489230336 }, { target := 748, numerator := 497038513919049405501307617280 }, { target := 763, numerator := 18869396860827192806086803456 }, { target := 766, numerator := 67635368707933863645284401152 }, { target := 768, numerator := 18874880275406939449416744960 }]

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
  [{ target := 115, numerator := 3735002230457291369533669376 }, { target := 117, numerator := 149324696185447411089626103808 }, { target := 120, numerator := 149324659693175947273705619456 }, { target := 127, numerator := 3735002230457291369533669376 }, { target := 176, numerator := 2915123692064227410367741952 }, { target := 178, numerator := 116546104339861394021171593216 }, { target := 181, numerator := 116546075858088544213623898112 }, { target := 188, numerator := 2915123692064227410367741952 }, { target := 211, numerator := 39080876996736048720242540544 }, { target := 213, numerator := 1562446211306266813596331671552 }, { target := 216, numerator := 1562445829472499545863895384064 }, { target := 223, numerator := 39080876996736048720242540544 }, { target := 237, numerator := 3461709384326270049811693568 }, { target := 239, numerator := 138398498903585405400141266944 }, { target := 242, numerator := 138398465081480146253678379008 }, { target := 249, numerator := 3461709384326270049811693568 }, { target := 286, numerator := 2915123692064227410367741952 }, { target := 288, numerator := 116546104339861394021171593216 }, { target := 291, numerator := 116546075858088544213623898112 }, { target := 298, numerator := 2915123692064227410367741952 }, { target := 312, numerator := 3461709384326270049811693568 }, { target := 314, numerator := 138398498903585405400141266944 }, { target := 317, numerator := 138398465081480146253678379008 }, { target := 324, numerator := 3461709384326270049811693568 }, { target := 392, numerator := 3370611768949262943237701632 }, { target := 394, numerator := 134756433142964736836979654656 }, { target := 397, numerator := 134756400210914879247002632192 }, { target := 404, numerator := 3370611768949262943237701632 }, { target := 427, numerator := 127354466297055934990440726528 }, { target := 429, numerator := 5091607933347694651299933978624 }, { target := 432, numerator := 5091606689050243275332694048768 }, { target := 439, numerator := 127354466297055934990440726528 }, { target := 453, numerator := 3370611768949262943237701632 }, { target := 455, numerator := 134756433142964736836979654656 }, { target := 458, numerator := 134756400210914879247002632192 }, { target := 465, numerator := 3370611768949262943237701632 }, { target := 502, numerator := 39080876996736048720242540544 }, { target := 504, numerator := 1562446211306266813596331671552 }, { target := 507, numerator := 1562445829472499545863895384064 }, { target := 514, numerator := 39080876996736048720242540544 }, { target := 528, numerator := 127354466297055934990440726528 }, { target := 530, numerator := 5091607933347694651299933978624 }, { target := 533, numerator := 5091606689050243275332694048768 }, { target := 540, numerator := 127354466297055934990440726528 }, { target := 573, numerator := 3279514153572255836663709696 }, { target := 575, numerator := 131114367382344068273818042368 }, { target := 578, numerator := 131114335340349612240326885376 }, { target := 585, numerator := 3279514153572255836663709696 }, { target := 642, numerator := 3370611768949262943237701632 }, { target := 644, numerator := 134756433142964736836979654656 }, { target := 647, numerator := 134756400210914879247002632192 }, { target := 654, numerator := 3370611768949262943237701632 }, { target := 668, numerator := 3370611768949262943237701632 }, { target := 670, numerator := 134756433142964736836979654656 }, { target := 673, numerator := 134756400210914879247002632192 }, { target := 680, numerator := 3370611768949262943237701632 }, { target := 713, numerator := 3735002230457291369533669376 }, { target := 715, numerator := 149324696185447411089626103808 }, { target := 718, numerator := 149324659693175947273705619456 }, { target := 725, numerator := 3735002230457291369533669376 }]

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
    Slot27.Left0.expected,
    Slot27.Left2.expected,
    Slot28.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 1363668324525301709068566528 }, { target := 11, numerator := 1015497688476288506753187840 }, { target := 12, numerator := 1073526127817790707139084288 }, { target := 13, numerator := 1392682544196052809261514752 }, { target := 14, numerator := 18656143248292957424065708032 }, { target := 15, numerator := 33743537477083529524398784512 }, { target := 16, numerator := 1015497688476288506753187840 }, { target := 17, numerator := 18656143248292957424065708032 }, { target := 18, numerator := 1102540347488541807332032512 }, { target := 19, numerator := 1102540347488541807332032512 }, { target := 20, numerator := 1073526127817790707139084288 }, { target := 21, numerator := 1073526127817790707139084288 }, { target := 22, numerator := 33743537477083529524398784512 }, { target := 23, numerator := 1073526127817790707139084288 }, { target := 24, numerator := 1363668324525301709068566528 }, { target := 25, numerator := 1392682544196052809261514752 }, { target := 26, numerator := 6346860552976803167207424 }, { target := 27, numerator := 92029478018163645924507648 }, { target := 28, numerator := 162902754193071281291657216 }, { target := 29, numerator := 5289050460814002639339520 }, { target := 30, numerator := 101549768847628850675318784 }, { target := 31, numerator := 5289050460814002639339520 }, { target := 32, numerator := 161844944100908480763789312 }, { target := 33, numerator := 169249614746048084458864640 }, { target := 34, numerator := 101549768847628850675318784 }, { target := 35, numerator := 2592692535891024093804232704 }, { target := 36, numerator := 166076184469559682875260928 }, { target := 37, numerator := 92029478018163645924507648 }, { target := 38, numerator := 161844944100908480763789312 }, { target := 39, numerator := 5289050460814002639339520 }, { target := 40, numerator := 166076184469559682875260928 }, { target := 41, numerator := 5289050460814002639339520 }, { target := 42, numerator := 161844944100908480763789312 }, { target := 43, numerator := 169249614746048084458864640 }, { target := 44, numerator := 6346860552976803167207424 }, { target := 141, numerator := 1363668324525301709068566528 }, { target := 142, numerator := 1015497688476288506753187840 }, { target := 143, numerator := 1073526127817790707139084288 }, { target := 144, numerator := 1392682544196052809261514752 }, { target := 145, numerator := 18656143248292957424065708032 }, { target := 146, numerator := 33743537477083529524398784512 }, { target := 147, numerator := 1015497688476288506753187840 }, { target := 148, numerator := 18656143248292957424065708032 }, { target := 149, numerator := 1102540347488541807332032512 }, { target := 150, numerator := 1102540347488541807332032512 }, { target := 151, numerator := 1073526127817790707139084288 }, { target := 152, numerator := 1073526127817790707139084288 }, { target := 153, numerator := 33743537477083529524398784512 }, { target := 154, numerator := 1073526127817790707139084288 }, { target := 155, numerator := 1363668324525301709068566528 }, { target := 156, numerator := 1392682544196052809261514752 }]

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
    Slot28.Left1.expected,
    Slot28.Left2.expected,
    Slot28.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 61, numerator := 126937211059536063344148480 }, { target := 62, numerator := 1840589560363272918490152960 }, { target := 63, numerator := 3258055083861425625833144320 }, { target := 64, numerator := 105781009216280052786790400 }, { target := 65, numerator := 2030995376952577013506375680 }, { target := 66, numerator := 105781009216280052786790400 }, { target := 67, numerator := 3236898882018169615275786240 }, { target := 68, numerator := 3384992294920961689177292800 }, { target := 69, numerator := 2030995376952577013506375680 }, { target := 70, numerator := 51853850717820481876084654080 }, { target := 71, numerator := 3321523689391193657505218560 }, { target := 72, numerator := 1840589560363272918490152960 }, { target := 73, numerator := 3236898882018169615275786240 }, { target := 74, numerator := 105781009216280052786790400 }, { target := 75, numerator := 3321523689391193657505218560 }, { target := 76, numerator := 105781009216280052786790400 }, { target := 77, numerator := 3236898882018169615275786240 }, { target := 78, numerator := 3384992294920961689177292800 }, { target := 79, numerator := 126937211059536063344148480 }, { target := 96, numerator := 6573534144154546137464832 }, { target := 97, numerator := 95316245090240918993240064 }, { target := 98, numerator := 168720709699966684194930688 }, { target := 99, numerator := 5477945120128788447887360 }, { target := 100, numerator := 105176546306472738199437312 }, { target := 101, numerator := 5477945120128788447887360 }, { target := 102, numerator := 167625120675940926505353216 }, { target := 103, numerator := 175294243844121230332395520 }, { target := 104, numerator := 105176546306472738199437312 }, { target := 105, numerator := 2685288697887132097154383872 }, { target := 106, numerator := 172007476772043957263663104 }, { target := 107, numerator := 95316245090240918993240064 }, { target := 108, numerator := 167625120675940926505353216 }, { target := 109, numerator := 5477945120128788447887360 }, { target := 110, numerator := 172007476772043957263663104 }, { target := 111, numerator := 5477945120128788447887360 }, { target := 112, numerator := 167625120675940926505353216 }, { target := 113, numerator := 175294243844121230332395520 }, { target := 114, numerator := 6573534144154546137464832 }, { target := 157, numerator := 118096941003604087504109568 }, { target := 158, numerator := 1712405644552259268809588736 }, { target := 159, numerator := 3031154819092504912605478912 }, { target := 160, numerator := 98414117503003406253424640 }, { target := 161, numerator := 1889551056057665400065753088 }, { target := 162, numerator := 98414117503003406253424640 }, { target := 163, numerator := 3011471995591904231354793984 }, { target := 164, numerator := 3149251760096109000109588480 }, { target := 165, numerator := 1889551056057665400065753088 }, { target := 166, numerator := 48242600399972269745428758528 }, { target := 167, numerator := 3090203289594306956357533696 }, { target := 168, numerator := 1712405644552259268809588736 }, { target := 169, numerator := 3011471995591904231354793984 }, { target := 170, numerator := 98414117503003406253424640 }, { target := 171, numerator := 3090203289594306956357533696 }, { target := 172, numerator := 98414117503003406253424640 }, { target := 173, numerator := 3011471995591904231354793984 }, { target := 174, numerator := 3149251760096109000109588480 }, { target := 175, numerator := 118096941003604087504109568 }]

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
    Slot28.Left4.expected,
    Slot28.Left5.expected,
    Slot28.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 192, numerator := 176805401118639516800778240 }, { target := 193, numerator := 2563678316220272993611284480 }, { target := 194, numerator := 4538005295378414264553308160 }, { target := 195, numerator := 147337834265532930667315200 }, { target := 196, numerator := 2828886417898232268812451840 }, { target := 197, numerator := 147337834265532930667315200 }, { target := 198, numerator := 4508537728525307678419845120 }, { target := 199, numerator := 4714810696497053781354086400 }, { target := 200, numerator := 2828886417898232268812451840 }, { target := 201, numerator := 72225006356964242613117911040 }, { target := 202, numerator := 4626407995937734022953697280 }, { target := 203, numerator := 2563678316220272993611284480 }, { target := 204, numerator := 4508537728525307678419845120 }, { target := 205, numerator := 147337834265532930667315200 }, { target := 206, numerator := 4626407995937734022953697280 }, { target := 207, numerator := 147337834265532930667315200 }, { target := 208, numerator := 4508537728525307678419845120 }, { target := 209, numerator := 4714810696497053781354086400 }, { target := 210, numerator := 176805401118639516800778240 }, { target := 267, numerator := 6346860552976803167207424 }, { target := 268, numerator := 92029478018163645924507648 }, { target := 269, numerator := 162902754193071281291657216 }, { target := 270, numerator := 5289050460814002639339520 }, { target := 271, numerator := 101549768847628850675318784 }, { target := 272, numerator := 5289050460814002639339520 }, { target := 273, numerator := 161844944100908480763789312 }, { target := 274, numerator := 169249614746048084458864640 }, { target := 275, numerator := 101549768847628850675318784 }, { target := 276, numerator := 2592692535891024093804232704 }, { target := 277, numerator := 166076184469559682875260928 }, { target := 278, numerator := 92029478018163645924507648 }, { target := 279, numerator := 161844944100908480763789312 }, { target := 280, numerator := 5289050460814002639339520 }, { target := 281, numerator := 166076184469559682875260928 }, { target := 282, numerator := 5289050460814002639339520 }, { target := 283, numerator := 161844944100908480763789312 }, { target := 284, numerator := 169249614746048084458864640 }, { target := 285, numerator := 6346860552976803167207424 }, { target := 373, numerator := 177032074709817259771035648 }, { target := 374, numerator := 2566965083292350266680016896 }, { target := 375, numerator := 4543823250885309667456581632 }, { target := 376, numerator := 147526728924847716475863040 }, { target := 377, numerator := 2832513195357076156336570368 }, { target := 378, numerator := 147526728924847716475863040 }, { target := 379, numerator := 4514317905100340124161409024 }, { target := 380, numerator := 4720855325595126927227617280 }, { target := 381, numerator := 2832513195357076156336570368 }, { target := 382, numerator := 72317602518960350616468062208 }, { target := 383, numerator := 4632339288240218297342099456 }, { target := 384, numerator := 2566965083292350266680016896 }, { target := 385, numerator := 4514317905100340124161409024 }, { target := 386, numerator := 147526728924847716475863040 }, { target := 387, numerator := 4632339288240218297342099456 }, { target := 388, numerator := 147526728924847716475863040 }, { target := 389, numerator := 4514317905100340124161409024 }, { target := 390, numerator := 4720855325595126927227617280 }, { target := 391, numerator := 177032074709817259771035648 }]

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
    Slot28.Left7.expected,
    Slot28.Left8.expected,
    Slot28.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 408, numerator := 177032074709817259771035648 }, { target := 409, numerator := 2566965083292350266680016896 }, { target := 410, numerator := 4543823250885309667456581632 }, { target := 411, numerator := 147526728924847716475863040 }, { target := 412, numerator := 2832513195357076156336570368 }, { target := 413, numerator := 147526728924847716475863040 }, { target := 414, numerator := 4514317905100340124161409024 }, { target := 415, numerator := 4720855325595126927227617280 }, { target := 416, numerator := 2832513195357076156336570368 }, { target := 417, numerator := 72317602518960350616468062208 }, { target := 418, numerator := 4632339288240218297342099456 }, { target := 419, numerator := 2566965083292350266680016896 }, { target := 420, numerator := 4514317905100340124161409024 }, { target := 421, numerator := 147526728924847716475863040 }, { target := 422, numerator := 4632339288240218297342099456 }, { target := 423, numerator := 147526728924847716475863040 }, { target := 424, numerator := 4514317905100340124161409024 }, { target := 425, numerator := 4720855325595126927227617280 }, { target := 426, numerator := 177032074709817259771035648 }, { target := 483, numerator := 126710537468358320373891072 }, { target := 484, numerator := 1837302793291195645421420544 }, { target := 485, numerator := 3252237128354530222929870848 }, { target := 486, numerator := 105592114556965266978242560 }, { target := 487, numerator := 2027368599493733125982257152 }, { target := 488, numerator := 105592114556965266978242560 }, { target := 489, numerator := 3231118705443137169534222336 }, { target := 490, numerator := 3378947665822888543303761920 }, { target := 491, numerator := 2027368599493733125982257152 }, { target := 492, numerator := 51761254555824373872734502912 }, { target := 493, numerator := 3315592397088709383116816384 }, { target := 494, numerator := 1837302793291195645421420544 }, { target := 495, numerator := 3231118705443137169534222336 }, { target := 496, numerator := 105592114556965266978242560 }, { target := 497, numerator := 3315592397088709383116816384 }, { target := 498, numerator := 105592114556965266978242560 }, { target := 499, numerator := 3231118705443137169534222336 }, { target := 500, numerator := 3378947665822888543303761920 }, { target := 501, numerator := 126710537468358320373891072 }, { target := 623, numerator := 6573534144154546137464832 }, { target := 624, numerator := 95316245090240918993240064 }, { target := 625, numerator := 168720709699966684194930688 }, { target := 626, numerator := 5477945120128788447887360 }, { target := 627, numerator := 105176546306472738199437312 }, { target := 628, numerator := 5477945120128788447887360 }, { target := 629, numerator := 167625120675940926505353216 }, { target := 630, numerator := 175294243844121230332395520 }, { target := 631, numerator := 105176546306472738199437312 }, { target := 632, numerator := 2685288697887132097154383872 }, { target := 633, numerator := 172007476772043957263663104 }, { target := 634, numerator := 95316245090240918993240064 }, { target := 635, numerator := 167625120675940926505353216 }, { target := 636, numerator := 5477945120128788447887360 }, { target := 637, numerator := 172007476772043957263663104 }, { target := 638, numerator := 5477945120128788447887360 }, { target := 639, numerator := 167625120675940926505353216 }, { target := 640, numerator := 175294243844121230332395520 }, { target := 641, numerator := 6573534144154546137464832 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15.Parent3
