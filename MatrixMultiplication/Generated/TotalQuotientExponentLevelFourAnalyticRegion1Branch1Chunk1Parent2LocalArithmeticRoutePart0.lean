import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 7; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
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
    Slot2.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 78211653833532345361104896 }, { target := 30, numerator := 15512095715916725491649740800 }, { target := 35, numerator := 15512095715916725491649740800 }, { target := 43, numerator := 78211653833532345361104896 }, { target := 55, numerator := 88303480134633293149634560 }, { target := 56, numerator := 17513656453454367490572288000 }, { target := 61, numerator := 17513656453454367490572288000 }, { target := 69, numerator := 88303480134633293149634560 }, { target := 104, numerator := 75688697258257108413972480 }, { target := 105, numerator := 15011705531532314991919104000 }, { target := 110, numerator := 15011705531532314991919104000 }, { target := 118, numerator := 75688697258257108413972480 }, { target := 130, numerator := 996567847233718594117304320 }, { target := 131, numerator := 197654122831842147393601536000 }, { target := 136, numerator := 197654122831842147393601536000 }, { target := 144, numerator := 996567847233718594117304320 }, { target := 165, numerator := 88303480134633293149634560 }, { target := 166, numerator := 17513656453454367490572288000 }, { target := 171, numerator := 17513656453454367490572288000 }, { target := 179, numerator := 88303480134633293149634560 }, { target := 226, numerator := 75688697258257108413972480 }, { target := 227, numerator := 15011705531532314991919104000 }, { target := 232, numerator := 15011705531532314991919104000 }, { target := 240, numerator := 75688697258257108413972480 }, { target := 261, numerator := 88303480134633293149634560 }, { target := 262, numerator := 17513656453454367490572288000 }, { target := 267, numerator := 17513656453454367490572288000 }, { target := 275, numerator := 88303480134633293149634560 }, { target := 371, numerator := 88303480134633293149634560 }, { target := 372, numerator := 17513656453454367490572288000 }, { target := 377, numerator := 17513656453454367490572288000 }, { target := 385, numerator := 88303480134633293149634560 }, { target := 397, numerator := 3660809990724368810289135616 }, { target := 398, numerator := 726066157541779635109153996800 }, { target := 403, numerator := 726066157541779635109153996800 }, { target := 411, numerator := 3660809990724368810289135616 }, { target := 432, numerator := 90826436709908530096766976 }, { target := 433, numerator := 18014046637838777990302924800 }, { target := 438, numerator := 18014046637838777990302924800 }, { target := 446, numerator := 90826436709908530096766976 }, { target := 493, numerator := 996567847233718594117304320 }, { target := 494, numerator := 197654122831842147393601536000 }, { target := 499, numerator := 197654122831842147393601536000 }, { target := 507, numerator := 996567847233718594117304320 }, { target := 528, numerator := 3660809990724368810289135616 }, { target := 529, numerator := 726066157541779635109153996800 }, { target := 534, numerator := 726066157541779635109153996800 }, { target := 542, numerator := 3660809990724368810289135616 }, { target := 624, numerator := 78211653833532345361104896 }, { target := 625, numerator := 15512095715916725491649740800 }, { target := 630, numerator := 15512095715916725491649740800 }, { target := 638, numerator := 78211653833532345361104896 }, { target := 760, numerator := 88303480134633293149634560 }, { target := 761, numerator := 17513656453454367490572288000 }, { target := 766, numerator := 17513656453454367490572288000 }, { target := 774, numerator := 88303480134633293149634560 }, { target := 795, numerator := 90826436709908530096766976 }, { target := 796, numerator := 18014046637838777990302924800 }, { target := 801, numerator := 18014046637838777990302924800 }, { target := 809, numerator := 90826436709908530096766976 }, { target := 891, numerator := 88303480134633293149634560 }, { target := 892, numerator := 17513656453454367490572288000 }, { target := 897, numerator := 17513656453454367490572288000 }, { target := 905, numerator := 88303480134633293149634560 }]

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
    Slot3.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 33200583722756985392726016 }, { target := 72, numerator := 5440936247597188291410001920 }, { target := 74, numerator := 56016545337453648691719045120 }, { target := 82, numerator := 5440936247597188291410001920 }, { target := 89, numerator := 33200583722756985392726016 }, { target := 146, numerator := 481408463979976288194527232 }, { target := 147, numerator := 78893575590159230225445027840 }, { target := 149, numerator := 812239907393077906029926154240 }, { target := 157, numerator := 78893575590159230225445027840 }, { target := 164, numerator := 481408463979976288194527232 }, { target := 181, numerator := 852148315550762625079967744 }, { target := 182, numerator := 139650697021661166146190049280 }, { target := 184, numerator := 1437757996994643649754122158080 }, { target := 192, numerator := 139650697021661166146190049280 }, { target := 199, numerator := 852148315550762625079967744 }, { target := 242, numerator := 27667153102297487827271680 }, { target := 243, numerator := 4534113539664323576175001600 }, { target := 245, numerator := 46680454447878040576432537600 }, { target := 253, numerator := 4534113539664323576175001600 }, { target := 260, numerator := 27667153102297487827271680 }, { target := 277, numerator := 531209339564111766283616256 }, { target := 278, numerator := 87054979961555012662560030720 }, { target := 280, numerator := 896264725399258379067504721920 }, { target := 288, numerator := 87054979961555012662560030720 }, { target := 295, numerator := 531209339564111766283616256 }, { target := 312, numerator := 27667153102297487827271680 }, { target := 313, numerator := 4534113539664323576175001600 }, { target := 315, numerator := 46680454447878040576432537600 }, { target := 323, numerator := 4534113539664323576175001600 }, { target := 330, numerator := 27667153102297487827271680 }, { target := 413, numerator := 846614884930303127514513408 }, { target := 414, numerator := 138743874313728301430955048960 }, { target := 416, numerator := 1428421906105068041638835650560 }, { target := 424, numerator := 138743874313728301430955048960 }, { target := 431, numerator := 846614884930303127514513408 }, { target := 448, numerator := 885348899273519610472693760 }, { target := 449, numerator := 145091633269258354437600051200 }, { target := 451, numerator := 1493774542332097298445841203200 }, { target := 459, numerator := 145091633269258354437600051200 }, { target := 466, numerator := 885348899273519610472693760 }, { target := 509, numerator := 531209339564111766283616256 }, { target := 510, numerator := 87054979961555012662560030720 }, { target := 512, numerator := 896264725399258379067504721920 }, { target := 520, numerator := 87054979961555012662560030720 }, { target := 527, numerator := 531209339564111766283616256 }, { target := 544, numerator := 13562438450746228532928577536 }, { target := 545, numerator := 2222622457143451417040985784320 }, { target := 547, numerator := 22882758770349815490567229931520 }, { target := 555, numerator := 2222622457143451417040985784320 }, { target := 562, numerator := 13562438450746228532928577536 }, { target := 579, numerator := 868748607412141117776330752 }, { target := 580, numerator := 142371165145459760291895050240 }, { target := 582, numerator := 1465766269663370474099981680640 }, { target := 590, numerator := 142371165145459760291895050240 }, { target := 597, numerator := 868748607412141117776330752 }, { target := 640, numerator := 481408463979976288194527232 }, { target := 641, numerator := 78893575590159230225445027840 }, { target := 643, numerator := 812239907393077906029926154240 }, { target := 651, numerator := 78893575590159230225445027840 }, { target := 658, numerator := 481408463979976288194527232 }]

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
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot3.Left16.expected,
    Slot3.Left17.expected,
    Slot3.Left18.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot4.Left4.expected,
    Slot4.Left5.expected,
    Slot4.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 2451375468707183461098586112 }, { target := 202, numerator := 98005536413385710791605354496 }, { target := 205, numerator := 98005512462594374088966275072 }, { target := 212, numerator := 2451375468707183461098586112 }, { target := 296, numerator := 1825492370313860024222351360 }, { target := 298, numerator := 72982846265287231440557178880 }, { target := 301, numerator := 72982828429591555172634460160 }, { target := 308, numerator := 1825492370313860024222351360 }, { target := 331, numerator := 1929806220046080597035057152 }, { target := 333, numerator := 77153294623303644665731874816 }, { target := 336, numerator := 77153275768425358325356429312 }, { target := 343, numerator := 1929806220046080597035057152 }, { target := 467, numerator := 2503532393573293747504939008 }, { target := 469, numerator := 100090760592393917404192702464 }, { target := 472, numerator := 100090736132011275665327259648 }, { target := 479, numerator := 2503532393573293747504939008 }, { target := 563, numerator := 33536902688908914159284912128 }, { target := 565, numerator := 1340799147102276851893664743424 }, { target := 568, numerator := 1340798819435067713600113082368 }, { target := 575, numerator := 33536902688908914159284912128 }, { target := 598, numerator := 60658503619286263090588418048 }, { target := 600, numerator := 2425115720186544290439085686784 }, { target := 603, numerator := 2425115127531856533307825061888 }, { target := 610, numerator := 60658503619286263090588418048 }, { target := 659, numerator := 1825492370313860024222351360 }, { target := 661, numerator := 72982846265287231440557178880 }, { target := 664, numerator := 72982828429591555172634460160 }, { target := 671, numerator := 1825492370313860024222351360 }, { target := 675, numerator := 846614884930303127514513408 }, { target := 676, numerator := 138743874313728301430955048960 }, { target := 678, numerator := 1428421906105068041638835650560 }, { target := 686, numerator := 138743874313728301430955048960 }, { target := 693, numerator := 846614884930303127514513408 }, { target := 776, numerator := 27667153102297487827271680 }, { target := 777, numerator := 4534113539664323576175001600 }, { target := 779, numerator := 46680454447878040576432537600 }, { target := 787, numerator := 4534113539664323576175001600 }, { target := 794, numerator := 27667153102297487827271680 }, { target := 811, numerator := 868748607412141117776330752 }, { target := 812, numerator := 142371165145459760291895050240 }, { target := 814, numerator := 1465766269663370474099981680640 }, { target := 822, numerator := 142371165145459760291895050240 }, { target := 829, numerator := 868748607412141117776330752 }, { target := 846, numerator := 27667153102297487827271680 }, { target := 847, numerator := 4534113539664323576175001600 }, { target := 849, numerator := 46680454447878040576432537600 }, { target := 857, numerator := 4534113539664323576175001600 }, { target := 864, numerator := 27667153102297487827271680 }, { target := 907, numerator := 846614884930303127514513408 }, { target := 908, numerator := 138743874313728301430955048960 }, { target := 910, numerator := 1428421906105068041638835650560 }, { target := 918, numerator := 138743874313728301430955048960 }, { target := 925, numerator := 846614884930303127514513408 }, { target := 942, numerator := 885348899273519610472693760 }, { target := 943, numerator := 145091633269258354437600051200 }, { target := 945, numerator := 1493774542332097298445841203200 }, { target := 953, numerator := 145091633269258354437600051200 }, { target := 960, numerator := 885348899273519610472693760 }, { target := 1017, numerator := 33200583722756985392726016 }, { target := 1018, numerator := 5440936247597188291410001920 }, { target := 1020, numerator := 56016545337453648691719045120 }, { target := 1028, numerator := 5440936247597188291410001920 }, { target := 1035, numerator := 33200583722756985392726016 }]

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
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot4.Left10.expected,
    Slot4.Left11.expected,
    Slot4.Left12.expected,
    Slot4.Left13.expected,
    Slot4.Left14.expected,
    Slot4.Left15.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 347, numerator := 637589120869652394261086208 }, { target := 350, numerator := 2322584568547031921656332288 }, { target := 352, numerator := 637589549756452108008161280 }, { target := 614, numerator := 15631217156804381278658887680 }, { target := 617, numerator := 56940782970830460014800404480 }, { target := 619, numerator := 15631227671448503293103308800 }, { target := 694, numerator := 33536902688908914159284912128 }, { target := 696, numerator := 1340799147102276851893664743424 }, { target := 699, numerator := 1340798819435067713600113082368 }, { target := 706, numerator := 33536902688908914159284912128 }, { target := 710, numerator := 11558873739636924050797756416 }, { target := 713, numerator := 42106210565271998063576088576 }, { target := 715, numerator := 11558881514939551119373762560 }, { target := 720, numerator := 1981963144912190883441410048 }, { target := 722, numerator := 79238518802311851278319222784 }, { target := 725, numerator := 79238499437842259901717413888 }, { target := 732, numerator := 1981963144912190883441410048 }, { target := 736, numerator := 12895754154363614554893582336 }, { target := 739, numerator := 46976145950935129512210333696 }, { target := 741, numerator := 12895762828945015216810229760 }, { target := 830, numerator := 1981963144912190883441410048 }, { target := 832, numerator := 79238518802311851278319222784 }, { target := 835, numerator := 79238499437842259901717413888 }, { target := 842, numerator := 1981963144912190883441410048 }, { target := 865, numerator := 1929806220046080597035057152 }, { target := 867, numerator := 77153294623303644665731874816 }, { target := 870, numerator := 77153275768425358325356429312 }, { target := 877, numerator := 1929806220046080597035057152 }, { target := 881, numerator := 637589120869652394261086208 }, { target := 884, numerator := 2322584568547031921656332288 }, { target := 886, numerator := 637589549756452108008161280 }, { target := 926, numerator := 1929806220046080597035057152 }, { target := 928, numerator := 77153294623303644665731874816 }, { target := 931, numerator := 77153275768425358325356429312 }, { target := 938, numerator := 1929806220046080597035057152 }, { target := 961, numerator := 60658503619286263090588418048 }, { target := 963, numerator := 2425115720186544290439085686784 }, { target := 966, numerator := 2425115127531856533307825061888 }, { target := 973, numerator := 60658503619286263090588418048 }, { target := 977, numerator := 12875186763367819316369031168 }, { target := 980, numerator := 46901223868078773643769806848 }, { target := 982, numerator := 12875195424114161923003514880 }, { target := 987, numerator := 1929806220046080597035057152 }, { target := 989, numerator := 77153294623303644665731874816 }, { target := 992, numerator := 77153275768425358325356429312 }, { target := 999, numerator := 1929806220046080597035057152 }, { target := 1003, numerator := 13101428064321566940139094016 }, { target := 1006, numerator := 47725366779498688196615602176 }, { target := 1008, numerator := 13101436877253548154877378560 }, { target := 1036, numerator := 2451375468707183461098586112 }, { target := 1038, numerator := 98005536413385710791605354496 }, { target := 1041, numerator := 98005512462594374088966275072 }, { target := 1048, numerator := 2451375468707183461098586112 }, { target := 1052, numerator := 637589120869652394261086208 }, { target := 1055, numerator := 2322584568547031921656332288 }, { target := 1057, numerator := 637589549756452108008161280 }, { target := 1062, numerator := 2503532393573293747504939008 }, { target := 1064, numerator := 100090760592393917404192702464 }, { target := 1067, numerator := 100090736132011275665327259648 }, { target := 1074, numerator := 2503532393573293747504939008 }, { target := 1078, numerator := 15631217156804381278658887680 }, { target := 1081, numerator := 56940782970830460014800404480 }, { target := 1083, numerator := 15631227671448503293103308800 }]

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
    Slot5.Left9.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 637589120869652394261086208 }, { target := 6, numerator := 15631217156804381278658887680 }, { target := 7, numerator := 11558873739636924050797756416 }, { target := 8, numerator := 12895754154363614554893582336 }, { target := 9, numerator := 637589120869652394261086208 }, { target := 10, numerator := 12875186763367819316369031168 }, { target := 11, numerator := 13101428064321566940139094016 }, { target := 12, numerator := 637589120869652394261086208 }, { target := 13, numerator := 15631217156804381278658887680 }, { target := 14, numerator := 637589120869652394261086208 }, { target := 29, numerator := 2462467665398166191691792384 }, { target := 30, numerator := 1833752516785868440621547520 }, { target := 31, numerator := 1938538374887918065799921664 }, { target := 32, numerator := 2514860594449191004280979456 }, { target := 33, numerator := 33688653379808954494847287296 }, { target := 34, numerator := 60932976486341857041224564736 }, { target := 35, numerator := 1833752516785868440621547520 }, { target := 36, numerator := 33688653379808954494847287296 }, { target := 37, numerator := 1990931303938942878389108736 }, { target := 38, numerator := 1990931303938942878389108736 }, { target := 39, numerator := 1938538374887918065799921664 }, { target := 40, numerator := 1938538374887918065799921664 }, { target := 41, numerator := 60932976486341857041224564736 }, { target := 42, numerator := 1938538374887918065799921664 }, { target := 43, numerator := 2462467665398166191691792384 }, { target := 44, numerator := 2514860594449191004280979456 }, { target := 94, numerator := 2322584568547031921656332288 }, { target := 95, numerator := 56940782970830460014800404480 }, { target := 96, numerator := 42106210565271998063576088576 }, { target := 97, numerator := 46976145950935129512210333696 }, { target := 98, numerator := 2322584568547031921656332288 }, { target := 99, numerator := 46901223868078773643769806848 }, { target := 100, numerator := 47725366779498688196615602176 }, { target := 101, numerator := 2322584568547031921656332288 }, { target := 102, numerator := 56940782970830460014800404480 }, { target := 103, numerator := 2322584568547031921656332288 }, { target := 216, numerator := 637589549756452108008161280 }, { target := 217, numerator := 15631227671448503293103308800 }, { target := 218, numerator := 11558881514939551119373762560 }, { target := 219, numerator := 12895762828945015216810229760 }, { target := 220, numerator := 637589549756452108008161280 }, { target := 221, numerator := 12875195424114161923003514880 }, { target := 222, numerator := 13101436877253548154877378560 }, { target := 223, numerator := 637589549756452108008161280 }, { target := 224, numerator := 15631227671448503293103308800 }, { target := 225, numerator := 637589549756452108008161280 }, { target := 1092, numerator := 637589120869652394261086208 }, { target := 1095, numerator := 2322584568547031921656332288 }, { target := 1097, numerator := 637589549756452108008161280 }]

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
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 104, numerator := 98449000379057139347223478272 }, { target := 105, numerator := 73313085388659571854315356160 }, { target := 106, numerator := 77502404553725833103133376512 }, { target := 107, numerator := 100543659961590269971632488448 }, { target := 108, numerator := 1346866111568802991494993543168 }, { target := 109, numerator := 2436089094486030916187678834688 }, { target := 110, numerator := 73313085388659571854315356160 }, { target := 111, numerator := 1346866111568802991494993543168 }, { target := 112, numerator := 79597064136258963727542386688 }, { target := 113, numerator := 79597064136258963727542386688 }, { target := 114, numerator := 77502404553725833103133376512 }, { target := 115, numerator := 77502404553725833103133376512 }, { target := 116, numerator := 2436089094486030916187678834688 }, { target := 117, numerator := 77502404553725833103133376512 }, { target := 118, numerator := 98449000379057139347223478272 }, { target := 119, numerator := 100543659961590269971632488448 }, { target := 226, numerator := 98448976319891181211540783104 }, { target := 227, numerator := 73313067472259390263913349120 }, { target := 228, numerator := 77502385613531355421851254784 }, { target := 229, numerator := 100543635390527163790509735936 }, { target := 230, numerator := 1346865782418936798277036670976 }, { target := 231, numerator := 2436088499149647739340892143616 }, { target := 232, numerator := 73313067472259390263913349120 }, { target := 233, numerator := 1346865782418936798277036670976 }, { target := 234, numerator := 79597044684167338000820207616 }, { target := 235, numerator := 79597044684167338000820207616 }, { target := 236, numerator := 77502385613531355421851254784 }, { target := 237, numerator := 77502385613531355421851254784 }, { target := 238, numerator := 2436088499149647739340892143616 }, { target := 239, numerator := 77502385613531355421851254784 }, { target := 240, numerator := 98448976319891181211540783104 }, { target := 241, numerator := 100543635390527163790509735936 }, { target := 624, numerator := 2462467665398166191691792384 }, { target := 625, numerator := 1833752516785868440621547520 }, { target := 626, numerator := 1938538374887918065799921664 }, { target := 627, numerator := 2514860594449191004280979456 }, { target := 628, numerator := 33688653379808954494847287296 }, { target := 629, numerator := 60932976486341857041224564736 }, { target := 630, numerator := 1833752516785868440621547520 }, { target := 631, numerator := 33688653379808954494847287296 }, { target := 632, numerator := 1990931303938942878389108736 }, { target := 633, numerator := 1990931303938942878389108736 }, { target := 634, numerator := 1938538374887918065799921664 }, { target := 635, numerator := 1938538374887918065799921664 }, { target := 636, numerator := 60932976486341857041224564736 }, { target := 637, numerator := 1938538374887918065799921664 }, { target := 638, numerator := 2462467665398166191691792384 }, { target := 639, numerator := 2514860594449191004280979456 }]

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
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 33027963703401229836091392 }, { target := 72, numerator := 478905473699317832623325184 }, { target := 73, numerator := 847717735053964899126345728 }, { target := 74, numerator := 27523303086167691530076160 }, { target := 75, numerator := 528447419254419677377462272 }, { target := 76, numerator := 27523303086167691530076160 }, { target := 77, numerator := 842213074436731360820330496 }, { target := 78, numerator := 880745698757366128962437120 }, { target := 79, numerator := 528447419254419677377462272 }, { target := 80, numerator := 13491923172839402388043333632 }, { target := 81, numerator := 864231716905665514044391424 }, { target := 82, numerator := 478905473699317832623325184 }, { target := 83, numerator := 842213074436731360820330496 }, { target := 84, numerator := 27523303086167691530076160 }, { target := 85, numerator := 864231716905665514044391424 }, { target := 86, numerator := 27523303086167691530076160 }, { target := 87, numerator := 842213074436731360820330496 }, { target := 88, numerator := 880745698757366128962437120 }, { target := 89, numerator := 33027963703401229836091392 }, { target := 146, numerator := 5412647150989230639981527040 }, { target := 147, numerator := 78483383689343844279732142080 }, { target := 148, numerator := 138924610208723586426192527360 }, { target := 149, numerator := 4510539292491025533317939200 }, { target := 150, numerator := 86602354415827690239704432640 }, { target := 151, numerator := 4510539292491025533317939200 }, { target := 152, numerator := 138022502350225381319528939520 }, { target := 153, numerator := 144337257359712817066174054400 }, { target := 154, numerator := 86602354415827690239704432640 }, { target := 155, numerator := 2211066361179100716432453795840 }, { target := 156, numerator := 141630933784218201746183290880 }, { target := 157, numerator := 78483383689343844279732142080 }, { target := 158, numerator := 138022502350225381319528939520 }, { target := 159, numerator := 4510539292491025533317939200 }, { target := 160, numerator := 141630933784218201746183290880 }, { target := 161, numerator := 4510539292491025533317939200 }, { target := 162, numerator := 138022502350225381319528939520 }, { target := 163, numerator := 144337257359712817066174054400 }, { target := 164, numerator := 5412647150989230639981527040 }, { target := 242, numerator := 55725298134659262303373885440 }, { target := 243, numerator := 808016822952559303398921338880 }, { target := 244, numerator := 1430282652122921065786596392960 }, { target := 245, numerator := 46437748445549385252811571200 }, { target := 246, numerator := 891604770154548196853982167040 }, { target := 247, numerator := 46437748445549385252811571200 }, { target := 248, numerator := 1420995102433811188736034078720 }, { target := 249, numerator := 1486007950257580328089970278400 }, { target := 250, numerator := 891604770154548196853982167040 }, { target := 251, numerator := 22763784288008308650928232202240 }, { target := 252, numerator := 1458145301190250696938283335680 }, { target := 253, numerator := 808016822952559303398921338880 }, { target := 254, numerator := 1420995102433811188736034078720 }, { target := 255, numerator := 46437748445549385252811571200 }, { target := 256, numerator := 1458145301190250696938283335680 }, { target := 257, numerator := 46437748445549385252811571200 }, { target := 258, numerator := 1420995102433811188736034078720 }, { target := 259, numerator := 1486007950257580328089970278400 }, { target := 260, numerator := 55725298134659262303373885440 }]

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
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 78211653833532345361104896 }, { target := 201, numerator := 88303480134633293149634560 }, { target := 202, numerator := 75688697258257108413972480 }, { target := 203, numerator := 996567847233718594117304320 }, { target := 204, numerator := 88303480134633293149634560 }, { target := 205, numerator := 75688697258257108413972480 }, { target := 206, numerator := 88303480134633293149634560 }, { target := 207, numerator := 88303480134633293149634560 }, { target := 208, numerator := 3660809990724368810289135616 }, { target := 209, numerator := 90826436709908530096766976 }, { target := 210, numerator := 996567847233718594117304320 }, { target := 211, numerator := 3660809990724368810289135616 }, { target := 212, numerator := 78211653833532345361104896 }, { target := 213, numerator := 88303480134633293149634560 }, { target := 214, numerator := 90826436709908530096766976 }, { target := 215, numerator := 88303480134633293149634560 }, { target := 640, numerator := 5412647150989230639981527040 }, { target := 641, numerator := 78483383689343844279732142080 }, { target := 642, numerator := 138924610208723586426192527360 }, { target := 643, numerator := 4510539292491025533317939200 }, { target := 644, numerator := 86602354415827690239704432640 }, { target := 645, numerator := 4510539292491025533317939200 }, { target := 646, numerator := 138022502350225381319528939520 }, { target := 647, numerator := 144337257359712817066174054400 }, { target := 648, numerator := 86602354415827690239704432640 }, { target := 649, numerator := 2211066361179100716432453795840 }, { target := 650, numerator := 141630933784218201746183290880 }, { target := 651, numerator := 78483383689343844279732142080 }, { target := 652, numerator := 138022502350225381319528939520 }, { target := 653, numerator := 4510539292491025533317939200 }, { target := 654, numerator := 141630933784218201746183290880 }, { target := 655, numerator := 4510539292491025533317939200 }, { target := 656, numerator := 138022502350225381319528939520 }, { target := 657, numerator := 144337257359712817066174054400 }, { target := 658, numerator := 5412647150989230639981527040 }, { target := 1017, numerator := 33027963703401229836091392 }, { target := 1018, numerator := 478905473699317832623325184 }, { target := 1019, numerator := 847717735053964899126345728 }, { target := 1020, numerator := 27523303086167691530076160 }, { target := 1021, numerator := 528447419254419677377462272 }, { target := 1022, numerator := 27523303086167691530076160 }, { target := 1023, numerator := 842213074436731360820330496 }, { target := 1024, numerator := 880745698757366128962437120 }, { target := 1025, numerator := 528447419254419677377462272 }, { target := 1026, numerator := 13491923172839402388043333632 }, { target := 1027, numerator := 864231716905665514044391424 }, { target := 1028, numerator := 478905473699317832623325184 }, { target := 1029, numerator := 842213074436731360820330496 }, { target := 1030, numerator := 27523303086167691530076160 }, { target := 1031, numerator := 864231716905665514044391424 }, { target := 1032, numerator := 27523303086167691530076160 }, { target := 1033, numerator := 842213074436731360820330496 }, { target := 1034, numerator := 880745698757366128962437120 }, { target := 1035, numerator := 33027963703401229836091392 }]

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
    Slot13.Left1.expected,
    Slot13.Left6.expected,
    Slot13.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 296, numerator := 15512095715916725491649740800 }, { target := 297, numerator := 17513656453454367490572288000 }, { target := 298, numerator := 15011705531532314991919104000 }, { target := 299, numerator := 197654122831842147393601536000 }, { target := 300, numerator := 17513656453454367490572288000 }, { target := 301, numerator := 15011705531532314991919104000 }, { target := 302, numerator := 17513656453454367490572288000 }, { target := 303, numerator := 17513656453454367490572288000 }, { target := 304, numerator := 726066157541779635109153996800 }, { target := 305, numerator := 18014046637838777990302924800 }, { target := 306, numerator := 197654122831842147393601536000 }, { target := 307, numerator := 726066157541779635109153996800 }, { target := 308, numerator := 15512095715916725491649740800 }, { target := 309, numerator := 17513656453454367490572288000 }, { target := 310, numerator := 18014046637838777990302924800 }, { target := 311, numerator := 17513656453454367490572288000 }, { target := 659, numerator := 15512095715916725491649740800 }, { target := 660, numerator := 17513656453454367490572288000 }, { target := 661, numerator := 15011705531532314991919104000 }, { target := 662, numerator := 197654122831842147393601536000 }, { target := 663, numerator := 17513656453454367490572288000 }, { target := 664, numerator := 15011705531532314991919104000 }, { target := 665, numerator := 17513656453454367490572288000 }, { target := 666, numerator := 17513656453454367490572288000 }, { target := 667, numerator := 726066157541779635109153996800 }, { target := 668, numerator := 18014046637838777990302924800 }, { target := 669, numerator := 197654122831842147393601536000 }, { target := 670, numerator := 726066157541779635109153996800 }, { target := 671, numerator := 15512095715916725491649740800 }, { target := 672, numerator := 17513656453454367490572288000 }, { target := 673, numerator := 18014046637838777990302924800 }, { target := 674, numerator := 17513656453454367490572288000 }, { target := 1036, numerator := 78211653833532345361104896 }, { target := 1037, numerator := 88303480134633293149634560 }, { target := 1038, numerator := 75688697258257108413972480 }, { target := 1039, numerator := 996567847233718594117304320 }, { target := 1040, numerator := 88303480134633293149634560 }, { target := 1041, numerator := 75688697258257108413972480 }, { target := 1042, numerator := 88303480134633293149634560 }, { target := 1043, numerator := 88303480134633293149634560 }, { target := 1044, numerator := 3660809990724368810289135616 }, { target := 1045, numerator := 90826436709908530096766976 }, { target := 1046, numerator := 996567847233718594117304320 }, { target := 1047, numerator := 3660809990724368810289135616 }, { target := 1048, numerator := 78211653833532345361104896 }, { target := 1049, numerator := 88303480134633293149634560 }, { target := 1050, numerator := 90826436709908530096766976 }, { target := 1051, numerator := 88303480134633293149634560 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent2
