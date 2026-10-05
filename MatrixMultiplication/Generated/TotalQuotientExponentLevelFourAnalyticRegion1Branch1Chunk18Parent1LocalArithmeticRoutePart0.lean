import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk18Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 75; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent1

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
    Slot2.Left6.expected,
    Slot2.Left14.expected,
    Slot3.Left0.expected,
    Slot3.Left2.expected,
    Slot3.Left7.expected,
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 89091686450472810153246720 }, { target := 111, numerator := 101465531790816256007864320 }, { target := 112, numerator := 79192610178198053469552640 }, { target := 113, numerator := 1061675930201467654326190080 }, { target := 114, numerator := 94041224586610188495093760 }, { target := 115, numerator := 79192610178198053469552640 }, { target := 116, numerator := 94041224586610188495093760 }, { target := 117, numerator := 91566455518541499324170240 }, { target := 118, numerator := 3459727157160027460951080960 }, { target := 119, numerator := 91566455518541499324170240 }, { target := 120, numerator := 1061675930201467654326190080 }, { target := 121, numerator := 3459727157160027460951080960 }, { target := 122, numerator := 89091686450472810153246720 }, { target := 123, numerator := 91566455518541499324170240 }, { target := 124, numerator := 91566455518541499324170240 }, { target := 125, numerator := 101465531790816256007864320 }, { target := 257, numerator := 9509605552960508493037568 }, { target := 258, numerator := 190192111059210169860751360 }, { target := 259, numerator := 9849234322709098082074624 }, { target := 260, numerator := 176946589039015175888306176 }, { target := 261, numerator := 264910440403899879448903680 }, { target := 262, numerator := 9509605552960508493037568 }, { target := 263, numerator := 265250069173648469037940736 }, { target := 264, numerator := 265250069173648469037940736 }, { target := 265, numerator := 189852482289461580271714304 }, { target := 266, numerator := 9849234322709098082074624 }, { target := 353, numerator := 1886086079602778037446246400 }, { target := 354, numerator := 37721721592055560748924928000 }, { target := 355, numerator := 1953446296731448681640755200 }, { target := 356, numerator := 35094673124037405625339084800 }, { target := 357, numerator := 52540969360363102471716864000 }, { target := 358, numerator := 1886086079602778037446246400 }, { target := 359, numerator := 52608329577491773115911372800 }, { target := 360, numerator := 52608329577491773115911372800 }, { target := 361, numerator := 37654361374926890104730419200 }, { target := 362, numerator := 1953446296731448681640755200 }, { target := 389, numerator := 839218831220488955393736704 }, { target := 391, numerator := 839218831220488955393736704 }, { target := 695, numerator := 1886086079602778037446246400 }, { target := 696, numerator := 37721721592055560748924928000 }, { target := 697, numerator := 1953446296731448681640755200 }, { target := 698, numerator := 35094673124037405625339084800 }, { target := 699, numerator := 52540969360363102471716864000 }, { target := 700, numerator := 1886086079602778037446246400 }, { target := 701, numerator := 52608329577491773115911372800 }, { target := 702, numerator := 52608329577491773115911372800 }, { target := 703, numerator := 37654361374926890104730419200 }, { target := 704, numerator := 1953446296731448681640755200 }, { target := 731, numerator := 37931164430082189027499311104 }, { target := 733, numerator := 37931164430082189027499311104 }, { target := 982, numerator := 9509605552960508493037568 }, { target := 983, numerator := 190192111059210169860751360 }, { target := 984, numerator := 9849234322709098082074624 }, { target := 985, numerator := 176946589039015175888306176 }, { target := 986, numerator := 264910440403899879448903680 }, { target := 987, numerator := 9509605552960508493037568 }, { target := 988, numerator := 265250069173648469037940736 }, { target := 989, numerator := 265250069173648469037940736 }, { target := 990, numerator := 189852482289461580271714304 }, { target := 991, numerator := 9849234322709098082074624 }, { target := 992, numerator := 843697995829490813878927360 }, { target := 994, numerator := 843697995829490813878927360 }]

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
    Slot5.Left1.expected,
    Slot5.Left3.expected,
    Slot5.Left11.expected,
    Slot5.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 206, numerator := 28698335134922447880286371840 }, { target := 207, numerator := 32684215014772787863659479040 }, { target := 208, numerator := 25509631231042175893587886080 }, { target := 209, numerator := 341988493691159170573412597760 }, { target := 210, numerator := 30292687086862583873635614720 }, { target := 211, numerator := 25509631231042175893587886080 }, { target := 212, numerator := 30292687086862583873635614720 }, { target := 213, numerator := 29495511110892515876960993280 }, { target := 214, numerator := 1114452014406155059351120773120 }, { target := 215, numerator := 29495511110892515876960993280 }, { target := 216, numerator := 341988493691159170573412597760 }, { target := 217, numerator := 1114452014406155059351120773120 }, { target := 218, numerator := 28698335134922447880286371840 }, { target := 219, numerator := 29495511110892515876960993280 }, { target := 220, numerator := 29495511110892515876960993280 }, { target := 221, numerator := 32684215014772787863659479040 }, { target := 302, numerator := 305218862623542953807657828352 }, { target := 303, numerator := 347610371321257252947610304512 }, { target := 304, numerator := 271305655665371514495695847424 }, { target := 305, numerator := 3637191446263886866207922454528 }, { target := 306, numerator := 322175466102628673463638818816 }, { target := 307, numerator := 271305655665371514495695847424 }, { target := 308, numerator := 322175466102628673463638818816 }, { target := 309, numerator := 313697164363085813635648323584 }, { target := 310, numerator := 11852665831880918039530712334336 }, { target := 311, numerator := 313697164363085813635648323584 }, { target := 312, numerator := 3637191446263886866207922454528 }, { target := 313, numerator := 11852665831880918039530712334336 }, { target := 314, numerator := 305218862623542953807657828352 }, { target := 315, numerator := 313697164363085813635648323584 }, { target := 316, numerator := 313697164363085813635648323584 }, { target := 317, numerator := 347610371321257252947610304512 }, { target := 679, numerator := 28698421631705409504373899264 }, { target := 680, numerator := 32684313524997827491092496384 }, { target := 681, numerator := 25509708117071475114999021568 }, { target := 682, numerator := 341989524444489463260455632896 }, { target := 683, numerator := 30292778389022376699061338112 }, { target := 684, numerator := 25509708117071475114999021568 }, { target := 685, numerator := 30292778389022376699061338112 }, { target := 686, numerator := 29495600010363893101717618688 }, { target := 687, numerator := 1114455373364560069086519754752 }, { target := 688, numerator := 29495600010363893101717618688 }, { target := 689, numerator := 341989524444489463260455632896 }, { target := 690, numerator := 1114455373364560069086519754752 }, { target := 691, numerator := 28698421631705409504373899264 }, { target := 692, numerator := 29495600010363893101717618688 }, { target := 693, numerator := 29495600010363893101717618688 }, { target := 694, numerator := 32684313524997827491092496384 }, { target := 966, numerator := 89091686450472810153246720 }, { target := 967, numerator := 101465531790816256007864320 }, { target := 968, numerator := 79192610178198053469552640 }, { target := 969, numerator := 1061675930201467654326190080 }, { target := 970, numerator := 94041224586610188495093760 }, { target := 971, numerator := 79192610178198053469552640 }, { target := 972, numerator := 94041224586610188495093760 }, { target := 973, numerator := 91566455518541499324170240 }, { target := 974, numerator := 3459727157160027460951080960 }, { target := 975, numerator := 91566455518541499324170240 }, { target := 976, numerator := 1061675930201467654326190080 }, { target := 977, numerator := 3459727157160027460951080960 }, { target := 978, numerator := 89091686450472810153246720 }, { target := 979, numerator := 91566455518541499324170240 }, { target := 980, numerator := 91566455518541499324170240 }, { target := 981, numerator := 101465531790816256007864320 }]

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
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left6.expected,
    Slot6.Left14.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left2.expected,
    Slot7.Left3.expected,
    Slot7.Left4.expected,
    Slot7.Left5.expected,
    Slot7.Left6.expected,
    Slot7.Left7.expected,
    Slot7.Left8.expected,
    Slot7.Left9.expected,
    Slot8.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 2249715746656660479132303360 }, { target := 57, numerator := 33745736199849907186984550400 }, { target := 58, numerator := 59242514661958725950483988480 }, { target := 59, numerator := 2249715746656660479132303360 }, { target := 60, numerator := 37495262444277674652205056000 }, { target := 61, numerator := 2249715746656660479132303360 }, { target := 62, numerator := 59242514661958725950483988480 }, { target := 63, numerator := 58867562037515949203961937920 }, { target := 64, numerator := 37495262444277674652205056000 }, { target := 65, numerator := 908510209024848056822928506880 }, { target := 66, numerator := 58117656788630395710917836800 }, { target := 67, numerator := 33745736199849907186984550400 }, { target := 68, numerator := 59242514661958725950483988480 }, { target := 69, numerator := 2249715746656660479132303360 }, { target := 70, numerator := 58117656788630395710917836800 }, { target := 71, numerator := 2249715746656660479132303360 }, { target := 72, numerator := 59242514661958725950483988480 }, { target := 73, numerator := 59242514661958725950483988480 }, { target := 74, numerator := 2249715746656660479132303360 }, { target := 257, numerator := 4886943269494738430497652736 }, { target := 260, numerator := 17849649795078796876342886400 }, { target := 262, numerator := 4886941623003765936771563520 }, { target := 353, numerator := 857123936433382204101202280448 }, { target := 356, numerator := 3130660875851962776546390835200 }, { target := 358, numerator := 857123647654334480111747727360 }, { target := 389, numerator := 1798881405143168355089252352 }, { target := 391, numerator := 1798881834029968068836327424 }, { target := 656, numerator := 43579352750403852731355758592 }, { target := 658, numerator := 43579363140532452248260706304 }, { target := 695, numerator := 857124039193086758525123690496 }, { target := 698, numerator := 3130661251183665682087044710400 }, { target := 700, numerator := 857123750414004413113533726720 }, { target := 731, numerator := 33018178049240735291799502848 }, { target := 733, numerator := 33018185921388768747350654976 }, { target := 745, numerator := 36790026156798991520212451328 }, { target := 747, numerator := 36790034928225798569104244736 }, { target := 872, numerator := 1798881405143168355089252352 }, { target := 874, numerator := 1798881834029968068836327424 }, { target := 947, numerator := 36790026156798991520212451328 }, { target := 949, numerator := 36790034928225798569104244736 }, { target := 961, numerator := 36731997724375018347467636736 }, { target := 963, numerator := 36732006481966767341077266432 }, { target := 982, numerator := 4886840509790184006576242688 }, { target := 985, numerator := 17849274463375891335689011200 }, { target := 987, numerator := 4886838863333832934985564160 }, { target := 992, numerator := 1798881405143168355089252352 }, { target := 994, numerator := 1798881834029968068836327424 }, { target := 1006, numerator := 43579352750403852731355758592 }, { target := 1008, numerator := 43579363140532452248260706304 }, { target := 1011, numerator := 1798881405143168355089252352 }, { target := 1013, numerator := 1798881834029968068836327424 }]

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
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 1724119472595404790700179456 }, { target := 112, numerator := 67249942462045588622866907136 }, { target := 115, numerator := 67249917795001767183224143872 }, { target := 122, numerator := 1724127694943345270581100544 }, { target := 152, numerator := 88042535868720763321322569728 }, { target := 153, numerator := 1320638038030811449819838545920 }, { target := 154, numerator := 2318453444542980100794827669504 }, { target := 155, numerator := 88042535868720763321322569728 }, { target := 156, numerator := 1467375597812012722022042828800 }, { target := 157, numerator := 88042535868720763321322569728 }, { target := 158, numerator := 2318453444542980100794827669504 }, { target := 159, numerator := 2303779688564859973574607241216 }, { target := 160, numerator := 1467375597812012722022042828800 }, { target := 161, numerator := 35554510734985068254594097741824 }, { target := 162, numerator := 2274432176608619719134166384640 }, { target := 163, numerator := 1320638038030811449819838545920 }, { target := 164, numerator := 2318453444542980100794827669504 }, { target := 165, numerator := 88042535868720763321322569728 }, { target := 166, numerator := 2274432176608619719134166384640 }, { target := 167, numerator := 88042535868720763321322569728 }, { target := 168, numerator := 2318453444542980100794827669504 }, { target := 169, numerator := 2318453444542980100794827669504 }, { target := 170, numerator := 88042535868720763321322569728 }, { target := 283, numerator := 88042535868720763321322569728 }, { target := 284, numerator := 1320638038030811449819838545920 }, { target := 285, numerator := 2318453444542980100794827669504 }, { target := 286, numerator := 88042535868720763321322569728 }, { target := 287, numerator := 1467375597812012722022042828800 }, { target := 288, numerator := 88042535868720763321322569728 }, { target := 289, numerator := 2318453444542980100794827669504 }, { target := 290, numerator := 2303779688564859973574607241216 }, { target := 291, numerator := 1467375597812012722022042828800 }, { target := 292, numerator := 35554510734985068254594097741824 }, { target := 293, numerator := 2274432176608619719134166384640 }, { target := 294, numerator := 1320638038030811449819838545920 }, { target := 295, numerator := 2318453444542980100794827669504 }, { target := 296, numerator := 88042535868720763321322569728 }, { target := 297, numerator := 2274432176608619719134166384640 }, { target := 298, numerator := 88042535868720763321322569728 }, { target := 299, numerator := 2318453444542980100794827669504 }, { target := 300, numerator := 2318453444542980100794827669504 }, { target := 301, numerator := 88042535868720763321322569728 }, { target := 660, numerator := 2249715746656660479132303360 }, { target := 661, numerator := 33745736199849907186984550400 }, { target := 662, numerator := 59242514661958725950483988480 }, { target := 663, numerator := 2249715746656660479132303360 }, { target := 664, numerator := 37495262444277674652205056000 }, { target := 665, numerator := 2249715746656660479132303360 }, { target := 666, numerator := 59242514661958725950483988480 }, { target := 667, numerator := 58867562037515949203961937920 }, { target := 668, numerator := 37495262444277674652205056000 }, { target := 669, numerator := 908510209024848056822928506880 }, { target := 670, numerator := 58117656788630395710917836800 }, { target := 671, numerator := 33745736199849907186984550400 }, { target := 672, numerator := 59242514661958725950483988480 }, { target := 673, numerator := 2249715746656660479132303360 }, { target := 674, numerator := 58117656788630395710917836800 }, { target := 675, numerator := 2249715746656660479132303360 }, { target := 676, numerator := 59242514661958725950483988480 }, { target := 677, numerator := 59242514661958725950483988480 }, { target := 678, numerator := 2249715746656660479132303360 }]

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
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected,
    Slot10.Left4.expected,
    Slot10.Left5.expected,
    Slot10.Left6.expected,
    Slot10.Left7.expected,
    Slot10.Left8.expected,
    Slot10.Left9.expected,
    Slot10.Left10.expected,
    Slot10.Left11.expected,
    Slot10.Left12.expected,
    Slot10.Left13.expected,
    Slot10.Left14.expected,
    Slot10.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 206, numerator := 203779852411244618953739206656 }, { target := 208, numerator := 7948511438682806570471009550336 }, { target := 211, numerator := 7948508523196595056481792950272 }, { target := 218, numerator := 203780824239981790283478073344 }, { target := 257, numerator := 52751518758614794346736648192 }, { target := 260, numerator := 189745644254139760551055589376 }, { target := 262, numerator := 52751536356808640665648889856 }, { target := 302, numerator := 1933830178591246199723095228416 }, { target := 304, numerator := 75429789123521594330271392464896 }, { target := 307, numerator := 75429761456138610293404065595392 }, { target := 314, numerator := 1933839401052240878678870851584 }, { target := 353, numerator := 39563639068961095760052486144 }, { target := 356, numerator := 142309233190604820413291692032 }, { target := 358, numerator := 39563652267606480499236667392 }, { target := 379, numerator := 41761619017236712191166513152 }, { target := 382, numerator := 150215301701193977102919008256 }, { target := 384, numerator := 41761632949140173860305371136 }, { target := 524, numerator := 53850508732752602562293661696 }, { target := 527, numerator := 193698678509434338895869247488 }, { target := 529, numerator := 53850526697575487346183241728 }, { target := 620, numerator := 720937423034402189405400858624 }, { target := 623, numerator := 2593190471473243394197759721472 }, { target := 625, numerator := 720937663543051422430534828032 }, { target := 646, numerator := 1260541500336066023243894489088 }, { target := 649, numerator := 4534130290822881361501265854464 }, { target := 651, numerator := 1260541920859573142572901597184 }, { target := 679, numerator := 203779992174496288490444029952 }, { target := 681, numerator := 7948516890202137151339088576512 }, { target := 684, numerator := 7948513974713926039115319476224 }, { target := 691, numerator := 203780964003899992565033730048 }, { target := 695, numerator := 38464649094823287544495472640 }, { target := 698, numerator := 138356198935310242068478033920 }, { target := 700, numerator := 38464661926839633818702315520 }, { target := 721, numerator := 720937423034402189405400858624 }, { target := 724, numerator := 2593190471473243394197759721472 }, { target := 726, numerator := 720937663543051422430534828032 }, { target := 735, numerator := 40662629043098903975609499648 }, { target := 738, numerator := 146262267445899398758105350144 }, { target := 740, numerator := 40662642608373327179771019264 }, { target := 836, numerator := 41761619017236712191166513152 }, { target := 839, numerator := 150215301701193977102919008256 }, { target := 841, numerator := 41761632949140173860305371136 }, { target := 862, numerator := 41761619017236712191166513152 }, { target := 865, numerator := 150215301701193977102919008256 }, { target := 867, numerator := 41761632949140173860305371136 }, { target := 911, numerator := 40662629043098903975609499648 }, { target := 914, numerator := 146262267445899398758105350144 }, { target := 916, numerator := 40662642608373327179771019264 }, { target := 937, numerator := 1260541500336066023243894489088 }, { target := 940, numerator := 4534130290822881361501265854464 }, { target := 942, numerator := 1260541920859573142572901597184 }, { target := 951, numerator := 40662629043098903975609499648 }, { target := 954, numerator := 146262267445899398758105350144 }, { target := 956, numerator := 40662642608373327179771019264 }, { target := 966, numerator := 1724119472595404790700179456 }, { target := 968, numerator := 67249942462045588622866907136 }, { target := 971, numerator := 67249917795001767183224143872 }, { target := 978, numerator := 1724127694943345270581100544 }, { target := 982, numerator := 52751518758614794346736648192 }, { target := 985, numerator := 189745644254139760551055589376 }, { target := 987, numerator := 52751536356808640665648889856 }, { target := 996, numerator := 53850508732752602562293661696 }, { target := 999, numerator := 193698678509434338895869247488 }, { target := 1001, numerator := 53850526697575487346183241728 }]

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
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 50760895409233103994029604864 }, { target := 15, numerator := 38070671556924827995522203648 }, { target := 16, numerator := 40185708865642873995273437184 }, { target := 17, numerator := 51818414063592126993905221632 }, { target := 18, numerator := 693732237259519087918404599808 }, { target := 19, numerator := 1212973896549799380857332432896 }, { target := 20, numerator := 37013152902565804995646586880 }, { target := 21, numerator := 693732237259519087918404599808 }, { target := 22, numerator := 39128190211283850995397820416 }, { target := 23, numerator := 40185708865642873995273437184 }, { target := 24, numerator := 40185708865642873995273437184 }, { target := 25, numerator := 39128190211283850995397820416 }, { target := 26, numerator := 1212973896549799380857332432896 }, { target := 27, numerator := 39128190211283850995397820416 }, { target := 28, numerator := 50760895409233103994029604864 }, { target := 29, numerator := 51818414063592126993905221632 }, { target := 56, numerator := 1737225110478309050088947712 }, { target := 57, numerator := 205328854667749012172137562112 }, { target := 59, numerator := 1948529901232564794146666053632 }, { target := 67, numerator := 205328995493390263656334229504 }, { target := 74, numerator := 1737225110478309050088947712 }, { target := 136, numerator := 182585431263417505435921416192 }, { target := 137, numerator := 136939073447563129076941062144 }, { target := 138, numerator := 144546799750205525136771121152 }, { target := 139, numerator := 186389294414738703465836445696 }, { target := 140, numerator := 2495334227266705907624259354624 }, { target := 141, numerator := 4363031034565414140312538841088 }, { target := 142, numerator := 133135210296241931047026032640 }, { target := 143, numerator := 2495334227266705907624259354624 }, { target := 144, numerator := 140742936598884327106856091648 }, { target := 145, numerator := 144546799750205525136771121152 }, { target := 146, numerator := 144546799750205525136771121152 }, { target := 147, numerator := 140742936598884327106856091648 }, { target := 148, numerator := 4363031034565414140312538841088 }, { target := 149, numerator := 140742936598884327106856091648 }, { target := 150, numerator := 182585431263417505435921416192 }, { target := 151, numerator := 186389294414738703465836445696 }, { target := 152, numerator := 67761132903057759482331267072 }, { target := 153, numerator := 8008930866848469796091143913472 }, { target := 155, numerator := 76003157453007822665552171630592 }, { target := 163, numerator := 8008936359806714207388118810624 }, { target := 170, numerator := 67761132903057759482331267072 }, { target := 267, numerator := 50760912343344163659397988352 }, { target := 268, numerator := 38070684257508122744548491264 }, { target := 269, numerator := 40185722271814129563690074112 }, { target := 270, numerator := 51818431350497167068968779776 }, { target := 271, numerator := 693732468692370236678439174144 }, { target := 272, numerator := 1212974301204494910777697763328 }, { target := 273, numerator := 37013165250355119334977699840 }, { target := 274, numerator := 693732468692370236678439174144 }, { target := 275, numerator := 39128203264661126154119282688 }, { target := 276, numerator := 40185722271814129563690074112 }, { target := 277, numerator := 40185722271814129563690074112 }, { target := 278, numerator := 39128203264661126154119282688 }, { target := 279, numerator := 1212974301204494910777697763328 }, { target := 280, numerator := 39128203264661126154119282688 }, { target := 281, numerator := 50760912343344163659397988352 }, { target := 282, numerator := 51818431350497167068968779776 }, { target := 283, numerator := 67761108048511071156745273344 }, { target := 284, numerator := 8008927929200623228363833606144 }, { target := 286, numerator := 76003129575315339594620819472384 }, { target := 294, numerator := 8008933422156852841777513627648 }, { target := 301, numerator := 67761108048511071156745273344 }]

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
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left2.expected,
    Slot13.Left3.expected,
    Slot13.Left4.expected,
    Slot13.Left5.expected,
    Slot13.Left6.expected,
    Slot13.Left7.expected,
    Slot13.Left8.expected,
    Slot13.Left9.expected,
    Slot13.Left10.expected,
    Slot13.Left11.expected,
    Slot13.Left12.expected,
    Slot13.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 2230919921009786066388910080 }, { target := 112, numerator := 87306961982928109129049309184 }, { target := 115, numerator := 87306961982928109129049309184 }, { target := 122, numerator := 2230919921009786066388910080 }, { target := 206, numerator := 33463798815146790995833651200 }, { target := 208, numerator := 1309604429743921636935739637760 }, { target := 211, numerator := 1309604429743921636935739637760 }, { target := 218, numerator := 33463798815146790995833651200 }, { target := 241, numerator := 58747557919924366414907965440 }, { target := 243, numerator := 2299083332217106873731631808512 }, { target := 246, numerator := 2299083332217106873731631808512 }, { target := 253, numerator := 58747557919924366414907965440 }, { target := 302, numerator := 2230919921009786066388910080 }, { target := 304, numerator := 87306961982928109129049309184 }, { target := 307, numerator := 87306961982928109129049309184 }, { target := 314, numerator := 2230919921009786066388910080 }, { target := 337, numerator := 37181998683496434439815168000 }, { target := 339, numerator := 1455116033048801818817488486400 }, { target := 342, numerator := 1455116033048801818817488486400 }, { target := 349, numerator := 37181998683496434439815168000 }, { target := 363, numerator := 2230919921009786066388910080 }, { target := 365, numerator := 87306961982928109129049309184 }, { target := 368, numerator := 87306961982928109129049309184 }, { target := 375, numerator := 2230919921009786066388910080 }, { target := 473, numerator := 58747557919924366414907965440 }, { target := 475, numerator := 2299083332217106873731631808512 }, { target := 478, numerator := 2299083332217106873731631808512 }, { target := 485, numerator := 58747557919924366414907965440 }, { target := 508, numerator := 58375737933089402070509813760 }, { target := 510, numerator := 2284532171886618855543456923648 }, { target := 513, numerator := 2284532171886618855543456923648 }, { target := 520, numerator := 58375737933089402070509813760 }, { target := 569, numerator := 37181998683496434439815168000 }, { target := 571, numerator := 1455116033048801818817488486400 }, { target := 574, numerator := 1455116033048801818817488486400 }, { target := 581, numerator := 37181998683496434439815168000 }, { target := 604, numerator := 900919828101118606476721520640 }, { target := 606, numerator := 35257461480772468069947746025472 }, { target := 609, numerator := 35257461480772468069947746025472 }, { target := 616, numerator := 900919828101118606476721520640 }, { target := 630, numerator := 57632097959419473381713510400 }, { target := 632, numerator := 2255429851225642819167107153920 }, { target := 635, numerator := 2255429851225642819167107153920 }, { target := 642, numerator := 57632097959419473381713510400 }, { target := 660, numerator := 1737233395327205158617612288 }, { target := 661, numerator := 205329833883697868081240997888 }, { target := 663, numerator := 1948539193796725817790450106368 }, { target := 671, numerator := 205329974710010718859869290496 }, { target := 678, numerator := 1737233395327205158617612288 }, { target := 679, numerator := 33463798815146790995833651200 }, { target := 681, numerator := 1309604429743921636935739637760 }, { target := 684, numerator := 1309604429743921636935739637760 }, { target := 691, numerator := 33463798815146790995833651200 }, { target := 705, numerator := 58747557919924366414907965440 }, { target := 707, numerator := 2299083332217106873731631808512 }, { target := 710, numerator := 2299083332217106873731631808512 }, { target := 717, numerator := 58747557919924366414907965440 }, { target := 785, numerator := 2230919921009786066388910080 }, { target := 787, numerator := 87306961982928109129049309184 }, { target := 790, numerator := 87306961982928109129049309184 }, { target := 797, numerator := 2230919921009786066388910080 }]

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
    Slot13.Left14.expected,
    Slot13.Left15.expected,
    Slot13.Left16.expected,
    Slot13.Left17.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 1798881405143168355089252352 }, { target := 5, numerator := 43579352750403852731355758592 }, { target := 6, numerator := 33018178049240735291799502848 }, { target := 7, numerator := 36790026156798991520212451328 }, { target := 8, numerator := 1798881405143168355089252352 }, { target := 9, numerator := 36790026156798991520212451328 }, { target := 10, numerator := 36731997724375018347467636736 }, { target := 11, numerator := 1798881405143168355089252352 }, { target := 12, numerator := 43579352750403852731355758592 }, { target := 13, numerator := 1798881405143168355089252352 }, { target := 14, numerator := 4688287039027472640640024576 }, { target := 15, numerator := 822281499993000813690584301568 }, { target := 20, numerator := 822281598575481605739549556736 }, { target := 28, numerator := 4688188456546680591674769408 }, { target := 56, numerator := 92682714119301848566333440 }, { target := 57, numerator := 29855081848614139637457223680 }, { target := 59, numerator := 317521350368445836782630600704 }, { target := 67, numerator := 29855171831831731192650006528 }, { target := 74, numerator := 92682714119301848566333440 }, { target := 91, numerator := 105555313302538216422768640 }, { target := 92, numerator := 34001620994254992364881838080 }, { target := 94, numerator := 361621537919618869669107073024 }, { target := 102, numerator := 34001723475141693858295840768 }, { target := 109, numerator := 105555313302538216422768640 }, { target := 126, numerator := 1798881834029968068836327424 }, { target := 127, numerator := 43579363140532452248260706304 }, { target := 128, numerator := 33018185921388768747350654976 }, { target := 129, numerator := 36790034928225798569104244736 }, { target := 130, numerator := 1798881834029968068836327424 }, { target := 131, numerator := 36790034928225798569104244736 }, { target := 132, numerator := 36732006481966767341077266432 }, { target := 133, numerator := 1798881834029968068836327424 }, { target := 134, numerator := 43579363140532452248260706304 }, { target := 135, numerator := 1798881834029968068836327424 }, { target := 136, numerator := 17124054274953642531776102400 }, { target := 137, numerator := 3003398238622208192133935923200 }, { target := 142, numerator := 3003398598696524800701392486400 }, { target := 150, numerator := 17123694200637033964319539200 }, { target := 267, numerator := 4688285459467027484057272320 }, { target := 268, numerator := 822281222952938769538099445760 }, { target := 273, numerator := 822281321535386347539812843520 }, { target := 281, numerator := 4688186877019449482343874560 }, { target := 820, numerator := 57632097959419473381713510400 }, { target := 822, numerator := 2255429851225642819167107153920 }, { target := 825, numerator := 2255429851225642819167107153920 }, { target := 832, numerator := 57632097959419473381713510400 }, { target := 846, numerator := 2230919921009786066388910080 }, { target := 848, numerator := 87306961982928109129049309184 }, { target := 851, numerator := 87306961982928109129049309184 }, { target := 858, numerator := 2230919921009786066388910080 }, { target := 895, numerator := 58747557919924366414907965440 }, { target := 897, numerator := 2299083332217106873731631808512 }, { target := 900, numerator := 2299083332217106873731631808512 }, { target := 907, numerator := 58747557919924366414907965440 }, { target := 921, numerator := 58747557919924366414907965440 }, { target := 923, numerator := 2299083332217106873731631808512 }, { target := 926, numerator := 2299083332217106873731631808512 }, { target := 933, numerator := 58747557919924366414907965440 }, { target := 966, numerator := 2230919921009786066388910080 }, { target := 968, numerator := 87306961982928109129049309184 }, { target := 971, numerator := 87306961982928109129049309184 }, { target := 978, numerator := 2230919921009786066388910080 }]

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
    Slot16.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 152, numerator := 82384634772712754281185280 }, { target := 153, numerator := 26537850532101457455517532160 }, { target := 155, numerator := 282241200327507410473449422848 }, { target := 163, numerator := 26537930517183761060133339136 }, { target := 170, numerator := 82384634772712754281185280 }, { target := 187, numerator := 1104469009921680362082140160 }, { target := 188, numerator := 355773058695985164013031915520 }, { target := 190, numerator := 3783796091890646221659681325056 }, { target := 198, numerator := 355774130995994796712412577792 }, { target := 205, numerator := 1104469009921680362082140160 }, { target := 222, numerator := 97831753792596395708907520 }, { target := 223, numerator := 31513697506870480728427069440 }, { target := 225, numerator := 335161425388915049937221189632 }, { target := 233, numerator := 31513792489155716258908340224 }, { target := 240, numerator := 97831753792596395708907520 }, { target := 283, numerator := 82384634772712754281185280 }, { target := 284, numerator := 26537850532101457455517532160 }, { target := 286, numerator := 282241200327507410473449422848 }, { target := 294, numerator := 26537930517183761060133339136 }, { target := 301, numerator := 82384634772712754281185280 }, { target := 318, numerator := 97831753792596395708907520 }, { target := 319, numerator := 31513697506870480728427069440 }, { target := 321, numerator := 335161425388915049937221189632 }, { target := 329, numerator := 31513792489155716258908340224 }, { target := 336, numerator := 97831753792596395708907520 }, { target := 419, numerator := 95257233955949122137620480 }, { target := 420, numerator := 30684389677742310182942146560 }, { target := 422, numerator := 326341387878680443359925895168 }, { target := 430, numerator := 30684482160493723725779173376 }, { target := 437, numerator := 95257233955949122137620480 }, { target := 454, numerator := 3599178731632888452659281920 }, { target := 455, numerator := 1159372345121182422587922186240 }, { target := 457, numerator := 12330412439307979995058821660672 }, { target := 465, numerator := 1159375839469465561314575253504 }, { target := 472, numerator := 3599178731632888452659281920 }, { target := 489, numerator := 95257233955949122137620480 }, { target := 490, numerator := 30684389677742310182942146560 }, { target := 492, numerator := 326341387878680443359925895168 }, { target := 500, numerator := 30684482160493723725779173376 }, { target := 507, numerator := 95257233955949122137620480 }, { target := 550, numerator := 1104469009921680362082140160 }, { target := 551, numerator := 355773058695985164013031915520 }, { target := 553, numerator := 3783796091890646221659681325056 }, { target := 561, numerator := 355774130995994796712412577792 }, { target := 568, numerator := 1104469009921680362082140160 }, { target := 585, numerator := 3599178731632888452659281920 }, { target := 586, numerator := 1159372345121182422587922186240 }, { target := 588, numerator := 12330412439307979995058821660672 }, { target := 596, numerator := 1159375839469465561314575253504 }, { target := 603, numerator := 3599178731632888452659281920 }, { target := 660, numerator := 92682714119301848566333440 }, { target := 661, numerator := 29855081848614139637457223680 }, { target := 663, numerator := 317521350368445836782630600704 }, { target := 671, numerator := 29855171831831731192650006528 }, { target := 678, numerator := 92682714119301848566333440 }, { target := 766, numerator := 95257233955949122137620480 }, { target := 767, numerator := 30684389677742310182942146560 }, { target := 769, numerator := 326341387878680443359925895168 }, { target := 777, numerator := 30684482160493723725779173376 }, { target := 784, numerator := 95257233955949122137620480 }]

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
    Slot16.Left14.expected,
    Slot16.Left15.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left2.expected,
    Slot19.Left3.expected,
    Slot19.Left4.expected,
    Slot19.Left5.expected,
    Slot19.Left6.expected,
    Slot19.Left7.expected,
    Slot19.Left8.expected,
    Slot19.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 839218831220488955393736704 }, { target := 6, numerator := 37931164430082189027499311104 }, { target := 11, numerator := 843697995829490813878927360 }, { target := 14, numerator := 9509605552960508493037568 }, { target := 15, numerator := 1886086079602778037446246400 }, { target := 20, numerator := 1886086079602778037446246400 }, { target := 28, numerator := 9509605552960508493037568 }, { target := 40, numerator := 190192111059210169860751360 }, { target := 41, numerator := 37721721592055560748924928000 }, { target := 46, numerator := 37721721592055560748924928000 }, { target := 54, numerator := 190192111059210169860751360 }, { target := 75, numerator := 9849234322709098082074624 }, { target := 76, numerator := 1953446296731448681640755200 }, { target := 81, numerator := 1953446296731448681640755200 }, { target := 89, numerator := 9849234322709098082074624 }, { target := 126, numerator := 839218831220488955393736704 }, { target := 128, numerator := 37931164430082189027499311104 }, { target := 133, numerator := 843697995829490813878927360 }, { target := 136, numerator := 176946589039015175888306176 }, { target := 137, numerator := 35094673124037405625339084800 }, { target := 142, numerator := 35094673124037405625339084800 }, { target := 150, numerator := 176946589039015175888306176 }, { target := 171, numerator := 264910440403899879448903680 }, { target := 172, numerator := 52540969360363102471716864000 }, { target := 177, numerator := 52540969360363102471716864000 }, { target := 185, numerator := 264910440403899879448903680 }, { target := 267, numerator := 9509605552960508493037568 }, { target := 268, numerator := 1886086079602778037446246400 }, { target := 273, numerator := 1886086079602778037446246400 }, { target := 281, numerator := 9509605552960508493037568 }, { target := 403, numerator := 265250069173648469037940736 }, { target := 404, numerator := 52608329577491773115911372800 }, { target := 409, numerator := 52608329577491773115911372800 }, { target := 417, numerator := 265250069173648469037940736 }, { target := 438, numerator := 265250069173648469037940736 }, { target := 439, numerator := 52608329577491773115911372800 }, { target := 444, numerator := 52608329577491773115911372800 }, { target := 452, numerator := 265250069173648469037940736 }, { target := 534, numerator := 189852482289461580271714304 }, { target := 535, numerator := 37654361374926890104730419200 }, { target := 540, numerator := 37654361374926890104730419200 }, { target := 548, numerator := 189852482289461580271714304 }, { target := 750, numerator := 9849234322709098082074624 }, { target := 751, numerator := 1953446296731448681640755200 }, { target := 756, numerator := 1953446296731448681640755200 }, { target := 764, numerator := 9849234322709098082074624 }, { target := 801, numerator := 95257233955949122137620480 }, { target := 802, numerator := 30684389677742310182942146560 }, { target := 804, numerator := 326341387878680443359925895168 }, { target := 812, numerator := 30684482160493723725779173376 }, { target := 819, numerator := 95257233955949122137620480 }, { target := 876, numerator := 105555313302538216422768640 }, { target := 877, numerator := 34001620994254992364881838080 }, { target := 879, numerator := 361621537919618869669107073024 }, { target := 887, numerator := 34001723475141693858295840768 }, { target := 894, numerator := 105555313302538216422768640 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent1
