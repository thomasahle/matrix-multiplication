import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk10Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 44; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent2

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
  [{ target := 131, numerator := 28616798427799513277682155520 }, { target := 134, numerator := 104085464513777090517427814400 }, { target := 136, numerator := 28616798427799513277682155520 }, { target := 227, numerator := 763114624741320354071524147200 }, { target := 230, numerator := 2775612387034055747131408384000 }, { target := 232, numerator := 763114624741320354071524147200 }, { target := 253, numerator := 729728359908887588580894965760 }, { target := 256, numerator := 2654179345101315808194409267200 }, { target := 258, numerator := 729728359908887588580894965760 }, { target := 263, numerator := 135061224768443995067410022400 }, { target := 265, numerator := 135061160366248747728937943040 }, { target := 302, numerator := 23847332023166261064735129600 }, { target := 305, numerator := 86737887094814242097856512000 }, { target := 307, numerator := 23847332023166261064735129600 }, { target := 328, numerator := 748806225527420597432683069440 }, { target := 331, numerator := 2723569654777167201872694476800 }, { target := 333, numerator := 748806225527420597432683069440 }, { target := 338, numerator := 138920116904685252069336023040 }, { target := 340, numerator := 138920050662427283378336169984 }, { target := 342, numerator := 23847332023166261064735129600 }, { target := 345, numerator := 86737887094814242097856512000 }, { target := 347, numerator := 23847332023166261064735129600 }, { target := 352, numerator := 135061224768443995067410022400 }, { target := 354, numerator := 135061160366248747728937943040 }, { target := 356, numerator := 3384992294920961689177292800 }, { target := 443, numerator := 729728359908887588580894965760 }, { target := 446, numerator := 2654179345101315808194409267200 }, { target := 448, numerator := 729728359908887588580894965760 }, { target := 479, numerator := 119625656223478967059706019840 }, { target := 481, numerator := 119625599181534605131345035264 }, { target := 554, numerator := 5599252489686063909794626928640 }, { target := 556, numerator := 5599249819755055227276827295744 }, { target := 568, numerator := 1524262393815296515760770252800 }, { target := 570, numerator := 1524261666990521581512299642880 }, { target := 572, numerator := 67835245590216072251112947712 }, { target := 599, numerator := 138920116904685252069336023040 }, { target := 601, numerator := 138920050662427283378336169984 }, { target := 613, numerator := 5599252489686063909794626928640 }, { target := 615, numerator := 5599249819755055227276827295744 }, { target := 617, numerator := 113871140801141151223924129792 }, { target := 618, numerator := 135061224768443995067410022400 }, { target := 620, numerator := 135061160366248747728937943040 }, { target := 622, numerator := 109267551280048643326643011584 }, { target := 694, numerator := 135061224768443995067410022400 }, { target := 696, numerator := 135061160366248747728937943040 }, { target := 708, numerator := 115766764087237710057780019200 }, { target := 710, numerator := 115766708885356069481946808320 }, { target := 712, numerator := 3384992294920961689177292800 }, { target := 739, numerator := 135061224768443995067410022400 }, { target := 741, numerator := 135061160366248747728937943040 }, { target := 753, numerator := 1524262393815296515760770252800 }, { target := 755, numerator := 1524261666990521581512299642880 }, { target := 757, numerator := 109267551280048643326643011584 }, { target := 758, numerator := 115766764087237710057780019200 }, { target := 760, numerator := 115766708885356069481946808320 }, { target := 762, numerator := 72980433878495934018662432768 }, { target := 773, numerator := 135061224768443995067410022400 }, { target := 775, numerator := 135061160366248747728937943040 }, { target := 777, numerator := 3520391986717800156744384512 }, { target := 778, numerator := 119625656223478967059706019840 }, { target := 780, numerator := 119625599181534605131345035264 }, { target := 782, numerator := 67835245590216072251112947712 }, { target := 783, numerator := 3249592603124123221610201088 }]

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
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected,
    Slot3.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 2888519281252289431159701504 }, { target := 82, numerator := 106669174195503864897412792320 }, { target := 85, numerator := 106669148074914256524687704064 }, { target := 92, numerator := 2888545401841897803884789760 }, { target := 115, numerator := 2828341796226200068010541056 }, { target := 117, numerator := 104446899733097534378716692480 }, { target := 120, numerator := 104446874156686876180423376896 }, { target := 127, numerator := 2828367372636858266303856640 }, { target := 176, numerator := 2226566945965306436518936576 }, { target := 178, numerator := 82224155109034229191755694080 }, { target := 181, numerator := 82224134974413072737780105216 }, { target := 188, numerator := 2226587080586462890494525440 }, { target := 211, numerator := 69986415085341929342473601024 }, { target := 213, numerator := 2584505199778562393243564113920 }, { target := 216, numerator := 2584504566898443340379412496384 }, { target := 223, numerator := 69987047965460982206625218560 }, { target := 237, numerator := 2226566945965306436518936576 }, { target := 239, numerator := 82224155109034229191755694080 }, { target := 242, numerator := 82224134974413072737780105216 }, { target := 249, numerator := 2226587080586462890494525440 }, { target := 286, numerator := 2226566945965306436518936576 }, { target := 288, numerator := 82224155109034229191755694080 }, { target := 291, numerator := 82224134974413072737780105216 }, { target := 298, numerator := 2226587080586462890494525440 }, { target := 312, numerator := 2286744430991395799668097024 }, { target := 314, numerator := 84446429571440559710451793920 }, { target := 317, numerator := 84446408892640453082044432384 }, { target := 324, numerator := 2286765109791502428075458560 }, { target := 469, numerator := 414943577203092942526391255040 }, { target := 472, numerator := 1509239235449767812502703308800 }, { target := 474, numerator := 414943577203092942526391255040 }, { target := 518, numerator := 748806225527420597432683069440 }, { target := 521, numerator := 2723569654777167201872694476800 }, { target := 523, numerator := 748806225527420597432683069440 }, { target := 544, numerator := 11689962157756101173933160529920 }, { target := 547, numerator := 42518912253877941476369262182400 }, { target := 549, numerator := 11689962157756101173933160529920 }, { target := 558, numerator := 457868774844792212442914488320 }, { target := 561, numerator := 1665367432220433448278845030400 }, { target := 563, numerator := 457868774844792212442914488320 }, { target := 589, numerator := 763114624741320354071524147200 }, { target := 592, numerator := 2775612387034055747131408384000 }, { target := 594, numerator := 763114624741320354071524147200 }, { target := 603, numerator := 729728359908887588580894965760 }, { target := 606, numerator := 2654179345101315808194409267200 }, { target := 608, numerator := 729728359908887588580894965760 }, { target := 658, numerator := 23847332023166261064735129600 }, { target := 661, numerator := 86737887094814242097856512000 }, { target := 663, numerator := 23847332023166261064735129600 }, { target := 684, numerator := 457868774844792212442914488320 }, { target := 687, numerator := 1665367432220433448278845030400 }, { target := 689, numerator := 457868774844792212442914488320 }, { target := 698, numerator := 23847332023166261064735129600 }, { target := 701, numerator := 86737887094814242097856512000 }, { target := 703, numerator := 23847332023166261064735129600 }, { target := 729, numerator := 734497826313520840793841991680 }, { target := 732, numerator := 2671526922520278656613980569600 }, { target := 734, numerator := 734497826313520840793841991680 }, { target := 743, numerator := 414943577203092942526391255040 }, { target := 746, numerator := 1509239235449767812502703308800 }, { target := 748, numerator := 414943577203092942526391255040 }, { target := 763, numerator := 28616798427799513277682155520 }, { target := 766, numerator := 104085464513777090517427814400 }, { target := 768, numerator := 28616798427799513277682155520 }]

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
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot3.Left10.expected,
    Slot3.Left11.expected,
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot4.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 4391800829068770048737280 }, { target := 27, numerator := 73782253928355336818786304 }, { target := 28, numerator := 159861550178103229774036992 }, { target := 29, numerator := 5270160994882524058484736 }, { target := 30, numerator := 84322575918120384935755776 }, { target := 31, numerator := 6148521160696278068232192 }, { target := 32, numerator := 159861550178103229774036992 }, { target := 33, numerator := 159861550178103229774036992 }, { target := 34, numerator := 84322575918120384935755776 }, { target := 35, numerator := 1972796932417691505892786176 }, { target := 36, numerator := 158104829846475721754542080 }, { target := 37, numerator := 73782253928355336818786304 }, { target := 38, numerator := 159861550178103229774036992 }, { target := 39, numerator := 6148521160696278068232192 }, { target := 40, numerator := 158104829846475721754542080 }, { target := 41, numerator := 6148521160696278068232192 }, { target := 42, numerator := 159861550178103229774036992 }, { target := 43, numerator := 159861550178103229774036992 }, { target := 44, numerator := 5270160994882524058484736 }, { target := 392, numerator := 2286744430991395799668097024 }, { target := 394, numerator := 84446429571440559710451793920 }, { target := 397, numerator := 84446408892640453082044432384 }, { target := 404, numerator := 2286765109791502428075458560 }, { target := 427, numerator := 38694122871775460504910168064 }, { target := 429, numerator := 1428922479327270523521592197120 }, { target := 432, numerator := 1428922129420205561361962369024 }, { target := 439, numerator := 38694472778840422664539996160 }, { target := 453, numerator := 2106211975913127710220615680 }, { target := 455, numerator := 77779606184221568154363494400 }, { target := 458, numerator := 77779587137958312049251450880 }, { target := 465, numerator := 2106231022176383815332659200 }, { target := 502, numerator := 69986415085341929342473601024 }, { target := 504, numerator := 2584505199778562393243564113920 }, { target := 507, numerator := 2584504566898443340379412496384 }, { target := 514, numerator := 69987047965460982206625218560 }, { target := 528, numerator := 38694122871775460504910168064 }, { target := 530, numerator := 1428922479327270523521592197120 }, { target := 533, numerator := 1428922129420205561361962369024 }, { target := 540, numerator := 38694472778840422664539996160 }, { target := 573, numerator := 2888519281252289431159701504 }, { target := 575, numerator := 106669174195503864897412792320 }, { target := 578, numerator := 106669148074914256524687704064 }, { target := 585, numerator := 2888545401841897803884789760 }, { target := 642, numerator := 2226566945965306436518936576 }, { target := 644, numerator := 82224155109034229191755694080 }, { target := 647, numerator := 82224134974413072737780105216 }, { target := 654, numerator := 2226587080586462890494525440 }, { target := 668, numerator := 2106211975913127710220615680 }, { target := 670, numerator := 77779606184221568154363494400 }, { target := 673, numerator := 77779587137958312049251450880 }, { target := 680, numerator := 2106231022176383815332659200 }, { target := 713, numerator := 2828341796226200068010541056 }, { target := 715, numerator := 104446899733097534378716692480 }, { target := 718, numerator := 104446874156686876180423376896 }, { target := 725, numerator := 2828367372636858266303856640 }]

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
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 61, numerator := 107669955809427910872268800 }, { target := 62, numerator := 1808855257598388902654115840 }, { target := 63, numerator := 3919186391463175955750584320 }, { target := 64, numerator := 129203946971313493046722560 }, { target := 65, numerator := 2067263151541015888747560960 }, { target := 66, numerator := 150737938133199075221176320 }, { target := 67, numerator := 3919186391463175955750584320 }, { target := 68, numerator := 3919186391463175955750584320 }, { target := 69, numerator := 2067263151541015888747560960 }, { target := 70, numerator := 48365344149595017563823144960 }, { target := 71, numerator := 3876118409139404791401676800 }, { target := 72, numerator := 1808855257598388902654115840 }, { target := 73, numerator := 3919186391463175955750584320 }, { target := 74, numerator := 150737938133199075221176320 }, { target := 75, numerator := 3876118409139404791401676800 }, { target := 76, numerator := 150737938133199075221176320 }, { target := 77, numerator := 3919186391463175955750584320 }, { target := 78, numerator := 3919186391463175955750584320 }, { target := 79, numerator := 129203946971313493046722560 }, { target := 96, numerator := 4391800829068770048737280 }, { target := 97, numerator := 73782253928355336818786304 }, { target := 98, numerator := 159861550178103229774036992 }, { target := 99, numerator := 5270160994882524058484736 }, { target := 100, numerator := 84322575918120384935755776 }, { target := 101, numerator := 6148521160696278068232192 }, { target := 102, numerator := 159861550178103229774036992 }, { target := 103, numerator := 159861550178103229774036992 }, { target := 104, numerator := 84322575918120384935755776 }, { target := 105, numerator := 1972796932417691505892786176 }, { target := 106, numerator := 158104829846475721754542080 }, { target := 107, numerator := 73782253928355336818786304 }, { target := 108, numerator := 159861550178103229774036992 }, { target := 109, numerator := 6148521160696278068232192 }, { target := 110, numerator := 158104829846475721754542080 }, { target := 111, numerator := 6148521160696278068232192 }, { target := 112, numerator := 159861550178103229774036992 }, { target := 113, numerator := 159861550178103229774036992 }, { target := 114, numerator := 5270160994882524058484736 }, { target := 157, numerator := 90244423487638920033730560 }, { target := 158, numerator := 1516106314592333856566673408 }, { target := 159, numerator := 3284897014950056689227792384 }, { target := 160, numerator := 108293308185166704040476672 }, { target := 161, numerator := 1732692930962667264647626752 }, { target := 162, numerator := 126342192882694488047222784 }, { target := 163, numerator := 3284897014950056689227792384 }, { target := 164, numerator := 3284897014950056689227792384 }, { target := 165, numerator := 1732692930962667264647626752 }, { target := 166, numerator := 40537795030647402879151767552 }, { target := 167, numerator := 3248799245555001121214300160 }, { target := 168, numerator := 1516106314592333856566673408 }, { target := 169, numerator := 3284897014950056689227792384 }, { target := 170, numerator := 126342192882694488047222784 }, { target := 171, numerator := 3248799245555001121214300160 }, { target := 172, numerator := 126342192882694488047222784 }, { target := 173, numerator := 3284897014950056689227792384 }, { target := 174, numerator := 3284897014950056689227792384 }, { target := 175, numerator := 108293308185166704040476672 }]

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
    Slot4.Left4.expected,
    Slot4.Left5.expected,
    Slot4.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 192, numerator := 88686042548291937113210880 }, { target := 193, numerator := 1489925514811304543501942784 }, { target := 194, numerator := 3228171948757826510920876032 }, { target := 195, numerator := 106423251057950324535853056 }, { target := 196, numerator := 1702772016927205192573648896 }, { target := 197, numerator := 124160459567608711958495232 }, { target := 198, numerator := 3228171948757826510920876032 }, { target := 199, numerator := 3228171948757826510920876032 }, { target := 200, numerator := 1702772016927205192573648896 }, { target := 201, numerator := 39837770312692738151254327296 }, { target := 202, numerator := 3192697531738509736075591680 }, { target := 203, numerator := 1489925514811304543501942784 }, { target := 204, numerator := 3228171948757826510920876032 }, { target := 205, numerator := 124160459567608711958495232 }, { target := 206, numerator := 3192697531738509736075591680 }, { target := 207, numerator := 124160459567608711958495232 }, { target := 208, numerator := 3228171948757826510920876032 }, { target := 209, numerator := 3228171948757826510920876032 }, { target := 210, numerator := 106423251057950324535853056 }, { target := 267, numerator := 4391800829068770048737280 }, { target := 268, numerator := 73782253928355336818786304 }, { target := 269, numerator := 159861550178103229774036992 }, { target := 270, numerator := 5270160994882524058484736 }, { target := 271, numerator := 84322575918120384935755776 }, { target := 272, numerator := 6148521160696278068232192 }, { target := 273, numerator := 159861550178103229774036992 }, { target := 274, numerator := 159861550178103229774036992 }, { target := 275, numerator := 84322575918120384935755776 }, { target := 276, numerator := 1972796932417691505892786176 }, { target := 277, numerator := 158104829846475721754542080 }, { target := 278, numerator := 73782253928355336818786304 }, { target := 279, numerator := 159861550178103229774036992 }, { target := 280, numerator := 6148521160696278068232192 }, { target := 281, numerator := 158104829846475721754542080 }, { target := 282, numerator := 6148521160696278068232192 }, { target := 283, numerator := 159861550178103229774036992 }, { target := 284, numerator := 159861550178103229774036992 }, { target := 285, numerator := 5270160994882524058484736 }, { target := 373, numerator := 88827713542778026469621760 }, { target := 374, numerator := 1492305587518670844689645568 }, { target := 375, numerator := 3233328772957120163494232064 }, { target := 376, numerator := 106593256251333631763546112 }, { target := 377, numerator := 1705492100021338108216737792 }, { target := 378, numerator := 124358798959889237057470464 }, { target := 379, numerator := 3233328772957120163494232064 }, { target := 380, numerator := 3233328772957120163494232064 }, { target := 381, numerator := 1705492100021338108216737792 }, { target := 382, numerator := 39901408923415889490154094592 }, { target := 383, numerator := 3197797687540008952906383360 }, { target := 384, numerator := 1492305587518670844689645568 }, { target := 385, numerator := 3233328772957120163494232064 }, { target := 386, numerator := 124358798959889237057470464 }, { target := 387, numerator := 3197797687540008952906383360 }, { target := 388, numerator := 124358798959889237057470464 }, { target := 389, numerator := 3233328772957120163494232064 }, { target := 390, numerator := 3233328772957120163494232064 }, { target := 391, numerator := 106593256251333631763546112 }]

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
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left7.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 263, numerator := 105897332908669339322516766720 }, { target := 265, numerator := 105897332908669339322516766720 }, { target := 338, numerator := 8866692071831766893146335608832 }, { target := 340, numerator := 8866692071831766893146335608832 }, { target := 356, numerator := 20339123827290455933548756992 }, { target := 408, numerator := 79619098901182218302914560 }, { target := 409, numerator := 1337600861539861267488964608 }, { target := 410, numerator := 2898135200003032746226089984 }, { target := 411, numerator := 95542918681418661963497472 }, { target := 412, numerator := 1528686698902698591415959552 }, { target := 413, numerator := 111466738461655105624080384 }, { target := 414, numerator := 2898135200003032746226089984 }, { target := 415, numerator := 2898135200003032746226089984 }, { target := 416, numerator := 1528686698902698591415959552 }, { target := 417, numerator := 35764899226411052461669220352 }, { target := 418, numerator := 2866287560442559858904924160 }, { target := 419, numerator := 1337600861539861267488964608 }, { target := 420, numerator := 2898135200003032746226089984 }, { target := 421, numerator := 111466738461655105624080384 }, { target := 422, numerator := 2866287560442559858904924160 }, { target := 423, numerator := 111466738461655105624080384 }, { target := 424, numerator := 2898135200003032746226089984 }, { target := 425, numerator := 2898135200003032746226089984 }, { target := 426, numerator := 95542918681418661963497472 }, { target := 483, numerator := 107669955809427910872268800 }, { target := 484, numerator := 1808855257598388902654115840 }, { target := 485, numerator := 3919186391463175955750584320 }, { target := 486, numerator := 129203946971313493046722560 }, { target := 487, numerator := 2067263151541015888747560960 }, { target := 488, numerator := 150737938133199075221176320 }, { target := 489, numerator := 3919186391463175955750584320 }, { target := 490, numerator := 3919186391463175955750584320 }, { target := 491, numerator := 2067263151541015888747560960 }, { target := 492, numerator := 48365344149595017563823144960 }, { target := 493, numerator := 3876118409139404791401676800 }, { target := 494, numerator := 1808855257598388902654115840 }, { target := 495, numerator := 3919186391463175955750584320 }, { target := 496, numerator := 150737938133199075221176320 }, { target := 497, numerator := 3876118409139404791401676800 }, { target := 498, numerator := 150737938133199075221176320 }, { target := 499, numerator := 3919186391463175955750584320 }, { target := 500, numerator := 3919186391463175955750584320 }, { target := 501, numerator := 129203946971313493046722560 }, { target := 617, numerator := 197006239888212100913534337024 }, { target := 623, numerator := 4391800829068770048737280 }, { target := 624, numerator := 73782253928355336818786304 }, { target := 625, numerator := 159861550178103229774036992 }, { target := 626, numerator := 5270160994882524058484736 }, { target := 627, numerator := 84322575918120384935755776 }, { target := 628, numerator := 6148521160696278068232192 }, { target := 629, numerator := 159861550178103229774036992 }, { target := 630, numerator := 159861550178103229774036992 }, { target := 631, numerator := 84322575918120384935755776 }, { target := 632, numerator := 1972796932417691505892786176 }, { target := 633, numerator := 158104829846475721754542080 }, { target := 634, numerator := 73782253928355336818786304 }, { target := 635, numerator := 159861550178103229774036992 }, { target := 636, numerator := 6148521160696278068232192 }, { target := 637, numerator := 158104829846475721754542080 }, { target := 638, numerator := 6148521160696278068232192 }, { target := 639, numerator := 159861550178103229774036992 }, { target := 640, numerator := 159861550178103229774036992 }, { target := 641, numerator := 5270160994882524058484736 }, { target := 777, numerator := 20339123827290455933548756992 }]

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
    Slot6.Left6.expected,
    Slot6.Left14.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 2879246528623622023838433280 }, { target := 27, numerator := 459663626429790450411854888960 }, { target := 29, numerator := 4586751749201293491358253711360 }, { target := 37, numerator := 459663626429790450411854888960 }, { target := 44, numerator := 2878917997527247808637173760 }, { target := 80, numerator := 82279909675816790051273048064 }, { target := 82, numerator := 3091467577613972113360733339648 }, { target := 85, numerator := 3091233763380770956560664887296 }, { target := 92, numerator := 82513723909017946851341500416 }, { target := 131, numerator := 75195442909161445255062487040 }, { target := 134, numerator := 258132807529950475135108513792 }, { target := 136, numerator := 75195442909161445255062487040 }, { target := 157, numerator := 9844338958416788439796023296 }, { target := 158, numerator := 1571621082267336000908686262272 }, { target := 160, numerator := 15682414995854340621388535037952 }, { target := 168, numerator := 1571621082267336000908686262272 }, { target := 175, numerator := 9843215688339378947733061632 }, { target := 176, numerator := 2879591697632695119170336980992 }, { target := 178, numerator := 108193657541341754191251236716544 }, { target := 181, numerator := 108185474626127491442333437657088 }, { target := 188, numerator := 2887774612846957868088136040448 }, { target := 227, numerator := 7884106568995376655957030338560 }, { target := 230, numerator := 27064759309664887388042153689088 }, { target := 232, numerator := 7884106568995376655957030338560 }, { target := 267, numerator := 2879245598622417672483110912 }, { target := 268, numerator := 459663477957708630946987638784 }, { target := 270, numerator := 4586750267673189381068233375744 }, { target := 278, numerator := 459663477957708630946987638784 }, { target := 285, numerator := 2878917067632159523501768704 }, { target := 286, numerator := 2879593109963303673611811815424 }, { target := 288, numerator := 108193710606230892021036947079168 }, { target := 291, numerator := 108185527687003219442590166286336 }, { target := 298, numerator := 2887776029190976252058592608256 }, { target := 302, numerator := 84982788658525326481324769280000 }, { target := 305, numerator := 291731054163082775740802924544000 }, { target := 307, numerator := 84982788658525326481324769280000 }, { target := 573, numerator := 82279203510512512830535630848 }, { target := 575, numerator := 3091441045169403198467878158336 }, { target := 578, numerator := 3091207232942906956432300572672 }, { target := 585, numerator := 82513015737008754866113216512 }, { target := 589, numerator := 7884112583187403302477485834240 }, { target := 592, numerator := 27064779955334529070076476260352 }, { target := 594, numerator := 7884112583187403302477485834240 }, { target := 599, numerator := 8866695280679792003070258315264 }, { target := 601, numerator := 8866695280679792003070258315264 }, { target := 763, numerator := 75195442909161445255062487040 }, { target := 766, numerator := 258132807529950475135108513792 }, { target := 768, numerator := 75195442909161445255062487040 }, { target := 773, numerator := 105894124060644229398594060288 }, { target := 775, numerator := 105894124060644229398594060288 }]

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
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left6.expected,
    Slot12.Left14.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 1305935142616521799158988800 }, { target := 11, numerator := 1015727333146183621568102400 }, { target := 12, numerator := 1160831237881352710363545600 }, { target := 13, numerator := 1363976704510589434677166080 }, { target := 14, numerator := 16106533425603768856294195200 }, { target := 15, numerator := 36217934621898204563342622720 }, { target := 16, numerator := 1015727333146183621568102400 }, { target := 17, numerator := 16106533425603768856294195200 }, { target := 18, numerator := 1160831237881352710363545600 }, { target := 19, numerator := 1131810456934318892604456960 }, { target := 20, numerator := 1131810456934318892604456960 }, { target := 21, numerator := 1131810456934318892604456960 }, { target := 22, numerator := 36217934621898204563342622720 }, { target := 23, numerator := 1131810456934318892604456960 }, { target := 24, numerator := 1305935142616521799158988800 }, { target := 25, numerator := 1363976704510589434677166080 }, { target := 80, numerator := 235740591180988899740086173696 }, { target := 82, numerator := 8543317054811006573281208696832 }, { target := 85, numerator := 8543320194446681285460681031680 }, { target := 92, numerator := 235737451545314187560613838848 }, { target := 131, numerator := 31795983007649311066322632704 }, { target := 134, numerator := 107779795225554389231640510464 }, { target := 136, numerator := 31795983007649311066322632704 }, { target := 141, numerator := 1305344627751077218206351360 }, { target := 142, numerator := 1015268043806393391938273280 }, { target := 143, numerator := 1160306335778735305072312320 }, { target := 144, numerator := 1363359944540013983459966976 }, { target := 145, numerator := 16099250408929952357878333440 }, { target := 146, numerator := 36201557676296541518256144384 }, { target := 147, numerator := 1015268043806393391938273280 }, { target := 148, numerator := 16099250408929952357878333440 }, { target := 149, numerator := 1160306335778735305072312320 }, { target := 150, numerator := 1131298677384266922445504512 }, { target := 151, numerator := 1131298677384266922445504512 }, { target := 152, numerator := 1131298677384266922445504512 }, { target := 153, numerator := 36201557676296541518256144384 }, { target := 154, numerator := 1131298677384266922445504512 }, { target := 155, numerator := 1305344627751077218206351360 }, { target := 156, numerator := 1363359944540013983459966976 }, { target := 176, numerator := 8543317054811006573281208696832 }, { target := 178, numerator := 309612637914308787033456607494144 }, { target := 181, numerator := 309612751695744861690822981058560 }, { target := 188, numerator := 8543203273374931915914835132416 }, { target := 227, numerator := 4696100295661403240437502705664 }, { target := 230, numerator := 15918511722165841413029257805824 }, { target := 232, numerator := 4696100295661403240437502705664 }, { target := 263, numerator := 22114063048808875044278108160 }, { target := 265, numerator := 22114063048808875044278108160 }, { target := 302, numerator := 48946668013240189621196984156160 }, { target := 305, numerator := 165915985493232832206219048386560 }, { target := 307, numerator := 48946668013240189621196984156160 }, { target := 338, numerator := 1859554796664969142802390712320 }, { target := 340, numerator := 1859554796664969142802390712320 }, { target := 589, numerator := 4696100295661403240437502705664 }, { target := 592, numerator := 15918511722165841413029257805824 }, { target := 594, numerator := 4696100295661403240437502705664 }, { target := 599, numerator := 1859554348040153270186095411200 }, { target := 601, numerator := 1859554348040153270186095411200 }, { target := 763, numerator := 31795983007649311066322632704 }, { target := 766, numerator := 107779795225554389231640510464 }, { target := 768, numerator := 31795983007649311066322632704 }, { target := 773, numerator := 22114511673624747660573409280 }, { target := 775, numerator := 22114511673624747660573409280 }]

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
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
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
    Slot18.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 22579622270889061887315542016 }, { target := 11, numerator := 1898703318700021124756125253632 }, { target := 16, numerator := 1898702860630472286400539525120 }, { target := 24, numerator := 22580080340437900242901270528 }, { target := 26, numerator := 31827995072091948177892048896 }, { target := 27, numerator := 4700828310054216130687125159936 }, { target := 29, numerator := 48995947316550776270702342307840 }, { target := 37, numerator := 4700828310054216130687125159936 }, { target := 44, numerator := 31827995072091948177892048896 }, { target := 141, numerator := 22579622270889061887315542016 }, { target := 142, numerator := 1898703318700021124756125253632 }, { target := 147, numerator := 1898702860630472286400539525120 }, { target := 155, numerator := 22580080340437900242901270528 }, { target := 157, numerator := 107888307478487240366029275136 }, { target := 158, numerator := 15934538414058281223160674123776 }, { target := 160, numerator := 166083029022548948825606130237440 }, { target := 168, numerator := 15934538414058281223160674123776 }, { target := 175, numerator := 107888307478487240366029275136 }, { target := 263, numerator := 1305935142616521799158988800 }, { target := 265, numerator := 1305344627751077218206351360 }, { target := 267, numerator := 31827995072091948177892048896 }, { target := 268, numerator := 4700828310054216130687125159936 }, { target := 270, numerator := 48995947316550776270702342307840 }, { target := 278, numerator := 4700828310054216130687125159936 }, { target := 285, numerator := 31827995072091948177892048896 }, { target := 286, numerator := 8543320194446681285460681031680 }, { target := 288, numerator := 309612751695744861690822981058560 }, { target := 291, numerator := 309612865477222750581879629414400 }, { target := 298, numerator := 8543206412968792394404032675840 }, { target := 338, numerator := 1015727333146183621568102400 }, { target := 340, numerator := 1015268043806393391938273280 }, { target := 352, numerator := 1160831237881352710363545600 }, { target := 354, numerator := 1160306335778735305072312320 }, { target := 479, numerator := 1363976704510589434677166080 }, { target := 481, numerator := 1363359944540013983459966976 }, { target := 554, numerator := 16106533425603768856294195200 }, { target := 556, numerator := 16099250408929952357878333440 }, { target := 568, numerator := 36217934621898204563342622720 }, { target := 570, numerator := 36201557676296541518256144384 }, { target := 573, numerator := 235737451545314187560613838848 }, { target := 575, numerator := 8543203273374931915914835132416 }, { target := 578, numerator := 8543206412968792394404032675840 }, { target := 585, numerator := 235734311951453709071416295424 }, { target := 599, numerator := 1015727333146183621568102400 }, { target := 601, numerator := 1015268043806393391938273280 }, { target := 613, numerator := 16106533425603768856294195200 }, { target := 615, numerator := 16099250408929952357878333440 }, { target := 618, numerator := 1160831237881352710363545600 }, { target := 620, numerator := 1160306335778735305072312320 }, { target := 694, numerator := 1131810456934318892604456960 }, { target := 696, numerator := 1131298677384266922445504512 }, { target := 708, numerator := 1131810456934318892604456960 }, { target := 710, numerator := 1131298677384266922445504512 }, { target := 739, numerator := 1131810456934318892604456960 }, { target := 741, numerator := 1131298677384266922445504512 }, { target := 753, numerator := 36217934621898204563342622720 }, { target := 755, numerator := 36201557676296541518256144384 }, { target := 758, numerator := 1131810456934318892604456960 }, { target := 760, numerator := 1131298677384266922445504512 }, { target := 773, numerator := 1305935142616521799158988800 }, { target := 775, numerator := 1305344627751077218206351360 }, { target := 778, numerator := 1363976704510589434677166080 }, { target := 780, numerator := 1363359944540013983459966976 }]

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
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left3.expected,
    Slot19.Left11.expected,
    Slot19.Left18.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot23.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 20339123827290455933548756992 }, { target := 2, numerator := 197006239888212100913534337024 }, { target := 7, numerator := 20339123827290455933548756992 }, { target := 10, numerator := 107066177642760612383471697920 }, { target := 11, numerator := 8964558430240506042077310615552 }, { target := 16, numerator := 8964561674506279773523572424704 }, { target := 24, numerator := 107062933376986880937209888768 }, { target := 26, numerator := 75336726441148596402383749120 }, { target := 27, numerator := 7898919892509893189636383047680 }, { target := 29, numerator := 85142461480112380859740323840000 }, { target := 37, numerator := 7898925918001890402193081630720 }, { target := 44, numerator := 75336726441148596402383749120 }, { target := 80, numerator := 82251379887440986726012551168 }, { target := 82, numerator := 2878593226170270467603356975104 }, { target := 85, numerator := 2878594638011166605763818815488 }, { target := 92, numerator := 82250673966992917645781630976 }, { target := 131, numerator := 2925070080803308315995013120 }, { target := 134, numerator := 10001012787993713454752989184 }, { target := 136, numerator := 2925069136001023789286555648 }, { target := 141, numerator := 107066177642760612383471697920 }, { target := 142, numerator := 8964558430240506042077310615552 }, { target := 147, numerator := 8964561674506279773523572424704 }, { target := 155, numerator := 107062933376986880937209888768 }, { target := 157, numerator := 258617809191735322103854923776 }, { target := 158, numerator := 27115610859169966667713283620864 }, { target := 160, numerator := 292279183040683596102796050432000 }, { target := 168, numerator := 27115631543630431494980507795456 }, { target := 175, numerator := 258617809191735322103854923776 }, { target := 176, numerator := 3090395640173745354652910616576 }, { target := 178, numerator := 108156142403498015718924173180928 }, { target := 181, numerator := 108156195449987400033512315682816 }, { target := 188, numerator := 3090369116929053197358839365632 }, { target := 227, numerator := 466979227911431677739364515840 }, { target := 230, numerator := 1596633619385649040710946521088 }, { target := 232, numerator := 466979077076398953985931739136 }, { target := 267, numerator := 75336726441148596402383749120 }, { target := 268, numerator := 7898919892509893189636383047680 }, { target := 270, numerator := 85142461480112380859740323840000 }, { target := 278, numerator := 7898925918001890402193081630720 }, { target := 285, numerator := 75336726441148596402383749120 }, { target := 286, numerator := 3090161907013440592151316529152 }, { target := 288, numerator := 108147962325632995086077427449856 }, { target := 291, numerator := 108148015368110361183421445701632 }, { target := 298, numerator := 3090135385774757543479307403264 }, { target := 302, numerator := 4659750450780093918276422205440 }, { target := 305, numerator := 15932002502419661692285965303808 }, { target := 307, numerator := 4659748945673293190846507646976 }, { target := 573, numerator := 82485113047745749227606638592 }, { target := 575, numerator := 2886773304035291100450102706176 }, { target := 578, numerator := 2886774719888205455854688796672 }, { target := 585, numerator := 82484405121288571525313593344 }, { target := 589, numerator := 466979227911431677739364515840 }, { target := 592, numerator := 1596633619385649040710946521088 }, { target := 594, numerator := 466979077076398953985931739136 }, { target := 763, numerator := 2924736321095320718058455040 }, { target := 766, numerator := 9999871640938944660429078528 }, { target := 768, numerator := 2924735376400841107430178816 }]

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
    Slot24.Left0.expected,
    Slot24.Left1.expected,
    Slot24.Left2.expected,
    Slot24.Left3.expected,
    Slot24.Left4.expected,
    Slot24.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 4391800829068770048737280 }, { target := 132, numerator := 107669955809427910872268800 }, { target := 133, numerator := 4391800829068770048737280 }, { target := 134, numerator := 90244423487638920033730560 }, { target := 135, numerator := 88686042548291937113210880 }, { target := 136, numerator := 4391800829068770048737280 }, { target := 137, numerator := 88827713542778026469621760 }, { target := 138, numerator := 79619098901182218302914560 }, { target := 139, numerator := 107669955809427910872268800 }, { target := 140, numerator := 4391800829068770048737280 }, { target := 227, numerator := 73782253928355336818786304 }, { target := 228, numerator := 1808855257598388902654115840 }, { target := 229, numerator := 73782253928355336818786304 }, { target := 230, numerator := 1516106314592333856566673408 }, { target := 231, numerator := 1489925514811304543501942784 }, { target := 232, numerator := 73782253928355336818786304 }, { target := 233, numerator := 1492305587518670844689645568 }, { target := 234, numerator := 1337600861539861267488964608 }, { target := 235, numerator := 1808855257598388902654115840 }, { target := 236, numerator := 73782253928355336818786304 }, { target := 253, numerator := 159861550178103229774036992 }, { target := 254, numerator := 3919186391463175955750584320 }, { target := 255, numerator := 159861550178103229774036992 }, { target := 256, numerator := 3284897014950056689227792384 }, { target := 257, numerator := 3228171948757826510920876032 }, { target := 258, numerator := 159861550178103229774036992 }, { target := 259, numerator := 3233328772957120163494232064 }, { target := 260, numerator := 2898135200003032746226089984 }, { target := 261, numerator := 3919186391463175955750584320 }, { target := 262, numerator := 159861550178103229774036992 }, { target := 302, numerator := 5270160994882524058484736 }, { target := 303, numerator := 129203946971313493046722560 }, { target := 304, numerator := 5270160994882524058484736 }, { target := 305, numerator := 108293308185166704040476672 }, { target := 306, numerator := 106423251057950324535853056 }, { target := 307, numerator := 5270160994882524058484736 }, { target := 308, numerator := 106593256251333631763546112 }, { target := 309, numerator := 95542918681418661963497472 }, { target := 310, numerator := 129203946971313493046722560 }, { target := 311, numerator := 5270160994882524058484736 }, { target := 328, numerator := 84322575918120384935755776 }, { target := 329, numerator := 2067263151541015888747560960 }, { target := 330, numerator := 84322575918120384935755776 }, { target := 331, numerator := 1732692930962667264647626752 }, { target := 332, numerator := 1702772016927205192573648896 }, { target := 333, numerator := 84322575918120384935755776 }, { target := 334, numerator := 1705492100021338108216737792 }, { target := 335, numerator := 1528686698902698591415959552 }, { target := 336, numerator := 2067263151541015888747560960 }, { target := 337, numerator := 84322575918120384935755776 }, { target := 342, numerator := 6148521160696278068232192 }, { target := 343, numerator := 150737938133199075221176320 }, { target := 344, numerator := 6148521160696278068232192 }, { target := 345, numerator := 126342192882694488047222784 }, { target := 346, numerator := 124160459567608711958495232 }, { target := 347, numerator := 6148521160696278068232192 }, { target := 348, numerator := 124358798959889237057470464 }, { target := 349, numerator := 111466738461655105624080384 }, { target := 350, numerator := 150737938133199075221176320 }, { target := 351, numerator := 6148521160696278068232192 }]

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
    Slot24.Left6.expected,
    Slot24.Left7.expected,
    Slot24.Left8.expected,
    Slot24.Left9.expected,
    Slot24.Left10.expected,
    Slot24.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 443, numerator := 159861550178103229774036992 }, { target := 444, numerator := 3919186391463175955750584320 }, { target := 445, numerator := 159861550178103229774036992 }, { target := 446, numerator := 3284897014950056689227792384 }, { target := 447, numerator := 3228171948757826510920876032 }, { target := 448, numerator := 159861550178103229774036992 }, { target := 449, numerator := 3233328772957120163494232064 }, { target := 450, numerator := 2898135200003032746226089984 }, { target := 451, numerator := 3919186391463175955750584320 }, { target := 452, numerator := 159861550178103229774036992 }, { target := 469, numerator := 159861550178103229774036992 }, { target := 470, numerator := 3919186391463175955750584320 }, { target := 471, numerator := 159861550178103229774036992 }, { target := 472, numerator := 3284897014950056689227792384 }, { target := 473, numerator := 3228171948757826510920876032 }, { target := 474, numerator := 159861550178103229774036992 }, { target := 475, numerator := 3233328772957120163494232064 }, { target := 476, numerator := 2898135200003032746226089984 }, { target := 477, numerator := 3919186391463175955750584320 }, { target := 478, numerator := 159861550178103229774036992 }, { target := 518, numerator := 84322575918120384935755776 }, { target := 519, numerator := 2067263151541015888747560960 }, { target := 520, numerator := 84322575918120384935755776 }, { target := 521, numerator := 1732692930962667264647626752 }, { target := 522, numerator := 1702772016927205192573648896 }, { target := 523, numerator := 84322575918120384935755776 }, { target := 524, numerator := 1705492100021338108216737792 }, { target := 525, numerator := 1528686698902698591415959552 }, { target := 526, numerator := 2067263151541015888747560960 }, { target := 527, numerator := 84322575918120384935755776 }, { target := 544, numerator := 1972796932417691505892786176 }, { target := 545, numerator := 48365344149595017563823144960 }, { target := 546, numerator := 1972796932417691505892786176 }, { target := 547, numerator := 40537795030647402879151767552 }, { target := 548, numerator := 39837770312692738151254327296 }, { target := 549, numerator := 1972796932417691505892786176 }, { target := 550, numerator := 39901408923415889490154094592 }, { target := 551, numerator := 35764899226411052461669220352 }, { target := 552, numerator := 48365344149595017563823144960 }, { target := 553, numerator := 1972796932417691505892786176 }, { target := 558, numerator := 158104829846475721754542080 }, { target := 559, numerator := 3876118409139404791401676800 }, { target := 560, numerator := 158104829846475721754542080 }, { target := 561, numerator := 3248799245555001121214300160 }, { target := 562, numerator := 3192697531738509736075591680 }, { target := 563, numerator := 158104829846475721754542080 }, { target := 564, numerator := 3197797687540008952906383360 }, { target := 565, numerator := 2866287560442559858904924160 }, { target := 566, numerator := 3876118409139404791401676800 }, { target := 567, numerator := 158104829846475721754542080 }, { target := 589, numerator := 73782253928355336818786304 }, { target := 590, numerator := 1808855257598388902654115840 }, { target := 591, numerator := 73782253928355336818786304 }, { target := 592, numerator := 1516106314592333856566673408 }, { target := 593, numerator := 1489925514811304543501942784 }, { target := 594, numerator := 73782253928355336818786304 }, { target := 595, numerator := 1492305587518670844689645568 }, { target := 596, numerator := 1337600861539861267488964608 }, { target := 597, numerator := 1808855257598388902654115840 }, { target := 598, numerator := 73782253928355336818786304 }]

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
    Slot24.Left12.expected,
    Slot24.Left13.expected,
    Slot24.Left14.expected,
    Slot24.Left15.expected,
    Slot24.Left16.expected,
    Slot24.Left17.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 603, numerator := 159861550178103229774036992 }, { target := 604, numerator := 3919186391463175955750584320 }, { target := 605, numerator := 159861550178103229774036992 }, { target := 606, numerator := 3284897014950056689227792384 }, { target := 607, numerator := 3228171948757826510920876032 }, { target := 608, numerator := 159861550178103229774036992 }, { target := 609, numerator := 3233328772957120163494232064 }, { target := 610, numerator := 2898135200003032746226089984 }, { target := 611, numerator := 3919186391463175955750584320 }, { target := 612, numerator := 159861550178103229774036992 }, { target := 658, numerator := 6148521160696278068232192 }, { target := 659, numerator := 150737938133199075221176320 }, { target := 660, numerator := 6148521160696278068232192 }, { target := 661, numerator := 126342192882694488047222784 }, { target := 662, numerator := 124160459567608711958495232 }, { target := 663, numerator := 6148521160696278068232192 }, { target := 664, numerator := 124358798959889237057470464 }, { target := 665, numerator := 111466738461655105624080384 }, { target := 666, numerator := 150737938133199075221176320 }, { target := 667, numerator := 6148521160696278068232192 }, { target := 684, numerator := 158104829846475721754542080 }, { target := 685, numerator := 3876118409139404791401676800 }, { target := 686, numerator := 158104829846475721754542080 }, { target := 687, numerator := 3248799245555001121214300160 }, { target := 688, numerator := 3192697531738509736075591680 }, { target := 689, numerator := 158104829846475721754542080 }, { target := 690, numerator := 3197797687540008952906383360 }, { target := 691, numerator := 2866287560442559858904924160 }, { target := 692, numerator := 3876118409139404791401676800 }, { target := 693, numerator := 158104829846475721754542080 }, { target := 698, numerator := 6148521160696278068232192 }, { target := 699, numerator := 150737938133199075221176320 }, { target := 700, numerator := 6148521160696278068232192 }, { target := 701, numerator := 126342192882694488047222784 }, { target := 702, numerator := 124160459567608711958495232 }, { target := 703, numerator := 6148521160696278068232192 }, { target := 704, numerator := 124358798959889237057470464 }, { target := 705, numerator := 111466738461655105624080384 }, { target := 706, numerator := 150737938133199075221176320 }, { target := 707, numerator := 6148521160696278068232192 }, { target := 729, numerator := 159861550178103229774036992 }, { target := 730, numerator := 3919186391463175955750584320 }, { target := 731, numerator := 159861550178103229774036992 }, { target := 732, numerator := 3284897014950056689227792384 }, { target := 733, numerator := 3228171948757826510920876032 }, { target := 734, numerator := 159861550178103229774036992 }, { target := 735, numerator := 3233328772957120163494232064 }, { target := 736, numerator := 2898135200003032746226089984 }, { target := 737, numerator := 3919186391463175955750584320 }, { target := 738, numerator := 159861550178103229774036992 }, { target := 743, numerator := 159861550178103229774036992 }, { target := 744, numerator := 3919186391463175955750584320 }, { target := 745, numerator := 159861550178103229774036992 }, { target := 746, numerator := 3284897014950056689227792384 }, { target := 747, numerator := 3228171948757826510920876032 }, { target := 748, numerator := 159861550178103229774036992 }, { target := 749, numerator := 3233328772957120163494232064 }, { target := 750, numerator := 2898135200003032746226089984 }, { target := 751, numerator := 3919186391463175955750584320 }, { target := 752, numerator := 159861550178103229774036992 }]

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
    Slot24.Left18.expected,
    Slot25.Left0.expected,
    Slot25.Left2.expected,
    Slot25.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 2864040304292524266488856576 }, { target := 81, numerator := 2804372797953096677603672064 }, { target := 82, numerator := 2207697734558820788751826944 }, { target := 83, numerator := 69393309872754285873469587456 }, { target := 84, numerator := 2207697734558820788751826944 }, { target := 85, numerator := 2207697734558820788751826944 }, { target := 86, numerator := 2267365240898248377637011456 }, { target := 87, numerator := 2267365240898248377637011456 }, { target := 88, numerator := 38366206576251939653173641216 }, { target := 89, numerator := 2088362721879965610981457920 }, { target := 90, numerator := 69393309872754285873469587456 }, { target := 91, numerator := 38366206576251939653173641216 }, { target := 92, numerator := 2864040304292524266488856576 }, { target := 93, numerator := 2207697734558820788751826944 }, { target := 94, numerator := 2088362721879965610981457920 }, { target := 95, numerator := 2804372797953096677603672064 }, { target := 176, numerator := 105765198142999594855909294080 }, { target := 177, numerator := 103561756515020436629744517120 }, { target := 178, numerator := 81527340235228854368096747520 }, { target := 179, numerator := 2562602613339761017029635604480 }, { target := 180, numerator := 81527340235228854368096747520 }, { target := 181, numerator := 81527340235228854368096747520 }, { target := 182, numerator := 83730781863208012594261524480 }, { target := 183, numerator := 83730781863208012594261524480 }, { target := 184, numerator := 1416812966790598739423951585280 }, { target := 185, numerator := 77120456979270537915767193600 }, { target := 186, numerator := 2562602613339761017029635604480 }, { target := 187, numerator := 1416812966790598739423951585280 }, { target := 188, numerator := 105765198142999594855909294080 }, { target := 189, numerator := 81527340235228854368096747520 }, { target := 190, numerator := 77120456979270537915767193600 }, { target := 191, numerator := 103561756515020436629744517120 }, { target := 286, numerator := 105765172243770915367698825216 }, { target := 287, numerator := 103561731155359021297538433024 }, { target := 288, numerator := 81527320271240080595934511104 }, { target := 289, numerator := 2562601985823032803596536119296 }, { target := 290, numerator := 81527320271240080595934511104 }, { target := 291, numerator := 81527320271240080595934511104 }, { target := 292, numerator := 83730761359651974666094903296 }, { target := 293, numerator := 83730761359651974666094903296 }, { target := 294, numerator := 1416812619848847887113132179456 }, { target := 295, numerator := 77120438094416292455613726720 }, { target := 296, numerator := 2562601985823032803596536119296 }, { target := 297, numerator := 1416812619848847887113132179456 }, { target := 298, numerator := 105765172243770915367698825216 }, { target := 299, numerator := 81527320271240080595934511104 }, { target := 300, numerator := 77120438094416292455613726720 }, { target := 301, numerator := 103561731155359021297538433024 }, { target := 763, numerator := 5270160994882524058484736 }, { target := 764, numerator := 129203946971313493046722560 }, { target := 765, numerator := 5270160994882524058484736 }, { target := 766, numerator := 108293308185166704040476672 }, { target := 767, numerator := 106423251057950324535853056 }, { target := 768, numerator := 5270160994882524058484736 }, { target := 769, numerator := 106593256251333631763546112 }, { target := 770, numerator := 95542918681418661963497472 }, { target := 771, numerator := 129203946971313493046722560 }, { target := 772, numerator := 5270160994882524058484736 }]

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
    Slot25.Left12.expected,
    Slot26.Left0.expected,
    Slot26.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 28513860303958507834237255680 }, { target := 27, numerator := 760369608105560208912993484800 }, { target := 28, numerator := 727103437750941949773050019840 }, { target := 29, numerator := 23761550253298756528531046400 }, { target := 30, numerator := 746112677953580954995874856960 }, { target := 31, numerator := 23761550253298756528531046400 }, { target := 32, numerator := 727103437750941949773050019840 }, { target := 33, numerator := 413450974407398363596440207360 }, { target := 34, numerator := 746112677953580954995874856960 }, { target := 35, numerator := 11647911934167050450285918945280 }, { target := 36, numerator := 456221764863336125347796090880 }, { target := 37, numerator := 760369608105560208912993484800 }, { target := 38, numerator := 727103437750941949773050019840 }, { target := 39, numerator := 23761550253298756528531046400 }, { target := 40, numerator := 456221764863336125347796090880 }, { target := 41, numerator := 23761550253298756528531046400 }, { target := 42, numerator := 731855747801601701078756229120 }, { target := 43, numerator := 413450974407398363596440207360 }, { target := 44, numerator := 28513860303958507834237255680 }, { target := 157, numerator := 103711056368044079400458649600 }, { target := 158, numerator := 2765628169814508784012230656000 }, { target := 159, numerator := 2644631937385124024711695564800 }, { target := 160, numerator := 86425880306703399500382208000 }, { target := 161, numerator := 2713772641630486744312001331200 }, { target := 162, numerator := 86425880306703399500382208000 }, { target := 163, numerator := 2644631937385124024711695564800 }, { target := 164, numerator := 1503810317336639151306650419200 }, { target := 165, numerator := 2713772641630486744312001331200 }, { target := 166, numerator := 42365966526346006435087358361600 }, { target := 167, numerator := 1659376901888705270407338393600 }, { target := 168, numerator := 2765628169814508784012230656000 }, { target := 169, numerator := 2644631937385124024711695564800 }, { target := 170, numerator := 86425880306703399500382208000 }, { target := 171, numerator := 1659376901888705270407338393600 }, { target := 172, numerator := 86425880306703399500382208000 }, { target := 173, numerator := 2661917113446464704611772006400 }, { target := 174, numerator := 1503810317336639151306650419200 }, { target := 175, numerator := 103711056368044079400458649600 }, { target := 573, numerator := 2864066203521203754699325440 }, { target := 574, numerator := 2804398157614512009809756160 }, { target := 575, numerator := 2207717698547594560914063360 }, { target := 576, numerator := 69393937389482499306569072640 }, { target := 577, numerator := 2207717698547594560914063360 }, { target := 578, numerator := 2207717698547594560914063360 }, { target := 579, numerator := 2267385744454286305803632640 }, { target := 580, numerator := 2267385744454286305803632640 }, { target := 581, numerator := 38366553518002791963993047040 }, { target := 582, numerator := 2088381606734211071134924800 }, { target := 583, numerator := 69393937389482499306569072640 }, { target := 584, numerator := 38366553518002791963993047040 }, { target := 585, numerator := 2864066203521203754699325440 }, { target := 586, numerator := 2207717698547594560914063360 }, { target := 587, numerator := 2088381606734211071134924800 }, { target := 588, numerator := 2804398157614512009809756160 }]

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
    Slot26.Left5.expected,
    Slot27.Left0.expected,
    Slot27.Left2.expected,
    Slot28.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 3384992294920961689177292800 }, { target := 1, numerator := 67835245590216072251112947712 }, { target := 2, numerator := 113871140801141151223924129792 }, { target := 3, numerator := 109267551280048643326643011584 }, { target := 4, numerator := 3384992294920961689177292800 }, { target := 5, numerator := 109267551280048643326643011584 }, { target := 6, numerator := 72980433878495934018662432768 }, { target := 7, numerator := 3520391986717800156744384512 }, { target := 8, numerator := 67835245590216072251112947712 }, { target := 9, numerator := 3249592603124123221610201088 }, { target := 10, numerator := 130999233046084777170645811200 }, { target := 11, numerator := 134742068275972913661235691520 }, { target := 12, numerator := 130999233046084777170645811200 }, { target := 13, numerator := 116027892126532231208286289920 }, { target := 14, numerator := 5430853918567686047845916344320 }, { target := 15, numerator := 1478419915805813913783002726400 }, { target := 16, numerator := 134742068275972913661235691520 }, { target := 17, numerator := 5430853918567686047845916344320 }, { target := 18, numerator := 130999233046084777170645811200 }, { target := 19, numerator := 130999233046084777170645811200 }, { target := 20, numerator := 112285056896644094717696409600 }, { target := 21, numerator := 130999233046084777170645811200 }, { target := 22, numerator := 1478419915805813913783002726400 }, { target := 23, numerator := 112285056896644094717696409600 }, { target := 24, numerator := 130999233046084777170645811200 }, { target := 25, numerator := 116027892126532231208286289920 }, { target := 141, numerator := 130999170580797657571676651520 }, { target := 142, numerator := 134742004025963304930867412992 }, { target := 143, numerator := 130999170580797657571676651520 }, { target := 144, numerator := 116027836800135068134913605632 }, { target := 145, numerator := 5430851328935354318185794895872 }, { target := 146, numerator := 1478419210840430706880350781440 }, { target := 147, numerator := 134742004025963304930867412992 }, { target := 148, numerator := 5430851328935354318185794895872 }, { target := 149, numerator := 130999170580797657571676651520 }, { target := 150, numerator := 130999170580797657571676651520 }, { target := 151, numerator := 112285003354969420775722844160 }, { target := 152, numerator := 130999170580797657571676651520 }, { target := 153, numerator := 1478419210840430706880350781440 }, { target := 154, numerator := 112285003354969420775722844160 }, { target := 155, numerator := 130999170580797657571676651520 }, { target := 156, numerator := 116027836800135068134913605632 }, { target := 267, numerator := 28513860303958507834237255680 }, { target := 268, numerator := 760369608105560208912993484800 }, { target := 269, numerator := 727103437750941949773050019840 }, { target := 270, numerator := 23761550253298756528531046400 }, { target := 271, numerator := 746112677953580954995874856960 }, { target := 272, numerator := 23761550253298756528531046400 }, { target := 273, numerator := 727103437750941949773050019840 }, { target := 274, numerator := 413450974407398363596440207360 }, { target := 275, numerator := 746112677953580954995874856960 }, { target := 276, numerator := 11647911934167050450285918945280 }, { target := 277, numerator := 456221764863336125347796090880 }, { target := 278, numerator := 760369608105560208912993484800 }, { target := 279, numerator := 727103437750941949773050019840 }, { target := 280, numerator := 23761550253298756528531046400 }, { target := 281, numerator := 456221764863336125347796090880 }, { target := 282, numerator := 23761550253298756528531046400 }, { target := 283, numerator := 731855747801601701078756229120 }, { target := 284, numerator := 413450974407398363596440207360 }, { target := 285, numerator := 28513860303958507834237255680 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent2
