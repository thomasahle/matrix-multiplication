import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk8Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 34; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent0

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
    Slot0.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 161618270509730737793531904 }, { target := 30, numerator := 121213702882298053345148928 }, { target := 31, numerator := 127947797486870167419879424 }, { target := 32, numerator := 164985317812016794830897152 }, { target := 33, numerator := 2208783030299653416511602688 }, { target := 34, numerator := 3862003255722107421857939456 }, { target := 35, numerator := 117846655580011996307783680 }, { target := 36, numerator := 2208783030299653416511602688 }, { target := 37, numerator := 124580750184584110382514176 }, { target := 38, numerator := 127947797486870167419879424 }, { target := 39, numerator := 127947797486870167419879424 }, { target := 40, numerator := 124580750184584110382514176 }, { target := 41, numerator := 3862003255722107421857939456 }, { target := 42, numerator := 124580750184584110382514176 }, { target := 43, numerator := 161618270509730737793531904 }, { target := 44, numerator := 164985317812016794830897152 }, { target := 55, numerator := 182472240898083091057213440 }, { target := 56, numerator := 136854180673562318292910080 }, { target := 57, numerator := 144457190710982447086960640 }, { target := 58, numerator := 186273745916793155454238720 }, { target := 59, numerator := 2493787292273802244448583680 }, { target := 60, numerator := 4360326256460443863387996160 }, { target := 61, numerator := 133052675654852253895884800 }, { target := 62, numerator := 2493787292273802244448583680 }, { target := 63, numerator := 140655685692272382689935360 }, { target := 64, numerator := 144457190710982447086960640 }, { target := 65, numerator := 144457190710982447086960640 }, { target := 66, numerator := 140655685692272382689935360 }, { target := 67, numerator := 4360326256460443863387996160 }, { target := 68, numerator := 140655685692272382689935360 }, { target := 69, numerator := 182472240898083091057213440 }, { target := 70, numerator := 186273745916793155454238720 }, { target := 104, numerator := 156404777912642649477611520 }, { target := 105, numerator := 117303583434481987108208640 }, { target := 106, numerator := 123820449180842097503109120 }, { target := 107, numerator := 159663210785822704675061760 }, { target := 108, numerator := 2137531964806116209527357440 }, { target := 109, numerator := 3737422505537523311475425280 }, { target := 110, numerator := 114045150561301931910758400 }, { target := 111, numerator := 2137531964806116209527357440 }, { target := 112, numerator := 120562016307662042305658880 }, { target := 113, numerator := 123820449180842097503109120 }, { target := 114, numerator := 123820449180842097503109120 }, { target := 115, numerator := 120562016307662042305658880 }, { target := 116, numerator := 3737422505537523311475425280 }, { target := 117, numerator := 120562016307662042305658880 }, { target := 118, numerator := 156404777912642649477611520 }, { target := 119, numerator := 159663210785822704675061760 }, { target := 130, numerator := 2059329575849794884788551680 }, { target := 131, numerator := 1544497181887346163591413760 }, { target := 132, numerator := 1630302580881087617124270080 }, { target := 133, numerator := 2102232275346665611554979840 }, { target := 134, numerator := 28144170869947196758776872960 }, { target := 135, numerator := 49209396322910723601093099520 }, { target := 136, numerator := 1501594482390475436824985600 }, { target := 137, numerator := 28144170869947196758776872960 }, { target := 138, numerator := 1587399881384216890357841920 }, { target := 139, numerator := 1630302580881087617124270080 }, { target := 140, numerator := 1630302580881087617124270080 }, { target := 141, numerator := 1587399881384216890357841920 }, { target := 142, numerator := 49209396322910723601093099520 }, { target := 143, numerator := 1587399881384216890357841920 }, { target := 144, numerator := 2059329575849794884788551680 }, { target := 145, numerator := 2102232275346665611554979840 }]

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
    Slot0.Left4.expected,
    Slot0.Left5.expected,
    Slot0.Left6.expected,
    Slot0.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 165, numerator := 182472240898083091057213440 }, { target := 166, numerator := 136854180673562318292910080 }, { target := 167, numerator := 144457190710982447086960640 }, { target := 168, numerator := 186273745916793155454238720 }, { target := 169, numerator := 2493787292273802244448583680 }, { target := 170, numerator := 4360326256460443863387996160 }, { target := 171, numerator := 133052675654852253895884800 }, { target := 172, numerator := 2493787292273802244448583680 }, { target := 173, numerator := 140655685692272382689935360 }, { target := 174, numerator := 144457190710982447086960640 }, { target := 175, numerator := 144457190710982447086960640 }, { target := 176, numerator := 140655685692272382689935360 }, { target := 177, numerator := 4360326256460443863387996160 }, { target := 178, numerator := 140655685692272382689935360 }, { target := 179, numerator := 182472240898083091057213440 }, { target := 180, numerator := 186273745916793155454238720 }, { target := 226, numerator := 156404777912642649477611520 }, { target := 227, numerator := 117303583434481987108208640 }, { target := 228, numerator := 123820449180842097503109120 }, { target := 229, numerator := 159663210785822704675061760 }, { target := 230, numerator := 2137531964806116209527357440 }, { target := 231, numerator := 3737422505537523311475425280 }, { target := 232, numerator := 114045150561301931910758400 }, { target := 233, numerator := 2137531964806116209527357440 }, { target := 234, numerator := 120562016307662042305658880 }, { target := 235, numerator := 123820449180842097503109120 }, { target := 236, numerator := 123820449180842097503109120 }, { target := 237, numerator := 120562016307662042305658880 }, { target := 238, numerator := 3737422505537523311475425280 }, { target := 239, numerator := 120562016307662042305658880 }, { target := 240, numerator := 156404777912642649477611520 }, { target := 241, numerator := 159663210785822704675061760 }, { target := 261, numerator := 182472240898083091057213440 }, { target := 262, numerator := 136854180673562318292910080 }, { target := 263, numerator := 144457190710982447086960640 }, { target := 264, numerator := 186273745916793155454238720 }, { target := 265, numerator := 2493787292273802244448583680 }, { target := 266, numerator := 4360326256460443863387996160 }, { target := 267, numerator := 133052675654852253895884800 }, { target := 268, numerator := 2493787292273802244448583680 }, { target := 269, numerator := 140655685692272382689935360 }, { target := 270, numerator := 144457190710982447086960640 }, { target := 271, numerator := 144457190710982447086960640 }, { target := 272, numerator := 140655685692272382689935360 }, { target := 273, numerator := 4360326256460443863387996160 }, { target := 274, numerator := 140655685692272382689935360 }, { target := 275, numerator := 182472240898083091057213440 }, { target := 276, numerator := 186273745916793155454238720 }, { target := 371, numerator := 182472240898083091057213440 }, { target := 372, numerator := 136854180673562318292910080 }, { target := 373, numerator := 144457190710982447086960640 }, { target := 374, numerator := 186273745916793155454238720 }, { target := 375, numerator := 2493787292273802244448583680 }, { target := 376, numerator := 4360326256460443863387996160 }, { target := 377, numerator := 133052675654852253895884800 }, { target := 378, numerator := 2493787292273802244448583680 }, { target := 379, numerator := 140655685692272382689935360 }, { target := 380, numerator := 144457190710982447086960640 }, { target := 381, numerator := 144457190710982447086960640 }, { target := 382, numerator := 140655685692272382689935360 }, { target := 383, numerator := 4360326256460443863387996160 }, { target := 384, numerator := 140655685692272382689935360 }, { target := 385, numerator := 182472240898083091057213440 }, { target := 386, numerator := 186273745916793155454238720 }]

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
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 397, numerator := 7564777758374816146400477184 }, { target := 398, numerator := 5673583318781112109800357888 }, { target := 399, numerator := 5988782392046729449233711104 }, { target := 400, numerator := 7722377295007624816117153792 }, { target := 401, numerator := 103385296031122487334139854848 }, { target := 402, numerator := 180766668517831544165028069376 }, { target := 403, numerator := 5515983782148303440083681280 }, { target := 404, numerator := 103385296031122487334139854848 }, { target := 405, numerator := 5831182855413920779517034496 }, { target := 406, numerator := 5988782392046729449233711104 }, { target := 407, numerator := 5988782392046729449233711104 }, { target := 408, numerator := 5831182855413920779517034496 }, { target := 409, numerator := 180766668517831544165028069376 }, { target := 410, numerator := 5831182855413920779517034496 }, { target := 411, numerator := 7564777758374816146400477184 }, { target := 412, numerator := 7722377295007624816117153792 }, { target := 432, numerator := 187685733495171179373133824 }, { target := 433, numerator := 140764300121378384529850368 }, { target := 434, numerator := 148584539017010517003730944 }, { target := 435, numerator := 191595852942987245610074112 }, { target := 436, numerator := 2565038357767339451432828928 }, { target := 437, numerator := 4484907006645027973770510336 }, { target := 438, numerator := 136854180673562318292910080 }, { target := 439, numerator := 2565038357767339451432828928 }, { target := 440, numerator := 144674419569194450766790656 }, { target := 441, numerator := 148584539017010517003730944 }, { target := 442, numerator := 148584539017010517003730944 }, { target := 443, numerator := 144674419569194450766790656 }, { target := 444, numerator := 4484907006645027973770510336 }, { target := 445, numerator := 144674419569194450766790656 }, { target := 446, numerator := 187685733495171179373133824 }, { target := 447, numerator := 191595852942987245610074112 }, { target := 493, numerator := 2059329575849794884788551680 }, { target := 494, numerator := 1544497181887346163591413760 }, { target := 495, numerator := 1630302580881087617124270080 }, { target := 496, numerator := 2102232275346665611554979840 }, { target := 497, numerator := 28144170869947196758776872960 }, { target := 498, numerator := 49209396322910723601093099520 }, { target := 499, numerator := 1501594482390475436824985600 }, { target := 500, numerator := 28144170869947196758776872960 }, { target := 501, numerator := 1587399881384216890357841920 }, { target := 502, numerator := 1630302580881087617124270080 }, { target := 503, numerator := 1630302580881087617124270080 }, { target := 504, numerator := 1587399881384216890357841920 }, { target := 505, numerator := 49209396322910723601093099520 }, { target := 506, numerator := 1587399881384216890357841920 }, { target := 507, numerator := 2059329575849794884788551680 }, { target := 508, numerator := 2102232275346665611554979840 }, { target := 528, numerator := 7564777758374816146400477184 }, { target := 529, numerator := 5673583318781112109800357888 }, { target := 530, numerator := 5988782392046729449233711104 }, { target := 531, numerator := 7722377295007624816117153792 }, { target := 532, numerator := 103385296031122487334139854848 }, { target := 533, numerator := 180766668517831544165028069376 }, { target := 534, numerator := 5515983782148303440083681280 }, { target := 535, numerator := 103385296031122487334139854848 }, { target := 536, numerator := 5831182855413920779517034496 }, { target := 537, numerator := 5988782392046729449233711104 }, { target := 538, numerator := 5988782392046729449233711104 }, { target := 539, numerator := 5831182855413920779517034496 }, { target := 540, numerator := 180766668517831544165028069376 }, { target := 541, numerator := 5831182855413920779517034496 }, { target := 542, numerator := 7564777758374816146400477184 }, { target := 543, numerator := 7722377295007624816117153792 }]

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
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected,
    Slot0.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 624, numerator := 161618270509730737793531904 }, { target := 625, numerator := 121213702882298053345148928 }, { target := 626, numerator := 127947797486870167419879424 }, { target := 627, numerator := 164985317812016794830897152 }, { target := 628, numerator := 2208783030299653416511602688 }, { target := 629, numerator := 3862003255722107421857939456 }, { target := 630, numerator := 117846655580011996307783680 }, { target := 631, numerator := 2208783030299653416511602688 }, { target := 632, numerator := 124580750184584110382514176 }, { target := 633, numerator := 127947797486870167419879424 }, { target := 634, numerator := 127947797486870167419879424 }, { target := 635, numerator := 124580750184584110382514176 }, { target := 636, numerator := 3862003255722107421857939456 }, { target := 637, numerator := 124580750184584110382514176 }, { target := 638, numerator := 161618270509730737793531904 }, { target := 639, numerator := 164985317812016794830897152 }, { target := 760, numerator := 182472240898083091057213440 }, { target := 761, numerator := 136854180673562318292910080 }, { target := 762, numerator := 144457190710982447086960640 }, { target := 763, numerator := 186273745916793155454238720 }, { target := 764, numerator := 2493787292273802244448583680 }, { target := 765, numerator := 4360326256460443863387996160 }, { target := 766, numerator := 133052675654852253895884800 }, { target := 767, numerator := 2493787292273802244448583680 }, { target := 768, numerator := 140655685692272382689935360 }, { target := 769, numerator := 144457190710982447086960640 }, { target := 770, numerator := 144457190710982447086960640 }, { target := 771, numerator := 140655685692272382689935360 }, { target := 772, numerator := 4360326256460443863387996160 }, { target := 773, numerator := 140655685692272382689935360 }, { target := 774, numerator := 182472240898083091057213440 }, { target := 775, numerator := 186273745916793155454238720 }, { target := 795, numerator := 187685733495171179373133824 }, { target := 796, numerator := 140764300121378384529850368 }, { target := 797, numerator := 148584539017010517003730944 }, { target := 798, numerator := 191595852942987245610074112 }, { target := 799, numerator := 2565038357767339451432828928 }, { target := 800, numerator := 4484907006645027973770510336 }, { target := 801, numerator := 136854180673562318292910080 }, { target := 802, numerator := 2565038357767339451432828928 }, { target := 803, numerator := 144674419569194450766790656 }, { target := 804, numerator := 148584539017010517003730944 }, { target := 805, numerator := 148584539017010517003730944 }, { target := 806, numerator := 144674419569194450766790656 }, { target := 807, numerator := 4484907006645027973770510336 }, { target := 808, numerator := 144674419569194450766790656 }, { target := 809, numerator := 187685733495171179373133824 }, { target := 810, numerator := 191595852942987245610074112 }, { target := 891, numerator := 182472240898083091057213440 }, { target := 892, numerator := 136854180673562318292910080 }, { target := 893, numerator := 144457190710982447086960640 }, { target := 894, numerator := 186273745916793155454238720 }, { target := 895, numerator := 2493787292273802244448583680 }, { target := 896, numerator := 4360326256460443863387996160 }, { target := 897, numerator := 133052675654852253895884800 }, { target := 898, numerator := 2493787292273802244448583680 }, { target := 899, numerator := 140655685692272382689935360 }, { target := 900, numerator := 144457190710982447086960640 }, { target := 901, numerator := 144457190710982447086960640 }, { target := 902, numerator := 140655685692272382689935360 }, { target := 903, numerator := 4360326256460443863387996160 }, { target := 904, numerator := 140655685692272382689935360 }, { target := 905, numerator := 182472240898083091057213440 }, { target := 906, numerator := 186273745916793155454238720 }]

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
  [{ target := 71, numerator := 65366332773094975504121856 }, { target := 72, numerator := 7725880866662800397546029056 }, { target := 74, numerator := 73317069373482345072024354816 }, { target := 82, numerator := 7725886165490035570614730752 }, { target := 89, numerator := 65366332773094975504121856 }, { target := 146, numerator := 947811825209877144809766912 }, { target := 147, numerator := 112025272566610605764417421312 }, { target := 149, numerator := 1063097505915494003544353144832 }, { target := 157, numerator := 112025349399605515773913595904 }, { target := 164, numerator := 947811825209877144809766912 }, { target := 181, numerator := 1677735874509437704605794304 }, { target := 182, numerator := 198297608911011876870348079104 }, { target := 184, numerator := 1881804780586046856848625106944 }, { target := 192, numerator := 198297744914244246312444755968 }, { target := 199, numerator := 1677735874509437704605794304 }, { target := 242, numerator := 54471943977579146253434880 }, { target := 243, numerator := 6438234055552333664621690880 }, { target := 245, numerator := 61097557811235287560020295680 }, { target := 253, numerator := 6438238471241696308845608960 }, { target := 260, numerator := 54471943977579146253434880 }, { target := 277, numerator := 1045861324369519608065949696 }, { target := 278, numerator := 123614093866604806360736464896 }, { target := 280, numerator := 1173073109975717521152389677056 }, { target := 288, numerator := 123614178647840569129835692032 }, { target := 295, numerator := 1045861324369519608065949696 }, { target := 312, numerator := 54471943977579146253434880 }, { target := 313, numerator := 6438234055552333664621690880 }, { target := 315, numerator := 61097557811235287560020295680 }, { target := 323, numerator := 6438238471241696308845608960 }, { target := 330, numerator := 54471943977579146253434880 }, { target := 413, numerator := 1666841485713921875355107328 }, { target := 414, numerator := 197009962099901410137423740928 }, { target := 416, numerator := 1869585269023799799336621047808 }, { target := 424, numerator := 197010097219995907050675634176 }, { target := 431, numerator := 1666841485713921875355107328 }, { target := 448, numerator := 1743102207282532680109916160 }, { target := 449, numerator := 206023489777674677267894108160 }, { target := 451, numerator := 1955121849959529201920649461760 }, { target := 459, numerator := 206023631079734281883059486720 }, { target := 466, numerator := 1743102207282532680109916160 }, { target := 509, numerator := 1045861324369519608065949696 }, { target := 510, numerator := 123614093866604806360736464896 }, { target := 512, numerator := 1173073109975717521152389677056 }, { target := 520, numerator := 123614178647840569129835692032 }, { target := 527, numerator := 1045861324369519608065949696 }, { target := 544, numerator := 26702146937809297493433778176 }, { target := 545, numerator := 3156022334031753962397552869376 }, { target := 547, numerator := 29950022839067537961921948942336 }, { target := 555, numerator := 3156024498602679530596117512192 }, { target := 562, numerator := 26702146937809297493433778176 }, { target := 579, numerator := 1710419040895985192357855232 }, { target := 580, numerator := 202160549344343277069121093632 }, { target := 582, numerator := 1918463315272788029384637284352 }, { target := 590, numerator := 202160687996989264097752121344 }, { target := 597, numerator := 1710419040895985192357855232 }, { target := 640, numerator := 947811825209877144809766912 }, { target := 641, numerator := 112025272566610605764417421312 }, { target := 643, numerator := 1063097505915494003544353144832 }, { target := 651, numerator := 112025349399605515773913595904 }, { target := 658, numerator := 947811825209877144809766912 }]

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
    Slot1.Left12.expected,
    Slot1.Left13.expected,
    Slot1.Left14.expected,
    Slot1.Left15.expected,
    Slot1.Left16.expected,
    Slot1.Left17.expected,
    Slot1.Left18.expected,
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
  [{ target := 200, numerator := 8177148044885081051721891840 }, { target := 202, numerator := 320012362057537530264113119232 }, { target := 205, numerator := 320012362057537530264113119232 }, { target := 212, numerator := 8177148044885081051721891840 }, { target := 296, numerator := 6089365565339953974686515200 }, { target := 298, numerator := 238307078127953479983914024960 }, { target := 301, numerator := 238307078127953479983914024960 }, { target := 308, numerator := 6089365565339953974686515200 }, { target := 331, numerator := 6437329311930808487525744640 }, { target := 333, numerator := 251924625449550821697280540672 }, { target := 336, numerator := 251924625449550821697280540672 }, { target := 343, numerator := 6437329311930808487525744640 }, { target := 467, numerator := 8351129918180508308141506560 }, { target := 469, numerator := 326821135718336201120796377088 }, { target := 472, numerator := 326821135718336201120796377088 }, { target := 479, numerator := 8351129918180508308141506560 }, { target := 563, numerator := 111870344528959725877812264960 }, { target := 565, numerator := 4378041463893545360847334801408 }, { target := 568, numerator := 4378041463893545360847334801408 }, { target := 575, numerator := 111870344528959725877812264960 }, { target := 598, numerator := 202340918642581899216011919360 }, { target := 600, numerator := 7918603767508854206322628886528 }, { target := 603, numerator := 7918603767508854206322628886528 }, { target := 610, numerator := 202340918642581899216011919360 }, { target := 659, numerator := 6089365565339953974686515200 }, { target := 661, numerator := 238307078127953479983914024960 }, { target := 664, numerator := 238307078127953479983914024960 }, { target := 671, numerator := 6089365565339953974686515200 }, { target := 675, numerator := 1666841485713921875355107328 }, { target := 676, numerator := 197009962099901410137423740928 }, { target := 678, numerator := 1869585269023799799336621047808 }, { target := 686, numerator := 197010097219995907050675634176 }, { target := 693, numerator := 1666841485713921875355107328 }, { target := 776, numerator := 54471943977579146253434880 }, { target := 777, numerator := 6438234055552333664621690880 }, { target := 779, numerator := 61097557811235287560020295680 }, { target := 787, numerator := 6438238471241696308845608960 }, { target := 794, numerator := 54471943977579146253434880 }, { target := 811, numerator := 1710419040895985192357855232 }, { target := 812, numerator := 202160549344343277069121093632 }, { target := 814, numerator := 1918463315272788029384637284352 }, { target := 822, numerator := 202160687996989264097752121344 }, { target := 829, numerator := 1710419040895985192357855232 }, { target := 846, numerator := 54471943977579146253434880 }, { target := 847, numerator := 6438234055552333664621690880 }, { target := 849, numerator := 61097557811235287560020295680 }, { target := 857, numerator := 6438238471241696308845608960 }, { target := 864, numerator := 54471943977579146253434880 }, { target := 907, numerator := 1666841485713921875355107328 }, { target := 908, numerator := 197009962099901410137423740928 }, { target := 910, numerator := 1869585269023799799336621047808 }, { target := 918, numerator := 197010097219995907050675634176 }, { target := 925, numerator := 1666841485713921875355107328 }, { target := 942, numerator := 1743102207282532680109916160 }, { target := 943, numerator := 206023489777674677267894108160 }, { target := 945, numerator := 1955121849959529201920649461760 }, { target := 953, numerator := 206023631079734281883059486720 }, { target := 960, numerator := 1743102207282532680109916160 }, { target := 1017, numerator := 65366332773094975504121856 }, { target := 1018, numerator := 7725880866662800397546029056 }, { target := 1020, numerator := 73317069373482345072024354816 }, { target := 1028, numerator := 7725886165490035570614730752 }, { target := 1035, numerator := 65366332773094975504121856 }]

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
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot2.Left10.expected,
    Slot2.Left11.expected,
    Slot2.Left12.expected,
    Slot2.Left13.expected,
    Slot2.Left14.expected,
    Slot2.Left15.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected,
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 347, numerator := 7345106039350305276496445440 }, { target := 350, numerator := 27285238515232282451011174400 }, { target := 352, numerator := 7343559902437337218290810880 }, { target := 614, numerator := 180073567416330064843138662400 }, { target := 617, numerator := 668928428115372085895757824000 }, { target := 619, numerator := 180035662124270202771000524800 }, { target := 694, numerator := 111870344528959725877812264960 }, { target := 696, numerator := 4378041463893545360847334801408 }, { target := 699, numerator := 4378041463893545360847334801408 }, { target := 706, numerator := 111870344528959725877812264960 }, { target := 710, numerator := 133159664326286179528742010880 }, { target := 713, numerator := 494654969211630410886073548800 }, { target := 715, numerator := 133131634360315597312239861760 }, { target := 720, numerator := 6611311185226235743945359360 }, { target := 722, numerator := 258733399110349492553963798528 }, { target := 725, numerator := 258733399110349492553963798528 }, { target := 732, numerator := 6611311185226235743945359360 }, { target := 736, numerator := 148560693118472303495589396480 }, { target := 739, numerator := 551865953195181970864000204800 }, { target := 741, numerator := 148529421252522917286075432960 }, { target := 830, numerator := 6611311185226235743945359360 }, { target := 832, numerator := 258733399110349492553963798528 }, { target := 835, numerator := 258733399110349492553963798528 }, { target := 842, numerator := 6611311185226235743945359360 }, { target := 865, numerator := 6437329311930808487525744640 }, { target := 867, numerator := 251924625449550821697280540672 }, { target := 870, numerator := 251924625449550821697280540672 }, { target := 877, numerator := 6437329311930808487525744640 }, { target := 881, numerator := 7345106039350305276496445440 }, { target := 884, numerator := 27285238515232282451011174400 }, { target := 886, numerator := 7343559902437337218290810880 }, { target := 926, numerator := 6437329311930808487525744640 }, { target := 928, numerator := 251924625449550821697280540672 }, { target := 931, numerator := 251924625449550821697280540672 }, { target := 938, numerator := 6437329311930808487525744640 }, { target := 961, numerator := 202340918642581899216011919360 }, { target := 963, numerator := 7918603767508854206322628886528 }, { target := 966, numerator := 7918603767508854206322628886528 }, { target := 973, numerator := 202340918642581899216011919360 }, { target := 977, numerator := 148323754213977132357637898240 }, { target := 980, numerator := 550985784210819639172032102400 }, { target := 982, numerator := 148292532223412035440324116480 }, { target := 987, numerator := 6437329311930808487525744640 }, { target := 989, numerator := 251924625449550821697280540672 }, { target := 992, numerator := 251924625449550821697280540672 }, { target := 999, numerator := 6437329311930808487525744640 }, { target := 1003, numerator := 150930082163424014875104378880 }, { target := 1006, numerator := 560667643038805287783681228800 }, { target := 1008, numerator := 150898311543631735743588597760 }, { target := 1036, numerator := 8177148044885081051721891840 }, { target := 1038, numerator := 320012362057537530264113119232 }, { target := 1041, numerator := 320012362057537530264113119232 }, { target := 1048, numerator := 8177148044885081051721891840 }, { target := 1052, numerator := 7345106039350305276496445440 }, { target := 1055, numerator := 27285238515232282451011174400 }, { target := 1057, numerator := 7343559902437337218290810880 }, { target := 1062, numerator := 8351129918180508308141506560 }, { target := 1064, numerator := 326821135718336201120796377088 }, { target := 1067, numerator := 326821135718336201120796377088 }, { target := 1074, numerator := 8351129918180508308141506560 }, { target := 1078, numerator := 180073567416330064843138662400 }, { target := 1081, numerator := 668928428115372085895757824000 }, { target := 1083, numerator := 180035662124270202771000524800 }]

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
    Slot3.Left9.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 637589120869652394261086208 }, { target := 6, numerator := 15446110637842224131937927168 }, { target := 7, numerator := 11702845476607490720469614592 }, { target := 8, numerator := 13039725891334181224565440512 }, { target := 9, numerator := 637589120869652394261086208 }, { target := 10, numerator := 13039725891334181224565440512 }, { target := 11, numerator := 13019158500338385986040889344 }, { target := 12, numerator := 637589120869652394261086208 }, { target := 13, numerator := 15446110637842224131937927168 }, { target := 14, numerator := 637589120869652394261086208 }, { target := 29, numerator := 1233067128879652039714406400 }, { target := 30, numerator := 216268389688347678060262195200 }, { target := 35, numerator := 216268415616541821501859430400 }, { target := 43, numerator := 1233041200685508598117171200 }, { target := 71, numerator := 36250391369417169232199680 }, { target := 72, numerator := 11677025340293277178354728960 }, { target := 74, numerator := 124190075014267369714654117888 }, { target := 82, numerator := 11677060534848004767839420416 }, { target := 89, numerator := 36250391369417169232199680 }, { target := 94, numerator := 2322584568547031921656332288 }, { target := 95, numerator := 56266484225123257198835662848 }, { target := 96, numerator := 42630665145266489142659776512 }, { target := 97, numerator := 47500600530929620591294021632 }, { target := 98, numerator := 2322584568547031921656332288 }, { target := 99, numerator := 47500600530929620591294021632 }, { target := 100, numerator := 47425678448073264722853494784 }, { target := 101, numerator := 2322584568547031921656332288 }, { target := 102, numerator := 56266484225123257198835662848 }, { target := 103, numerator := 2322584568547031921656332288 }, { target := 104, numerator := 49297795030679944724427571200 }, { target := 105, numerator := 8646370093539289350119463321600 }, { target := 110, numerator := 8646371130143680516087558963200 }, { target := 118, numerator := 49296758426288778756331929600 }, { target := 216, numerator := 637589549756452108008161280 }, { target := 217, numerator := 15446121027970823648842874880 }, { target := 218, numerator := 11702853348755524176020766720 }, { target := 219, numerator := 13039734662760988273457233920 }, { target := 220, numerator := 637589549756452108008161280 }, { target := 221, numerator := 13039734662760988273457233920 }, { target := 222, numerator := 13019167257930134979650519040 }, { target := 223, numerator := 637589549756452108008161280 }, { target := 224, numerator := 15446121027970823648842874880 }, { target := 225, numerator := 637589549756452108008161280 }, { target := 226, numerator := 49297782983185024038626918400 }, { target := 227, numerator := 8646367980521866979464917811200 }, { target := 232, numerator := 8646369017126004817953973862400 }, { target := 240, numerator := 49296746379047185549570867200 }, { target := 624, numerator := 1233067128879652039714406400 }, { target := 625, numerator := 216268389688347678060262195200 }, { target := 630, numerator := 216268415616541821501859430400 }, { target := 638, numerator := 1233041200685508598117171200 }, { target := 746, numerator := 49711023776537017984724500480 }, { target := 748, numerator := 49711035628570085343111413760 }, { target := 1013, numerator := 49565952695477085052862464000 }, { target := 1015, numerator := 49565964512922507273043968000 }, { target := 1088, numerator := 49227453506337241545184378880 }, { target := 1090, numerator := 49227465243078158442886594560 }, { target := 1092, numerator := 7345106039350305276496445440 }, { target := 1095, numerator := 27285238515232282451011174400 }, { target := 1097, numerator := 7343559902437337218290810880 }, { target := 1102, numerator := 49565952695477085052862464000 }, { target := 1104, numerator := 49565964512922507273043968000 }]

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
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left7.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left2.expected,
    Slot11.Left3.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot13.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 9903516772508180046959083520 }, { target := 2, numerator := 9903516772508180046959083520 }, { target := 3, numerator := 9903516772508180046959083520 }, { target := 4, numerator := 9903516772508180046959083520 }, { target := 5, numerator := 15327688865885907402973249536 }, { target := 7, numerator := 692783651982074262373464539136 }, { target := 12, numerator := 15409497375123029272811274240 }, { target := 90, numerator := 9903523856057904351426904064 }, { target := 91, numerator := 9903523856057904351426904064 }, { target := 92, numerator := 9903523856057904351426904064 }, { target := 93, numerator := 9903523856057904351426904064 }, { target := 146, numerator := 5940740983305447031806361600 }, { target := 147, numerator := 1913639560335920139269780275200 }, { target := 149, numerator := 20352361463867360868024513986560 }, { target := 157, numerator := 1913645328045612668830005329920 }, { target := 164, numerator := 5940740983305447031806361600 }, { target := 200, numerator := 2874307986423417537678016512 }, { target := 202, numerator := 112489198675896023590977404928 }, { target := 205, numerator := 112489239933115786228307853312 }, { target := 212, numerator := 2874349243643180175008464896 }, { target := 242, numerator := 61162228610261673655769497600 }, { target := 243, numerator := 19701660213063756693086876467200 }, { target := 245, numerator := 209535441472677563848470990684160 }, { target := 253, numerator := 19701719593868232675294309253120 }, { target := 260, numerator := 61162228610261673655769497600 }, { target := 296, numerator := 570075409699468076507568537600 }, { target := 298, numerator := 22310527029402206551402767974400 }, { target := 301, numerator := 22310535212146216706252577177600 }, { target := 308, numerator := 570083592443478231357377740800 }, { target := 347, numerator := 15027145946946968042130636800 }, { target := 350, numerator := 53863224365144699070683545600 }, { target := 352, numerator := 15031512809957228426559488000 }, { target := 640, numerator := 5940740983305447031806361600 }, { target := 641, numerator := 1913639560335920139269780275200 }, { target := 643, numerator := 20352361463867360868024513986560 }, { target := 651, numerator := 1913645328045612668830005329920 }, { target := 658, numerator := 5940740983305447031806361600 }, { target := 659, numerator := 570075409699468076507568537600 }, { target := 661, numerator := 22310527029402206551402767974400 }, { target := 664, numerator := 22310535212146216706252577177600 }, { target := 671, numerator := 570083592443478231357377740800 }, { target := 710, numerator := 679199658805955159189671116800 }, { target := 713, numerator := 2434519751132619890423863705600 }, { target := 715, numerator := 679397033069643853136396288000 }, { target := 746, numerator := 9903516772508180046959083520 }, { target := 748, numerator := 9903523856057904351426904064 }, { target := 1013, numerator := 9903516772508180046959083520 }, { target := 1015, numerator := 9903523856057904351426904064 }, { target := 1017, numerator := 36250391369417169232199680 }, { target := 1018, numerator := 11677025340293277178354728960 }, { target := 1020, numerator := 124190075014267369714654117888 }, { target := 1028, numerator := 11677060534848004767839420416 }, { target := 1035, numerator := 36250391369417169232199680 }, { target := 1036, numerator := 2874307986423417537678016512 }, { target := 1038, numerator := 112489198675896023590977404928 }, { target := 1041, numerator := 112489239933115786228307853312 }, { target := 1048, numerator := 2874349243643180175008464896 }, { target := 1052, numerator := 15107350367767675757658112000 }, { target := 1055, numerator := 54150708677135424190152704000 }, { target := 1057, numerator := 15111740538045981440081920000 }, { target := 1088, numerator := 9903516772508180046959083520 }, { target := 1090, numerator := 9903523856057904351426904064 }, { target := 1102, numerator := 9903516772508180046959083520 }, { target := 1104, numerator := 9903523856057904351426904064 }]

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
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left6.expected,
    Slot16.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 2884210856316349208781127680 }, { target := 30, numerator := 572039493798346519492952064000 }, { target := 35, numerator := 572039493798346519492952064000 }, { target := 43, numerator := 2884210856316349208781127680 }, { target := 71, numerator := 36173221829514205593600000 }, { target := 72, numerator := 5928094381957271519232000000 }, { target := 74, numerator := 61032026952762447101952000000 }, { target := 82, numerator := 5928094381957271519232000000 }, { target := 89, numerator := 36173221829514205593600000 }, { target := 94, numerator := 54940488852447593052097216512 }, { target := 96, numerator := 2483210146155272288232340979712 }, { target := 101, numerator := 55233722850678132673955758080 }, { target := 104, numerator := 112876758361256561139955793920 }, { target := 105, numerator := 22387393616928140079572975616000 }, { target := 110, numerator := 22387393616928140079572975616000 }, { target := 118, numerator := 112876758361256561139955793920 }, { target := 146, numerator := 11652167383209097769779200000 }, { target := 147, numerator := 1909565819920090612629504000000 }, { target := 149, numerator := 19659719478176979137593344000000 }, { target := 157, numerator := 1909565819920090612629504000000 }, { target := 164, numerator := 11652167383209097769779200000 }, { target := 200, numerator := 1249508023931380733577265152 }, { target := 202, numerator := 49955098964422343987419938816 }, { target := 205, numerator := 49955086756294157692475277312 }, { target := 212, numerator := 1249508023931380733577265152 }, { target := 216, numerator := 15332143066156372995090677760 }, { target := 218, numerator := 692984973731036730199124213760 }, { target := 223, numerator := 15413975348806901068883558400 }, { target := 226, numerator := 112876799760620061116260679680 }, { target := 227, numerator := 22387401827864205394301681664000 }, { target := 232, numerator := 22387401827864205394301681664000 }, { target := 240, numerator := 112876799760620061116260679680 }, { target := 242, numerator := 123925700187201340188917760000 }, { target := 243, numerator := 20309035521421661323866931200000 }, { target := 245, numerator := 209089384119888468449112883200000 }, { target := 253, numerator := 20309035521421661323866931200000 }, { target := 260, numerator := 123925700187201340188917760000 }, { target := 296, numerator := 219151968217525647101065691136 }, { target := 298, numerator := 8761655028119813208121056165888 }, { target := 301, numerator := 8761652886928825205857783382016 }, { target := 308, numerator := 219151968217525647101065691136 }, { target := 624, numerator := 2884252255679849185086013440 }, { target := 625, numerator := 572047704734411834221658112000 }, { target := 630, numerator := 572047704734411834221658112000 }, { target := 638, numerator := 2884252255679849185086013440 }, { target := 640, numerator := 11652202502841941958328320000 }, { target := 641, numerator := 1909571575351529406096998400000 }, { target := 643, numerator := 19659778732572078906959462400000 }, { target := 651, numerator := 1909571575351529406096998400000 }, { target := 658, numerator := 11652202502841941958328320000 }, { target := 659, numerator := 219151994491429045788550889472 }, { target := 661, numerator := 8761656078545596256302059749376 }, { target := 664, numerator := 8761653937354351548860026847232 }, { target := 671, numerator := 219151994491429045788550889472 }, { target := 1017, numerator := 36173221829514205593600000 }, { target := 1018, numerator := 5928094381957271519232000000 }, { target := 1020, numerator := 61032026952762447101952000000 }, { target := 1028, numerator := 5928094381957271519232000000 }, { target := 1035, numerator := 36173221829514205593600000 }, { target := 1036, numerator := 1249481750027982046092066816 }, { target := 1038, numerator := 49954048538639295806416355328 }, { target := 1041, numerator := 49954036330767814690231812096 }, { target := 1048, numerator := 1249481750027982046092066816 }]

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
    Slot17.Left1.expected,
    Slot17.Left2.expected,
    Slot17.Left3.expected,
    Slot17.Left4.expected,
    Slot17.Left5.expected,
    Slot17.Left6.expected,
    Slot17.Left7.expected,
    Slot17.Left8.expected,
    Slot17.Left9.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 49711023776537017984724500480 }, { target := 2, numerator := 49565952695477085052862464000 }, { target := 3, numerator := 49227453506337241545184378880 }, { target := 4, numerator := 49565952695477085052862464000 }, { target := 5, numerator := 7450036125626738209017823232 }, { target := 6, numerator := 182646046950849065769469214720 }, { target := 7, numerator := 135061945245233124950581182464 }, { target := 8, numerator := 150682988734450479259812102144 }, { target := 9, numerator := 7450036125626738209017823232 }, { target := 10, numerator := 150442664988462519962747011072 }, { target := 11, numerator := 153086226194330072230463012864 }, { target := 12, numerator := 7450036125626738209017823232 }, { target := 13, numerator := 182646046950849065769469214720 }, { target := 14, numerator := 7450036125626738209017823232 }, { target := 90, numerator := 49711035628570085343111413760 }, { target := 91, numerator := 49565964512922507273043968000 }, { target := 92, numerator := 49227465243078158442886594560 }, { target := 93, numerator := 49565964512922507273043968000 }, { target := 94, numerator := 27675027636878457914597048320 }, { target := 95, numerator := 678484548517020258551411507200 }, { target := 96, numerator := 501721468771796559613017456640 }, { target := 97, numerator := 559749752526541713304914493440 }, { target := 98, numerator := 27675027636878457914597048320 }, { target := 99, numerator := 558857009699545634017346846720 }, { target := 100, numerator := 568677180796502506180590960640 }, { target := 101, numerator := 27675027636878457914597048320 }, { target := 102, numerator := 678484548517020258551411507200 }, { target := 103, numerator := 27675027636878457914597048320 }, { target := 347, numerator := 637589120869652394261086208 }, { target := 350, numerator := 2322584568547031921656332288 }, { target := 352, numerator := 637589549756452108008161280 }, { target := 614, numerator := 15446110637842224131937927168 }, { target := 617, numerator := 56266484225123257198835662848 }, { target := 619, numerator := 15446121027970823648842874880 }, { target := 710, numerator := 11702845476607490720469614592 }, { target := 713, numerator := 42630665145266489142659776512 }, { target := 715, numerator := 11702853348755524176020766720 }, { target := 736, numerator := 13039725891334181224565440512 }, { target := 739, numerator := 47500600530929620591294021632 }, { target := 741, numerator := 13039734662760988273457233920 }, { target := 881, numerator := 637589120869652394261086208 }, { target := 884, numerator := 2322584568547031921656332288 }, { target := 886, numerator := 637589549756452108008161280 }, { target := 977, numerator := 13039725891334181224565440512 }, { target := 980, numerator := 47500600530929620591294021632 }, { target := 982, numerator := 13039734662760988273457233920 }, { target := 1003, numerator := 13019158500338385986040889344 }, { target := 1006, numerator := 47425678448073264722853494784 }, { target := 1008, numerator := 13019167257930134979650519040 }, { target := 1052, numerator := 637589120869652394261086208 }, { target := 1055, numerator := 2322584568547031921656332288 }, { target := 1057, numerator := 637589549756452108008161280 }, { target := 1078, numerator := 15446110637842224131937927168 }, { target := 1081, numerator := 56266484225123257198835662848 }, { target := 1083, numerator := 15446121027970823648842874880 }, { target := 1092, numerator := 637589120869652394261086208 }, { target := 1095, numerator := 2322584568547031921656332288 }, { target := 1097, numerator := 637589549756452108008161280 }]

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
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected,
    Slot21.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 8222450804136521943975198720 }, { target := 30, numerator := 6123101662654856766790041600 }, { target := 31, numerator := 6472993186235134296320901120 }, { target := 32, numerator := 8397396565926660708740628480 }, { target := 33, numerator := 112490124831059225744171335680 }, { target := 34, numerator := 203461920961931383422194810880 }, { target := 35, numerator := 6123101662654856766790041600 }, { target := 36, numerator := 112490124831059225744171335680 }, { target := 37, numerator := 6647938948025273061086330880 }, { target := 38, numerator := 6647938948025273061086330880 }, { target := 39, numerator := 6472993186235134296320901120 }, { target := 40, numerator := 6472993186235134296320901120 }, { target := 41, numerator := 203461920961931383422194810880 }, { target := 42, numerator := 6472993186235134296320901120 }, { target := 43, numerator := 8222450804136521943975198720 }, { target := 44, numerator := 8397396565926660708740628480 }, { target := 104, numerator := 321785283730986491650617901056 }, { target := 105, numerator := 239627338948606961867481415680 }, { target := 106, numerator := 253320329745670216831337496576 }, { target := 107, numerator := 328631779129518119132545941504 }, { target := 108, numerator := 4402296541255836470879730008064 }, { target := 109, numerator := 7962474148492282761482311041024 }, { target := 110, numerator := 239627338948606961867481415680 }, { target := 111, numerator := 4402296541255836470879730008064 }, { target := 112, numerator := 260166825144201844313265537024 }, { target := 113, numerator := 260166825144201844313265537024 }, { target := 114, numerator := 253320329745670216831337496576 }, { target := 115, numerator := 253320329745670216831337496576 }, { target := 116, numerator := 7962474148492282761482311041024 }, { target := 117, numerator := 253320329745670216831337496576 }, { target := 118, numerator := 321785283730986491650617901056 }, { target := 119, numerator := 328631779129518119132545941504 }, { target := 216, numerator := 7448467901043584892837822464 }, { target := 217, numerator := 182607600154616919953443389440 }, { target := 218, numerator := 135033514851177248702414716928 }, { target := 219, numerator := 150651270127558958961590796288 }, { target := 220, numerator := 7448467901043584892837822464 }, { target := 221, numerator := 150410996969460778803757318144 }, { target := 222, numerator := 153054001708540760539925577728 }, { target := 223, numerator := 7448467901043584892837822464 }, { target := 224, numerator := 182607600154616919953443389440 }, { target := 225, numerator := 7448467901043584892837822464 }, { target := 226, numerator := 321785283730986491650617901056 }, { target := 227, numerator := 239627338948606961867481415680 }, { target := 228, numerator := 253320329745670216831337496576 }, { target := 229, numerator := 328631779129518119132545941504 }, { target := 230, numerator := 4402296541255836470879730008064 }, { target := 231, numerator := 7962474148492282761482311041024 }, { target := 232, numerator := 239627338948606961867481415680 }, { target := 233, numerator := 4402296541255836470879730008064 }, { target := 234, numerator := 260166825144201844313265537024 }, { target := 235, numerator := 260166825144201844313265537024 }, { target := 236, numerator := 253320329745670216831337496576 }, { target := 237, numerator := 253320329745670216831337496576 }, { target := 238, numerator := 7962474148492282761482311041024 }, { target := 239, numerator := 253320329745670216831337496576 }, { target := 240, numerator := 321785283730986491650617901056 }, { target := 241, numerator := 328631779129518119132545941504 }]

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
    Slot21.Left12.expected,
    Slot22.Left0.expected,
    Slot22.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 66134344515859798976102400 }, { target := 72, numerator := 958947995479967085153484800 }, { target := 73, numerator := 1697448175907068173719961600 }, { target := 74, numerator := 55111953763216499146752000 }, { target := 75, numerator := 1058149512253756783617638400 }, { target := 76, numerator := 55111953763216499146752000 }, { target := 77, numerator := 1686425785154424873890611200 }, { target := 78, numerator := 1763582520422927972696064000 }, { target := 79, numerator := 1058149512253756783617638400 }, { target := 80, numerator := 27015879734728727881737830400 }, { target := 81, numerator := 1730515348164998073208012800 }, { target := 82, numerator := 958947995479967085153484800 }, { target := 83, numerator := 1686425785154424873890611200 }, { target := 84, numerator := 55111953763216499146752000 }, { target := 85, numerator := 1730515348164998073208012800 }, { target := 86, numerator := 55111953763216499146752000 }, { target := 87, numerator := 1686425785154424873890611200 }, { target := 88, numerator := 1763582520422927972696064000 }, { target := 89, numerator := 66134344515859798976102400 }, { target := 146, numerator := 7816654923842911629370982400 }, { target := 147, numerator := 113341496395722218625879244800 }, { target := 148, numerator := 200627476378634731820521881600 }, { target := 149, numerator := 6513879103202426357809152000 }, { target := 150, numerator := 125066478781486586069935718400 }, { target := 151, numerator := 6513879103202426357809152000 }, { target := 152, numerator := 199324700557994246548960051200 }, { target := 153, numerator := 208444131302477643449892864000 }, { target := 154, numerator := 125066478781486586069935718400 }, { target := 155, numerator := 3193103536389829400598046310400 }, { target := 156, numerator := 204535803840556187635207372800 }, { target := 157, numerator := 113341496395722218625879244800 }, { target := 158, numerator := 199324700557994246548960051200 }, { target := 159, numerator := 6513879103202426357809152000 }, { target := 160, numerator := 204535803840556187635207372800 }, { target := 161, numerator := 6513879103202426357809152000 }, { target := 162, numerator := 199324700557994246548960051200 }, { target := 163, numerator := 208444131302477643449892864000 }, { target := 164, numerator := 7816654923842911629370982400 }, { target := 624, numerator := 8222450804136521943975198720 }, { target := 625, numerator := 6123101662654856766790041600 }, { target := 626, numerator := 6472993186235134296320901120 }, { target := 627, numerator := 8397396565926660708740628480 }, { target := 628, numerator := 112490124831059225744171335680 }, { target := 629, numerator := 203461920961931383422194810880 }, { target := 630, numerator := 6123101662654856766790041600 }, { target := 631, numerator := 112490124831059225744171335680 }, { target := 632, numerator := 6647938948025273061086330880 }, { target := 633, numerator := 6647938948025273061086330880 }, { target := 634, numerator := 6472993186235134296320901120 }, { target := 635, numerator := 6472993186235134296320901120 }, { target := 636, numerator := 203461920961931383422194810880 }, { target := 637, numerator := 6472993186235134296320901120 }, { target := 638, numerator := 8222450804136521943975198720 }, { target := 639, numerator := 8397396565926660708740628480 }]

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
    Slot22.Left3.expected,
    Slot22.Left11.expected,
    Slot22.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 242, numerator := 74178497081525871319606886400 }, { target := 243, numerator := 1075588207682125134134299852800 }, { target := 244, numerator := 1903914758425830697203243417600 }, { target := 245, numerator := 61815414234604892766339072000 }, { target := 246, numerator := 1186855953304413941113710182400 }, { target := 247, numerator := 61815414234604892766339072000 }, { target := 248, numerator := 1891551675578909718649975603200 }, { target := 249, numerator := 1978093255507356568522850304000 }, { target := 250, numerator := 1186855953304413941113710182400 }, { target := 251, numerator := 30301916057803318434059413094400 }, { target := 252, numerator := 1941004006966593632863046860800 }, { target := 253, numerator := 1075588207682125134134299852800 }, { target := 254, numerator := 1891551675578909718649975603200 }, { target := 255, numerator := 61815414234604892766339072000 }, { target := 256, numerator := 1941004006966593632863046860800 }, { target := 257, numerator := 61815414234604892766339072000 }, { target := 258, numerator := 1891551675578909718649975603200 }, { target := 259, numerator := 1978093255507356568522850304000 }, { target := 260, numerator := 74178497081525871319606886400 }, { target := 640, numerator := 7816660284927908051209420800 }, { target := 641, numerator := 113341574131454666742536601600 }, { target := 642, numerator := 200627613979816306647708467200 }, { target := 643, numerator := 6513883570773256709341184000 }, { target := 644, numerator := 125066564558846528819350732800 }, { target := 645, numerator := 6513883570773256709341184000 }, { target := 646, numerator := 199324837265661655305840230400 }, { target := 647, numerator := 208444274264744214698917888000 }, { target := 648, numerator := 125066564558846528819350732800 }, { target := 649, numerator := 3193105726393050438919048396800 }, { target := 650, numerator := 204535944122280260673313177600 }, { target := 651, numerator := 113341574131454666742536601600 }, { target := 652, numerator := 199324837265661655305840230400 }, { target := 653, numerator := 6513883570773256709341184000 }, { target := 654, numerator := 204535944122280260673313177600 }, { target := 655, numerator := 6513883570773256709341184000 }, { target := 656, numerator := 199324837265661655305840230400 }, { target := 657, numerator := 208444274264744214698917888000 }, { target := 658, numerator := 7816660284927908051209420800 }, { target := 1017, numerator := 66134344515859798976102400 }, { target := 1018, numerator := 958947995479967085153484800 }, { target := 1019, numerator := 1697448175907068173719961600 }, { target := 1020, numerator := 55111953763216499146752000 }, { target := 1021, numerator := 1058149512253756783617638400 }, { target := 1022, numerator := 55111953763216499146752000 }, { target := 1023, numerator := 1686425785154424873890611200 }, { target := 1024, numerator := 1763582520422927972696064000 }, { target := 1025, numerator := 1058149512253756783617638400 }, { target := 1026, numerator := 27015879734728727881737830400 }, { target := 1027, numerator := 1730515348164998073208012800 }, { target := 1028, numerator := 958947995479967085153484800 }, { target := 1029, numerator := 1686425785154424873890611200 }, { target := 1030, numerator := 55111953763216499146752000 }, { target := 1031, numerator := 1730515348164998073208012800 }, { target := 1032, numerator := 55111953763216499146752000 }, { target := 1033, numerator := 1686425785154424873890611200 }, { target := 1034, numerator := 1763582520422927972696064000 }, { target := 1035, numerator := 66134344515859798976102400 }]

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
    Slot23.Left0.expected,
    Slot23.Left1.expected,
    Slot23.Left2.expected,
    Slot23.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 154591389183220705715552256 }, { target := 201, numerator := 174538665206862087098204160 }, { target := 202, numerator := 149604570177310360369889280 }, { target := 203, numerator := 1969793507334586411536875520 }, { target := 204, numerator := 174538665206862087098204160 }, { target := 205, numerator := 149604570177310360369889280 }, { target := 206, numerator := 174538665206862087098204160 }, { target := 207, numerator := 174538665206862087098204160 }, { target := 208, numerator := 7235874377575911096556978176 }, { target := 209, numerator := 179525484212772432443867136 }, { target := 210, numerator := 1969793507334586411536875520 }, { target := 211, numerator := 7235874377575911096556978176 }, { target := 212, numerator := 154591389183220705715552256 }, { target := 213, numerator := 174538665206862087098204160 }, { target := 214, numerator := 179525484212772432443867136 }, { target := 215, numerator := 174538665206862087098204160 }, { target := 296, numerator := 115943541887415529286664192 }, { target := 297, numerator := 130903998905146565323653120 }, { target := 298, numerator := 112203427632982770277416960 }, { target := 299, numerator := 1477345130500939808652656640 }, { target := 300, numerator := 130903998905146565323653120 }, { target := 301, numerator := 112203427632982770277416960 }, { target := 302, numerator := 130903998905146565323653120 }, { target := 303, numerator := 130903998905146565323653120 }, { target := 304, numerator := 5426905783181933322417733632 }, { target := 305, numerator := 134644113159579324332900352 }, { target := 306, numerator := 1477345130500939808652656640 }, { target := 307, numerator := 5426905783181933322417733632 }, { target := 308, numerator := 115943541887415529286664192 }, { target := 309, numerator := 130903998905146565323653120 }, { target := 310, numerator := 134644113159579324332900352 }, { target := 311, numerator := 130903998905146565323653120 }, { target := 331, numerator := 122384849770049725358145536 }, { target := 332, numerator := 138176443288765818952744960 }, { target := 333, numerator := 118436951390370701959495680 }, { target := 334, numerator := 1559419859973214242466693120 }, { target := 335, numerator := 138176443288765818952744960 }, { target := 336, numerator := 118436951390370701959495680 }, { target := 337, numerator := 138176443288765818952744960 }, { target := 338, numerator := 138176443288765818952744960 }, { target := 339, numerator := 5728400548914262951440941056 }, { target := 340, numerator := 142124341668444842351394816 }, { target := 341, numerator := 1559419859973214242466693120 }, { target := 342, numerator := 5728400548914262951440941056 }, { target := 343, numerator := 122384849770049725358145536 }, { target := 344, numerator := 138176443288765818952744960 }, { target := 345, numerator := 142124341668444842351394816 }, { target := 346, numerator := 138176443288765818952744960 }, { target := 467, numerator := 157812043124537803751292928 }, { target := 468, numerator := 178174887398671713912750080 }, { target := 469, numerator := 152721332056004326210928640 }, { target := 470, numerator := 2010830872070723628443893760 }, { target := 471, numerator := 178174887398671713912750080 }, { target := 472, numerator := 152721332056004326210928640 }, { target := 473, numerator := 178174887398671713912750080 }, { target := 474, numerator := 178174887398671713912750080 }, { target := 475, numerator := 7386621760442075911068581888 }, { target := 476, numerator := 183265598467205191453114368 }, { target := 477, numerator := 2010830872070723628443893760 }, { target := 478, numerator := 7386621760442075911068581888 }, { target := 479, numerator := 157812043124537803751292928 }, { target := 480, numerator := 178174887398671713912750080 }, { target := 481, numerator := 183265598467205191453114368 }, { target := 482, numerator := 178174887398671713912750080 }]

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
    Slot23.Left4.expected,
    Slot23.Left5.expected,
    Slot23.Left6.expected,
    Slot23.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 563, numerator := 2112748985504016311445880832 }, { target := 564, numerator := 2385361757827115190342123520 }, { target := 565, numerator := 2044595792423241591721820160 }, { target := 566, numerator := 26920511266906014291003965440 }, { target := 567, numerator := 2385361757827115190342123520 }, { target := 568, numerator := 2044595792423241591721820160 }, { target := 569, numerator := 2385361757827115190342123520 }, { target := 570, numerator := 2385361757827115190342123520 }, { target := 571, numerator := 98890283160204118319612035072 }, { target := 572, numerator := 2453514950907889910066184192 }, { target := 573, numerator := 26920511266906014291003965440 }, { target := 574, numerator := 98890283160204118319612035072 }, { target := 575, numerator := 2112748985504016311445880832 }, { target := 576, numerator := 2385361757827115190342123520 }, { target := 577, numerator := 2453514950907889910066184192 }, { target := 578, numerator := 2385361757827115190342123520 }, { target := 598, numerator := 3694090070690711446994550784 }, { target := 599, numerator := 4170746854005641956284170240 }, { target := 600, numerator := 3574925874861978819672145920 }, { target := 601, numerator := 47069857352349387792349921280 }, { target := 602, numerator := 4170746854005641956284170240 }, { target := 603, numerator := 3574925874861978819672145920 }, { target := 604, numerator := 4170746854005641956284170240 }, { target := 605, numerator := 4170746854005641956284170240 }, { target := 606, numerator := 172907248147491042244809457664 }, { target := 607, numerator := 4289911049834374583606575104 }, { target := 608, numerator := 47069857352349387792349921280 }, { target := 609, numerator := 172907248147491042244809457664 }, { target := 610, numerator := 3694090070690711446994550784 }, { target := 611, numerator := 4170746854005641956284170240 }, { target := 612, numerator := 4289911049834374583606575104 }, { target := 613, numerator := 4170746854005641956284170240 }, { target := 659, numerator := 112722887946098431250923520 }, { target := 660, numerator := 127267776713336938509107200 }, { target := 661, numerator := 109086665754288804436377600 }, { target := 662, numerator := 1436307765764802591745638400 }, { target := 663, numerator := 127267776713336938509107200 }, { target := 664, numerator := 109086665754288804436377600 }, { target := 665, numerator := 127267776713336938509107200 }, { target := 666, numerator := 127267776713336938509107200 }, { target := 667, numerator := 5276158400315768507906129920 }, { target := 668, numerator := 130903998905146565323653120 }, { target := 669, numerator := 1436307765764802591745638400 }, { target := 670, numerator := 5276158400315768507906129920 }, { target := 671, numerator := 112722887946098431250923520 }, { target := 672, numerator := 127267776713336938509107200 }, { target := 673, numerator := 130903998905146565323653120 }, { target := 674, numerator := 127267776713336938509107200 }, { target := 694, numerator := 2112748985504016311445880832 }, { target := 695, numerator := 2385361757827115190342123520 }, { target := 696, numerator := 2044595792423241591721820160 }, { target := 697, numerator := 26920511266906014291003965440 }, { target := 698, numerator := 2385361757827115190342123520 }, { target := 699, numerator := 2044595792423241591721820160 }, { target := 700, numerator := 2385361757827115190342123520 }, { target := 701, numerator := 2385361757827115190342123520 }, { target := 702, numerator := 98890283160204118319612035072 }, { target := 703, numerator := 2453514950907889910066184192 }, { target := 704, numerator := 26920511266906014291003965440 }, { target := 705, numerator := 98890283160204118319612035072 }, { target := 706, numerator := 2112748985504016311445880832 }, { target := 707, numerator := 2385361757827115190342123520 }, { target := 708, numerator := 2453514950907889910066184192 }, { target := 709, numerator := 2385361757827115190342123520 }]

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
    Slot23.Left8.expected,
    Slot23.Left9.expected,
    Slot23.Left10.expected,
    Slot23.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 720, numerator := 119164195828732627322404864 }, { target := 721, numerator := 134540221096956192138199040 }, { target := 722, numerator := 115320189511676736118456320 }, { target := 723, numerator := 1518382495237077025559674880 }, { target := 724, numerator := 134540221096956192138199040 }, { target := 725, numerator := 115320189511676736118456320 }, { target := 726, numerator := 134540221096956192138199040 }, { target := 727, numerator := 134540221096956192138199040 }, { target := 728, numerator := 5577653166048098136929337344 }, { target := 729, numerator := 138384227414012083342147584 }, { target := 730, numerator := 1518382495237077025559674880 }, { target := 731, numerator := 5577653166048098136929337344 }, { target := 732, numerator := 119164195828732627322404864 }, { target := 733, numerator := 134540221096956192138199040 }, { target := 734, numerator := 138384227414012083342147584 }, { target := 735, numerator := 134540221096956192138199040 }, { target := 830, numerator := 122384849770049725358145536 }, { target := 831, numerator := 138176443288765818952744960 }, { target := 832, numerator := 118436951390370701959495680 }, { target := 833, numerator := 1559419859973214242466693120 }, { target := 834, numerator := 138176443288765818952744960 }, { target := 835, numerator := 118436951390370701959495680 }, { target := 836, numerator := 138176443288765818952744960 }, { target := 837, numerator := 138176443288765818952744960 }, { target := 838, numerator := 5728400548914262951440941056 }, { target := 839, numerator := 142124341668444842351394816 }, { target := 840, numerator := 1559419859973214242466693120 }, { target := 841, numerator := 5728400548914262951440941056 }, { target := 842, numerator := 122384849770049725358145536 }, { target := 843, numerator := 138176443288765818952744960 }, { target := 844, numerator := 142124341668444842351394816 }, { target := 845, numerator := 138176443288765818952744960 }, { target := 865, numerator := 122384849770049725358145536 }, { target := 866, numerator := 138176443288765818952744960 }, { target := 867, numerator := 118436951390370701959495680 }, { target := 868, numerator := 1559419859973214242466693120 }, { target := 869, numerator := 138176443288765818952744960 }, { target := 870, numerator := 118436951390370701959495680 }, { target := 871, numerator := 138176443288765818952744960 }, { target := 872, numerator := 138176443288765818952744960 }, { target := 873, numerator := 5728400548914262951440941056 }, { target := 874, numerator := 142124341668444842351394816 }, { target := 875, numerator := 1559419859973214242466693120 }, { target := 876, numerator := 5728400548914262951440941056 }, { target := 877, numerator := 122384849770049725358145536 }, { target := 878, numerator := 138176443288765818952744960 }, { target := 879, numerator := 142124341668444842351394816 }, { target := 880, numerator := 138176443288765818952744960 }, { target := 926, numerator := 119164195828732627322404864 }, { target := 927, numerator := 134540221096956192138199040 }, { target := 928, numerator := 115320189511676736118456320 }, { target := 929, numerator := 1518382495237077025559674880 }, { target := 930, numerator := 134540221096956192138199040 }, { target := 931, numerator := 115320189511676736118456320 }, { target := 932, numerator := 134540221096956192138199040 }, { target := 933, numerator := 134540221096956192138199040 }, { target := 934, numerator := 5577653166048098136929337344 }, { target := 935, numerator := 138384227414012083342147584 }, { target := 936, numerator := 1518382495237077025559674880 }, { target := 937, numerator := 5577653166048098136929337344 }, { target := 938, numerator := 119164195828732627322404864 }, { target := 939, numerator := 134540221096956192138199040 }, { target := 940, numerator := 138384227414012083342147584 }, { target := 941, numerator := 134540221096956192138199040 }]

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
    Slot23.Left12.expected,
    Slot23.Left13.expected,
    Slot23.Left14.expected,
    Slot23.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 961, numerator := 3694090070690711446994550784 }, { target := 962, numerator := 4170746854005641956284170240 }, { target := 963, numerator := 3574925874861978819672145920 }, { target := 964, numerator := 47069857352349387792349921280 }, { target := 965, numerator := 4170746854005641956284170240 }, { target := 966, numerator := 3574925874861978819672145920 }, { target := 967, numerator := 4170746854005641956284170240 }, { target := 968, numerator := 4170746854005641956284170240 }, { target := 969, numerator := 172907248147491042244809457664 }, { target := 970, numerator := 4289911049834374583606575104 }, { target := 971, numerator := 47069857352349387792349921280 }, { target := 972, numerator := 172907248147491042244809457664 }, { target := 973, numerator := 3694090070690711446994550784 }, { target := 974, numerator := 4170746854005641956284170240 }, { target := 975, numerator := 4289911049834374583606575104 }, { target := 976, numerator := 4170746854005641956284170240 }, { target := 987, numerator := 119164195828732627322404864 }, { target := 988, numerator := 134540221096956192138199040 }, { target := 989, numerator := 115320189511676736118456320 }, { target := 990, numerator := 1518382495237077025559674880 }, { target := 991, numerator := 134540221096956192138199040 }, { target := 992, numerator := 115320189511676736118456320 }, { target := 993, numerator := 134540221096956192138199040 }, { target := 994, numerator := 134540221096956192138199040 }, { target := 995, numerator := 5577653166048098136929337344 }, { target := 996, numerator := 138384227414012083342147584 }, { target := 997, numerator := 1518382495237077025559674880 }, { target := 998, numerator := 5577653166048098136929337344 }, { target := 999, numerator := 119164195828732627322404864 }, { target := 1000, numerator := 134540221096956192138199040 }, { target := 1001, numerator := 138384227414012083342147584 }, { target := 1002, numerator := 134540221096956192138199040 }, { target := 1036, numerator := 154591389183220705715552256 }, { target := 1037, numerator := 174538665206862087098204160 }, { target := 1038, numerator := 149604570177310360369889280 }, { target := 1039, numerator := 1969793507334586411536875520 }, { target := 1040, numerator := 174538665206862087098204160 }, { target := 1041, numerator := 149604570177310360369889280 }, { target := 1042, numerator := 174538665206862087098204160 }, { target := 1043, numerator := 174538665206862087098204160 }, { target := 1044, numerator := 7235874377575911096556978176 }, { target := 1045, numerator := 179525484212772432443867136 }, { target := 1046, numerator := 1969793507334586411536875520 }, { target := 1047, numerator := 7235874377575911096556978176 }, { target := 1048, numerator := 154591389183220705715552256 }, { target := 1049, numerator := 174538665206862087098204160 }, { target := 1050, numerator := 179525484212772432443867136 }, { target := 1051, numerator := 174538665206862087098204160 }, { target := 1062, numerator := 157812043124537803751292928 }, { target := 1063, numerator := 178174887398671713912750080 }, { target := 1064, numerator := 152721332056004326210928640 }, { target := 1065, numerator := 2010830872070723628443893760 }, { target := 1066, numerator := 178174887398671713912750080 }, { target := 1067, numerator := 152721332056004326210928640 }, { target := 1068, numerator := 178174887398671713912750080 }, { target := 1069, numerator := 178174887398671713912750080 }, { target := 1070, numerator := 7386621760442075911068581888 }, { target := 1071, numerator := 183265598467205191453114368 }, { target := 1072, numerator := 2010830872070723628443893760 }, { target := 1073, numerator := 7386621760442075911068581888 }, { target := 1074, numerator := 157812043124537803751292928 }, { target := 1075, numerator := 178174887398671713912750080 }, { target := 1076, numerator := 183265598467205191453114368 }, { target := 1077, numerator := 178174887398671713912750080 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent0
