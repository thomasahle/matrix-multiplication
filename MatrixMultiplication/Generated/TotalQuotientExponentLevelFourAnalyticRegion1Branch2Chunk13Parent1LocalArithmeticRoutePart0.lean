import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk13Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 55; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent1

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
    Slot1.Left11.expected,
    Slot1.Left12.expected,
    Slot1.Left13.expected,
    Slot1.Left14.expected,
    Slot1.Left15.expected,
    Slot1.Left16.expected,
    Slot1.Left17.expected,
    Slot1.Left18.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 8656250280780061107277529088 }, { target := 89, numerator := 30967163848261784005200838656 }, { target := 91, numerator := 8656247403087985608587476992 }, { target := 112, numerator := 8475911733263809834209247232 }, { target := 115, numerator := 30322014601422996838425821184 }, { target := 117, numerator := 8475908915523652575075237888 }, { target := 122, numerator := 8530180583200823456726777856 }, { target := 124, numerator := 8530180583200823456726777856 }, { target := 161, numerator := 6672526258101297103526428672 }, { target := 164, numerator := 23870522133035125170675646464 }, { target := 166, numerator := 6672524039880322239952846848 }, { target := 197, numerator := 227471482218688625512714076160 }, { target := 199, numerator := 227471482218688625512714076160 }, { target := 211, numerator := 217519604871620998146532835328 }, { target := 213, numerator := 217519604871620998146532835328 }, { target := 215, numerator := 18278958392573193121557381120 }, { target := 242, numerator := 7108483819334019547272314880 }, { target := 244, numerator := 7108483819334019547272314880 }, { target := 256, numerator := 223206391927088213784350687232 }, { target := 258, numerator := 223206391927088213784350687232 }, { target := 260, numerator := 18801214346646712925030449152 }, { target := 261, numerator := 7108483819334019547272314880 }, { target := 263, numerator := 7108483819334019547272314880 }, { target := 265, numerator := 18278958392573193121557381120 }, { target := 337, numerator := 217519604871620998146532835328 }, { target := 339, numerator := 217519604871620998146532835328 }, { target := 351, numerator := 123687618456411940122538278912 }, { target := 353, numerator := 123687618456411940122538278912 }, { target := 355, numerator := 16189934576279113907665108992 }, { target := 382, numerator := 223206391927088213784350687232 }, { target := 384, numerator := 223206391927088213784350687232 }, { target := 396, numerator := 3484578768237536382072888754176 }, { target := 398, numerator := 3484578768237536382072888754176 }, { target := 400, numerator := 757793389360677234839421714432 }, { target := 401, numerator := 136482889331213175307628445696 }, { target := 403, numerator := 136482889331213175307628445696 }, { target := 405, numerator := 206291101859040322371861872640 }, { target := 416, numerator := 227471482218688625512714076160 }, { target := 418, numerator := 227471482218688625512714076160 }, { target := 420, numerator := 18801214346646712925030449152 }, { target := 421, numerator := 217519604871620998146532835328 }, { target := 423, numerator := 217519604871620998146532835328 }, { target := 425, numerator := 757793389360677234839421714432 }, { target := 426, numerator := 18278958392573193121557381120 }, { target := 453, numerator := 7108483819334019547272314880 }, { target := 455, numerator := 7108483819334019547272314880 }, { target := 467, numerator := 136482889331213175307628445696 }, { target := 469, numerator := 136482889331213175307628445696 }, { target := 471, numerator := 18278958392573193121557381120 }, { target := 472, numerator := 7108483819334019547272314880 }, { target := 474, numerator := 7108483819334019547272314880 }, { target := 476, numerator := 15667678622205594104192040960 }, { target := 487, numerator := 218941301635487802055987298304 }, { target := 489, numerator := 218941301635487802055987298304 }, { target := 491, numerator := 18278958392573193121557381120 }, { target := 492, numerator := 123687618456411940122538278912 }, { target := 494, numerator := 123687618456411940122538278912 }, { target := 496, numerator := 206291101859040322371861872640 }, { target := 497, numerator := 15667678622205594104192040960 }, { target := 498, numerator := 8530180583200823456726777856 }, { target := 500, numerator := 8530180583200823456726777856 }, { target := 502, numerator := 18278958392573193121557381120 }, { target := 503, numerator := 16189934576279113907665108992 }]

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
    Slot2.Left15.expected,
    Slot3.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 14053762653020064155959296 }, { target := 36, numerator := 16688843150461326185201664 }, { target := 37, numerator := 12736222404299433141338112 }, { target := 38, numerator := 131314844789156224457244672 }, { target := 39, numerator := 15810482984647572175454208 }, { target := 40, numerator := 12736222404299433141338112 }, { target := 41, numerator := 15810482984647572175454208 }, { target := 42, numerator := 15810482984647572175454208 }, { target := 43, numerator := 677215687842404341515288576 }, { target := 44, numerator := 15810482984647572175454208 }, { target := 45, numerator := 131314844789156224457244672 }, { target := 46, numerator := 677215687842404341515288576 }, { target := 47, numerator := 14053762653020064155959296 }, { target := 48, numerator := 15810482984647572175454208 }, { target := 49, numerator := 15810482984647572175454208 }, { target := 50, numerator := 16688843150461326185201664 }, { target := 187, numerator := 209733730761400230578411798528 }, { target := 190, numerator := 750308574073509474959345319936 }, { target := 192, numerator := 209733661037319317974734077952 }, { target := 201, numerator := 6672526258101297103526428672 }, { target := 204, numerator := 23870522133035125170675646464 }, { target := 206, numerator := 6672524039880322239952846848 }, { target := 232, numerator := 6672526258101297103526428672 }, { target := 235, numerator := 23870522133035125170675646464 }, { target := 237, numerator := 6672524039880322239952846848 }, { target := 246, numerator := 6852864805617548376594710528 }, { target := 249, numerator := 24515671379873912337450663936 }, { target := 251, numerator := 6852862527444655273465085952 }, { target := 301, numerator := 6852864805617548376594710528 }, { target := 304, numerator := 24515671379873912337450663936 }, { target := 306, numerator := 6852862527444655273465085952 }, { target := 327, numerator := 115957686052949568582905233408 }, { target := 330, numerator := 414830965717340148236336234496 }, { target := 332, numerator := 115957647503866140548369743872 }, { target := 341, numerator := 6311849163068794557389864960 }, { target := 344, numerator := 22580223639357550837125611520 }, { target := 346, numerator := 6311847064751656172928368640 }, { target := 372, numerator := 209733730761400230578411798528 }, { target := 375, numerator := 750308574073509474959345319936 }, { target := 377, numerator := 209733661037319317974734077952 }, { target := 386, numerator := 115957686052949568582905233408 }, { target := 389, numerator := 414830965717340148236336234496 }, { target := 391, numerator := 115957647503866140548369743872 }, { target := 406, numerator := 8656250280780061107277529088 }, { target := 409, numerator := 30967163848261784005200838656 }, { target := 411, numerator := 8656247403087985608587476992 }, { target := 443, numerator := 6672526258101297103526428672 }, { target := 446, numerator := 23870522133035125170675646464 }, { target := 448, numerator := 6672524039880322239952846848 }, { target := 457, numerator := 6311849163068794557389864960 }, { target := 460, numerator := 22580223639357550837125611520 }, { target := 462, numerator := 6311847064751656172928368640 }, { target := 477, numerator := 8475911733263809834209247232 }, { target := 480, numerator := 30322014601422996838425821184 }, { target := 482, numerator := 8475908915523652575075237888 }]

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
  [{ target := 70, numerator := 344543858590169314791260160 }, { target := 71, numerator := 409145832075826061314621440 }, { target := 72, numerator := 312242871847340941529579520 }, { target := 73, numerator := 3219331678701894535080837120 }, { target := 74, numerator := 387611840913940479140167680 }, { target := 75, numerator := 312242871847340941529579520 }, { target := 76, numerator := 387611840913940479140167680 }, { target := 77, numerator := 387611840913940479140167680 }, { target := 78, numerator := 16602707185813783856503848960 }, { target := 79, numerator := 387611840913940479140167680 }, { target := 80, numerator := 3219331678701894535080837120 }, { target := 81, numerator := 16602707185813783856503848960 }, { target := 82, numerator := 344543858590169314791260160 }, { target := 83, numerator := 387611840913940479140167680 }, { target := 84, numerator := 387611840913940479140167680 }, { target := 85, numerator := 409145832075826061314621440 }, { target := 96, numerator := 14053762653020064155959296 }, { target := 97, numerator := 16688843150461326185201664 }, { target := 98, numerator := 12736222404299433141338112 }, { target := 99, numerator := 131314844789156224457244672 }, { target := 100, numerator := 15810482984647572175454208 }, { target := 101, numerator := 12736222404299433141338112 }, { target := 102, numerator := 15810482984647572175454208 }, { target := 103, numerator := 15810482984647572175454208 }, { target := 104, numerator := 677215687842404341515288576 }, { target := 105, numerator := 15810482984647572175454208 }, { target := 106, numerator := 131314844789156224457244672 }, { target := 107, numerator := 677215687842404341515288576 }, { target := 108, numerator := 14053762653020064155959296 }, { target := 109, numerator := 15810482984647572175454208 }, { target := 110, numerator := 15810482984647572175454208 }, { target := 111, numerator := 16688843150461326185201664 }, { target := 145, numerator := 288782155160444544107937792 }, { target := 146, numerator := 342928809253027896128176128 }, { target := 147, numerator := 261708828114152868097818624 }, { target := 148, numerator := 2698308262280403709008543744 }, { target := 149, numerator := 324879924555500112121430016 }, { target := 150, numerator := 261708828114152868097818624 }, { target := 151, numerator := 324879924555500112121430016 }, { target := 152, numerator := 324879924555500112121430016 }, { target := 153, numerator := 13915690101793921469201252352 }, { target := 154, numerator := 324879924555500112121430016 }, { target := 155, numerator := 2698308262280403709008543744 }, { target := 156, numerator := 13915690101793921469201252352 }, { target := 157, numerator := 288782155160444544107937792 }, { target := 158, numerator := 324879924555500112121430016 }, { target := 159, numerator := 324879924555500112121430016 }, { target := 160, numerator := 342928809253027896128176128 }, { target := 171, numerator := 283795336154534198762274816 }, { target := 172, numerator := 337006961683509361030201344 }, { target := 173, numerator := 257189523390046617628311552 }, { target := 174, numerator := 2651712672193928919685005312 }, { target := 175, numerator := 319269753173850973607559168 }, { target := 176, numerator := 257189523390046617628311552 }, { target := 177, numerator := 319269753173850973607559168 }, { target := 178, numerator := 319269753173850973607559168 }, { target := 179, numerator := 13675387760946616702857117696 }, { target := 180, numerator := 319269753173850973607559168 }, { target := 181, numerator := 2651712672193928919685005312 }, { target := 182, numerator := 13675387760946616702857117696 }, { target := 183, numerator := 283795336154534198762274816 }, { target := 184, numerator := 319269753173850973607559168 }, { target := 185, numerator := 319269753173850973607559168 }, { target := 186, numerator := 337006961683509361030201344 }]

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
  [{ target := 216, numerator := 14053762653020064155959296 }, { target := 217, numerator := 16688843150461326185201664 }, { target := 218, numerator := 12736222404299433141338112 }, { target := 219, numerator := 131314844789156224457244672 }, { target := 220, numerator := 15810482984647572175454208 }, { target := 221, numerator := 12736222404299433141338112 }, { target := 222, numerator := 15810482984647572175454208 }, { target := 223, numerator := 15810482984647572175454208 }, { target := 224, numerator := 677215687842404341515288576 }, { target := 225, numerator := 15810482984647572175454208 }, { target := 226, numerator := 131314844789156224457244672 }, { target := 227, numerator := 677215687842404341515288576 }, { target := 228, numerator := 14053762653020064155959296 }, { target := 229, numerator := 15810482984647572175454208 }, { target := 230, numerator := 15810482984647572175454208 }, { target := 231, numerator := 16688843150461326185201664 }, { target := 285, numerator := 284248683336889684702789632 }, { target := 286, numerator := 337545311462556500584562688 }, { target := 287, numerator := 257600369274056276761903104 }, { target := 288, numerator := 2655948634929062991441690624 }, { target := 289, numerator := 319779768754000895290638336 }, { target := 290, numerator := 257600369274056276761903104 }, { target := 291, numerator := 319779768754000895290638336 }, { target := 292, numerator := 319779768754000895290638336 }, { target := 293, numerator := 13697233428296371681615675392 }, { target := 294, numerator := 319779768754000895290638336 }, { target := 295, numerator := 2655948634929062991441690624 }, { target := 296, numerator := 13697233428296371681615675392 }, { target := 297, numerator := 284248683336889684702789632 }, { target := 298, numerator := 319779768754000895290638336 }, { target := 299, numerator := 319779768754000895290638336 }, { target := 300, numerator := 337545311462556500584562688 }, { target := 311, numerator := 254781116483783098569326592 }, { target := 312, numerator := 302552575824492429551075328 }, { target := 313, numerator := 230895386813428433078452224 }, { target := 314, numerator := 2380611057145348327257145344 }, { target := 315, numerator := 286628756044255985890492416 }, { target := 316, numerator := 230895386813428433078452224 }, { target := 317, numerator := 286628756044255985890492416 }, { target := 318, numerator := 286628756044255985890492416 }, { target := 319, numerator := 12277265050562298062309425152 }, { target := 320, numerator := 286628756044255985890492416 }, { target := 321, numerator := 2380611057145348327257145344 }, { target := 322, numerator := 12277265050562298062309425152 }, { target := 323, numerator := 254781116483783098569326592 }, { target := 324, numerator := 286628756044255985890492416 }, { target := 325, numerator := 286628756044255985890492416 }, { target := 326, numerator := 302552575824492429551075328 }, { target := 356, numerator := 344543858590169314791260160 }, { target := 357, numerator := 409145832075826061314621440 }, { target := 358, numerator := 312242871847340941529579520 }, { target := 359, numerator := 3219331678701894535080837120 }, { target := 360, numerator := 387611840913940479140167680 }, { target := 361, numerator := 312242871847340941529579520 }, { target := 362, numerator := 387611840913940479140167680 }, { target := 363, numerator := 387611840913940479140167680 }, { target := 364, numerator := 16602707185813783856503848960 }, { target := 365, numerator := 387611840913940479140167680 }, { target := 366, numerator := 3219331678701894535080837120 }, { target := 367, numerator := 16602707185813783856503848960 }, { target := 368, numerator := 344543858590169314791260160 }, { target := 369, numerator := 387611840913940479140167680 }, { target := 370, numerator := 387611840913940479140167680 }, { target := 371, numerator := 409145832075826061314621440 }]

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
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left6.expected,
    Slot4.Left14.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left3.expected,
    Slot5.Left11.expected,
    Slot5.Left18.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 79984442153847102035407667200 }, { target := 37, numerator := 2953719038129462558091902976000 }, { target := 40, numerator := 2953718314838189373480186675200 }, { target := 47, numerator := 79985165445120286647123968000 }, { target := 86, numerator := 782225220628705836260558635008 }, { target := 89, numerator := 2845121743753054394043345141760 }, { target := 91, numerator := 782225220628705836260558635008 }, { target := 122, numerator := 92964403603495769387586027520 }, { target := 124, numerator := 92964359274624309874856558592 }, { target := 145, numerator := 273472226894982902761694167040 }, { target := 147, numerator := 10098965514139293023095436083200 }, { target := 150, numerator := 10098963041157424986282671472640 }, { target := 157, numerator := 273474699876850939574458777600 }, { target := 161, numerator := 27375932470953628764401905434624 }, { target := 164, numerator := 99572167547888379914628659937280 }, { target := 166, numerator := 27375932470953628764401905434624 }, { target := 197, numerator := 9747150050282641247561874145280 }, { target := 199, numerator := 9747145402480418813742088716288 }, { target := 215, numerator := 58909774598200162272128532480 }, { target := 216, numerator := 79984416318745177641325690880 }, { target := 218, numerator := 2953718084073519287034603110400 }, { target := 221, numerator := 2953717360782479726653556654080 }, { target := 228, numerator := 79985139609784738022372147200 }, { target := 232, numerator := 27375945897811123260131458940928 }, { target := 235, numerator := 99572216384263378357843038044160 }, { target := 237, numerator := 27375945897811123260131458940928 }, { target := 242, numerator := 105064535277033234612501872640000 }, { target := 244, numerator := 105064485178370749631922438144000 }, { target := 260, numerator := 4932464463800453106121140338688 }, { target := 406, numerator := 782218507199958588395781881856 }, { target := 409, numerator := 2845097325565555172436156088320 }, { target := 411, numerator := 782218507199958588395781881856 }, { target := 416, numerator := 9747157485650441255221586821120 }, { target := 418, numerator := 9747152837844673362595153969152 }, { target := 420, numerator := 4932466248854983630847031115776 }, { target := 427, numerator := 14053762653020064155959296 }, { target := 428, numerator := 16688843150461326185201664 }, { target := 429, numerator := 12736222404299433141338112 }, { target := 430, numerator := 131314844789156224457244672 }, { target := 431, numerator := 15810482984647572175454208 }, { target := 432, numerator := 12736222404299433141338112 }, { target := 433, numerator := 15810482984647572175454208 }, { target := 434, numerator := 15810482984647572175454208 }, { target := 435, numerator := 677215687842404341515288576 }, { target := 436, numerator := 15810482984647572175454208 }, { target := 437, numerator := 131314844789156224457244672 }, { target := 438, numerator := 677215687842404341515288576 }, { target := 439, numerator := 14053762653020064155959296 }, { target := 440, numerator := 15810482984647572175454208 }, { target := 441, numerator := 15810482984647572175454208 }, { target := 442, numerator := 16688843150461326185201664 }, { target := 498, numerator := 92964403603495769387586027520 }, { target := 500, numerator := 92964359274624309874856558592 }, { target := 502, numerator := 58907989543669637546237755392 }]

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
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 435311714205507266386329600 }, { target := 17, numerator := 7313236798652522075290337280 }, { target := 18, numerator := 15845346397080464496462397440 }, { target := 19, numerator := 522374057046608719663595520 }, { target := 20, numerator := 8357984912745739514617528320 }, { target := 21, numerator := 609436399887710172940861440 }, { target := 22, numerator := 15845346397080464496462397440 }, { target := 23, numerator := 15845346397080464496462397440 }, { target := 24, numerator := 8357984912745739514617528320 }, { target := 25, numerator := 195542022021113864060739256320 }, { target := 26, numerator := 15671221711398261589907865600 }, { target := 27, numerator := 7313236798652522075290337280 }, { target := 28, numerator := 15845346397080464496462397440 }, { target := 29, numerator := 609436399887710172940861440 }, { target := 30, numerator := 15671221711398261589907865600 }, { target := 31, numerator := 609436399887710172940861440 }, { target := 32, numerator := 15845346397080464496462397440 }, { target := 33, numerator := 15845346397080464496462397440 }, { target := 34, numerator := 522374057046608719663595520 }, { target := 86, numerator := 3394957753735541297682820628480 }, { target := 89, numerator := 11654296357772490590956451528704 }, { target := 91, numerator := 3394957753735541297682820628480 }, { target := 122, numerator := 51178604256801434176623476736 }, { target := 124, numerator := 51178604256801434176623476736 }, { target := 126, numerator := 435114875917025739402117120 }, { target := 127, numerator := 7309929915406032421955567616 }, { target := 128, numerator := 15838181483379736914237063168 }, { target := 129, numerator := 522137851100430887282540544 }, { target := 130, numerator := 8354205617606894196520648704 }, { target := 131, numerator := 609160826283836035162963968 }, { target := 132, numerator := 15838181483379736914237063168 }, { target := 133, numerator := 15838181483379736914237063168 }, { target := 134, numerator := 8354205617606894196520648704 }, { target := 135, numerator := 195453602261927962139431010304 }, { target := 136, numerator := 15664135533012926618476216320 }, { target := 137, numerator := 7309929915406032421955567616 }, { target := 138, numerator := 15838181483379736914237063168 }, { target := 139, numerator := 609160826283836035162963968 }, { target := 140, numerator := 15664135533012926618476216320 }, { target := 141, numerator := 609160826283836035162963968 }, { target := 142, numerator := 15838181483379736914237063168 }, { target := 143, numerator := 15838181483379736914237063168 }, { target := 144, numerator := 522137851100430887282540544 }, { target := 161, numerator := 123034392730371393097283309404160 }, { target := 164, numerator := 422355557591428315386340565843968 }, { target := 166, numerator := 123034392730371393097283309404160 }, { target := 197, numerator := 7558812021131205820819886309376 }, { target := 199, numerator := 7558812021131205820819886309376 }, { target := 215, numerator := 22346842659848968465796825088 }, { target := 232, numerator := 123034437945030541828610745958400 }, { target := 235, numerator := 422355712805447357354020773560320 }, { target := 237, numerator := 123034437945030541828610745958400 }, { target := 242, numerator := 78784233572398622044746877501440 }, { target := 244, numerator := 78784233572398622044746877501440 }, { target := 260, numerator := 1879129057682495133779257982976 }, { target := 406, numerator := 3394912539076392566355384074240 }, { target := 409, numerator := 11654141143753448623276243812352 }, { target := 411, numerator := 3394912539076392566355384074240 }, { target := 416, numerator := 7558812021131205820819886309376 }, { target := 418, numerator := 7558812021131205820819886309376 }, { target := 420, numerator := 1879128604335312778293317468160 }, { target := 498, numerator := 51178604256801434176623476736 }, { target := 500, numerator := 51178604256801434176623476736 }, { target := 502, numerator := 22347296007031323951737339904 }]

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
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
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
  [{ target := 0, numerator := 2611279770367599017365340160 }, { target := 1, numerator := 2030995376952577013506375680 }, { target := 2, numerator := 2321137573660088015435857920 }, { target := 3, numerator := 2727336649050603418137133056 }, { target := 4, numerator := 32205783834533721214172528640 }, { target := 5, numerator := 72419492298194746081598767104 }, { target := 6, numerator := 2030995376952577013506375680 }, { target := 7, numerator := 32205783834533721214172528640 }, { target := 8, numerator := 2321137573660088015435857920 }, { target := 9, numerator := 2263109134318585815049961472 }, { target := 10, numerator := 2263109134318585815049961472 }, { target := 11, numerator := 2263109134318585815049961472 }, { target := 12, numerator := 72419492298194746081598767104 }, { target := 13, numerator := 2263109134318585815049961472 }, { target := 14, numerator := 2611279770367599017365340160 }, { target := 15, numerator := 2727336649050603418137133056 }, { target := 16, numerator := 7118533015209566152287059968 }, { target := 17, numerator := 1136453814601144918169800933376 }, { target := 19, numerator := 11340100069467792151024360226816 }, { target := 27, numerator := 1136453814601144918169800933376 }, { target := 34, numerator := 7117720768174512573310304256 }, { target := 35, numerator := 1395191253314394480481123958784 }, { target := 37, numerator := 52420919531706279313959643250688 }, { target := 40, numerator := 52416954826660443011154104549376 }, { target := 47, numerator := 1399155958360230783286662660096 }, { target := 122, numerator := 6932292325858153084349317120 }, { target := 124, numerator := 6932292325858153084349317120 }, { target := 126, numerator := 7118533015209566152287059968 }, { target := 127, numerator := 1136453814601144918169800933376 }, { target := 129, numerator := 11340100069467792151024360226816 }, { target := 137, numerator := 1136453814601144918169800933376 }, { target := 144, numerator := 7117720768174512573310304256 }, { target := 145, numerator := 4729321548150719762416999071744 }, { target := 147, numerator := 177692759846529672578665868689408 }, { target := 150, numerator := 177679320567175825971163552546816 }, { target := 157, numerator := 4742760827504566369919315214336 }, { target := 197, numerator := 1106721011312161475543265443840 }, { target := 199, numerator := 1106721011312161475543265443840 }, { target := 215, numerator := 2611279770367599017365340160 }, { target := 216, numerator := 1395191253314394480481123958784 }, { target := 218, numerator := 52420919531706279313959643250688 }, { target := 221, numerator := 52416954826660443011154104549376 }, { target := 228, numerator := 1399155958360230783286662660096 }, { target := 242, numerator := 11043411404859623170328955453440 }, { target := 244, numerator := 11043411404859623170328955453440 }, { target := 260, numerator := 2030995376952577013506375680 }, { target := 265, numerator := 2321137573660088015435857920 }, { target := 355, numerator := 2727336649050603418137133056 }, { target := 400, numerator := 32205783834533721214172528640 }, { target := 405, numerator := 72419492298194746081598767104 }, { target := 416, numerator := 1106721011312161475543265443840 }, { target := 418, numerator := 1106721011312161475543265443840 }, { target := 420, numerator := 2030995376952577013506375680 }, { target := 425, numerator := 32205783834533721214172528640 }, { target := 426, numerator := 2321137573660088015435857920 }, { target := 471, numerator := 2263109134318585815049961472 }, { target := 476, numerator := 2263109134318585815049961472 }, { target := 491, numerator := 2263109134318585815049961472 }, { target := 496, numerator := 72419492298194746081598767104 }, { target := 497, numerator := 2263109134318585815049961472 }, { target := 498, numerator := 6931501329472272418776023040 }, { target := 500, numerator := 6931501329472272418776023040 }, { target := 502, numerator := 2611279770367599017365340160 }, { target := 503, numerator := 2727336649050603418137133056 }]

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
    Slot21.Left4.expected,
    Slot21.Left5.expected,
    Slot21.Left6.expected,
    Slot21.Left7.expected,
    Slot21.Left8.expected,
    Slot21.Left9.expected,
    Slot21.Left10.expected,
    Slot21.Left11.expected,
    Slot21.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 21881283437768781622759391232 }, { target := 1, numerator := 1839980535647443151825523441664 }, { target := 6, numerator := 1839980091744993762078873354240 }, { target := 14, numerator := 21881727340218171369409478656 }, { target := 16, numerator := 51178604256801434176623476736 }, { target := 17, numerator := 7558812021131205820819886309376 }, { target := 19, numerator := 78784233572398622044746877501440 }, { target := 27, numerator := 7558812021131205820819886309376 }, { target := 34, numerator := 51178604256801434176623476736 }, { target := 35, numerator := 3415516642030266012848441262080 }, { target := 37, numerator := 123779453647188337342926930575360 }, { target := 40, numerator := 123779499135654465174363334246400 }, { target := 47, numerator := 3415471153564138181412037591040 }, { target := 86, numerator := 1389284270406343916578513354752 }, { target := 89, numerator := 4709298471396735562384913989632 }, { target := 91, numerator := 1389284270406343916578513354752 }, { target := 122, numerator := 435311714205507266386329600 }, { target := 124, numerator := 435114875917025739402117120 }, { target := 126, numerator := 51178604256801434176623476736 }, { target := 127, numerator := 7558812021131205820819886309376 }, { target := 129, numerator := 78784233572398622044746877501440 }, { target := 137, numerator := 7558812021131205820819886309376 }, { target := 144, numerator := 51178604256801434176623476736 }, { target := 145, numerator := 11724871426551896064862122409984 }, { target := 147, numerator := 424913221444424449714477468745728 }, { target := 150, numerator := 424913377598374975585877984542720 }, { target := 157, numerator := 11724715272601370193461606612992 }, { target := 161, numerator := 52198979009242076273979754020864 }, { target := 164, numerator := 176940441415057066753763022209024 }, { target := 166, numerator := 52198979009242076273979754020864 }, { target := 197, numerator := 7313236798652522075290337280 }, { target := 199, numerator := 7309929915406032421955567616 }, { target := 211, numerator := 15845346397080464496462397440 }, { target := 213, numerator := 15838181483379736914237063168 }, { target := 216, numerator := 3415516642030266012848441262080 }, { target := 218, numerator := 123779453647188337342926930575360 }, { target := 221, numerator := 123779499135654465174363334246400 }, { target := 228, numerator := 3415471153564138181412037591040 }, { target := 232, numerator := 52195031090027491121868966985728 }, { target := 235, numerator := 176927059035137796661534206722048 }, { target := 237, numerator := 52195031090027491121868966985728 }, { target := 242, numerator := 522374057046608719663595520 }, { target := 244, numerator := 522137851100430887282540544 }, { target := 256, numerator := 8357984912745739514617528320 }, { target := 258, numerator := 8354205617606894196520648704 }, { target := 261, numerator := 609436399887710172940861440 }, { target := 263, numerator := 609160826283836035162963968 }, { target := 337, numerator := 15845346397080464496462397440 }, { target := 339, numerator := 15838181483379736914237063168 }, { target := 351, numerator := 15845346397080464496462397440 }, { target := 353, numerator := 15838181483379736914237063168 }, { target := 382, numerator := 8357984912745739514617528320 }, { target := 384, numerator := 8354205617606894196520648704 }, { target := 396, numerator := 195542022021113864060739256320 }, { target := 398, numerator := 195453602261927962139431010304 }, { target := 401, numerator := 15671221711398261589907865600 }, { target := 403, numerator := 15664135533012926618476216320 }, { target := 406, numerator := 1393232189620929068689300389888 }, { target := 409, numerator := 4722680851316005654613729476608 }, { target := 411, numerator := 1393232189620929068689300389888 }, { target := 416, numerator := 7313236798652522075290337280 }, { target := 418, numerator := 7309929915406032421955567616 }, { target := 421, numerator := 15845346397080464496462397440 }, { target := 423, numerator := 15838181483379736914237063168 }]

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
    Slot23.Left0.expected,
    Slot23.Left3.expected,
    Slot23.Left5.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected,
    Slot25.Left0.expected,
    Slot26.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 57974698810927143823364587520 }, { target := 1, numerator := 4854171377073461786976360333312 }, { target := 6, numerator := 4854173133793793414484379828224 }, { target := 14, numerator := 57972942090595516315345092608 }, { target := 16, numerator := 92816794197964655114185605120 }, { target := 17, numerator := 9731673470336177860379337031680 }, { target := 19, numerator := 104897713214033816964657315840000 }, { target := 27, numerator := 9731680893898058846115169566720 }, { target := 34, numerator := 92816794197964655114185605120 }, { target := 35, numerator := 783006079346578265345919811584 }, { target := 37, numerator := 27403260579235089836290502295552 }, { target := 40, numerator := 27403274019495985873817639583744 }, { target := 47, numerator := 782999359216130246582351167488 }, { target := 86, numerator := 80191229512051560899648946176 }, { target := 87, numerator := 344543858590169314791260160 }, { target := 88, numerator := 14053762653020064155959296 }, { target := 89, numerator := 274419978271577041047396548608 }, { target := 90, numerator := 283795336154534198762274816 }, { target := 91, numerator := 80191203614696378856424603648 }, { target := 92, numerator := 284248683336889684702789632 }, { target := 93, numerator := 254781116483783098569326592 }, { target := 94, numerator := 344543858590169314791260160 }, { target := 95, numerator := 14053762653020064155959296 }, { target := 126, numerator := 92816749939478828277722775552 }, { target := 127, numerator := 9731668829913762067451612233728 }, { target := 129, numerator := 104897663194918271464834596864000 }, { target := 137, numerator := 9731676253472103223880331558912 }, { target := 144, numerator := 92816749939478828277722775552 }, { target := 145, numerator := 2847961895231719784004955668480 }, { target := 147, numerator := 99671565768550110266427640381440 }, { target := 150, numerator := 99671614653676169351961174343680 }, { target := 157, numerator := 2847937452668690241238188687360 }, { target := 161, numerator := 2960836433402063672689714790400 }, { target := 164, numerator := 10123300370799869632789641953280 }, { target := 166, numerator := 2960835477047190417846734684160 }, { target := 216, numerator := 783006079346578265345919811584 }, { target := 218, numerator := 27403260579235089836290502295552 }, { target := 221, numerator := 27403274019495985873817639583744 }, { target := 228, numerator := 782999359216130246582351167488 }, { target := 232, numerator := 2960835708367919950283753390080 }, { target := 235, numerator := 10123297891859009142876123693056 }, { target := 237, numerator := 2960834752013280882621396549632 }, { target := 406, numerator := 80177900783542263241454387200 }, { target := 409, numerator := 274133675057277086416806871040 }, { target := 411, numerator := 80177874885952894017606778880 }, { target := 453, numerator := 609436399887710172940861440 }, { target := 455, numerator := 609160826283836035162963968 }, { target := 467, numerator := 15671221711398261589907865600 }, { target := 469, numerator := 15664135533012926618476216320 }, { target := 472, numerator := 609436399887710172940861440 }, { target := 474, numerator := 609160826283836035162963968 }, { target := 487, numerator := 15845346397080464496462397440 }, { target := 489, numerator := 15838181483379736914237063168 }, { target := 492, numerator := 15845346397080464496462397440 }, { target := 494, numerator := 15838181483379736914237063168 }, { target := 498, numerator := 522374057046608719663595520 }, { target := 500, numerator := 522137851100430887282540544 }]

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
    Slot26.Left1.expected,
    Slot26.Left2.expected,
    Slot26.Left3.expected,
    Slot26.Left4.expected,
    Slot26.Left5.expected,
    Slot26.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 112, numerator := 16688843150461326185201664 }, { target := 113, numerator := 409145832075826061314621440 }, { target := 114, numerator := 16688843150461326185201664 }, { target := 115, numerator := 342928809253027896128176128 }, { target := 116, numerator := 337006961683509361030201344 }, { target := 117, numerator := 16688843150461326185201664 }, { target := 118, numerator := 337545311462556500584562688 }, { target := 119, numerator := 302552575824492429551075328 }, { target := 120, numerator := 409145832075826061314621440 }, { target := 121, numerator := 16688843150461326185201664 }, { target := 161, numerator := 12736222404299433141338112 }, { target := 162, numerator := 312242871847340941529579520 }, { target := 163, numerator := 12736222404299433141338112 }, { target := 164, numerator := 261708828114152868097818624 }, { target := 165, numerator := 257189523390046617628311552 }, { target := 166, numerator := 12736222404299433141338112 }, { target := 167, numerator := 257600369274056276761903104 }, { target := 168, numerator := 230895386813428433078452224 }, { target := 169, numerator := 312242871847340941529579520 }, { target := 170, numerator := 12736222404299433141338112 }, { target := 187, numerator := 131314844789156224457244672 }, { target := 188, numerator := 3219331678701894535080837120 }, { target := 189, numerator := 131314844789156224457244672 }, { target := 190, numerator := 2698308262280403709008543744 }, { target := 191, numerator := 2651712672193928919685005312 }, { target := 192, numerator := 131314844789156224457244672 }, { target := 193, numerator := 2655948634929062991441690624 }, { target := 194, numerator := 2380611057145348327257145344 }, { target := 195, numerator := 3219331678701894535080837120 }, { target := 196, numerator := 131314844789156224457244672 }, { target := 201, numerator := 15810482984647572175454208 }, { target := 202, numerator := 387611840913940479140167680 }, { target := 203, numerator := 15810482984647572175454208 }, { target := 204, numerator := 324879924555500112121430016 }, { target := 205, numerator := 319269753173850973607559168 }, { target := 206, numerator := 15810482984647572175454208 }, { target := 207, numerator := 319779768754000895290638336 }, { target := 208, numerator := 286628756044255985890492416 }, { target := 209, numerator := 387611840913940479140167680 }, { target := 210, numerator := 15810482984647572175454208 }, { target := 232, numerator := 12736222404299433141338112 }, { target := 233, numerator := 312242871847340941529579520 }, { target := 234, numerator := 12736222404299433141338112 }, { target := 235, numerator := 261708828114152868097818624 }, { target := 236, numerator := 257189523390046617628311552 }, { target := 237, numerator := 12736222404299433141338112 }, { target := 238, numerator := 257600369274056276761903104 }, { target := 239, numerator := 230895386813428433078452224 }, { target := 240, numerator := 312242871847340941529579520 }, { target := 241, numerator := 12736222404299433141338112 }, { target := 246, numerator := 15810482984647572175454208 }, { target := 247, numerator := 387611840913940479140167680 }, { target := 248, numerator := 15810482984647572175454208 }, { target := 249, numerator := 324879924555500112121430016 }, { target := 250, numerator := 319269753173850973607559168 }, { target := 251, numerator := 15810482984647572175454208 }, { target := 252, numerator := 319779768754000895290638336 }, { target := 253, numerator := 286628756044255985890492416 }, { target := 254, numerator := 387611840913940479140167680 }, { target := 255, numerator := 15810482984647572175454208 }]

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
    Slot26.Left7.expected,
    Slot26.Left8.expected,
    Slot26.Left9.expected,
    Slot26.Left10.expected,
    Slot26.Left11.expected,
    Slot26.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 301, numerator := 15810482984647572175454208 }, { target := 302, numerator := 387611840913940479140167680 }, { target := 303, numerator := 15810482984647572175454208 }, { target := 304, numerator := 324879924555500112121430016 }, { target := 305, numerator := 319269753173850973607559168 }, { target := 306, numerator := 15810482984647572175454208 }, { target := 307, numerator := 319779768754000895290638336 }, { target := 308, numerator := 286628756044255985890492416 }, { target := 309, numerator := 387611840913940479140167680 }, { target := 310, numerator := 15810482984647572175454208 }, { target := 327, numerator := 677215687842404341515288576 }, { target := 328, numerator := 16602707185813783856503848960 }, { target := 329, numerator := 677215687842404341515288576 }, { target := 330, numerator := 13915690101793921469201252352 }, { target := 331, numerator := 13675387760946616702857117696 }, { target := 332, numerator := 677215687842404341515288576 }, { target := 333, numerator := 13697233428296371681615675392 }, { target := 334, numerator := 12277265050562298062309425152 }, { target := 335, numerator := 16602707185813783856503848960 }, { target := 336, numerator := 677215687842404341515288576 }, { target := 341, numerator := 15810482984647572175454208 }, { target := 342, numerator := 387611840913940479140167680 }, { target := 343, numerator := 15810482984647572175454208 }, { target := 344, numerator := 324879924555500112121430016 }, { target := 345, numerator := 319269753173850973607559168 }, { target := 346, numerator := 15810482984647572175454208 }, { target := 347, numerator := 319779768754000895290638336 }, { target := 348, numerator := 286628756044255985890492416 }, { target := 349, numerator := 387611840913940479140167680 }, { target := 350, numerator := 15810482984647572175454208 }, { target := 372, numerator := 131314844789156224457244672 }, { target := 373, numerator := 3219331678701894535080837120 }, { target := 374, numerator := 131314844789156224457244672 }, { target := 375, numerator := 2698308262280403709008543744 }, { target := 376, numerator := 2651712672193928919685005312 }, { target := 377, numerator := 131314844789156224457244672 }, { target := 378, numerator := 2655948634929062991441690624 }, { target := 379, numerator := 2380611057145348327257145344 }, { target := 380, numerator := 3219331678701894535080837120 }, { target := 381, numerator := 131314844789156224457244672 }, { target := 386, numerator := 677215687842404341515288576 }, { target := 387, numerator := 16602707185813783856503848960 }, { target := 388, numerator := 677215687842404341515288576 }, { target := 389, numerator := 13915690101793921469201252352 }, { target := 390, numerator := 13675387760946616702857117696 }, { target := 391, numerator := 677215687842404341515288576 }, { target := 392, numerator := 13697233428296371681615675392 }, { target := 393, numerator := 12277265050562298062309425152 }, { target := 394, numerator := 16602707185813783856503848960 }, { target := 395, numerator := 677215687842404341515288576 }, { target := 406, numerator := 14053762653020064155959296 }, { target := 407, numerator := 344543858590169314791260160 }, { target := 408, numerator := 14053762653020064155959296 }, { target := 409, numerator := 288782155160444544107937792 }, { target := 410, numerator := 283795336154534198762274816 }, { target := 411, numerator := 14053762653020064155959296 }, { target := 412, numerator := 284248683336889684702789632 }, { target := 413, numerator := 254781116483783098569326592 }, { target := 414, numerator := 344543858590169314791260160 }, { target := 415, numerator := 14053762653020064155959296 }]

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
    Slot26.Left13.expected,
    Slot26.Left14.expected,
    Slot26.Left15.expected,
    Slot27.Left0.expected,
    Slot27.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 8822716632333523820879020032 }, { target := 36, numerator := 8638910035826575407944040448 }, { target := 37, numerator := 6800844070757091278594244608 }, { target := 38, numerator := 213767071737581004243381256192 }, { target := 39, numerator := 6800844070757091278594244608 }, { target := 40, numerator := 6800844070757091278594244608 }, { target := 41, numerator := 6984650667264039691529224192 }, { target := 42, numerator := 6984650667264039691529224192 }, { target := 43, numerator := 118187641553967829517191872512 }, { target := 44, numerator := 6433230877743194452724285440 }, { target := 45, numerator := 213767071737581004243381256192 }, { target := 46, numerator := 118187641553967829517191872512 }, { target := 47, numerator := 8822716632333523820879020032 }, { target := 48, numerator := 6800844070757091278594244608 }, { target := 49, numerator := 6433230877743194452724285440 }, { target := 50, numerator := 8638910035826575407944040448 }, { target := 145, numerator := 31562686229959126005300854784 }, { target := 146, numerator := 30905130266834977546857086976 }, { target := 147, numerator := 24329570635593492962419408896 }, { target := 148, numerator := 764737585113384657170101960704 }, { target := 149, numerator := 24329570635593492962419408896 }, { target := 150, numerator := 24329570635593492962419408896 }, { target := 151, numerator := 24987126598717641420863176704 }, { target := 152, numerator := 24987126598717641420863176704 }, { target := 153, numerator := 422808484288827458779342700544 }, { target := 154, numerator := 23014458709345196045531873280 }, { target := 155, numerator := 764737585113384657170101960704 }, { target := 156, numerator := 422808484288827458779342700544 }, { target := 157, numerator := 31562686229959126005300854784 }, { target := 158, numerator := 24329570635593492962419408896 }, { target := 159, numerator := 23014458709345196045531873280 }, { target := 160, numerator := 30905130266834977546857086976 }, { target := 443, numerator := 15810482984647572175454208 }, { target := 444, numerator := 387611840913940479140167680 }, { target := 445, numerator := 15810482984647572175454208 }, { target := 446, numerator := 324879924555500112121430016 }, { target := 447, numerator := 319269753173850973607559168 }, { target := 448, numerator := 15810482984647572175454208 }, { target := 449, numerator := 319779768754000895290638336 }, { target := 450, numerator := 286628756044255985890492416 }, { target := 451, numerator := 387611840913940479140167680 }, { target := 452, numerator := 15810482984647572175454208 }, { target := 457, numerator := 15810482984647572175454208 }, { target := 458, numerator := 387611840913940479140167680 }, { target := 459, numerator := 15810482984647572175454208 }, { target := 460, numerator := 324879924555500112121430016 }, { target := 461, numerator := 319269753173850973607559168 }, { target := 462, numerator := 15810482984647572175454208 }, { target := 463, numerator := 319779768754000895290638336 }, { target := 464, numerator := 286628756044255985890492416 }, { target := 465, numerator := 387611840913940479140167680 }, { target := 466, numerator := 15810482984647572175454208 }, { target := 477, numerator := 16688843150461326185201664 }, { target := 478, numerator := 409145832075826061314621440 }, { target := 479, numerator := 16688843150461326185201664 }, { target := 480, numerator := 342928809253027896128176128 }, { target := 481, numerator := 337006961683509361030201344 }, { target := 482, numerator := 16688843150461326185201664 }, { target := 483, numerator := 337545311462556500584562688 }, { target := 484, numerator := 302552575824492429551075328 }, { target := 485, numerator := 409145832075826061314621440 }, { target := 486, numerator := 16688843150461326185201664 }]

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
    Slot27.Left5.expected,
    Slot28.Left0.expected,
    Slot28.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 8994408097932841059813949440 }, { target := 17, numerator := 239850882611542428261705318400 }, { target := 18, numerator := 229357406497287447025255710720 }, { target := 19, numerator := 7495340081610700883178291200 }, { target := 20, numerator := 235353678562576007731798343680 }, { target := 21, numerator := 7495340081610700883178291200 }, { target := 22, numerator := 229357406497287447025255710720 }, { target := 23, numerator := 130418917420026195367302266880 }, { target := 24, numerator := 235353678562576007731798343680 }, { target := 25, numerator := 3674215708005565572933998346240 }, { target := 26, numerator := 143910529566925456957023191040 }, { target := 27, numerator := 239850882611542428261705318400 }, { target := 28, numerator := 229357406497287447025255710720 }, { target := 29, numerator := 7495340081610700883178291200 }, { target := 30, numerator := 143910529566925456957023191040 }, { target := 31, numerator := 7495340081610700883178291200 }, { target := 32, numerator := 230856474513609587201891368960 }, { target := 33, numerator := 130418917420026195367302266880 }, { target := 34, numerator := 8994408097932841059813949440 }, { target := 126, numerator := 8994408097932841059813949440 }, { target := 127, numerator := 239850882611542428261705318400 }, { target := 128, numerator := 229357406497287447025255710720 }, { target := 129, numerator := 7495340081610700883178291200 }, { target := 130, numerator := 235353678562576007731798343680 }, { target := 131, numerator := 7495340081610700883178291200 }, { target := 132, numerator := 229357406497287447025255710720 }, { target := 133, numerator := 130418917420026195367302266880 }, { target := 134, numerator := 235353678562576007731798343680 }, { target := 135, numerator := 3674215708005565572933998346240 }, { target := 136, numerator := 143910529566925456957023191040 }, { target := 137, numerator := 239850882611542428261705318400 }, { target := 138, numerator := 229357406497287447025255710720 }, { target := 139, numerator := 7495340081610700883178291200 }, { target := 140, numerator := 143910529566925456957023191040 }, { target := 141, numerator := 7495340081610700883178291200 }, { target := 142, numerator := 230856474513609587201891368960 }, { target := 143, numerator := 130418917420026195367302266880 }, { target := 144, numerator := 8994408097932841059813949440 }, { target := 216, numerator := 8822713699301216101060313088 }, { target := 217, numerator := 8638907163899107432288223232 }, { target := 218, numerator := 6800841809878020744567324672 }, { target := 219, numerator := 213767000672652381781940502528 }, { target := 220, numerator := 6800841809878020744567324672 }, { target := 221, numerator := 6800841809878020744567324672 }, { target := 222, numerator := 6984648345280129413339414528 }, { target := 223, numerator := 6984648345280129413339414528 }, { target := 224, numerator := 118187602263555874020453777408 }, { target := 225, numerator := 6433228739073803407023144960 }, { target := 226, numerator := 213767000672652381781940502528 }, { target := 227, numerator := 118187602263555874020453777408 }, { target := 228, numerator := 8822713699301216101060313088 }, { target := 229, numerator := 6800841809878020744567324672 }, { target := 230, numerator := 6433228739073803407023144960 }, { target := 231, numerator := 8638907163899107432288223232 }]

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
    Slot29.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 18278958392573193121557381120 }, { target := 1, numerator := 18801214346646712925030449152 }, { target := 2, numerator := 18278958392573193121557381120 }, { target := 3, numerator := 16189934576279113907665108992 }, { target := 4, numerator := 757793389360677234839421714432 }, { target := 5, numerator := 206291101859040322371861872640 }, { target := 6, numerator := 18801214346646712925030449152 }, { target := 7, numerator := 757793389360677234839421714432 }, { target := 8, numerator := 18278958392573193121557381120 }, { target := 9, numerator := 18278958392573193121557381120 }, { target := 10, numerator := 15667678622205594104192040960 }, { target := 11, numerator := 18278958392573193121557381120 }, { target := 12, numerator := 206291101859040322371861872640 }, { target := 13, numerator := 15667678622205594104192040960 }, { target := 14, numerator := 18278958392573193121557381120 }, { target := 15, numerator := 16189934576279113907665108992 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent1
