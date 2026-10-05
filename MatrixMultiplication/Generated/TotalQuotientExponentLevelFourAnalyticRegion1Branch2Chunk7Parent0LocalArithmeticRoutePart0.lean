import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk7Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 30; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent0

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
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 86643549869160539147468800 }, { target := 122, numerator := 13832399533584690783558041600 }, { target := 124, numerator := 138026546170521322127989145600 }, { target := 132, numerator := 13832399533584690783558041600 }, { target := 139, numerator := 86633663567258535434649600 }, { target := 196, numerator := 89119079865422268837396480 }, { target := 197, numerator := 14227610948829967663088271360 }, { target := 199, numerator := 141970161775393359903074549760 }, { target := 207, numerator := 14227610948829967663088271360 }, { target := 214, numerator := 89108911097751636447068160 }, { target := 250, numerator := 501465514271757305905152000 }, { target := 252, numerator := 18841347599562309489393664000 }, { target := 255, numerator := 18839922588582615426531328000 }, { target := 262, numerator := 502890525251451368767488000 }, { target := 466, numerator := 10049368906006016410339246080 }, { target := 468, numerator := 377580605895228682167449026560 }, { target := 471, numerator := 377552048675195613147687813120 }, { target := 478, numerator := 10077926126039085430100459520 }, { target := 562, numerator := 16869299900101915770649313280 }, { target := 564, numerator := 633822933249276091223202856960 }, { target := 567, numerator := 633774995879919182948513873920 }, { target := 574, numerator := 16917237269458824045338296320 }, { target := 597, numerator := 16187306800692325834618306560 }, { target := 599, numerator := 608198700513871350317627473920 }, { target := 602, numerator := 608152701159446825968431267840 }, { target := 609, numerator := 16233306155116850183814512640 }, { target := 613, numerator := 49524606999178363303834419200 }, { target := 616, numerator := 170009316415075142514937692160 }, { target := 618, numerator := 49524606999178363303834419200 }, { target := 733, numerator := 501465514271757305905152000 }, { target := 735, numerator := 18841347599562309489393664000 }, { target := 738, numerator := 18839922588582615426531328000 }, { target := 745, numerator := 502890525251451368767488000 }, { target := 829, numerator := 16187306800692325834618306560 }, { target := 831, numerator := 608198700513871350317627473920 }, { target := 834, numerator := 608152701159446825968431267840 }, { target := 841, numerator := 16233306155116850183814512640 }, { target := 864, numerator := 10811596487699087515315077120 }, { target := 866, numerator := 406219454246563392591327395840 }, { target := 869, numerator := 406188731009841188596015431680 }, { target := 876, numerator := 10842319724421291510627041280 }, { target := 880, numerator := 45266416490837793748738375680 }, { target := 883, numerator := 155391692947610737737952395264 }, { target := 885, numerator := 45266416490837793748738375680 }, { target := 925, numerator := 521524134842627598141358080 }, { target := 927, numerator := 19595001503544801868969410560 }, { target := 930, numerator := 19593519492125920043592581120 }, { target := 937, numerator := 523006146261509423518187520 }, { target := 960, numerator := 10049368906006016410339246080 }, { target := 962, numerator := 377580605895228682167449026560 }, { target := 965, numerator := 377552048675195613147687813120 }, { target := 972, numerator := 10077926126039085430100459520 }, { target := 976, numerator := 49524606999178363303834419200 }, { target := 979, numerator := 170009316415075142514937692160 }, { target := 981, numerator := 49524606999178363303834419200 }, { target := 986, numerator := 481406893700887013668945920 }, { target := 988, numerator := 18087693695579817109817917440 }, { target := 991, numerator := 18086325685039310809470074880 }, { target := 998, numerator := 482774904241393314016788480 }, { target := 1002, numerator := 45266416490837793748738375680 }, { target := 1005, numerator := 155391692947610737737952395264 }, { target := 1007, numerator := 45266416490837793748738375680 }, { target := 1012, numerator := 118842243771396506390315925504 }, { target := 1014, numerator := 118842243771396506390315925504 }]

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
  [{ target := 231, numerator := 86643549869160539147468800 }, { target := 232, numerator := 13832399533584690783558041600 }, { target := 234, numerator := 138026546170521322127989145600 }, { target := 242, numerator := 13832399533584690783558041600 }, { target := 249, numerator := 86633663567258535434649600 }, { target := 337, numerator := 76741429884113620387758080 }, { target := 338, numerator := 12251553872603583265437122560 }, { target := 340, numerator := 122252083751033171027647528960 }, { target := 348, numerator := 12251553872603583265437122560 }, { target := 355, numerator := 76732673445286131384975360 }, { target := 412, numerator := 3591994024575769780085063680 }, { target := 413, numerator := 573451763520896752198363381760 }, { target := 415, numerator := 5722186242669326811648921436160 }, { target := 423, numerator := 573451763520896752198363381760 }, { target := 430, numerator := 3591584166745489569019330560 }, { target := 447, numerator := 977834348523383227521433600 }, { target := 448, numerator := 156108509021884367414440755200 }, { target := 450, numerator := 1557728163924454921158734643200 }, { target := 458, numerator := 156108509021884367414440755200 }, { target := 465, numerator := 977722774544774899905331200 }, { target := 508, numerator := 89119079865422268837396480 }, { target := 509, numerator := 14227610948829967663088271360 }, { target := 511, numerator := 141970161775393359903074549760 }, { target := 519, numerator := 14227610948829967663088271360 }, { target := 526, numerator := 89108911097751636447068160 }, { target := 543, numerator := 3591994024575769780085063680 }, { target := 544, numerator := 573451763520896752198363381760 }, { target := 546, numerator := 5722186242669326811648921436160 }, { target := 554, numerator := 573451763520896752198363381760 }, { target := 561, numerator := 3591584166745489569019330560 }, { target := 578, numerator := 86643549869160539147468800 }, { target := 579, numerator := 13832399533584690783558041600 }, { target := 581, numerator := 138026546170521322127989145600 }, { target := 589, numerator := 13832399533584690783558041600 }, { target := 596, numerator := 86633663567258535434649600 }, { target := 679, numerator := 86643549869160539147468800 }, { target := 680, numerator := 13832399533584690783558041600 }, { target := 682, numerator := 138026546170521322127989145600 }, { target := 690, numerator := 13832399533584690783558041600 }, { target := 697, numerator := 86633663567258535434649600 }, { target := 714, numerator := 74265899887851890697830400 }, { target := 715, numerator := 11856342457358306385906892800 }, { target := 717, numerator := 118308468146161133252562124800 }, { target := 725, numerator := 11856342457358306385906892800 }, { target := 732, numerator := 74257425914793030372556800 }, { target := 775, numerator := 86643549869160539147468800 }, { target := 776, numerator := 13832399533584690783558041600 }, { target := 778, numerator := 138026546170521322127989145600 }, { target := 786, numerator := 13832399533584690783558041600 }, { target := 793, numerator := 86633663567258535434649600 }, { target := 810, numerator := 977834348523383227521433600 }, { target := 811, numerator := 156108509021884367414440755200 }, { target := 813, numerator := 1557728163924454921158734643200 }, { target := 821, numerator := 156108509021884367414440755200 }, { target := 828, numerator := 977722774544774899905331200 }, { target := 845, numerator := 74265899887851890697830400 }, { target := 846, numerator := 11856342457358306385906892800 }, { target := 848, numerator := 118308468146161133252562124800 }, { target := 856, numerator := 11856342457358306385906892800 }, { target := 863, numerator := 74257425914793030372556800 }]

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
    Slot4.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 71402181220989035631083520 }, { target := 35, numerator := 55535029838547027713064960 }, { target := 36, numerator := 63468605529768031672074240 }, { target := 37, numerator := 74575611497477437214687232 }, { target := 38, numerator := 880626901725531439450030080 }, { target := 39, numerator := 1980220492528762588168716288 }, { target := 40, numerator := 55535029838547027713064960 }, { target := 41, numerator := 880626901725531439450030080 }, { target := 42, numerator := 63468605529768031672074240 }, { target := 43, numerator := 61881890391523830880272384 }, { target := 44, numerator := 61881890391523830880272384 }, { target := 45, numerator := 61881890391523830880272384 }, { target := 46, numerator := 1980220492528762588168716288 }, { target := 47, numerator := 61881890391523830880272384 }, { target := 48, numerator := 71402181220989035631083520 }, { target := 49, numerator := 74575611497477437214687232 }, { target := 79, numerator := 1904058165893040950162227200 }, { target := 80, numerator := 1480934129027920739015065600 }, { target := 81, numerator := 1692496147460480844588646400 }, { target := 82, numerator := 1988682973266064992391659520 }, { target := 83, numerator := 23483384046014171718667468800 }, { target := 84, numerator := 52805879800767002351165767680 }, { target := 85, numerator := 1480934129027920739015065600 }, { target := 86, numerator := 23483384046014171718667468800 }, { target := 87, numerator := 1692496147460480844588646400 }, { target := 88, numerator := 1650183743773968823473930240 }, { target := 89, numerator := 1650183743773968823473930240 }, { target := 90, numerator := 1650183743773968823473930240 }, { target := 91, numerator := 52805879800767002351165767680 }, { target := 92, numerator := 1650183743773968823473930240 }, { target := 93, numerator := 1904058165893040950162227200 }, { target := 94, numerator := 1988682973266064992391659520 }, { target := 105, numerator := 1820755621135220408592629760 }, { target := 106, numerator := 1416143260882949206683156480 }, { target := 107, numerator := 1618449441009084807637893120 }, { target := 108, numerator := 1901678093185674648974524416 }, { target := 109, numerator := 22455985994001051705975767040 }, { target := 110, numerator := 50495622559483445998302265344 }, { target := 111, numerator := 1416143260882949206683156480 }, { target := 112, numerator := 22455985994001051705975767040 }, { target := 113, numerator := 1618449441009084807637893120 }, { target := 114, numerator := 1577988204983857687446945792 }, { target := 115, numerator := 1577988204983857687446945792 }, { target := 116, numerator := 1577988204983857687446945792 }, { target := 117, numerator := 50495622559483445998302265344 }, { target := 118, numerator := 1577988204983857687446945792 }, { target := 119, numerator := 1820755621135220408592629760 }, { target := 120, numerator := 1901678093185674648974524416 }, { target := 906, numerator := 86643549869160539147468800 }, { target := 907, numerator := 13832399533584690783558041600 }, { target := 909, numerator := 138026546170521322127989145600 }, { target := 917, numerator := 13832399533584690783558041600 }, { target := 924, numerator := 86633663567258535434649600 }, { target := 941, numerator := 76741429884113620387758080 }, { target := 942, numerator := 12251553872603583265437122560 }, { target := 944, numerator := 122252083751033171027647528960 }, { target := 952, numerator := 12251553872603583265437122560 }, { target := 959, numerator := 76732673445286131384975360 }]

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
    Slot4.Left3.expected,
    Slot4.Left4.expected,
    Slot4.Left5.expected,
    Slot4.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 154, numerator := 59501817684157529692569600 }, { target := 155, numerator := 46279191532122523094220800 }, { target := 156, numerator := 52890504608140026393395200 }, { target := 157, numerator := 62146342914564531012239360 }, { target := 158, numerator := 733855751437942866208358400 }, { target := 159, numerator := 1650183743773968823473930240 }, { target := 160, numerator := 46279191532122523094220800 }, { target := 161, numerator := 733855751437942866208358400 }, { target := 162, numerator := 52890504608140026393395200 }, { target := 163, numerator := 51568241992936525733560320 }, { target := 164, numerator := 51568241992936525733560320 }, { target := 165, numerator := 51568241992936525733560320 }, { target := 166, numerator := 1650183743773968823473930240 }, { target := 167, numerator := 51568241992936525733560320 }, { target := 168, numerator := 59501817684157529692569600 }, { target := 169, numerator := 62146342914564531012239360 }, { target := 180, numerator := 1868357075282546432346685440 }, { target := 181, numerator := 1453166614108647225158533120 }, { target := 182, numerator := 1660761844695596828752609280 }, { target := 183, numerator := 1951395167517326273784315904 }, { target := 184, numerator := 23043070595151405998942453760 }, { target := 185, numerator := 51815769554502621057081409536 }, { target := 186, numerator := 1453166614108647225158533120 }, { target := 187, numerator := 23043070595151405998942453760 }, { target := 188, numerator := 1660761844695596828752609280 }, { target := 189, numerator := 1619242798578206908033794048 }, { target := 190, numerator := 1619242798578206908033794048 }, { target := 191, numerator := 1619242798578206908033794048 }, { target := 192, numerator := 51815769554502621057081409536 }, { target := 193, numerator := 1619242798578206908033794048 }, { target := 194, numerator := 1868357075282546432346685440 }, { target := 195, numerator := 1951395167517326273784315904 }, { target := 215, numerator := 59501817684157529692569600 }, { target := 216, numerator := 46279191532122523094220800 }, { target := 217, numerator := 52890504608140026393395200 }, { target := 218, numerator := 62146342914564531012239360 }, { target := 219, numerator := 733855751437942866208358400 }, { target := 220, numerator := 1650183743773968823473930240 }, { target := 221, numerator := 46279191532122523094220800 }, { target := 222, numerator := 733855751437942866208358400 }, { target := 223, numerator := 52890504608140026393395200 }, { target := 224, numerator := 51568241992936525733560320 }, { target := 225, numerator := 51568241992936525733560320 }, { target := 226, numerator := 51568241992936525733560320 }, { target := 227, numerator := 1650183743773968823473930240 }, { target := 228, numerator := 51568241992936525733560320 }, { target := 229, numerator := 59501817684157529692569600 }, { target := 230, numerator := 62146342914564531012239360 }, { target := 295, numerator := 1820755621135220408592629760 }, { target := 296, numerator := 1416143260882949206683156480 }, { target := 297, numerator := 1618449441009084807637893120 }, { target := 298, numerator := 1901678093185674648974524416 }, { target := 299, numerator := 22455985994001051705975767040 }, { target := 300, numerator := 50495622559483445998302265344 }, { target := 301, numerator := 1416143260882949206683156480 }, { target := 302, numerator := 22455985994001051705975767040 }, { target := 303, numerator := 1618449441009084807637893120 }, { target := 304, numerator := 1577988204983857687446945792 }, { target := 305, numerator := 1577988204983857687446945792 }, { target := 306, numerator := 1577988204983857687446945792 }, { target := 307, numerator := 50495622559483445998302265344 }, { target := 308, numerator := 1577988204983857687446945792 }, { target := 309, numerator := 1820755621135220408592629760 }, { target := 310, numerator := 1901678093185674648974524416 }]

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
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot4.Left10.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 321, numerator := 1035331627704341016650711040 }, { target := 322, numerator := 805257932658931901839441920 }, { target := 323, numerator := 920294780181636459245076480 }, { target := 324, numerator := 1081346366713422839612964864 }, { target := 325, numerator := 12769090075020205872025436160 }, { target := 326, numerator := 28713197141667057528446386176 }, { target := 327, numerator := 805257932658931901839441920 }, { target := 328, numerator := 12769090075020205872025436160 }, { target := 329, numerator := 920294780181636459245076480 }, { target := 330, numerator := 897287410677095547763949568 }, { target := 331, numerator := 897287410677095547763949568 }, { target := 332, numerator := 897287410677095547763949568 }, { target := 333, numerator := 28713197141667057528446386176 }, { target := 334, numerator := 897287410677095547763949568 }, { target := 335, numerator := 1035331627704341016650711040 }, { target := 336, numerator := 1081346366713422839612964864 }, { target := 370, numerator := 1868357075282546432346685440 }, { target := 371, numerator := 1453166614108647225158533120 }, { target := 372, numerator := 1660761844695596828752609280 }, { target := 373, numerator := 1951395167517326273784315904 }, { target := 374, numerator := 23043070595151405998942453760 }, { target := 375, numerator := 51815769554502621057081409536 }, { target := 376, numerator := 1453166614108647225158533120 }, { target := 377, numerator := 23043070595151405998942453760 }, { target := 378, numerator := 1660761844695596828752609280 }, { target := 379, numerator := 1619242798578206908033794048 }, { target := 380, numerator := 1619242798578206908033794048 }, { target := 381, numerator := 1619242798578206908033794048 }, { target := 382, numerator := 51815769554502621057081409536 }, { target := 383, numerator := 1619242798578206908033794048 }, { target := 384, numerator := 1868357075282546432346685440 }, { target := 385, numerator := 1951395167517326273784315904 }, { target := 396, numerator := 29167791028774021055297617920 }, { target := 397, numerator := 22686059689046460820787036160 }, { target := 398, numerator := 25926925358910240938042327040 }, { target := 399, numerator := 30464137296719533102199734272 }, { target := 400, numerator := 359736089354879593015337287680 }, { target := 401, numerator := 808920071197999517266920603648 }, { target := 402, numerator := 22686059689046460820787036160 }, { target := 403, numerator := 359736089354879593015337287680 }, { target := 404, numerator := 25926925358910240938042327040 }, { target := 405, numerator := 25278752224937484914591268864 }, { target := 406, numerator := 25278752224937484914591268864 }, { target := 407, numerator := 25278752224937484914591268864 }, { target := 408, numerator := 808920071197999517266920603648 }, { target := 409, numerator := 25278752224937484914591268864 }, { target := 410, numerator := 29167791028774021055297617920 }, { target := 411, numerator := 30464137296719533102199734272 }, { target := 431, numerator := 1142434899535824570097336320 }, { target := 432, numerator := 888560477416752443409039360 }, { target := 433, numerator := 1015497688476288506753187840 }, { target := 434, numerator := 1193209783959638995434995712 }, { target := 435, numerator := 14090030427608503031200481280 }, { target := 436, numerator := 31683527880460201410699460608 }, { target := 437, numerator := 888560477416752443409039360 }, { target := 438, numerator := 14090030427608503031200481280 }, { target := 439, numerator := 1015497688476288506753187840 }, { target := 440, numerator := 990110246264381294084358144 }, { target := 441, numerator := 990110246264381294084358144 }, { target := 442, numerator := 990110246264381294084358144 }, { target := 443, numerator := 31683527880460201410699460608 }, { target := 444, numerator := 990110246264381294084358144 }, { target := 445, numerator := 1142434899535824570097336320 }, { target := 446, numerator := 1193209783959638995434995712 }]

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
    Slot4.Left11.expected,
    Slot4.Left12.expected,
    Slot4.Left13.expected,
    Slot4.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 492, numerator := 1904058165893040950162227200 }, { target := 493, numerator := 1480934129027920739015065600 }, { target := 494, numerator := 1692496147460480844588646400 }, { target := 495, numerator := 1988682973266064992391659520 }, { target := 496, numerator := 23483384046014171718667468800 }, { target := 497, numerator := 52805879800767002351165767680 }, { target := 498, numerator := 1480934129027920739015065600 }, { target := 499, numerator := 23483384046014171718667468800 }, { target := 500, numerator := 1692496147460480844588646400 }, { target := 501, numerator := 1650183743773968823473930240 }, { target := 502, numerator := 1650183743773968823473930240 }, { target := 503, numerator := 1650183743773968823473930240 }, { target := 504, numerator := 52805879800767002351165767680 }, { target := 505, numerator := 1650183743773968823473930240 }, { target := 506, numerator := 1904058165893040950162227200 }, { target := 507, numerator := 1988682973266064992391659520 }, { target := 527, numerator := 1820755621135220408592629760 }, { target := 528, numerator := 1416143260882949206683156480 }, { target := 529, numerator := 1618449441009084807637893120 }, { target := 530, numerator := 1901678093185674648974524416 }, { target := 531, numerator := 22455985994001051705975767040 }, { target := 532, numerator := 50495622559483445998302265344 }, { target := 533, numerator := 1416143260882949206683156480 }, { target := 534, numerator := 22455985994001051705975767040 }, { target := 535, numerator := 1618449441009084807637893120 }, { target := 536, numerator := 1577988204983857687446945792 }, { target := 537, numerator := 1577988204983857687446945792 }, { target := 538, numerator := 1577988204983857687446945792 }, { target := 539, numerator := 50495622559483445998302265344 }, { target := 540, numerator := 1577988204983857687446945792 }, { target := 541, numerator := 1820755621135220408592629760 }, { target := 542, numerator := 1901678093185674648974524416 }, { target := 637, numerator := 59501817684157529692569600 }, { target := 638, numerator := 46279191532122523094220800 }, { target := 639, numerator := 52890504608140026393395200 }, { target := 640, numerator := 62146342914564531012239360 }, { target := 641, numerator := 733855751437942866208358400 }, { target := 642, numerator := 1650183743773968823473930240 }, { target := 643, numerator := 46279191532122523094220800 }, { target := 644, numerator := 733855751437942866208358400 }, { target := 645, numerator := 52890504608140026393395200 }, { target := 646, numerator := 51568241992936525733560320 }, { target := 647, numerator := 51568241992936525733560320 }, { target := 648, numerator := 51568241992936525733560320 }, { target := 649, numerator := 1650183743773968823473930240 }, { target := 650, numerator := 51568241992936525733560320 }, { target := 651, numerator := 59501817684157529692569600 }, { target := 652, numerator := 62146342914564531012239360 }, { target := 663, numerator := 1142434899535824570097336320 }, { target := 664, numerator := 888560477416752443409039360 }, { target := 665, numerator := 1015497688476288506753187840 }, { target := 666, numerator := 1193209783959638995434995712 }, { target := 667, numerator := 14090030427608503031200481280 }, { target := 668, numerator := 31683527880460201410699460608 }, { target := 669, numerator := 888560477416752443409039360 }, { target := 670, numerator := 14090030427608503031200481280 }, { target := 671, numerator := 1015497688476288506753187840 }, { target := 672, numerator := 990110246264381294084358144 }, { target := 673, numerator := 990110246264381294084358144 }, { target := 674, numerator := 990110246264381294084358144 }, { target := 675, numerator := 31683527880460201410699460608 }, { target := 676, numerator := 990110246264381294084358144 }, { target := 677, numerator := 1142434899535824570097336320 }, { target := 678, numerator := 1193209783959638995434995712 }]

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
    Slot4.Left15.expected,
    Slot4.Left16.expected,
    Slot4.Left17.expected,
    Slot4.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 698, numerator := 59501817684157529692569600 }, { target := 699, numerator := 46279191532122523094220800 }, { target := 700, numerator := 52890504608140026393395200 }, { target := 701, numerator := 62146342914564531012239360 }, { target := 702, numerator := 733855751437942866208358400 }, { target := 703, numerator := 1650183743773968823473930240 }, { target := 704, numerator := 46279191532122523094220800 }, { target := 705, numerator := 733855751437942866208358400 }, { target := 706, numerator := 52890504608140026393395200 }, { target := 707, numerator := 51568241992936525733560320 }, { target := 708, numerator := 51568241992936525733560320 }, { target := 709, numerator := 51568241992936525733560320 }, { target := 710, numerator := 1650183743773968823473930240 }, { target := 711, numerator := 51568241992936525733560320 }, { target := 712, numerator := 59501817684157529692569600 }, { target := 713, numerator := 62146342914564531012239360 }, { target := 759, numerator := 1832655984672051914531143680 }, { target := 760, numerator := 1425399099189373711302000640 }, { target := 761, numerator := 1629027541930712812916572160 }, { target := 762, numerator := 1914107361768587555176972288 }, { target := 763, numerator := 22602757144288640279217438720 }, { target := 764, numerator := 50825659308238239762997051392 }, { target := 765, numerator := 1425399099189373711302000640 }, { target := 766, numerator := 22602757144288640279217438720 }, { target := 767, numerator := 1629027541930712812916572160 }, { target := 768, numerator := 1588301853382444992593657856 }, { target := 769, numerator := 1588301853382444992593657856 }, { target := 770, numerator := 1588301853382444992593657856 }, { target := 771, numerator := 50825659308238239762997051392 }, { target := 772, numerator := 1588301853382444992593657856 }, { target := 773, numerator := 1832655984672051914531143680 }, { target := 774, numerator := 1914107361768587555176972288 }, { target := 794, numerator := 1035331627704341016650711040 }, { target := 795, numerator := 805257932658931901839441920 }, { target := 796, numerator := 920294780181636459245076480 }, { target := 797, numerator := 1081346366713422839612964864 }, { target := 798, numerator := 12769090075020205872025436160 }, { target := 799, numerator := 28713197141667057528446386176 }, { target := 800, numerator := 805257932658931901839441920 }, { target := 801, numerator := 12769090075020205872025436160 }, { target := 802, numerator := 920294780181636459245076480 }, { target := 803, numerator := 897287410677095547763949568 }, { target := 804, numerator := 897287410677095547763949568 }, { target := 805, numerator := 897287410677095547763949568 }, { target := 806, numerator := 28713197141667057528446386176 }, { target := 807, numerator := 897287410677095547763949568 }, { target := 808, numerator := 1035331627704341016650711040 }, { target := 809, numerator := 1081346366713422839612964864 }, { target := 890, numerator := 71402181220989035631083520 }, { target := 891, numerator := 55535029838547027713064960 }, { target := 892, numerator := 63468605529768031672074240 }, { target := 893, numerator := 74575611497477437214687232 }, { target := 894, numerator := 880626901725531439450030080 }, { target := 895, numerator := 1980220492528762588168716288 }, { target := 896, numerator := 55535029838547027713064960 }, { target := 897, numerator := 880626901725531439450030080 }, { target := 898, numerator := 63468605529768031672074240 }, { target := 899, numerator := 61881890391523830880272384 }, { target := 900, numerator := 61881890391523830880272384 }, { target := 901, numerator := 61881890391523830880272384 }, { target := 902, numerator := 1980220492528762588168716288 }, { target := 903, numerator := 61881890391523830880272384 }, { target := 904, numerator := 71402181220989035631083520 }, { target := 905, numerator := 74575611497477437214687232 }]

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
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left7.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 173128997676409451553226752 }, { target := 35, numerator := 14558286162085724488103624704 }, { target := 40, numerator := 14558282649842653942398320640 }, { target := 48, numerator := 173132509919479997258530816 }, { target := 79, numerator := 18152263156599667999824150528 }, { target := 80, numerator := 1526410047248094992303554297856 }, { target := 85, numerator := 1526409678995743611789728808960 }, { target := 93, numerator := 18152631408951048513649639424 }, { target := 121, numerator := 210505494870755007046615040 }, { target := 122, numerator := 31090559976179419501444464640 }, { target := 124, numerator := 324051707095292779546909081600 }, { target := 132, numerator := 31090559976179419501444464640 }, { target := 139, numerator := 210505494870755007046615040 }, { target := 154, numerator := 195663253662464544828555264000 }, { target := 155, numerator := 16453174664287136620298108928000 }, { target := 160, numerator := 16453170694894856530538004480000 }, { target := 168, numerator := 195667223054744634588659712000 }, { target := 196, numerator := 17625442975577953827368730624 }, { target := 197, numerator := 2603185690118851011943159824384 }, { target := 199, numerator := 27132569095422052534825475112960 }, { target := 207, numerator := 2603185690118851011943159824384 }, { target := 214, numerator := 17625442975577953827368730624 }, { target := 250, numerator := 8920589056220325157904842752 }, { target := 252, numerator := 323285100122857121756724854784 }, { target := 255, numerator := 323285218928869697053167452160 }, { target := 262, numerator := 8920470250207749861462245376 }, { target := 492, numerator := 18152277003596202944193626112 }, { target := 493, numerator := 1526411211631535933335665639424 }, { target := 498, numerator := 1526410843378903640795082915840 }, { target := 506, numerator := 18152645256228495484776349696 }, { target := 508, numerator := 17625449354210190706970984448 }, { target := 509, numerator := 2603186632209451774917337939968 }, { target := 511, numerator := 27132578914674830534707689553920 }, { target := 519, numerator := 2603186632209451774917337939968 }, { target := 526, numerator := 17625449354210190706970984448 }, { target := 562, numerator := 86405477565157260305308319744 }, { target := 564, numerator := 3131363107275640387949085851648 }, { target := 567, numerator := 3131364258039361201031893483520 }, { target := 574, numerator := 86404326801436447222500687872 }, { target := 613, numerator := 25724718348480245599637078016 }, { target := 616, numerator := 87199847703002099589427757056 }, { target := 618, numerator := 25724718348480245599637078016 }, { target := 880, numerator := 25724718348480245599637078016 }, { target := 883, numerator := 87199847703002099589427757056 }, { target := 885, numerator := 25724718348480245599637078016 }, { target := 890, numerator := 173128997676409451553226752 }, { target := 891, numerator := 14558286162085724488103624704 }, { target := 896, numerator := 14558282649842653942398320640 }, { target := 904, numerator := 173132509919479997258530816 }, { target := 906, numerator := 210499116238518127444361216 }, { target := 907, numerator := 31089617885578656527266349056 }, { target := 909, numerator := 324041887842514779664694640640 }, { target := 917, numerator := 31089617885578656527266349056 }, { target := 924, numerator := 210499116238518127444361216 }, { target := 925, numerator := 8920589056220325157904842752 }, { target := 927, numerator := 323285100122857121756724854784 }, { target := 930, numerator := 323285218928869697053167452160 }, { target := 937, numerator := 8920470250207749861462245376 }, { target := 976, numerator := 25724718348480245599637078016 }, { target := 979, numerator := 87199847703002099589427757056 }, { target := 981, numerator := 25724718348480245599637078016 }, { target := 1002, numerator := 25724718348480245599637078016 }, { target := 1005, numerator := 87199847703002099589427757056 }, { target := 1007, numerator := 25724718348480245599637078016 }]

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
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected,
    Slot10.Left4.expected,
    Slot10.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 224875749594810649826820096 }, { target := 11, numerator := 5382509877398371037790339072 }, { target := 12, numerator := 4026001323390964859802746880 }, { target := 13, numerator := 4671612346421227693176520704 }, { target := 14, numerator := 224875749594810649826820096 }, { target := 15, numerator := 4664358289982685414149849088 }, { target := 16, numerator := 4686120459298312251229863936 }, { target := 17, numerator := 224875749594810649826820096 }, { target := 18, numerator := 5382509877398371037790339072 }, { target := 19, numerator := 224875749594810649826820096 }, { target := 55, numerator := 7870090573549446948074815488 }, { target := 56, numerator := 188374425986248052757145583616 }, { target := 57, numerator := 140900008655482034070371696640 }, { target := 58, numerator := 163494784818253026921296166912 }, { target := 59, numerator := 7870090573549446948074815488 }, { target := 60, numerator := 163240910928783689922971172864 }, { target := 61, numerator := 164002532597191700917946155008 }, { target := 62, numerator := 7870090573549446948074815488 }, { target := 63, numerator := 188374425986248052757145583616 }, { target := 64, numerator := 7870090573549446948074815488 }, { target := 144, numerator := 7870094433530644371798491136 }, { target := 145, numerator := 188374518376765745931434852352 }, { target := 146, numerator := 140900077761597020204779438080 }, { target := 147, numerator := 163494865006249515336717041664 }, { target := 148, numerator := 7870094433530644371798491136 }, { target := 149, numerator := 163240990992264655840852574208 }, { target := 150, numerator := 164002613034219234328445976576 }, { target := 151, numerator := 7870094433530644371798491136 }, { target := 152, numerator := 188374518376765745931434852352 }, { target := 153, numerator := 7870094433530644371798491136 }, { target := 250, numerator := 224875749594810649826820096 }, { target := 252, numerator := 7870090573549446948074815488 }, { target := 255, numerator := 7870094433530644371798491136 }, { target := 262, numerator := 224873819604211937964982272 }, { target := 466, numerator := 5382509877398371037790339072 }, { target := 468, numerator := 188374425986248052757145583616 }, { target := 471, numerator := 188374518376765745931434852352 }, { target := 478, numerator := 5382463682139524450645704704 }, { target := 482, numerator := 224873819604211937964982272 }, { target := 483, numerator := 5382463682139524450645704704 }, { target := 484, numerator := 4025966770333471792598876160 }, { target := 485, numerator := 4671572252422983485466083328 }, { target := 486, numerator := 224873819604211937964982272 }, { target := 487, numerator := 4664318258242202455209148416 }, { target := 488, numerator := 4686080240784545545979953152 }, { target := 489, numerator := 224873819604211937964982272 }, { target := 490, numerator := 5382463682139524450645704704 }, { target := 491, numerator := 224873819604211937964982272 }, { target := 562, numerator := 4026001323390964859802746880 }, { target := 564, numerator := 140900008655482034070371696640 }, { target := 567, numerator := 140900077761597020204779438080 }, { target := 574, numerator := 4025966770333471792598876160 }, { target := 597, numerator := 4671612346421227693176520704 }, { target := 599, numerator := 163494784818253026921296166912 }, { target := 602, numerator := 163494865006249515336717041664 }, { target := 609, numerator := 4671572252422983485466083328 }, { target := 733, numerator := 224875749594810649826820096 }, { target := 735, numerator := 7870090573549446948074815488 }, { target := 738, numerator := 7870094433530644371798491136 }, { target := 745, numerator := 224873819604211937964982272 }, { target := 829, numerator := 4664358289982685414149849088 }, { target := 831, numerator := 163240910928783689922971172864 }, { target := 834, numerator := 163240990992264655840852574208 }, { target := 841, numerator := 4664318258242202455209148416 }]

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
    Slot10.Left6.expected,
    Slot10.Left7.expected,
    Slot10.Left8.expected,
    Slot10.Left9.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left6.expected,
    Slot11.Left14.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 8920589056220325157904842752 }, { target := 12, numerator := 86405477565157260305308319744 }, { target := 17, numerator := 8920589056220325157904842752 }, { target := 34, numerator := 208214624914483187139215360 }, { target := 35, numerator := 17433630415988834620057583616 }, { target := 40, numerator := 17433636725204275693231276032 }, { target := 48, numerator := 208208315699042113965522944 }, { target := 55, numerator := 323285100122857121756724854784 }, { target := 57, numerator := 3131363107275640387949085851648 }, { target := 62, numerator := 323285100122857121756724854784 }, { target := 79, numerator := 30752210472206487487523061760 }, { target := 80, numerator := 2574855978860000154497587347456 }, { target := 85, numerator := 2574856910698103448467209715712 }, { target := 93, numerator := 30751278634103193517900693504 }, { target := 121, numerator := 172435093878107209262432256 }, { target := 122, numerator := 18079508594849769530886979584 }, { target := 124, numerator := 194879032204899556672929792000 }, { target := 132, numerator := 18079522386347320367262990336 }, { target := 139, numerator := 172435093878107209262432256 }, { target := 154, numerator := 320525146800422604195128934400 }, { target := 155, numerator := 26837293252787471551979732336640 }, { target := 160, numerator := 26837302965180183044003494625280 }, { target := 168, numerator := 320515434407711112171366645760 }, { target := 196, numerator := 14499936317748707556287578112 }, { target := 197, numerator := 1520292171307220864077888749568 }, { target := 199, numerator := 16387230076454322445467254784000 }, { target := 207, numerator := 1520293331023794306348348342272 }, { target := 214, numerator := 14499936317748707556287578112 }, { target := 492, numerator := 30752210472206487487523061760 }, { target := 493, numerator := 2574855978860000154497587347456 }, { target := 498, numerator := 2574856910698103448467209715712 }, { target := 506, numerator := 30751278634103193517900693504 }, { target := 508, numerator := 14499932819582763545835601920 }, { target := 509, numerator := 1520291804530830811742475386880 }, { target := 511, numerator := 16387226122971430251858493440000 }, { target := 519, numerator := 1520292964247124467886084587520 }, { target := 526, numerator := 14499932819582763545835601920 }, { target := 864, numerator := 4686120459298312251229863936 }, { target := 866, numerator := 164002532597191700917946155008 }, { target := 869, numerator := 164002613034219234328445976576 }, { target := 876, numerator := 4686080240784545545979953152 }, { target := 890, numerator := 208214624914483187139215360 }, { target := 891, numerator := 17433630415988834620057583616 }, { target := 896, numerator := 17433636725204275693231276032 }, { target := 904, numerator := 208208315699042113965522944 }, { target := 906, numerator := 172438592044051219714408448 }, { target := 907, numerator := 18079875371239821866300342272 }, { target := 909, numerator := 194882985687791750281691136000 }, { target := 917, numerator := 18079889163017158829526745088 }, { target := 924, numerator := 172438592044051219714408448 }, { target := 925, numerator := 224875749594810649826820096 }, { target := 927, numerator := 7870090573549446948074815488 }, { target := 930, numerator := 7870094433530644371798491136 }, { target := 937, numerator := 224873819604211937964982272 }, { target := 960, numerator := 5382509877398371037790339072 }, { target := 962, numerator := 188374425986248052757145583616 }, { target := 965, numerator := 188374518376765745931434852352 }, { target := 972, numerator := 5382463682139524450645704704 }, { target := 986, numerator := 224875749594810649826820096 }, { target := 988, numerator := 7870090573549446948074815488 }, { target := 991, numerator := 7870094433530644371798491136 }, { target := 998, numerator := 224873819604211937964982272 }]

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
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 22049758584411639085403209728 }, { target := 2, numerator := 22049758584411639085403209728 }, { target := 3, numerator := 22049758584411639085403209728 }, { target := 4, numerator := 22049758584411639085403209728 }, { target := 51, numerator := 74742726602573228219509506048 }, { target := 52, numerator := 74742726602573228219509506048 }, { target := 53, numerator := 74742726602573228219509506048 }, { target := 54, numerator := 74742726602573228219509506048 }, { target := 121, numerator := 72677220171363839838781440 }, { target := 122, numerator := 1938059204569702395700838400 }, { target := 123, numerator := 1853269114369777915888926720 }, { target := 124, numerator := 60564350142803199865651200 }, { target := 125, numerator := 1901720594484020475781447680 }, { target := 126, numerator := 60564350142803199865651200 }, { target := 127, numerator := 1853269114369777915888926720 }, { target := 128, numerator := 1053819692484775677662330880 }, { target := 129, numerator := 1901720594484020475781447680 }, { target := 130, numerator := 29688644440002128574142218240 }, { target := 131, numerator := 1162835522741821437420503040 }, { target := 132, numerator := 1938059204569702395700838400 }, { target := 133, numerator := 1853269114369777915888926720 }, { target := 134, numerator := 60564350142803199865651200 }, { target := 135, numerator := 1162835522741821437420503040 }, { target := 136, numerator := 60564350142803199865651200 }, { target := 137, numerator := 1865381984398338555862056960 }, { target := 138, numerator := 1053819692484775677662330880 }, { target := 139, numerator := 72677220171363839838781440 }, { target := 140, numerator := 22049758584411639085403209728 }, { target := 141, numerator := 22049758584411639085403209728 }, { target := 142, numerator := 22049758584411639085403209728 }, { target := 143, numerator := 22049758584411639085403209728 }, { target := 144, numerator := 323285218928869697053167452160 }, { target := 146, numerator := 3131364258039361201031893483520 }, { target := 151, numerator := 323285218928869697053167452160 }, { target := 196, numerator := 56526726799949653207941120 }, { target := 197, numerator := 1507379381331990752211763200 }, { target := 198, numerator := 1441431533398716156802498560 }, { target := 199, numerator := 47105605666624711006617600 }, { target := 200, numerator := 1479116017932015925607792640 }, { target := 201, numerator := 47105605666624711006617600 }, { target := 202, numerator := 1441431533398716156802498560 }, { target := 203, numerator := 819637538599269971515146240 }, { target := 204, numerator := 1479116017932015925607792640 }, { target := 205, numerator := 23091167897779433335443947520 }, { target := 206, numerator := 904427628799194451327057920 }, { target := 207, numerator := 1507379381331990752211763200 }, { target := 208, numerator := 1441431533398716156802498560 }, { target := 209, numerator := 47105605666624711006617600 }, { target := 210, numerator := 904427628799194451327057920 }, { target := 211, numerator := 47105605666624711006617600 }, { target := 212, numerator := 1450852654532041099003822080 }, { target := 213, numerator := 819637538599269971515146240 }, { target := 214, numerator := 56526726799949653207941120 }, { target := 482, numerator := 8920470250207749861462245376 }, { target := 484, numerator := 86404326801436447222500687872 }, { target := 489, numerator := 8920470250207749861462245376 }]

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
    Slot15.Left2.expected,
    Slot15.Left3.expected,
    Slot15.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 231, numerator := 64601973485656746523361280 }, { target := 232, numerator := 1722719292950846573956300800 }, { target := 233, numerator := 1647350323884247036345712640 }, { target := 234, numerator := 53834977904713955436134400 }, { target := 235, numerator := 1690418306208018200694620160 }, { target := 236, numerator := 53834977904713955436134400 }, { target := 237, numerator := 1647350323884247036345712640 }, { target := 238, numerator := 936728615542022824588738560 }, { target := 239, numerator := 1690418306208018200694620160 }, { target := 240, numerator := 26389906168890780954793082880 }, { target := 241, numerator := 1033631575770507944373780480 }, { target := 242, numerator := 1722719292950846573956300800 }, { target := 243, numerator := 1647350323884247036345712640 }, { target := 244, numerator := 53834977904713955436134400 }, { target := 245, numerator := 1033631575770507944373780480 }, { target := 246, numerator := 53834977904713955436134400 }, { target := 247, numerator := 1658117319465189827432939520 }, { target := 248, numerator := 936728615542022824588738560 }, { target := 249, numerator := 64601973485656746523361280 }, { target := 337, numerator := 75907318845646677164949504 }, { target := 338, numerator := 2024195169217244724398653440 }, { target := 339, numerator := 1935636630563990267706212352 }, { target := 340, numerator := 63256099038038897637457920 }, { target := 341, numerator := 1986241509794421385816178688 }, { target := 342, numerator := 63256099038038897637457920 }, { target := 343, numerator := 1935636630563990267706212352 }, { target := 344, numerator := 1100656123261876818891767808 }, { target := 345, numerator := 1986241509794421385816178688 }, { target := 346, numerator := 31008139748446667621881872384 }, { target := 347, numerator := 1214517101530346834639192064 }, { target := 348, numerator := 2024195169217244724398653440 }, { target := 349, numerator := 1935636630563990267706212352 }, { target := 350, numerator := 63256099038038897637457920 }, { target := 351, numerator := 1214517101530346834639192064 }, { target := 352, numerator := 63256099038038897637457920 }, { target := 353, numerator := 1948287850371598047233703936 }, { target := 354, numerator := 1100656123261876818891767808 }, { target := 355, numerator := 75907318845646677164949504 }, { target := 412, numerator := 896352382113487358011637760 }, { target := 413, numerator := 23902730189692996213643673600 }, { target := 414, numerator := 22856985743893927629296762880 }, { target := 415, numerator := 746960318427906131676364800 }, { target := 416, numerator := 23454553998636252534637854720 }, { target := 417, numerator := 746960318427906131676364800 }, { target := 418, numerator := 22856985743893927629296762880 }, { target := 419, numerator := 12997109540645566691168747520 }, { target := 420, numerator := 23454553998636252534637854720 }, { target := 421, numerator := 366159948093359585747754024960 }, { target := 422, numerator := 14341638113815797728186204160 }, { target := 423, numerator := 23902730189692996213643673600 }, { target := 424, numerator := 22856985743893927629296762880 }, { target := 425, numerator := 746960318427906131676364800 }, { target := 426, numerator := 14341638113815797728186204160 }, { target := 427, numerator := 746960318427906131676364800 }, { target := 428, numerator := 23006377807579508855632035840 }, { target := 429, numerator := 12997109540645566691168747520 }, { target := 430, numerator := 896352382113487358011637760 }]

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
    Slot15.Left5.expected,
    Slot15.Left6.expected,
    Slot15.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 447, numerator := 2015581572752490491528871936 }, { target := 448, numerator := 53748841940066413107436584960 }, { target := 449, numerator := 51397330105188507533986234368 }, { target := 450, numerator := 1679651310627075409607393280 }, { target := 451, numerator := 52741051153690167861672148992 }, { target := 452, numerator := 1679651310627075409607393280 }, { target := 453, numerator := 51397330105188507533986234368 }, { target := 454, numerator := 29225932804911112127168643072 }, { target := 455, numerator := 52741051153690167861672148992 }, { target := 456, numerator := 823365072469392365789544185856 }, { target := 457, numerator := 32249305164039847864461950976 }, { target := 458, numerator := 53748841940066413107436584960 }, { target := 459, numerator := 51397330105188507533986234368 }, { target := 460, numerator := 1679651310627075409607393280 }, { target := 461, numerator := 32249305164039847864461950976 }, { target := 462, numerator := 1679651310627075409607393280 }, { target := 463, numerator := 51733260367313922615907713024 }, { target := 464, numerator := 29225932804911112127168643072 }, { target := 465, numerator := 2015581572752490491528871936 }, { target := 508, numerator := 56526726799949653207941120 }, { target := 509, numerator := 1507379381331990752211763200 }, { target := 510, numerator := 1441431533398716156802498560 }, { target := 511, numerator := 47105605666624711006617600 }, { target := 512, numerator := 1479116017932015925607792640 }, { target := 513, numerator := 47105605666624711006617600 }, { target := 514, numerator := 1441431533398716156802498560 }, { target := 515, numerator := 819637538599269971515146240 }, { target := 516, numerator := 1479116017932015925607792640 }, { target := 517, numerator := 23091167897779433335443947520 }, { target := 518, numerator := 904427628799194451327057920 }, { target := 519, numerator := 1507379381331990752211763200 }, { target := 520, numerator := 1441431533398716156802498560 }, { target := 521, numerator := 47105605666624711006617600 }, { target := 522, numerator := 904427628799194451327057920 }, { target := 523, numerator := 47105605666624711006617600 }, { target := 524, numerator := 1450852654532041099003822080 }, { target := 525, numerator := 819637538599269971515146240 }, { target := 526, numerator := 56526726799949653207941120 }, { target := 543, numerator := 896352382113487358011637760 }, { target := 544, numerator := 23902730189692996213643673600 }, { target := 545, numerator := 22856985743893927629296762880 }, { target := 546, numerator := 746960318427906131676364800 }, { target := 547, numerator := 23454553998636252534637854720 }, { target := 548, numerator := 746960318427906131676364800 }, { target := 549, numerator := 22856985743893927629296762880 }, { target := 550, numerator := 12997109540645566691168747520 }, { target := 551, numerator := 23454553998636252534637854720 }, { target := 552, numerator := 366159948093359585747754024960 }, { target := 553, numerator := 14341638113815797728186204160 }, { target := 554, numerator := 23902730189692996213643673600 }, { target := 555, numerator := 22856985743893927629296762880 }, { target := 556, numerator := 746960318427906131676364800 }, { target := 557, numerator := 14341638113815797728186204160 }, { target := 558, numerator := 746960318427906131676364800 }, { target := 559, numerator := 23006377807579508855632035840 }, { target := 560, numerator := 12997109540645566691168747520 }, { target := 561, numerator := 896352382113487358011637760 }]

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
    Slot15.Left8.expected,
    Slot15.Left9.expected,
    Slot15.Left10.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 578, numerator := 64601973485656746523361280 }, { target := 579, numerator := 1722719292950846573956300800 }, { target := 580, numerator := 1647350323884247036345712640 }, { target := 581, numerator := 53834977904713955436134400 }, { target := 582, numerator := 1690418306208018200694620160 }, { target := 583, numerator := 53834977904713955436134400 }, { target := 584, numerator := 1647350323884247036345712640 }, { target := 585, numerator := 936728615542022824588738560 }, { target := 586, numerator := 1690418306208018200694620160 }, { target := 587, numerator := 26389906168890780954793082880 }, { target := 588, numerator := 1033631575770507944373780480 }, { target := 589, numerator := 1722719292950846573956300800 }, { target := 590, numerator := 1647350323884247036345712640 }, { target := 591, numerator := 53834977904713955436134400 }, { target := 592, numerator := 1033631575770507944373780480 }, { target := 593, numerator := 53834977904713955436134400 }, { target := 594, numerator := 1658117319465189827432939520 }, { target := 595, numerator := 936728615542022824588738560 }, { target := 596, numerator := 64601973485656746523361280 }, { target := 679, numerator := 62986924148515327860277248 }, { target := 680, numerator := 1679651310627075409607393280 }, { target := 681, numerator := 1606166565787140860437069824 }, { target := 682, numerator := 52489103457096106550231040 }, { target := 683, numerator := 1648157848552817745677254656 }, { target := 684, numerator := 52489103457096106550231040 }, { target := 685, numerator := 1606166565787140860437069824 }, { target := 686, numerator := 913310400153472253974020096 }, { target := 687, numerator := 1648157848552817745677254656 }, { target := 688, numerator := 25730158514668511430923255808 }, { target := 689, numerator := 1007790786376245245764435968 }, { target := 690, numerator := 1679651310627075409607393280 }, { target := 691, numerator := 1606166565787140860437069824 }, { target := 692, numerator := 52489103457096106550231040 }, { target := 693, numerator := 1007790786376245245764435968 }, { target := 694, numerator := 52489103457096106550231040 }, { target := 695, numerator := 1616664386478560081747116032 }, { target := 696, numerator := 913310400153472253974020096 }, { target := 697, numerator := 62986924148515327860277248 }, { target := 714, numerator := 62986924148515327860277248 }, { target := 715, numerator := 1679651310627075409607393280 }, { target := 716, numerator := 1606166565787140860437069824 }, { target := 717, numerator := 52489103457096106550231040 }, { target := 718, numerator := 1648157848552817745677254656 }, { target := 719, numerator := 52489103457096106550231040 }, { target := 720, numerator := 1606166565787140860437069824 }, { target := 721, numerator := 913310400153472253974020096 }, { target := 722, numerator := 1648157848552817745677254656 }, { target := 723, numerator := 25730158514668511430923255808 }, { target := 724, numerator := 1007790786376245245764435968 }, { target := 725, numerator := 1679651310627075409607393280 }, { target := 726, numerator := 1606166565787140860437069824 }, { target := 727, numerator := 52489103457096106550231040 }, { target := 728, numerator := 1007790786376245245764435968 }, { target := 729, numerator := 52489103457096106550231040 }, { target := 730, numerator := 1616664386478560081747116032 }, { target := 731, numerator := 913310400153472253974020096 }, { target := 732, numerator := 62986924148515327860277248 }]

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
    Slot15.Left11.expected,
    Slot15.Left12.expected,
    Slot15.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 775, numerator := 62986924148515327860277248 }, { target := 776, numerator := 1679651310627075409607393280 }, { target := 777, numerator := 1606166565787140860437069824 }, { target := 778, numerator := 52489103457096106550231040 }, { target := 779, numerator := 1648157848552817745677254656 }, { target := 780, numerator := 52489103457096106550231040 }, { target := 781, numerator := 1606166565787140860437069824 }, { target := 782, numerator := 913310400153472253974020096 }, { target := 783, numerator := 1648157848552817745677254656 }, { target := 784, numerator := 25730158514668511430923255808 }, { target := 785, numerator := 1007790786376245245764435968 }, { target := 786, numerator := 1679651310627075409607393280 }, { target := 787, numerator := 1606166565787140860437069824 }, { target := 788, numerator := 52489103457096106550231040 }, { target := 789, numerator := 1007790786376245245764435968 }, { target := 790, numerator := 52489103457096106550231040 }, { target := 791, numerator := 1616664386478560081747116032 }, { target := 792, numerator := 913310400153472253974020096 }, { target := 793, numerator := 62986924148515327860277248 }, { target := 810, numerator := 2015581572752490491528871936 }, { target := 811, numerator := 53748841940066413107436584960 }, { target := 812, numerator := 51397330105188507533986234368 }, { target := 813, numerator := 1679651310627075409607393280 }, { target := 814, numerator := 52741051153690167861672148992 }, { target := 815, numerator := 1679651310627075409607393280 }, { target := 816, numerator := 51397330105188507533986234368 }, { target := 817, numerator := 29225932804911112127168643072 }, { target := 818, numerator := 52741051153690167861672148992 }, { target := 819, numerator := 823365072469392365789544185856 }, { target := 820, numerator := 32249305164039847864461950976 }, { target := 821, numerator := 53748841940066413107436584960 }, { target := 822, numerator := 51397330105188507533986234368 }, { target := 823, numerator := 1679651310627075409607393280 }, { target := 824, numerator := 32249305164039847864461950976 }, { target := 825, numerator := 1679651310627075409607393280 }, { target := 826, numerator := 51733260367313922615907713024 }, { target := 827, numerator := 29225932804911112127168643072 }, { target := 828, numerator := 2015581572752490491528871936 }, { target := 845, numerator := 62986924148515327860277248 }, { target := 846, numerator := 1679651310627075409607393280 }, { target := 847, numerator := 1606166565787140860437069824 }, { target := 848, numerator := 52489103457096106550231040 }, { target := 849, numerator := 1648157848552817745677254656 }, { target := 850, numerator := 52489103457096106550231040 }, { target := 851, numerator := 1606166565787140860437069824 }, { target := 852, numerator := 913310400153472253974020096 }, { target := 853, numerator := 1648157848552817745677254656 }, { target := 854, numerator := 25730158514668511430923255808 }, { target := 855, numerator := 1007790786376245245764435968 }, { target := 856, numerator := 1679651310627075409607393280 }, { target := 857, numerator := 1606166565787140860437069824 }, { target := 858, numerator := 52489103457096106550231040 }, { target := 859, numerator := 1007790786376245245764435968 }, { target := 860, numerator := 52489103457096106550231040 }, { target := 861, numerator := 1616664386478560081747116032 }, { target := 862, numerator := 913310400153472253974020096 }, { target := 863, numerator := 62986924148515327860277248 }]

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
    Slot15.Left14.expected,
    Slot15.Left15.expected,
    Slot16.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 87350844153806747630305280 }, { target := 35, numerator := 89846582558201226134028288 }, { target := 36, numerator := 87350844153806747630305280 }, { target := 37, numerator := 77367890536228833615413248 }, { target := 38, numerator := 3621316424776388308902084608 }, { target := 39, numerator := 985816669735819008970588160 }, { target := 40, numerator := 89846582558201226134028288 }, { target := 41, numerator := 3621316424776388308902084608 }, { target := 42, numerator := 87350844153806747630305280 }, { target := 43, numerator := 87350844153806747630305280 }, { target := 44, numerator := 74872152131834355111690240 }, { target := 45, numerator := 87350844153806747630305280 }, { target := 46, numerator := 985816669735819008970588160 }, { target := 47, numerator := 74872152131834355111690240 }, { target := 48, numerator := 87350844153806747630305280 }, { target := 49, numerator := 77367890536228833615413248 }, { target := 906, numerator := 72677220171363839838781440 }, { target := 907, numerator := 1938059204569702395700838400 }, { target := 908, numerator := 1853269114369777915888926720 }, { target := 909, numerator := 60564350142803199865651200 }, { target := 910, numerator := 1901720594484020475781447680 }, { target := 911, numerator := 60564350142803199865651200 }, { target := 912, numerator := 1853269114369777915888926720 }, { target := 913, numerator := 1053819692484775677662330880 }, { target := 914, numerator := 1901720594484020475781447680 }, { target := 915, numerator := 29688644440002128574142218240 }, { target := 916, numerator := 1162835522741821437420503040 }, { target := 917, numerator := 1938059204569702395700838400 }, { target := 918, numerator := 1853269114369777915888926720 }, { target := 919, numerator := 60564350142803199865651200 }, { target := 920, numerator := 1162835522741821437420503040 }, { target := 921, numerator := 60564350142803199865651200 }, { target := 922, numerator := 1865381984398338555862056960 }, { target := 923, numerator := 1053819692484775677662330880 }, { target := 924, numerator := 72677220171363839838781440 }, { target := 941, numerator := 75907318845646677164949504 }, { target := 942, numerator := 2024195169217244724398653440 }, { target := 943, numerator := 1935636630563990267706212352 }, { target := 944, numerator := 63256099038038897637457920 }, { target := 945, numerator := 1986241509794421385816178688 }, { target := 946, numerator := 63256099038038897637457920 }, { target := 947, numerator := 1935636630563990267706212352 }, { target := 948, numerator := 1100656123261876818891767808 }, { target := 949, numerator := 1986241509794421385816178688 }, { target := 950, numerator := 31008139748446667621881872384 }, { target := 951, numerator := 1214517101530346834639192064 }, { target := 952, numerator := 2024195169217244724398653440 }, { target := 953, numerator := 1935636630563990267706212352 }, { target := 954, numerator := 63256099038038897637457920 }, { target := 955, numerator := 1214517101530346834639192064 }, { target := 956, numerator := 63256099038038897637457920 }, { target := 957, numerator := 1948287850371598047233703936 }, { target := 958, numerator := 1100656123261876818891767808 }, { target := 959, numerator := 75907318845646677164949504 }]

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
    Slot16.Left1.expected,
    Slot16.Left3.expected,
    Slot16.Left11.expected,
    Slot16.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 79, numerator := 13945317080797627034852392960 }, { target := 80, numerator := 14343754711677559235848175616 }, { target := 81, numerator := 13945317080797627034852392960 }, { target := 82, numerator := 12351566557277898230869262336 }, { target := 83, numerator := 578133002406781623644880633856 }, { target := 84, numerator := 157382864197573219393334149120 }, { target := 85, numerator := 14343754711677559235848175616 }, { target := 86, numerator := 578133002406781623644880633856 }, { target := 87, numerator := 13945317080797627034852392960 }, { target := 88, numerator := 13945317080797627034852392960 }, { target := 89, numerator := 11953128926397966029873479680 }, { target := 90, numerator := 13945317080797627034852392960 }, { target := 91, numerator := 157382864197573219393334149120 }, { target := 92, numerator := 11953128926397966029873479680 }, { target := 93, numerator := 13945317080797627034852392960 }, { target := 94, numerator := 12351566557277898230869262336 }, { target := 154, numerator := 139153293486199047206584975360 }, { target := 155, numerator := 143129101871519019983915974656 }, { target := 156, numerator := 139153293486199047206584975360 }, { target := 157, numerator := 123250059944919156097260978176 }, { target := 158, numerator := 5768897967099280499907279978496 }, { target := 159, numerator := 1570444312201389247045744721920 }, { target := 160, numerator := 143129101871519019983915974656 }, { target := 161, numerator := 5768897967099280499907279978496 }, { target := 162, numerator := 139153293486199047206584975360 }, { target := 163, numerator := 139153293486199047206584975360 }, { target := 164, numerator := 119274251559599183319929978880 }, { target := 165, numerator := 139153293486199047206584975360 }, { target := 166, numerator := 1570444312201389247045744721920 }, { target := 167, numerator := 119274251559599183319929978880 }, { target := 168, numerator := 139153293486199047206584975360 }, { target := 169, numerator := 123250059944919156097260978176 }, { target := 492, numerator := 13945317080797627034852392960 }, { target := 493, numerator := 14343754711677559235848175616 }, { target := 494, numerator := 13945317080797627034852392960 }, { target := 495, numerator := 12351566557277898230869262336 }, { target := 496, numerator := 578133002406781623644880633856 }, { target := 497, numerator := 157382864197573219393334149120 }, { target := 498, numerator := 14343754711677559235848175616 }, { target := 499, numerator := 578133002406781623644880633856 }, { target := 500, numerator := 13945317080797627034852392960 }, { target := 501, numerator := 13945317080797627034852392960 }, { target := 502, numerator := 11953128926397966029873479680 }, { target := 503, numerator := 13945317080797627034852392960 }, { target := 504, numerator := 157382864197573219393334149120 }, { target := 505, numerator := 11953128926397966029873479680 }, { target := 506, numerator := 13945317080797627034852392960 }, { target := 507, numerator := 12351566557277898230869262336 }, { target := 890, numerator := 87340877147399421438197760 }, { target := 891, numerator := 89836330780182262050717696 }, { target := 892, numerator := 87340877147399421438197760 }, { target := 893, numerator := 77359062616268058988118016 }, { target := 894, numerator := 3620903221167901728766427136 }, { target := 895, numerator := 985704184949222041945374720 }, { target := 896, numerator := 89836330780182262050717696 }, { target := 897, numerator := 3620903221167901728766427136 }, { target := 898, numerator := 87340877147399421438197760 }, { target := 899, numerator := 87340877147399421438197760 }, { target := 900, numerator := 74863608983485218375598080 }, { target := 901, numerator := 87340877147399421438197760 }, { target := 902, numerator := 985704184949222041945374720 }, { target := 903, numerator := 74863608983485218375598080 }, { target := 904, numerator := 87340877147399421438197760 }, { target := 905, numerator := 77359062616268058988118016 }]

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
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left3.expected,
    Slot18.Left5.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 118842243771396506390315925504 }, { target := 1, numerator := 53334192152961314327206297600 }, { target := 2, numerator := 48748448528594547114025943040 }, { target := 3, numerator := 53334192152961314327206297600 }, { target := 4, numerator := 48748448528594547114025943040 }, { target := 10, numerator := 507733833200154272228966400 }, { target := 11, numerator := 10174986017331091615468486656 }, { target := 12, numerator := 17080166148853189717782429696 }, { target := 13, numerator := 16389648135700979907551035392 }, { target := 14, numerator := 507733833200154272228966400 }, { target := 15, numerator := 16389648135700979907551035392 }, { target := 16, numerator := 10946741443795326109256515584 }, { target := 17, numerator := 528043186528160443118125056 }, { target := 18, numerator := 10174986017331091615468486656 }, { target := 19, numerator := 487424479872148101339807744 }, { target := 50, numerator := 118842243771396506390315925504 }, { target := 51, numerator := 183086956139311691939163668480 }, { target := 52, numerator := 167344900097426948333179502592 }, { target := 53, numerator := 183086956139311691939163668480 }, { target := 54, numerator := 167344900097426948333179502592 }, { target := 55, numerator := 19076864444556838358011084800 }, { target := 56, numerator := 382300363468919040694542139392 }, { target := 57, numerator := 641745719914892042363492892672 }, { target := 58, numerator := 615801184270294742196597817344 }, { target := 59, numerator := 19076864444556838358011084800 }, { target := 60, numerator := 615801184270294742196597817344 }, { target := 61, numerator := 411297197424645434998718988288 }, { target := 62, numerator := 19839939022339111892331528192 }, { target := 63, numerator := 382300363468919040694542139392 }, { target := 64, numerator := 18313789866774564823690641408 }, { target := 140, numerator := 53334192152961314327206297600 }, { target := 141, numerator := 48748448528594547114025943040 }, { target := 142, numerator := 53334192152961314327206297600 }, { target := 143, numerator := 48748448528594547114025943040 }, { target := 144, numerator := 19075421620939898119362969600 }, { target := 145, numerator := 382271449283635558312033910784 }, { target := 146, numerator := 641697183328418172735370297344 }, { target := 147, numerator := 615754609923939911293036658688 }, { target := 148, numerator := 19075421620939898119362969600 }, { target := 149, numerator := 615754609923939911293036658688 }, { target := 150, numerator := 411266090147464203453465624576 }, { target := 151, numerator := 19838438485777494044137488384 }, { target := 152, numerator := 382271449283635558312033910784 }, { target := 153, numerator := 18312404756102302194588450816 }, { target := 482, numerator := 509176656817094510877081600 }, { target := 483, numerator := 10203900202614573997976715264 }, { target := 484, numerator := 17128702735327059345905025024 }, { target := 485, numerator := 16436222482055810811112194048 }, { target := 486, numerator := 509176656817094510877081600 }, { target := 487, numerator := 16436222482055810811112194048 }, { target := 488, numerator := 10977848720976557654509879296 }, { target := 489, numerator := 529543723089778291312164864 }, { target := 490, numerator := 10203900202614573997976715264 }, { target := 491, numerator := 488809590544410730441998336 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent0
