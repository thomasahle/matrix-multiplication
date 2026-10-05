import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk4Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 18; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent0

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
    Slot2.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 224581582825831717427740672 }, { target := 1, numerator := 39389499674306337079344234496 }, { target := 6, numerator := 39389504396672819948989448192 }, { target := 14, numerator := 224576860459348847782526976 }, { target := 16, numerator := 37164286350421159449722880 }, { target := 17, numerator := 11971410433761635328180879360 }, { target := 19, numerator := 127320984280582217455273771008 }, { target := 27, numerator := 11971446515593043504063840256 }, { target := 34, numerator := 37164286350421159449722880 }, { target := 35, numerator := 451086865910646161736204288 }, { target := 37, numerator := 17653779733830870486610870272 }, { target := 40, numerator := 17653786208638040358663487488 }, { target := 47, numerator := 451093340717816033788821504 }, { target := 51, numerator := 40660313287270593671987200 }, { target := 52, numerator := 13097555382540848467437158400 }, { target := 54, numerator := 139298009386731055907099115520 }, { target := 62, numerator := 13097594858573166205877616640 }, { target := 69, numerator := 40660313287270593671987200 }, { target := 70, numerator := 9416438325884738626243264512 }, { target := 72, numerator := 368522651943719421408001916928 }, { target := 75, numerator := 368522787105319092487100301312 }, { target := 82, numerator := 9416573487484409705341648896 }, { target := 96, numerator := 488677438069866675214221312 }, { target := 98, numerator := 19124928044983443027161776128 }, { target := 101, numerator := 19124935059357877055218778112 }, { target := 108, numerator := 488684452444300703271223296 }, { target := 126, numerator := 37164286350421159449722880 }, { target := 127, numerator := 11971410433761635328180879360 }, { target := 129, numerator := 127320984280582217455273771008 }, { target := 137, numerator := 11971446515593043504063840256 }, { target := 144, numerator := 37164286350421159449722880 }, { target := 145, numerator := 10130659196909928382325587968 }, { target := 147, numerator := 396474469855618299678469128192 }, { target := 150, numerator := 396474615268995989721650823168 }, { target := 157, numerator := 10130804610287618425507282944 }, { target := 171, numerator := 15167795866245477188379869184 }, { target := 173, numerator := 593608343550063020112290512896 }, { target := 176, numerator := 593608561265454107060059766784 }, { target := 183, numerator := 15168013581636564136149123072 }, { target := 216, numerator := 469882151990256418475212800 }, { target := 218, numerator := 18389353889407156756886323200 }, { target := 221, numerator := 18389360633997958706941132800 }, { target := 228, numerator := 469888896581058368530022400 }, { target := 266, numerator := 40660313287270593671987200 }, { target := 267, numerator := 13097555382540848467437158400 }, { target := 269, numerator := 139298009386731055907099115520 }, { target := 277, numerator := 13097594858573166205877616640 }, { target := 284, numerator := 40660313287270593671987200 }, { target := 285, numerator := 15167795866245477188379869184 }, { target := 287, numerator := 593608343550063020112290512896 }, { target := 290, numerator := 593608561265454107060059766784 }, { target := 297, numerator := 15168013581636564136149123072 }, { target := 311, numerator := 15806835592952225917506158592 }, { target := 313, numerator := 618617864839656753301655912448 }, { target := 316, numerator := 618618091727691330901499707392 }, { target := 323, numerator := 15807062480986803517349953536 }, { target := 356, numerator := 9416438325884738626243264512 }, { target := 358, numerator := 368522651943719421408001916928 }, { target := 361, numerator := 368522787105319092487100301312 }, { target := 368, numerator := 9416573487484409705341648896 }, { target := 427, numerator := 469882151990256418475212800 }, { target := 429, numerator := 18389353889407156756886323200 }, { target := 432, numerator := 18389360633997958706941132800 }, { target := 439, numerator := 469888896581058368530022400 }]

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
    Slot3.Left11.expected,
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot4.Left4.expected,
    Slot4.Left5.expected,
    Slot4.Left6.expected,
    Slot4.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 41230047766388932298762354688 }, { target := 89, numerator := 147784770392666063295423184896 }, { target := 91, numerator := 41242029148025735537051566080 }, { target := 112, numerator := 46550053929793955821183303680 }, { target := 115, numerator := 166853773023977813398058434560 }, { target := 117, numerator := 46563581296158088509574348800 }, { target := 122, numerator := 6847353393491983860592803840 }, { target := 124, numerator := 6847358291102535430478757888 }, { target := 161, numerator := 39900046225537676418157117440 }, { target := 164, numerator := 143017519734838125769764372480 }, { target := 166, numerator := 39911641110992647293920870400 }, { target := 187, numerator := 525350608636246072839068712960 }, { target := 190, numerator := 1883064009842035322635230904320 }, { target := 192, numerator := 525503274628069856036624793600 }, { target := 197, numerator := 99286624205633765978595655680 }, { target := 199, numerator := 99286695220986763741941989376 }, { target := 201, numerator := 46550053929793955821183303680 }, { target := 204, numerator := 166853773023977813398058434560 }, { target := 206, numerator := 46563581296158088509574348800 }, { target := 211, numerator := 175748737099627585755215298560 }, { target := 213, numerator := 175748862804965076048954785792 }, { target := 232, numerator := 39900046225537676418157117440 }, { target := 235, numerator := 143017519734838125769764372480 }, { target := 237, numerator := 39911641110992647293920870400 }, { target := 242, numerator := 5706127827909986550494003200 }, { target := 244, numerator := 5706131909252112858732298240 }, { target := 246, numerator := 46550053929793955821183303680 }, { target := 249, numerator := 166853773023977813398058434560 }, { target := 251, numerator := 46563581296158088509574348800 }, { target := 256, numerator := 109557654295871741769484861440 }, { target := 258, numerator := 109557732657640566887660126208 }, { target := 261, numerator := 5706127827909986550494003200 }, { target := 263, numerator := 5706131909252112858732298240 }, { target := 301, numerator := 46550053929793955821183303680 }, { target := 304, numerator := 166853773023977813398058434560 }, { target := 306, numerator := 46563581296158088509574348800 }, { target := 327, numerator := 1929832235775172282758199246848 }, { target := 330, numerator := 6917280704508337349730936815616 }, { target := 332, numerator := 1930393041735011040782639431680 }, { target := 337, numerator := 174607511534045588445116497920 }, { target := 339, numerator := 174607636423114653477208326144 }, { target := 341, numerator := 47880055470645211701788540928 }, { target := 344, numerator := 171621023681805750923717246976 }, { target := 346, numerator := 47893969333191176752705044480 }, { target := 351, numerator := 182596090493119569615808102400 }, { target := 353, numerator := 182596221096067611479433543680 }, { target := 372, numerator := 525350608636246072839068712960 }, { target := 375, numerator := 1883064009842035322635230904320 }, { target := 377, numerator := 525503274628069856036624793600 }, { target := 386, numerator := 1929832235775172282758199246848 }, { target := 389, numerator := 6917280704508337349730936815616 }, { target := 391, numerator := 1930393041735011040782639431680 }, { target := 406, numerator := 41230047766388932298762354688 }, { target := 409, numerator := 147784770392666063295423184896 }, { target := 411, numerator := 41242029148025735537051566080 }, { target := 443, numerator := 46550053929793955821183303680 }, { target := 446, numerator := 166853773023977813398058434560 }, { target := 448, numerator := 46563581296158088509574348800 }, { target := 457, numerator := 47880055470645211701788540928 }, { target := 460, numerator := 171621023681805750923717246976 }, { target := 462, numerator := 47893969333191176752705044480 }, { target := 477, numerator := 46550053929793955821183303680 }, { target := 480, numerator := 166853773023977813398058434560 }, { target := 482, numerator := 46563581296158088509574348800 }]

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
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot4.Left10.expected,
    Slot4.Left11.expected,
    Slot4.Left12.expected,
    Slot4.Left13.expected,
    Slot4.Left14.expected,
    Slot4.Left15.expected,
    Slot4.Left16.expected,
    Slot4.Left17.expected,
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
    Slot6.Left0.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 198731348698603279527968768 }, { target := 1, numerator := 39415349908433565517244006400 }, { target := 6, numerator := 39415349908433565517244006400 }, { target := 14, numerator := 198731348698603279527968768 }, { target := 16, numerator := 726691921483429614419181568 }, { target := 17, numerator := 119090810253588833035784028160 }, { target := 19, numerator := 1226086002163745720180156661760 }, { target := 27, numerator := 119090810253588833035784028160 }, { target := 34, numerator := 726691921483429614419181568 }, { target := 35, numerator := 93365079744690072064685506560 }, { target := 37, numerator := 3732718565337770886760476180480 }, { target := 40, numerator := 3732717653128453446297830031360 }, { target := 47, numerator := 93365079744690072064685506560 }, { target := 126, numerator := 726691921483429614419181568 }, { target := 127, numerator := 119090810253588833035784028160 }, { target := 129, numerator := 1226086002163745720180156661760 }, { target := 137, numerator := 119090810253588833035784028160 }, { target := 144, numerator := 726691921483429614419181568 }, { target := 145, numerator := 340106639775166907998703452160 }, { target := 147, numerator := 13597400355196636360867085025280 }, { target := 150, numerator := 13597397032236418529328323624960 }, { target := 157, numerator := 340106639775166907998703452160 }, { target := 215, numerator := 2727336649050603418137133056 }, { target := 216, numerator := 93365142548538108400998809600 }, { target := 218, numerator := 3732721076223962822105418956800 }, { target := 221, numerator := 3732720164014031766193543577600 }, { target := 228, numerator := 93365142548538108400998809600 }, { target := 260, numerator := 2030995376952577013506375680 }, { target := 265, numerator := 2147052255635581414278168576 }, { target := 355, numerator := 2785365088392105618523029504 }, { target := 382, numerator := 109557654295871741769484861440 }, { target := 384, numerator := 109557732657640566887660126208 }, { target := 396, numerator := 2797143861241475407052160368640 }, { target := 398, numerator := 2797145861915385723350572597248 }, { target := 400, numerator := 37312286496585914848131416064 }, { target := 401, numerator := 179172413796373577685511700480 }, { target := 403, numerator := 179172541950516343764194164736 }, { target := 405, numerator := 67487074954167059048797569024 }, { target := 416, numerator := 99286624205633765978595655680 }, { target := 418, numerator := 99286695220986763741941989376 }, { target := 420, numerator := 2030995376952577013506375680 }, { target := 421, numerator := 174607511534045588445116497920 }, { target := 423, numerator := 174607636423114653477208326144 }, { target := 425, numerator := 37312286496585914848131416064 }, { target := 426, numerator := 2205080694977083614664065024 }, { target := 453, numerator := 5706127827909986550494003200 }, { target := 455, numerator := 5706131909252112858732298240 }, { target := 467, numerator := 179172413796373577685511700480 }, { target := 469, numerator := 179172541950516343764194164736 }, { target := 471, numerator := 2205080694977083614664065024 }, { target := 472, numerator := 5706127827909986550494003200 }, { target := 474, numerator := 5706131909252112858732298240 }, { target := 476, numerator := 2147052255635581414278168576 }, { target := 487, numerator := 174607511534045588445116497920 }, { target := 489, numerator := 174607636423114653477208326144 }, { target := 491, numerator := 2147052255635581414278168576 }, { target := 492, numerator := 182596090493119569615808102400 }, { target := 494, numerator := 182596221096067611479433543680 }, { target := 496, numerator := 67487074954167059048797569024 }, { target := 497, numerator := 2147052255635581414278168576 }, { target := 498, numerator := 6847353393491983860592803840 }, { target := 500, numerator := 6847358291102535430478757888 }, { target := 502, numerator := 2727336649050603418137133056 }, { target := 503, numerator := 2785365088392105618523029504 }]

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
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left6.expected,
    Slot11.Left14.expected,
    Slot12.Left0.expected,
    Slot13.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 2727336649050603418137133056 }, { target := 1, numerator := 2030995376952577013506375680 }, { target := 2, numerator := 2147052255635581414278168576 }, { target := 3, numerator := 2785365088392105618523029504 }, { target := 4, numerator := 37312286496585914848131416064 }, { target := 5, numerator := 67487074954167059048797569024 }, { target := 6, numerator := 2030995376952577013506375680 }, { target := 7, numerator := 37312286496585914848131416064 }, { target := 8, numerator := 2205080694977083614664065024 }, { target := 9, numerator := 2205080694977083614664065024 }, { target := 10, numerator := 2147052255635581414278168576 }, { target := 11, numerator := 2147052255635581414278168576 }, { target := 12, numerator := 67487074954167059048797569024 }, { target := 13, numerator := 2147052255635581414278168576 }, { target := 14, numerator := 2727336649050603418137133056 }, { target := 15, numerator := 2785365088392105618523029504 }, { target := 16, numerator := 7079467067847644330443407360 }, { target := 17, numerator := 102652272483790842791429406720 }, { target := 18, numerator := 181706321408089537814714122240 }, { target := 19, numerator := 5899555889873036942036172800 }, { target := 20, numerator := 113271473085562309287094517760 }, { target := 21, numerator := 5899555889873036942036172800 }, { target := 22, numerator := 180526410230114930426306887680 }, { target := 23, numerator := 188785788475937182145157529600 }, { target := 24, numerator := 113271473085562309287094517760 }, { target := 25, numerator := 2891962297215762708986131906560 }, { target := 26, numerator := 185246054942013359979935825920 }, { target := 27, numerator := 102652272483790842791429406720 }, { target := 28, numerator := 180526410230114930426306887680 }, { target := 29, numerator := 5899555889873036942036172800 }, { target := 30, numerator := 185246054942013359979935825920 }, { target := 31, numerator := 5899555889873036942036172800 }, { target := 32, numerator := 180526410230114930426306887680 }, { target := 33, numerator := 188785788475937182145157529600 }, { target := 34, numerator := 7079467067847644330443407360 }, { target := 86, numerator := 92851143525911961576256045056 }, { target := 89, numerator := 338234493134202686486783983616 }, { target := 91, numerator := 92851205984050742666681384960 }, { target := 122, numerator := 707051599281174759975419904 }, { target := 124, numerator := 707051599281174759975419904 }, { target := 161, numerator := 3712171490666186826833354293248 }, { target := 164, numerator := 13522552279846930105669651529728 }, { target := 166, numerator := 3712173987730986879965389127680 }, { target := 197, numerator := 115872139706194540251033108480 }, { target := 199, numerator := 115872139706194540251033108480 }, { target := 215, numerator := 198731348698603279527968768 }, { target := 232, numerator := 3712170583478205078703530049536 }, { target := 235, numerator := 13522548975178236408983397072896 }, { target := 237, numerator := 3712173080542394894086056181760 }, { target := 242, numerator := 1192948542645806646661774049280 }, { target := 244, numerator := 1192948542645806646661774049280 }, { target := 260, numerator := 39415349908433565517244006400 }, { target := 406, numerator := 92851143525911961576256045056 }, { target := 409, numerator := 338234493134202686486783983616 }, { target := 411, numerator := 92851205984050742666681384960 }, { target := 416, numerator := 115872139706194540251033108480 }, { target := 418, numerator := 115872139706194540251033108480 }, { target := 420, numerator := 39415349908433565517244006400 }, { target := 498, numerator := 707051599281174759975419904 }, { target := 500, numerator := 707051599281174759975419904 }, { target := 502, numerator := 198731348698603279527968768 }]

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
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 41122677850330627787567661056 }, { target := 36, numerator := 46428829831018450727898972160 }, { target := 37, numerator := 39796139855158672052484833280 }, { target := 38, numerator := 523982508092922515357716971520 }, { target := 39, numerator := 46428829831018450727898972160 }, { target := 40, numerator := 39796139855158672052484833280 }, { target := 41, numerator := 46428829831018450727898972160 }, { target := 42, numerator := 46428829831018450727898972160 }, { target := 43, numerator := 1924806630994507771605183102976 }, { target := 44, numerator := 47755367826190406462981799936 }, { target := 45, numerator := 523982508092922515357716971520 }, { target := 46, numerator := 1924806630994507771605183102976 }, { target := 47, numerator := 41122677850330627787567661056 }, { target := 48, numerator := 46428829831018450727898972160 }, { target := 49, numerator := 47755367826190406462981799936 }, { target := 50, numerator := 46428829831018450727898972160 }, { target := 126, numerator := 7079472131478892563715325952 }, { target := 127, numerator := 102652345906443942173872226304 }, { target := 128, numerator := 181706451374624909135360032768 }, { target := 129, numerator := 5899560109565743803096104960 }, { target := 130, numerator := 113271554103662281019445215232 }, { target := 131, numerator := 5899560109565743803096104960 }, { target := 132, numerator := 180526539352711760374740811776 }, { target := 133, numerator := 188785923506103801699075358720 }, { target := 134, numerator := 113271554103662281019445215232 }, { target := 135, numerator := 2891964365709127612277710651392 }, { target := 136, numerator := 185246187440364355417217695744 }, { target := 137, numerator := 102652345906443942173872226304 }, { target := 138, numerator := 180526539352711760374740811776 }, { target := 139, numerator := 5899560109565743803096104960 }, { target := 140, numerator := 185246187440364355417217695744 }, { target := 141, numerator := 5899560109565743803096104960 }, { target := 142, numerator := 180526539352711760374740811776 }, { target := 143, numerator := 188785923506103801699075358720 }, { target := 144, numerator := 7079472131478892563715325952 }, { target := 145, numerator := 147399914219768495422258020352 }, { target := 146, numerator := 166419257990061204509000990720 }, { target := 147, numerator := 142645078277195318150572277760 }, { target := 148, numerator := 1878160197316405022315868323840 }, { target := 149, numerator := 166419257990061204509000990720 }, { target := 150, numerator := 142645078277195318150572277760 }, { target := 151, numerator := 166419257990061204509000990720 }, { target := 152, numerator := 166419257990061204509000990720 }, { target := 153, numerator := 6899266952673680221216012500992 }, { target := 154, numerator := 171174093932634381780686733312 }, { target := 155, numerator := 1878160197316405022315868323840 }, { target := 156, numerator := 6899266952673680221216012500992 }, { target := 157, numerator := 147399914219768495422258020352 }, { target := 158, numerator := 166419257990061204509000990720 }, { target := 159, numerator := 171174093932634381780686733312 }, { target := 160, numerator := 166419257990061204509000990720 }]

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
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 456870030858218548425129984 }, { target := 87, numerator := 9537161894165312198374588416 }, { target := 88, numerator := 494942533429736760793890816 }, { target := 89, numerator := 10260539443024158233381044224 }, { target := 90, numerator := 15362254787607598690794995712 }, { target := 91, numerator := 475906282143977654609510400 }, { target := 92, numerator := 15362254787607598690794995712 }, { target := 93, numerator := 16009487331323408301063929856 }, { target := 94, numerator := 9537161894165312198374588416 }, { target := 95, numerator := 475906282143977654609510400 }, { target := 122, numerator := 37164286350421159449722880 }, { target := 123, numerator := 40660313287270593671987200 }, { target := 124, numerator := 37164286350421159449722880 }, { target := 125, numerator := 40660313287270593671987200 }, { target := 161, numerator := 17880110243238958569772548096 }, { target := 162, numerator := 373247301327613260144001941504 }, { target := 163, numerator := 19370119430175538450586927104 }, { target := 164, numerator := 401557475879408277879475142656 }, { target := 165, numerator := 601218706928909981908601929728 }, { target := 166, numerator := 18625114836707248510179737600 }, { target := 167, numerator := 601218706928909981908601929728 }, { target := 168, numerator := 626548863106831839882446372864 }, { target := 169, numerator := 373247301327613260144001941504 }, { target := 170, numerator := 18625114836707248510179737600 }, { target := 197, numerator := 11971410433761635328180879360 }, { target := 198, numerator := 13097555382540848467437158400 }, { target := 199, numerator := 11971410433761635328180879360 }, { target := 200, numerator := 13097555382540848467437158400 }, { target := 216, numerator := 41134628030452751850757160960 }, { target := 217, numerator := 46442321969866010154080665600 }, { target := 218, numerator := 39807704545599437274926284800 }, { target := 219, numerator := 524134776517059257453196083200 }, { target := 220, numerator := 46442321969866010154080665600 }, { target := 221, numerator := 39807704545599437274926284800 }, { target := 222, numerator := 46442321969866010154080665600 }, { target := 223, numerator := 46442321969866010154080665600 }, { target := 224, numerator := 1925365976522159449530601308160 }, { target := 225, numerator := 47769245454719324729911541760 }, { target := 226, numerator := 524134776517059257453196083200 }, { target := 227, numerator := 1925365976522159449530601308160 }, { target := 228, numerator := 41134628030452751850757160960 }, { target := 229, numerator := 46442321969866010154080665600 }, { target := 230, numerator := 47769245454719324729911541760 }, { target := 231, numerator := 46442321969866010154080665600 }, { target := 232, numerator := 17880116801056476773518147584 }, { target := 233, numerator := 373247438222053952647191330816 }, { target := 234, numerator := 19370126534477849837977993216 }, { target := 235, numerator := 401557623157060040871928397824 }, { target := 236, numerator := 601218927435524031509547712512 }, { target := 237, numerator := 18625121667767163305748070400 }, { target := 238, numerator := 601218927435524031509547712512 }, { target := 239, numerator := 626549092903687373605365088256 }, { target := 240, numerator := 373247438222053952647191330816 }, { target := 241, numerator := 18625121667767163305748070400 }, { target := 406, numerator := 456876588675736752170729472 }, { target := 407, numerator := 9537298788606004701563977728 }, { target := 408, numerator := 494949637732048148184956928 }, { target := 409, numerator := 10260686720675921225834299392 }, { target := 410, numerator := 15362475294221648291740778496 }, { target := 411, numerator := 475913113203892450177843200 }, { target := 412, numerator := 15362475294221648291740778496 }, { target := 413, numerator := 16009717128178942023982645248 }, { target := 414, numerator := 9537298788606004701563977728 }, { target := 415, numerator := 475913113203892450177843200 }]

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
    Slot16.Left3.expected,
    Slot16.Left11.expected,
    Slot16.Left18.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left6.expected,
    Slot17.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 215, numerator := 224581582825831717427740672 }, { target := 242, numerator := 127320984280582217455273771008 }, { target := 243, numerator := 139298009386731055907099115520 }, { target := 244, numerator := 127320984280582217455273771008 }, { target := 245, numerator := 139298009386731055907099115520 }, { target := 260, numerator := 39389499674306337079344234496 }, { target := 416, numerator := 11971446515593043504063840256 }, { target := 417, numerator := 13097594858573166205877616640 }, { target := 418, numerator := 11971446515593043504063840256 }, { target := 419, numerator := 13097594858573166205877616640 }, { target := 420, numerator := 39389504396672819948989448192 }, { target := 498, numerator := 37164286350421159449722880 }, { target := 499, numerator := 40660313287270593671987200 }, { target := 500, numerator := 37164286350421159449722880 }, { target := 501, numerator := 40660313287270593671987200 }, { target := 502, numerator := 224576860459348847782526976 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent0
