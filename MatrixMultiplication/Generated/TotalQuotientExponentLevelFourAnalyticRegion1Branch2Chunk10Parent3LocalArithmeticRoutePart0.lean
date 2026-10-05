import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk10Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 45; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent3

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
  [{ target := 86, numerator := 67362708241553962190342455296 }, { target := 89, numerator := 245012690567682474944621445120 }, { target := 91, numerator := 67362708241553962190342455296 }, { target := 112, numerator := 65959318486521587978043654144 }, { target := 115, numerator := 239908259514189090049941831680 }, { target := 117, numerator := 65959318486521587978043654144 }, { target := 122, numerator := 54662802892319760839312670720 }, { target := 124, numerator := 54662776827070384687716237312 }, { target := 161, numerator := 51925420936197845855055642624 }, { target := 164, numerator := 188863948979255241103145697280 }, { target := 166, numerator := 51925420936197845855055642624 }, { target := 197, numerator := 1457674743795193622381671219200 }, { target := 199, numerator := 1457674048721876925005766328320 }, { target := 211, numerator := 1393901473754153901402473103360 }, { target := 213, numerator := 1393900809090294809536764051456 }, { target := 215, numerator := 44681898292956694297140264960 }, { target := 242, numerator := 45552335743599800699427225600 }, { target := 244, numerator := 45552314022558653906430197760 }, { target := 256, numerator := 1430343342349033741962014883840 }, { target := 258, numerator := 1430342660308341732661908209664 }, { target := 260, numerator := 45958523958469742705629986816 }, { target := 261, numerator := 45552335743599800699427225600 }, { target := 263, numerator := 45552314022558653906430197760 }, { target := 265, numerator := 44681898292956694297140264960 }, { target := 337, numerator := 1393901473754153901402473103360 }, { target := 339, numerator := 1393900809090294809536764051456 }, { target := 351, numerator := 792610641938636532170033725440 }, { target := 353, numerator := 792610263992520577971885441024 }, { target := 355, numerator := 39575395630904500663181377536 }, { target := 382, numerator := 1430343342349033741962014883840 }, { target := 384, numerator := 1430342660308341732661908209664 }, { target := 396, numerator := 22329754981512622302859225989120 }, { target := 398, numerator := 22329744333858252144932082941952 }, { target := 400, numerator := 1852383840659433240718586413056 }, { target := 401, numerator := 874604846277116173429002731520 }, { target := 403, numerator := 874604429233126155003459796992 }, { target := 405, numerator := 504267137877654121353440133120 }, { target := 416, numerator := 1457674743795193622381671219200 }, { target := 418, numerator := 1457674048721876925005766328320 }, { target := 420, numerator := 45958523958469742705629986816 }, { target := 421, numerator := 1393901473754153901402473103360 }, { target := 423, numerator := 1393900809090294809536764051456 }, { target := 425, numerator := 1852383840659433240718586413056 }, { target := 426, numerator := 44681898292956694297140264960 }, { target := 453, numerator := 45552335743599800699427225600 }, { target := 455, numerator := 45552314022558653906430197760 }, { target := 467, numerator := 874604846277116173429002731520 }, { target := 469, numerator := 874604429233126155003459796992 }, { target := 471, numerator := 44681898292956694297140264960 }, { target := 472, numerator := 45552335743599800699427225600 }, { target := 474, numerator := 45552314022558653906430197760 }, { target := 476, numerator := 38298769965391452254691655680 }, { target := 487, numerator := 1403011940902873861542358548480 }, { target := 489, numerator := 1403011271894806540318050091008 }, { target := 491, numerator := 44681898292956694297140264960 }, { target := 492, numerator := 792610641938636532170033725440 }, { target := 494, numerator := 792610263992520577971885441024 }, { target := 496, numerator := 504267137877654121353440133120 }, { target := 497, numerator := 38298769965391452254691655680 }, { target := 498, numerator := 54662802892319760839312670720 }, { target := 500, numerator := 54662776827070384687716237312 }, { target := 502, numerator := 44681898292956694297140264960 }, { target := 503, numerator := 39575395630904500663181377536 }]

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
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 213426080367952529473929216 }, { target := 37, numerator := 7881541207771604424358625280 }, { target := 40, numerator := 7881539277781005712496787456 }, { target := 47, numerator := 213428010358551241335767040 }, { target := 70, numerator := 5232381325149803948393103360 }, { target := 72, numerator := 193224881222787721371372748800 }, { target := 75, numerator := 193224833906889172306372853760 }, { target := 82, numerator := 5232428641048353013392998400 }, { target := 96, numerator := 213426080367952529473929216 }, { target := 98, numerator := 7881541207771604424358625280 }, { target := 101, numerator := 7881539277781005712496787456 }, { target := 108, numerator := 213428010358551241335767040 }, { target := 145, numerator := 4385561715947927783061061632 }, { target := 147, numerator := 161952959656468129623111106560 }, { target := 150, numerator := 161952919998274214156788826112 }, { target := 157, numerator := 4385601374141843249383342080 }, { target := 171, numerator := 4309829880978654304860635136 }, { target := 173, numerator := 159156283744033044182209658880 }, { target := 176, numerator := 159156244770674502452354482176 }, { target := 183, numerator := 4309868854337196034715811840 }, { target := 187, numerator := 1632142285102651208903505739776 }, { target := 190, numerator := 5936453315212806632512390430720 }, { target := 192, numerator := 1632142285102651208903505739776 }, { target := 201, numerator := 51925420936197845855055642624 }, { target := 204, numerator := 188863948979255241103145697280 }, { target := 206, numerator := 51925420936197845855055642624 }, { target := 216, numerator := 213426080367952529473929216 }, { target := 218, numerator := 7881541207771604424358625280 }, { target := 221, numerator := 7881539277781005712496787456 }, { target := 228, numerator := 213428010358551241335767040 }, { target := 232, numerator := 51925420936197845855055642624 }, { target := 235, numerator := 188863948979255241103145697280 }, { target := 237, numerator := 51925420936197845855055642624 }, { target := 246, numerator := 53328810691230220067354443776 }, { target := 249, numerator := 193968380032748625997825310720 }, { target := 251, numerator := 53328810691230220067354443776 }, { target := 301, numerator := 53328810691230220067354443776 }, { target := 304, numerator := 193968380032748625997825310720 }, { target := 306, numerator := 53328810691230220067354443776 }, { target := 327, numerator := 902379612485816618508129140736 }, { target := 330, numerator := 3282149167396246487278991441920 }, { target := 332, numerator := 902379612485816618508129140736 }, { target := 341, numerator := 49118641426133097430458040320 }, { target := 344, numerator := 178655086872268471313786470400 }, { target := 346, numerator := 49118641426133097430458040320 }, { target := 372, numerator := 1632142285102651208903505739776 }, { target := 375, numerator := 5936453315212806632512390430720 }, { target := 377, numerator := 1632142285102651208903505739776 }, { target := 386, numerator := 902379612485816618508129140736 }, { target := 389, numerator := 3282149167396246487278991441920 }, { target := 391, numerator := 902379612485816618508129140736 }, { target := 406, numerator := 67362708241553962190342455296 }, { target := 409, numerator := 245012690567682474944621445120 }, { target := 411, numerator := 67362708241553962190342455296 }, { target := 443, numerator := 51925420936197845855055642624 }, { target := 446, numerator := 188863948979255241103145697280 }, { target := 448, numerator := 51925420936197845855055642624 }, { target := 457, numerator := 49118641426133097430458040320 }, { target := 460, numerator := 178655086872268471313786470400 }, { target := 462, numerator := 49118641426133097430458040320 }, { target := 477, numerator := 65959318486521587978043654144 }, { target := 480, numerator := 239908259514189090049941831680 }, { target := 482, numerator := 65959318486521587978043654144 }]

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
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 24202128224706931720192000 }, { target := 17, numerator := 406595754175076452899225600 }, { target := 18, numerator := 880957467379332314614988800 }, { target := 19, numerator := 29042553869648318064230400 }, { target := 20, numerator := 464680861914373089027686400 }, { target := 21, numerator := 33882979514589704408268800 }, { target := 22, numerator := 880957467379332314614988800 }, { target := 23, numerator := 880957467379332314614988800 }, { target := 24, numerator := 464680861914373089027686400 }, { target := 25, numerator := 10871595998538353728710246400 }, { target := 26, numerator := 871276616089449541926912000 }, { target := 27, numerator := 406595754175076452899225600 }, { target := 28, numerator := 880957467379332314614988800 }, { target := 29, numerator := 33882979514589704408268800 }, { target := 30, numerator := 871276616089449541926912000 }, { target := 31, numerator := 33882979514589704408268800 }, { target := 32, numerator := 880957467379332314614988800 }, { target := 33, numerator := 880957467379332314614988800 }, { target := 34, numerator := 29042553869648318064230400 }, { target := 51, numerator := 24036845397806494137712640 }, { target := 52, numerator := 403819002683149101513572352 }, { target := 53, numerator := 874941172480156386612740096 }, { target := 54, numerator := 28844214477367792965255168 }, { target := 55, numerator := 461507431637884687444082688 }, { target := 56, numerator := 33651583556929091792797696 }, { target := 57, numerator := 874941172480156386612740096 }, { target := 58, numerator := 874941172480156386612740096 }, { target := 59, numerator := 461507431637884687444082688 }, { target := 60, numerator := 10797350952694677166660517888 }, { target := 61, numerator := 865326434321033788957655040 }, { target := 62, numerator := 403819002683149101513572352 }, { target := 63, numerator := 874941172480156386612740096 }, { target := 64, numerator := 33651583556929091792797696 }, { target := 65, numerator := 865326434321033788957655040 }, { target := 66, numerator := 33651583556929091792797696 }, { target := 67, numerator := 874941172480156386612740096 }, { target := 68, numerator := 874941172480156386612740096 }, { target := 69, numerator := 28844214477367792965255168 }, { target := 285, numerator := 4316714593248588257424310272 }, { target := 287, numerator := 159410527008799870131382517760 }, { target := 290, numerator := 159410487973183567152757604352 }, { target := 297, numerator := 4316753628864891236049223680 }, { target := 311, numerator := 3869208295702881340785426432 }, { target := 313, numerator := 142884714798956183435146690560 }, { target := 316, numerator := 142884679810094361626554662912 }, { target := 323, numerator := 3869243284564703149377454080 }, { target := 356, numerator := 5232381325149803948393103360 }, { target := 358, numerator := 193224881222787721371372748800 }, { target := 361, numerator := 193224833906889172306372853760 }, { target := 368, numerator := 5232428641048353013392998400 }, { target := 427, numerator := 213426080367952529473929216 }, { target := 429, numerator := 7881541207771604424358625280 }, { target := 432, numerator := 7881539277781005712496787456 }, { target := 439, numerator := 213428010358551241335767040 }]

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
    Slot4.Left2.expected,
    Slot4.Left3.expected,
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
    Slot7.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 1353903862882822131973714083840 }, { target := 89, numerator := 4647715230213880365180814098432 }, { target := 91, numerator := 1353903862882822131973714083840 }, { target := 122, numerator := 68785966577646837834469867520 }, { target := 124, numerator := 68785966577646837834469867520 }, { target := 126, numerator := 24202128224706931720192000 }, { target := 127, numerator := 406595754175076452899225600 }, { target := 128, numerator := 880957467379332314614988800 }, { target := 129, numerator := 29042553869648318064230400 }, { target := 130, numerator := 464680861914373089027686400 }, { target := 131, numerator := 33882979514589704408268800 }, { target := 132, numerator := 880957467379332314614988800 }, { target := 133, numerator := 880957467379332314614988800 }, { target := 134, numerator := 464680861914373089027686400 }, { target := 135, numerator := 10871595998538353728710246400 }, { target := 136, numerator := 871276616089449541926912000 }, { target := 137, numerator := 406595754175076452899225600 }, { target := 138, numerator := 880957467379332314614988800 }, { target := 139, numerator := 33882979514589704408268800 }, { target := 140, numerator := 871276616089449541926912000 }, { target := 141, numerator := 33882979514589704408268800 }, { target := 142, numerator := 880957467379332314614988800 }, { target := 143, numerator := 880957467379332314614988800 }, { target := 144, numerator := 29042553869648318064230400 }, { target := 161, numerator := 47383259635445234049037652459520 }, { target := 164, numerator := 162658445331503852009711726493696 }, { target := 166, numerator := 47383259635445234049037652459520 }, { target := 197, numerator := 7212084535556991099212167905280 }, { target := 199, numerator := 7212084535556991099212167905280 }, { target := 215, numerator := 22441818894552442770334679040 }, { target := 232, numerator := 47383282875138545860191128125440 }, { target := 235, numerator := 162658525109307514390239208538112 }, { target := 237, numerator := 47383282875138545860191128125440 }, { target := 242, numerator := 77739062823291724879248752640000 }, { target := 244, numerator := 77739062823291724879248752640000 }, { target := 260, numerator := 1879034081447791659474720129024 }, { target := 266, numerator := 24272963721949976398397440 }, { target := 267, numerator := 407785790528759603493076992 }, { target := 268, numerator := 883535879478979140901666816 }, { target := 269, numerator := 29127556466339971678076928 }, { target := 270, numerator := 466040903461439546849230848 }, { target := 271, numerator := 33982149210729966957756416 }, { target := 272, numerator := 883535879478979140901666816 }, { target := 273, numerator := 883535879478979140901666816 }, { target := 274, numerator := 466040903461439546849230848 }, { target := 275, numerator := 10903415303899929398160130048 }, { target := 276, numerator := 873826693990199150342307840 }, { target := 277, numerator := 407785790528759603493076992 }, { target := 278, numerator := 883535879478979140901666816 }, { target := 279, numerator := 33982149210729966957756416 }, { target := 280, numerator := 873826693990199150342307840 }, { target := 281, numerator := 33982149210729966957756416 }, { target := 282, numerator := 883535879478979140901666816 }, { target := 283, numerator := 883535879478979140901666816 }, { target := 284, numerator := 29127556466339971678076928 }, { target := 406, numerator := 1353892243036166226396976250880 }, { target := 409, numerator := 4647675341312049174917073076224 }, { target := 411, numerator := 1353892243036166226396976250880 }, { target := 416, numerator := 7212090037113943642348841861120 }, { target := 418, numerator := 7212090037113943642348841861120 }, { target := 420, numerator := 1879034761468565192703630901248 }, { target := 498, numerator := 68785966577646837834469867520 }, { target := 500, numerator := 68785966577646837834469867520 }, { target := 502, numerator := 22441138873778909541423906816 }]

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
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot10.Left0.expected,
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
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 870426590122533005788446720 }, { target := 1, numerator := 676998458984192337835458560 }, { target := 2, numerator := 773712524553362671811952640 }, { target := 3, numerator := 909112216350201139379044352 }, { target := 4, numerator := 10735261278177907071390842880 }, { target := 5, numerator := 24139830766064915360532922368 }, { target := 6, numerator := 676998458984192337835458560 }, { target := 7, numerator := 10735261278177907071390842880 }, { target := 8, numerator := 773712524553362671811952640 }, { target := 9, numerator := 754369711439528605016653824 }, { target := 10, numerator := 754369711439528605016653824 }, { target := 11, numerator := 754369711439528605016653824 }, { target := 12, numerator := 24139830766064915360532922368 }, { target := 13, numerator := 754369711439528605016653824 }, { target := 14, numerator := 870426590122533005788446720 }, { target := 15, numerator := 909112216350201139379044352 }, { target := 16, numerator := 683036954691857462706831360 }, { target := 17, numerator := 109044932574532517712384491520 }, { target := 19, numerator := 1088104445227774524969524920320 }, { target := 27, numerator := 109044932574532517712384491520 }, { target := 34, numerator := 682959018024275096497029120 }, { target := 35, numerator := 190463837821363976749763788800 }, { target := 37, numerator := 7156215674671952188136855961600 }, { target := 40, numerator := 7155674434940792874292425523200 }, { target := 47, numerator := 191005077552523290594194227200 }, { target := 86, numerator := 1725163146198284008795995635712 }, { target := 89, numerator := 5847837149214486438930381012992 }, { target := 91, numerator := 1725163146198284008795995635712 }, { target := 122, numerator := 11797175106814321320949448704 }, { target := 124, numerator := 11797175106814321320949448704 }, { target := 126, numerator := 682728100551838368836616192 }, { target := 127, numerator := 108995624878012728215542431744 }, { target := 129, numerator := 1087612428565464666796776751104 }, { target := 137, numerator := 108995624878012728215542431744 }, { target := 144, numerator := 682650199125486036754366464 }, { target := 145, numerator := 651208765972096099108949852160 }, { target := 147, numerator := 24467586245448258853870365573120 }, { target := 150, numerator := 24465735710136910680328230666240 }, { target := 157, numerator := 653059301283444272651084759040 }, { target := 161, numerator := 62520483449249095073040489775104 }, { target := 164, numerator := 211927553928483042849980483108864 }, { target := 166, numerator := 62520483449249095073040489775104 }, { target := 197, numerator := 1742381026362734759371461361664 }, { target := 199, numerator := 1742381026362734759371461361664 }, { target := 215, numerator := 2793355332481121058224603136 }, { target := 216, numerator := 190463776301241681447506411520 }, { target := 218, numerator := 7156213363202916841442393456640 }, { target := 221, numerator := 7155672123646578820883184353280 }, { target := 228, numerator := 191005015857579702006715514880 }, { target := 232, numerator := 62520506425282757194591198248960 }, { target := 235, numerator := 211927631811031998897585504911360 }, { target := 237, numerator := 62520506425282757194591198248960 }, { target := 242, numerator := 18160546044712198170449448796160 }, { target := 244, numerator := 18160546044712198170449448796160 }, { target := 260, numerator := 234891132210311891722407247872 }, { target := 406, numerator := 1725140170164621887245287161856 }, { target := 409, numerator := 5847759266665530391325359210496 }, { target := 411, numerator := 1725140170164621887245287161856 }, { target := 416, numerator := 1742381026362734759371461361664 }, { target := 418, numerator := 1742381026362734759371461361664 }, { target := 420, numerator := 234891075541914097286664683520 }, { target := 498, numerator := 11797175106814321320949448704 }, { target := 500, numerator := 11797175106814321320949448704 }, { target := 502, numerator := 2793412000878915493967167488 }]

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
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
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
    Slot17.Left10.expected,
    Slot17.Left11.expected,
    Slot17.Left12.expected,
    Slot17.Left13.expected,
    Slot17.Left14.expected,
    Slot17.Left15.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left3.expected,
    Slot18.Left11.expected,
    Slot18.Left18.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot19.Left5.expected,
    Slot19.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 2793355332481121058224603136 }, { target := 1, numerator := 234891132210311891722407247872 }, { target := 6, numerator := 234891075541914097286664683520 }, { target := 14, numerator := 2793412000878915493967167488 }, { target := 16, numerator := 11559937581814398954349002752 }, { target := 17, numerator := 1707342285430394572254302175232 }, { target := 19, numerator := 17795343107798424532652476334080 }, { target := 27, numerator := 1707342285430394572254302175232 }, { target := 34, numerator := 11559937581814398954349002752 }, { target := 35, numerator := 1728715707304744266450534924288 }, { target := 37, numerator := 62649229439649104649898369744896 }, { target := 40, numerator := 62649252462996415772500206551040 }, { target := 47, numerator := 1728692683957433143848698118144 }, { target := 86, numerator := 192169484130212012362448240640 }, { target := 89, numerator := 657040486264383526862164328448 }, { target := 91, numerator := 192169422059163248744051245056 }, { target := 122, numerator := 662338865155740569897533440 }, { target := 124, numerator := 662039370232085690993082368 }, { target := 126, numerator := 11559937581814398954349002752 }, { target := 127, numerator := 1707342285430394572254302175232 }, { target := 129, numerator := 17795343107798424532652476334080 }, { target := 137, numerator := 1707342285430394572254302175232 }, { target := 144, numerator := 11559937581814398954349002752 }, { target := 145, numerator := 5859879371921941050061915947008 }, { target := 147, numerator := 212363968065391027608166005211136 }, { target := 150, numerator := 212364046108320475728629611888640 }, { target := 157, numerator := 5859801328992492929598309269504 }, { target := 161, numerator := 7220301188176477133105245716480 }, { target := 164, numerator := 24686698958094064157039353921536 }, { target := 166, numerator := 7220298856007719081813519368192 }, { target := 197, numerator := 105740540678334562630191022080 }, { target := 199, numerator := 105692727154436584936283570176 }, { target := 215, numerator := 870426590122533005788446720 }, { target := 216, numerator := 1728715707304744266450534924288 }, { target := 218, numerator := 62649229439649104649898369744896 }, { target := 221, numerator := 62649252462996415772500206551040 }, { target := 228, numerator := 1728692683957433143848698118144 }, { target := 232, numerator := 7219755101522352213465193512960 }, { target := 235, numerator := 24684831850824703910301319299072 }, { target := 237, numerator := 7219752769529981019279153168384 }, { target := 242, numerator := 1055131583251175296940145377280 }, { target := 244, numerator := 1054654476184693010227177455616 }, { target := 260, numerator := 676998458984192337835458560 }, { target := 265, numerator := 773712524553362671811952640 }, { target := 355, numerator := 909112216350201139379044352 }, { target := 400, numerator := 10735261278177907071390842880 }, { target := 405, numerator := 24139830766064915360532922368 }, { target := 406, numerator := 192715570784336932002500444160 }, { target := 409, numerator := 658907593533743773600198950912 }, { target := 411, numerator := 192715508536901311278417444864 }, { target := 416, numerator := 105740540678334562630191022080 }, { target := 418, numerator := 105692727154436584936283570176 }, { target := 420, numerator := 676998458984192337835458560 }, { target := 425, numerator := 10735261278177907071390842880 }, { target := 426, numerator := 773712524553362671811952640 }, { target := 471, numerator := 754369711439528605016653824 }, { target := 476, numerator := 754369711439528605016653824 }, { target := 491, numerator := 754369711439528605016653824 }, { target := 496, numerator := 24139830766064915360532922368 }, { target := 497, numerator := 754369711439528605016653824 }, { target := 498, numerator := 662263290205357669330452480 }, { target := 500, numerator := 661963829455016762913325056 }, { target := 502, numerator := 870426590122533005788446720 }, { target := 503, numerator := 909112216350201139379044352 }]

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
  [{ target := 0, numerator := 22909356788188951994716651520 }, { target := 1, numerator := 1918180624811287319047110131712 }, { target := 6, numerator := 1918181318999160300884956545024 }, { target := 14, numerator := 22908662600315970156870238208 }, { target := 16, numerator := 68904054073917476182683549696 }, { target := 17, numerator := 7224465796562239152601373343744 }, { target := 19, numerator := 77872520441872483205221711872000 }, { target := 27, numerator := 7224471307563924661477337726976 }, { target := 34, numerator := 68904054073917476182683549696 }, { target := 35, numerator := 1353701303956597891678685102080 }, { target := 37, numerator := 47376170578049147090023733002240 }, { target := 40, numerator := 47376193814265544880858364641280 }, { target := 47, numerator := 1353689685848398996261369282560 }, { target := 122, numerator := 24202128224706931720192000 }, { target := 123, numerator := 24036845397806494137712640 }, { target := 124, numerator := 24202128224706931720192000 }, { target := 125, numerator := 24272963721949976398397440 }, { target := 126, numerator := 68904054073917476182683549696 }, { target := 127, numerator := 7224465796562239152601373343744 }, { target := 129, numerator := 77872520441872483205221711872000 }, { target := 137, numerator := 7224471307563924661477337726976 }, { target := 144, numerator := 68904054073917476182683549696 }, { target := 145, numerator := 4647019880837726283737788841984 }, { target := 147, numerator := 162634109836989862803845521866752 }, { target := 150, numerator := 162634189602857887293532111110144 }, { target := 157, numerator := 4646979997903714038894494220288 }, { target := 197, numerator := 406595754175076452899225600 }, { target := 198, numerator := 403819002683149101513572352 }, { target := 199, numerator := 406595754175076452899225600 }, { target := 200, numerator := 407785790528759603493076992 }, { target := 211, numerator := 880957467379332314614988800 }, { target := 212, numerator := 874941172480156386612740096 }, { target := 213, numerator := 880957467379332314614988800 }, { target := 214, numerator := 883535879478979140901666816 }, { target := 216, numerator := 1353701303956597891678685102080 }, { target := 218, numerator := 47376170578049147090023733002240 }, { target := 221, numerator := 47376193814265544880858364641280 }, { target := 228, numerator := 1353689685848398996261369282560 }, { target := 242, numerator := 29042553869648318064230400 }, { target := 243, numerator := 28844214477367792965255168 }, { target := 244, numerator := 29042553869648318064230400 }, { target := 245, numerator := 29127556466339971678076928 }, { target := 256, numerator := 464680861914373089027686400 }, { target := 257, numerator := 461507431637884687444082688 }, { target := 258, numerator := 464680861914373089027686400 }, { target := 259, numerator := 466040903461439546849230848 }, { target := 261, numerator := 33882979514589704408268800 }, { target := 262, numerator := 33651583556929091792797696 }, { target := 263, numerator := 33882979514589704408268800 }, { target := 264, numerator := 33982149210729966957756416 }, { target := 337, numerator := 880957467379332314614988800 }, { target := 338, numerator := 874941172480156386612740096 }, { target := 339, numerator := 880957467379332314614988800 }, { target := 340, numerator := 883535879478979140901666816 }, { target := 351, numerator := 880957467379332314614988800 }, { target := 352, numerator := 874941172480156386612740096 }, { target := 353, numerator := 880957467379332314614988800 }, { target := 354, numerator := 883535879478979140901666816 }, { target := 382, numerator := 464680861914373089027686400 }, { target := 383, numerator := 461507431637884687444082688 }, { target := 384, numerator := 464680861914373089027686400 }, { target := 385, numerator := 466040903461439546849230848 }]

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
    Slot23.Left9.expected,
    Slot23.Left10.expected,
    Slot23.Left11.expected,
    Slot23.Left12.expected,
    Slot23.Left13.expected,
    Slot23.Left14.expected,
    Slot23.Left15.expected,
    Slot23.Left16.expected,
    Slot23.Left17.expected,
    Slot23.Left18.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 213426080367952529473929216 }, { target := 87, numerator := 5232381325149803948393103360 }, { target := 88, numerator := 213426080367952529473929216 }, { target := 89, numerator := 4385561715947927783061061632 }, { target := 90, numerator := 4309829880978654304860635136 }, { target := 91, numerator := 213426080367952529473929216 }, { target := 92, numerator := 4316714593248588257424310272 }, { target := 93, numerator := 3869208295702881340785426432 }, { target := 94, numerator := 5232381325149803948393103360 }, { target := 95, numerator := 213426080367952529473929216 }, { target := 161, numerator := 7881541207771604424358625280 }, { target := 162, numerator := 193224881222787721371372748800 }, { target := 163, numerator := 7881541207771604424358625280 }, { target := 164, numerator := 161952959656468129623111106560 }, { target := 165, numerator := 159156283744033044182209658880 }, { target := 166, numerator := 7881541207771604424358625280 }, { target := 167, numerator := 159410527008799870131382517760 }, { target := 168, numerator := 142884714798956183435146690560 }, { target := 169, numerator := 193224881222787721371372748800 }, { target := 170, numerator := 7881541207771604424358625280 }, { target := 396, numerator := 10871595998538353728710246400 }, { target := 397, numerator := 10797350952694677166660517888 }, { target := 398, numerator := 10871595998538353728710246400 }, { target := 399, numerator := 10903415303899929398160130048 }, { target := 401, numerator := 871276616089449541926912000 }, { target := 402, numerator := 865326434321033788957655040 }, { target := 403, numerator := 871276616089449541926912000 }, { target := 404, numerator := 873826693990199150342307840 }, { target := 416, numerator := 406595754175076452899225600 }, { target := 417, numerator := 403819002683149101513572352 }, { target := 418, numerator := 406595754175076452899225600 }, { target := 419, numerator := 407785790528759603493076992 }, { target := 421, numerator := 880957467379332314614988800 }, { target := 422, numerator := 874941172480156386612740096 }, { target := 423, numerator := 880957467379332314614988800 }, { target := 424, numerator := 883535879478979140901666816 }, { target := 453, numerator := 33882979514589704408268800 }, { target := 454, numerator := 33651583556929091792797696 }, { target := 455, numerator := 33882979514589704408268800 }, { target := 456, numerator := 33982149210729966957756416 }, { target := 467, numerator := 871276616089449541926912000 }, { target := 468, numerator := 865326434321033788957655040 }, { target := 469, numerator := 871276616089449541926912000 }, { target := 470, numerator := 873826693990199150342307840 }, { target := 472, numerator := 33882979514589704408268800 }, { target := 473, numerator := 33651583556929091792797696 }, { target := 474, numerator := 33882979514589704408268800 }, { target := 475, numerator := 33982149210729966957756416 }, { target := 487, numerator := 880957467379332314614988800 }, { target := 488, numerator := 874941172480156386612740096 }, { target := 489, numerator := 880957467379332314614988800 }, { target := 490, numerator := 883535879478979140901666816 }, { target := 492, numerator := 880957467379332314614988800 }, { target := 493, numerator := 874941172480156386612740096 }, { target := 494, numerator := 880957467379332314614988800 }, { target := 495, numerator := 883535879478979140901666816 }, { target := 498, numerator := 29042553869648318064230400 }, { target := 499, numerator := 28844214477367792965255168 }, { target := 500, numerator := 29042553869648318064230400 }, { target := 501, numerator := 29127556466339971678076928 }]

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
    Slot24.Left5.expected,
    Slot24.Left12.expected,
    Slot25.Left0.expected,
    Slot25.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 68845017224864440575949012992 }, { target := 36, numerator := 67410746032679764730616741888 }, { target := 37, numerator := 53068034110833006277294030848 }, { target := 38, numerator := 1668057396510778008121431293952 }, { target := 39, numerator := 53068034110833006277294030848 }, { target := 40, numerator := 53068034110833006277294030848 }, { target := 41, numerator := 54502305303017682122626301952 }, { target := 42, numerator := 54502305303017682122626301952 }, { target := 43, numerator := 922236376574746568548650319872 }, { target := 44, numerator := 50199491726463654586629488640 }, { target := 45, numerator := 1668057396510778008121431293952 }, { target := 46, numerator := 922236376574746568548650319872 }, { target := 47, numerator := 68845017224864440575949012992 }, { target := 48, numerator := 53068034110833006277294030848 }, { target := 49, numerator := 50199491726463654586629488640 }, { target := 50, numerator := 67410746032679764730616741888 }, { target := 145, numerator := 250404167866237835028977418240 }, { target := 146, numerator := 245187414369024546799207055360 }, { target := 147, numerator := 193019879396891664501503426560 }, { target := 148, numerator := 6067084317259054211222932029440 }, { target := 149, numerator := 193019879396891664501503426560 }, { target := 150, numerator := 193019879396891664501503426560 }, { target := 151, numerator := 198236632894104952731273789440 }, { target := 152, numerator := 198236632894104952731273789440 }, { target := 153, numerator := 3354372498708144331742343331840 }, { target := 154, numerator := 182586372402465088041962700800 }, { target := 155, numerator := 6067084317259054211222932029440 }, { target := 156, numerator := 3354372498708144331742343331840 }, { target := 157, numerator := 250404167866237835028977418240 }, { target := 158, numerator := 193019879396891664501503426560 }, { target := 159, numerator := 182586372402465088041962700800 }, { target := 160, numerator := 245187414369024546799207055360 }, { target := 232, numerator := 7881539277781005712496787456 }, { target := 233, numerator := 193224833906889172306372853760 }, { target := 234, numerator := 7881539277781005712496787456 }, { target := 235, numerator := 161952919998274214156788826112 }, { target := 236, numerator := 159156244770674502452354482176 }, { target := 237, numerator := 7881539277781005712496787456 }, { target := 238, numerator := 159410487973183567152757604352 }, { target := 239, numerator := 142884679810094361626554662912 }, { target := 240, numerator := 193224833906889172306372853760 }, { target := 241, numerator := 7881539277781005712496787456 }, { target := 406, numerator := 213428010358551241335767040 }, { target := 407, numerator := 5232428641048353013392998400 }, { target := 408, numerator := 213428010358551241335767040 }, { target := 409, numerator := 4385601374141843249383342080 }, { target := 410, numerator := 4309868854337196034715811840 }, { target := 411, numerator := 213428010358551241335767040 }, { target := 412, numerator := 4316753628864891236049223680 }, { target := 413, numerator := 3869243284564703149377454080 }, { target := 414, numerator := 5232428641048353013392998400 }, { target := 415, numerator := 213428010358551241335767040 }]

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
    Slot25.Left5.expected,
    Slot26.Left0.expected,
    Slot26.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 53734347641494796748623708160 }, { target := 17, numerator := 1432915937106527913296632217600 }, { target := 18, numerator := 1370225864858117317089904558080 }, { target := 19, numerator := 44778623034578997290519756800 }, { target := 20, numerator := 1406048763285780514922320363520 }, { target := 21, numerator := 44778623034578997290519756800 }, { target := 22, numerator := 1370225864858117317089904558080 }, { target := 23, numerator := 779148040801674552855043768320 }, { target := 24, numerator := 1406048763285780514922320363520 }, { target := 25, numerator := 21950481011550624471812784783360 }, { target := 26, numerator := 859749562263916747977979330560 }, { target := 27, numerator := 1432915937106527913296632217600 }, { target := 28, numerator := 1370225864858117317089904558080 }, { target := 29, numerator := 44778623034578997290519756800 }, { target := 30, numerator := 859749562263916747977979330560 }, { target := 31, numerator := 44778623034578997290519756800 }, { target := 32, numerator := 1379181589465033116548008509440 }, { target := 33, numerator := 779148040801674552855043768320 }, { target := 34, numerator := 53734347641494796748623708160 }, { target := 126, numerator := 53734322018967278366056513536 }, { target := 127, numerator := 1432915253839127423094840360960 }, { target := 128, numerator := 1370225211483665598334441095168 }, { target := 129, numerator := 44778601682472731971713761280 }, { target := 130, numerator := 1406048092829643783911812104192 }, { target := 131, numerator := 44778601682472731971713761280 }, { target := 132, numerator := 1370225211483665598334441095168 }, { target := 133, numerator := 779147669275025536307819446272 }, { target := 134, numerator := 1406048092829643783911812104192 }, { target := 135, numerator := 21950470544748133212534085779456 }, { target := 136, numerator := 859749152303476453856904216576 }, { target := 137, numerator := 1432915253839127423094840360960 }, { target := 138, numerator := 1370225211483665598334441095168 }, { target := 139, numerator := 44778601682472731971713761280 }, { target := 140, numerator := 859749152303476453856904216576 }, { target := 141, numerator := 44778601682472731971713761280 }, { target := 142, numerator := 1379180931820160144728783847424 }, { target := 143, numerator := 779147669275025536307819446272 }, { target := 144, numerator := 53734322018967278366056513536 }, { target := 216, numerator := 68845017224864440575949012992 }, { target := 217, numerator := 67410746032679764730616741888 }, { target := 218, numerator := 53068034110833006277294030848 }, { target := 219, numerator := 1668057396510778008121431293952 }, { target := 220, numerator := 53068034110833006277294030848 }, { target := 221, numerator := 53068034110833006277294030848 }, { target := 222, numerator := 54502305303017682122626301952 }, { target := 223, numerator := 54502305303017682122626301952 }, { target := 224, numerator := 922236376574746568548650319872 }, { target := 225, numerator := 50199491726463654586629488640 }, { target := 226, numerator := 1668057396510778008121431293952 }, { target := 227, numerator := 922236376574746568548650319872 }, { target := 228, numerator := 68845017224864440575949012992 }, { target := 229, numerator := 53068034110833006277294030848 }, { target := 230, numerator := 50199491726463654586629488640 }, { target := 231, numerator := 67410746032679764730616741888 }]

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
    Slot27.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 44681898292956694297140264960 }, { target := 1, numerator := 45958523958469742705629986816 }, { target := 2, numerator := 44681898292956694297140264960 }, { target := 3, numerator := 39575395630904500663181377536 }, { target := 4, numerator := 1852383840659433240718586413056 }, { target := 5, numerator := 504267137877654121353440133120 }, { target := 6, numerator := 45958523958469742705629986816 }, { target := 7, numerator := 1852383840659433240718586413056 }, { target := 8, numerator := 44681898292956694297140264960 }, { target := 9, numerator := 44681898292956694297140264960 }, { target := 10, numerator := 38298769965391452254691655680 }, { target := 11, numerator := 44681898292956694297140264960 }, { target := 12, numerator := 504267137877654121353440133120 }, { target := 13, numerator := 38298769965391452254691655680 }, { target := 14, numerator := 44681898292956694297140264960 }, { target := 15, numerator := 39575395630904500663181377536 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent3
