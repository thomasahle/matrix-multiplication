import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk22Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 90; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22.Parent0

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
    Slot0.Left6.expected,
    Slot0.Left14.expected,
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
    Slot2.Left3.expected,
    Slot2.Left11.expected,
    Slot2.Left18.expected,
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
  [{ target := 122, numerator := 522612972358322378135044096 }, { target := 123, numerator := 43730995199268433053089792 }, { target := 124, numerator := 522612972358322378135044096 }, { target := 125, numerator := 43730995199268433053089792 }, { target := 197, numerator := 14357030113964389125473697792 }, { target := 198, numerator := 6981530633394115651456466944 }, { target := 199, numerator := 14357030113964389125473697792 }, { target := 200, numerator := 6981530633394115651456466944 }, { target := 211, numerator := 17601959933589000783721922560 }, { target := 213, numerator := 17601959933589000783721922560 }, { target := 215, numerator := 1335985812202719848825880576 }, { target := 242, numerator := 62776736218825446342348767232 }, { target := 243, numerator := 69665176889331344859467874304 }, { target := 244, numerator := 62776736218825446342348767232 }, { target := 245, numerator := 69665176889331344859467874304 }, { target := 256, numerator := 9284550294640352061743431680 }, { target := 258, numerator := 9284550294640352061743431680 }, { target := 260, numerator := 39825520494036174291569999872 }, { target := 261, numerator := 676998458984192337835458560 }, { target := 263, numerator := 676998458984192337835458560 }, { target := 265, numerator := 773712524553362671811952640 }, { target := 337, numerator := 17601959933589000783721922560 }, { target := 339, numerator := 17601959933589000783721922560 }, { target := 351, numerator := 17601959933589000783721922560 }, { target := 353, numerator := 17601959933589000783721922560 }, { target := 355, numerator := 909112216350201139379044352 }, { target := 382, numerator := 9284550294640352061743431680 }, { target := 384, numerator := 9284550294640352061743431680 }, { target := 396, numerator := 217219791268356570111205703680 }, { target := 398, numerator := 217219791268356570111205703680 }, { target := 400, numerator := 10735261278177907071390842880 }, { target := 401, numerator := 17408531802450660115768934400 }, { target := 403, numerator := 17408531802450660115768934400 }, { target := 405, numerator := 24139830766064915360532922368 }, { target := 416, numerator := 14357030113964389125473697792 }, { target := 417, numerator := 6981530633394115651456466944 }, { target := 418, numerator := 14357030113964389125473697792 }, { target := 419, numerator := 6981530633394115651456466944 }, { target := 420, numerator := 39825511049303208552279572480 }, { target := 425, numerator := 10735261278177907071390842880 }, { target := 426, numerator := 773712524553362671811952640 }, { target := 471, numerator := 754369711439528605016653824 }, { target := 476, numerator := 754369711439528605016653824 }, { target := 491, numerator := 754369711439528605016653824 }, { target := 496, numerator := 24139830766064915360532922368 }, { target := 497, numerator := 754369711439528605016653824 }, { target := 498, numerator := 39038189623776907395858432 }, { target := 499, numerator := 43726005354996494619377664 }, { target := 500, numerator := 39038189623776907395858432 }, { target := 501, numerator := 43726005354996494619377664 }, { target := 502, numerator := 1335995256935685588116307968 }, { target := 503, numerator := 909112216350201139379044352 }]

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
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot3.Left16.expected,
    Slot3.Left17.expected,
    Slot3.Left18.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left5.expected,
    Slot4.Left12.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 5652091865811060501851930624 }, { target := 87, numerator := 3812600661483424397484097536 }, { target := 88, numerator := 214191048397945190869893120 }, { target := 89, numerator := 22845089401747304192040501248 }, { target := 90, numerator := 5790298008357784993182777344 }, { target := 91, numerator := 5652090058030141278315872256 }, { target := 92, numerator := 5790298008357784993182777344 }, { target := 93, numerator := 5790298008357784993182777344 }, { target := 94, numerator := 3812600661483424397484097536 }, { target := 95, numerator := 214191048397945190869893120 }, { target := 112, numerator := 6457507220678074431791169536 }, { target := 115, numerator := 23101305723342725087213125632 }, { target := 117, numerator := 6457505073938232853842100224 }, { target := 161, numerator := 12837888075192998613733081088 }, { target := 162, numerator := 140794270177540058964169850880 }, { target := 163, numerator := 7909790459412362863155609600 }, { target := 164, numerator := 142868292782194140794591379456 }, { target := 165, numerator := 213828002086114209400639979520 }, { target := 166, numerator := 12837886436891540567403528192 }, { target := 167, numerator := 213828002086114209400639979520 }, { target := 168, numerator := 213828002086114209400639979520 }, { target := 169, numerator := 140794270177540058964169850880 }, { target := 170, numerator := 7909790459412362863155609600 }, { target := 232, numerator := 7909788522504235123652689920 }, { target := 233, numerator := 140794235700575385201017880576 }, { target := 234, numerator := 7909788522504235123652689920 }, { target := 235, numerator := 125238318272983722791167590400 }, { target := 236, numerator := 213827949725031156176077717504 }, { target := 237, numerator := 7909788522504235123652689920 }, { target := 238, numerator := 213827949725031156176077717504 }, { target := 239, numerator := 213827949725031156176077717504 }, { target := 240, numerator := 140794235700575385201017880576 }, { target := 241, numerator := 7909788522504235123652689920 }, { target := 406, numerator := 214192985306072930372812800 }, { target := 407, numerator := 3812635138448098160636067840 }, { target := 408, numerator := 214192985306072930372812800 }, { target := 409, numerator := 3391388934012821397569536000 }, { target := 410, numerator := 5790350369440838217745039360 }, { target := 411, numerator := 214192985306072930372812800 }, { target := 412, numerator := 5790350369440838217745039360 }, { target := 413, numerator := 5790350369440838217745039360 }, { target := 414, numerator := 3812635138448098160636067840 }, { target := 415, numerator := 214192985306072930372812800 }, { target := 421, numerator := 17601959933589000783721922560 }, { target := 423, numerator := 17601959933589000783721922560 }, { target := 453, numerator := 676998458984192337835458560 }, { target := 455, numerator := 676998458984192337835458560 }, { target := 467, numerator := 17408531802450660115768934400 }, { target := 469, numerator := 17408531802450660115768934400 }, { target := 472, numerator := 676998458984192337835458560 }, { target := 474, numerator := 676998458984192337835458560 }, { target := 487, numerator := 17601959933589000783721922560 }, { target := 489, numerator := 17601959933589000783721922560 }, { target := 492, numerator := 17601959933589000783721922560 }, { target := 494, numerator := 17601959933589000783721922560 }, { target := 498, numerator := 580284393415022003858964480 }, { target := 500, numerator := 580284393415022003858964480 }]

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
    Slot6.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 5659855952817732262450692096 }, { target := 36, numerator := 6721078943971057061660196864 }, { target := 37, numerator := 5129244457241069862845939712 }, { target := 38, numerator := 52884279059140685827273654272 }, { target := 39, numerator := 6367337946919948795257028608 }, { target := 40, numerator := 5129244457241069862845939712 }, { target := 41, numerator := 6367337946919948795257028608 }, { target := 42, numerator := 6367337946919948795257028608 }, { target := 43, numerator := 272734308726404473396842725376 }, { target := 44, numerator := 6367337946919948795257028608 }, { target := 45, numerator := 52884279059140685827273654272 }, { target := 46, numerator := 272734308726404473396842725376 }, { target := 47, numerator := 5659855952817732262450692096 }, { target := 48, numerator := 6367337946919948795257028608 }, { target := 49, numerator := 6367337946919948795257028608 }, { target := 50, numerator := 6721078943971057061660196864 }, { target := 187, numerator := 50810385762703796186988412928 }, { target := 190, numerator := 181770800296828284238861172736 }, { target := 192, numerator := 50810368871250832192073367552 }, { target := 201, numerator := 6117638419589754724854792192 }, { target := 204, numerator := 21885447527377318503675592704 }, { target := 206, numerator := 6117636385836220598376726528 }, { target := 232, numerator := 4928097615780635750577471488 }, { target := 235, numerator := 17629943841498395461294227456 }, { target := 237, numerator := 4928095977479177704247918592 }, { target := 246, numerator := 6117638419589754724854792192 }, { target := 249, numerator := 21885447527377318503675592704 }, { target := 251, numerator := 6117636385836220598376726528 }, { target := 301, numerator := 6117638419589754724854792192 }, { target := 304, numerator := 21885447527377318503675592704 }, { target := 306, numerator := 6117636385836220598376726528 }, { target := 327, numerator := 262038845639094494047946932224 }, { target := 330, numerator := 937426669089328475907437887488 }, { target := 332, numerator := 262038758526651448963803119616 }, { target := 341, numerator := 6117638419589754724854792192 }, { target := 344, numerator := 21885447527377318503675592704 }, { target := 346, numerator := 6117636385836220598376726528 }, { target := 372, numerator := 50810385762703796186988412928 }, { target := 375, numerator := 181770800296828284238861172736 }, { target := 377, numerator := 50810368871250832192073367552 }, { target := 386, numerator := 262038845639094494047946932224 }, { target := 389, numerator := 937426669089328475907437887488 }, { target := 391, numerator := 262038758526651448963803119616 }, { target := 406, numerator := 5437900817413115310982037504 }, { target := 409, numerator := 19453731135446505336600526848 }, { target := 411, numerator := 5437899009632196087445979136 }, { target := 443, numerator := 6117638419589754724854792192 }, { target := 446, numerator := 21885447527377318503675592704 }, { target := 448, numerator := 6117636385836220598376726528 }, { target := 457, numerator := 6117638419589754724854792192 }, { target := 460, numerator := 21885447527377318503675592704 }, { target := 462, numerator := 6117636385836220598376726528 }, { target := 477, numerator := 6457507220678074431791169536 }, { target := 480, numerator := 23101305723342725087213125632 }, { target := 482, numerator := 6457505073938232853842100224 }]

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
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left2.expected,
    Slot7.Left3.expected,
    Slot7.Left4.expected,
    Slot7.Left5.expected,
    Slot7.Left6.expected,
    Slot7.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 206541368098018576910254080 }, { target := 37, numerator := 7627297943004778475185766400 }, { target := 40, numerator := 7627296075271941012093665280 }, { target := 47, numerator := 206543235830856040002355200 }, { target := 70, numerator := 3676436352144730669002522624 }, { target := 72, numerator := 135765903385485056858306641920 }, { target := 75, numerator := 135765870139840550015267241984 }, { target := 82, numerator := 3676469597789237512041922560 }, { target := 96, numerator := 206541368098018576910254080 }, { target := 98, numerator := 7627297943004778475185766400 }, { target := 101, numerator := 7627296075271941012093665280 }, { target := 108, numerator := 206543235830856040002355200 }, { target := 145, numerator := 23517999305928255471146237952 }, { target := 146, numerator := 24044216161030183254038151168 }, { target := 147, numerator := 139115084150291676235189714944 }, { target := 148, numerator := 189190016635474336656773873664 }, { target := 149, numerator := 22778731099923331503825616896 }, { target := 150, numerator := 139115054577855083069564780544 }, { target := 151, numerator := 22778731099923331503825616896 }, { target := 152, numerator := 22778731099923331503825616896 }, { target := 153, numerator := 975688982113382699413863923712 }, { target := 154, numerator := 22778731099923331503825616896 }, { target := 155, numerator := 189190016635474336656773873664 }, { target := 156, numerator := 975688982113382699413863923712 }, { target := 157, numerator := 23518028878364848636771172352 }, { target := 158, numerator := 22778731099923331503825616896 }, { target := 159, numerator := 22778731099923331503825616896 }, { target := 160, numerator := 24044216161030183254038151168 }, { target := 171, numerator := 5583501650916435529140535296 }, { target := 173, numerator := 206191287725895844779188551680 }, { target := 176, numerator := 206191237234851472026932084736 }, { target := 183, numerator := 5583552141960808281397002240 }, { target := 216, numerator := 5866395439347855320986681344 }, { target := 217, numerator := 6721076709609181133590757376 }, { target := 218, numerator := 12756540695074943024505028608 }, { target := 219, numerator := 52884261478240662077464117248 }, { target := 220, numerator := 6367335830156066337085980672 }, { target := 221, numerator := 12756538827342105561412927488 }, { target := 222, numerator := 6367335830156066337085980672 }, { target := 223, numerator := 6367335830156066337085980672 }, { target := 224, numerator := 272734218058351508105182838784 }, { target := 225, numerator := 6367335830156066337085980672 }, { target := 226, numerator := 52884261478240662077464117248 }, { target := 227, numerator := 272734218058351508105182838784 }, { target := 228, numerator := 5866397307080692784078782464 }, { target := 229, numerator := 6367335830156066337085980672 }, { target := 230, numerator := 6367335830156066337085980672 }, { target := 231, numerator := 6721076709609181133590757376 }, { target := 285, numerator := 5583501650916435529140535296 }, { target := 287, numerator := 206191287725895844779188551680 }, { target := 290, numerator := 206191237234851472026932084736 }, { target := 297, numerator := 5583552141960808281397002240 }, { target := 311, numerator := 5583501650916435529140535296 }, { target := 313, numerator := 206191287725895844779188551680 }, { target := 316, numerator := 206191237234851472026932084736 }, { target := 323, numerator := 5583552141960808281397002240 }]

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
    Slot7.Left8.expected,
    Slot7.Left9.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 522612972358322378135044096 }, { target := 17, numerator := 14357030113964389125473697792 }, { target := 18, numerator := 17601959933589000783721922560 }, { target := 19, numerator := 62776736218825446342348767232 }, { target := 20, numerator := 9284550294640352061743431680 }, { target := 21, numerator := 676998458984192337835458560 }, { target := 22, numerator := 17601959933589000783721922560 }, { target := 23, numerator := 17601959933589000783721922560 }, { target := 24, numerator := 9284550294640352061743431680 }, { target := 25, numerator := 217219791268356570111205703680 }, { target := 26, numerator := 17408531802450660115768934400 }, { target := 27, numerator := 14357030113964389125473697792 }, { target := 28, numerator := 17601959933589000783721922560 }, { target := 29, numerator := 676998458984192337835458560 }, { target := 30, numerator := 17408531802450660115768934400 }, { target := 31, numerator := 676998458984192337835458560 }, { target := 32, numerator := 17601959933589000783721922560 }, { target := 33, numerator := 17601959933589000783721922560 }, { target := 34, numerator := 619322583038798911254822912 }, { target := 51, numerator := 43730995199268433053089792 }, { target := 52, numerator := 6981530633394115651456466944 }, { target := 54, numerator := 69665176889331344859467874304 }, { target := 62, numerator := 6981530633394115651456466944 }, { target := 69, numerator := 43726005354996494619377664 }, { target := 126, numerator := 522612972358322378135044096 }, { target := 127, numerator := 14357030113964389125473697792 }, { target := 128, numerator := 17601959933589000783721922560 }, { target := 129, numerator := 62776736218825446342348767232 }, { target := 130, numerator := 9284550294640352061743431680 }, { target := 131, numerator := 676998458984192337835458560 }, { target := 132, numerator := 17601959933589000783721922560 }, { target := 133, numerator := 17601959933589000783721922560 }, { target := 134, numerator := 9284550294640352061743431680 }, { target := 135, numerator := 217219791268356570111205703680 }, { target := 136, numerator := 17408531802450660115768934400 }, { target := 137, numerator := 14357030113964389125473697792 }, { target := 138, numerator := 17601959933589000783721922560 }, { target := 139, numerator := 676998458984192337835458560 }, { target := 140, numerator := 17408531802450660115768934400 }, { target := 141, numerator := 676998458984192337835458560 }, { target := 142, numerator := 17601959933589000783721922560 }, { target := 143, numerator := 17601959933589000783721922560 }, { target := 144, numerator := 619322583038798911254822912 }, { target := 356, numerator := 3676436352144730669002522624 }, { target := 358, numerator := 135765903385485056858306641920 }, { target := 361, numerator := 135765870139840550015267241984 }, { target := 368, numerator := 3676469597789237512041922560 }, { target := 427, numerator := 206541368098018576910254080 }, { target := 429, numerator := 7627297943004778475185766400 }, { target := 432, numerator := 7627296075271941012093665280 }, { target := 439, numerator := 206543235830856040002355200 }]

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
    Slot9.Left3.expected,
    Slot10.Left0.expected,
    Slot11.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1335985812202719848825880576 }, { target := 1, numerator := 39825520494036174291569999872 }, { target := 2, numerator := 773712524553362671811952640 }, { target := 3, numerator := 909112216350201139379044352 }, { target := 4, numerator := 10735261278177907071390842880 }, { target := 5, numerator := 24139830766064915360532922368 }, { target := 6, numerator := 39825511049303208552279572480 }, { target := 7, numerator := 10735261278177907071390842880 }, { target := 8, numerator := 773712524553362671811952640 }, { target := 9, numerator := 754369711439528605016653824 }, { target := 10, numerator := 754369711439528605016653824 }, { target := 11, numerator := 754369711439528605016653824 }, { target := 12, numerator := 24139830766064915360532922368 }, { target := 13, numerator := 754369711439528605016653824 }, { target := 14, numerator := 1335995256935685588116307968 }, { target := 15, numerator := 909112216350201139379044352 }, { target := 266, numerator := 43730995199268433053089792 }, { target := 267, numerator := 6981530633394115651456466944 }, { target := 269, numerator := 69665176889331344859467874304 }, { target := 277, numerator := 6981530633394115651456466944 }, { target := 284, numerator := 43726005354996494619377664 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22.Parent0
