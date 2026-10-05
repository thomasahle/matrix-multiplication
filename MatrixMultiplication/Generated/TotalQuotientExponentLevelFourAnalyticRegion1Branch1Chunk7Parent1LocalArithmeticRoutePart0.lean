import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk7Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 31; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
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
    Slot3.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 55638184031407211525701632 }, { target := 17, numerator := 6576076142381391461096620032 }, { target := 19, numerator := 62405651738264345935978954752 }, { target := 27, numerator := 6576080652610317483081990144 }, { target := 34, numerator := 55638184031407211525701632 }, { target := 35, numerator := 480016470366331156215889920 }, { target := 37, numerator := 18785425391012399371901730816 }, { target := 40, numerator := 18785425391012399371901730816 }, { target := 47, numerator := 480016470366331156215889920 }, { target := 51, numerator := 60872041833952675186606080 }, { target := 52, numerator := 7194684532053260596496302080 }, { target := 54, numerator := 68276122044931339623208058880 }, { target := 62, numerator := 7194689466557300313801359360 }, { target := 69, numerator := 60872041833952675186606080 }, { target := 70, numerator := 10020343818897162886006702080 }, { target := 72, numerator := 392145755037383836888448630784 }, { target := 75, numerator := 392145755037383836888448630784 }, { target := 82, numerator := 10020343818897162886006702080 }, { target := 86, numerator := 94542007735066072201761390592 }, { target := 89, numerator := 351199998603204092690872401920 }, { target := 91, numerator := 94522106744229154766857437184 }, { target := 96, numerator := 520017842896858752567214080 }, { target := 98, numerator := 20350877506930099319560208384 }, { target := 101, numerator := 20350877506930099319560208384 }, { target := 108, numerator := 520017842896858752567214080 }, { target := 126, numerator := 55638184031407211525701632 }, { target := 127, numerator := 6576076142381391461096620032 }, { target := 129, numerator := 62405651738264345935978954752 }, { target := 137, numerator := 6576080652610317483081990144 }, { target := 144, numerator := 55638184031407211525701632 }, { target := 145, numerator := 10780369896977187216681861120 }, { target := 147, numerator := 421889345239820135893959704576 }, { target := 150, numerator := 421889345239820135893959704576 }, { target := 157, numerator := 10780369896977187216681861120 }, { target := 171, numerator := 16140553816067885127759298560 }, { target := 173, numerator := 631659928772791928880195698688 }, { target := 176, numerator := 631659928772791928880195698688 }, { target := 183, numerator := 16140553816067885127759298560 }, { target := 216, numerator := 500017156631594954391552000 }, { target := 218, numerator := 19568151448971249345730969600 }, { target := 221, numerator := 19568151448971249345730969600 }, { target := 228, numerator := 500017156631594954391552000 }, { target := 266, numerator := 60872041833952675186606080 }, { target := 267, numerator := 7194684532053260596496302080 }, { target := 269, numerator := 68276122044931339623208058880 }, { target := 277, numerator := 7194689466557300313801359360 }, { target := 284, numerator := 60872041833952675186606080 }, { target := 285, numerator := 16140553816067885127759298560 }, { target := 287, numerator := 631659928772791928880195698688 }, { target := 290, numerator := 631659928772791928880195698688 }, { target := 297, numerator := 16140553816067885127759298560 }, { target := 311, numerator := 16820577149086854265731809280 }, { target := 313, numerator := 658272614743392827990389817344 }, { target := 316, numerator := 658272614743392827990389817344 }, { target := 323, numerator := 16820577149086854265731809280 }, { target := 356, numerator := 10020343818897162886006702080 }, { target := 358, numerator := 392145755037383836888448630784 }, { target := 361, numerator := 392145755037383836888448630784 }, { target := 368, numerator := 10020343818897162886006702080 }, { target := 427, numerator := 500017156631594954391552000 }, { target := 429, numerator := 19568151448971249345730969600 }, { target := 432, numerator := 19568151448971249345730969600 }, { target := 439, numerator := 500017156631594954391552000 }]

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
    Slot4.Left7.expected,
    Slot4.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 112, numerator := 106740976475074597647149957120 }, { target := 115, numerator := 396516127455230427231630131200 }, { target := 117, numerator := 106718507614452271510968074240 }, { target := 122, numerator := 34120718265296225573950980096 }, { target := 124, numerator := 34120726400310362079863242752 }, { target := 161, numerator := 91492265550063940840414248960 }, { target := 164, numerator := 339870966390197509055682969600 }, { target := 166, numerator := 91473006526673375580829777920 }, { target := 187, numerator := 1204648163075841887732120944640 }, { target := 190, numerator := 4474967724137600535899825766400 }, { target := 192, numerator := 1204394585934532778480925409280 }, { target := 197, numerator := 494750414846795270822289211392 }, { target := 199, numerator := 494750532804500250158017019904 }, { target := 201, numerator := 106740976475074597647149957120 }, { target := 204, numerator := 396516127455230427231630131200 }, { target := 206, numerator := 106718507614452271510968074240 }, { target := 211, numerator := 875765102142603123064741822464 }, { target := 213, numerator := 875765310941299293383156563968 }, { target := 232, numerator := 91492265550063940840414248960 }, { target := 235, numerator := 339870966390197509055682969600 }, { target := 237, numerator := 91473006526673375580829777920 }, { target := 242, numerator := 28433931887746854644959150080 }, { target := 244, numerator := 28433938666925301733219368960 }, { target := 246, numerator := 106740976475074597647149957120 }, { target := 249, numerator := 396516127455230427231630131200 }, { target := 251, numerator := 106718507614452271510968074240 }, { target := 256, numerator := 545931492244739609183215681536 }, { target := 258, numerator := 545931622404965793277811884032 }, { target := 261, numerator := 28433931887746854644959150080 }, { target := 263, numerator := 28433938666925301733219368960 }, { target := 301, numerator := 106740976475074597647149957120 }, { target := 304, numerator := 396516127455230427231630131200 }, { target := 306, numerator := 106718507614452271510968074240 }, { target := 327, numerator := 4425175910438092605314702508032 }, { target := 330, numerator := 16438425741072552854659866296320 }, { target := 332, numerator := 4424244415673435598926133592064 }, { target := 337, numerator := 870078315765053752135749992448 }, { target := 339, numerator := 870078523207914233036512690176 }, { target := 341, numerator := 109790718660076729008497098752 }, { target := 344, numerator := 407845159668237010866819563520 }, { target := 346, numerator := 109767607832008050696995733504 }, { target := 351, numerator := 909885820407899348638692802560 }, { target := 353, numerator := 909886037341609655463019806720 }, { target := 372, numerator := 1204648163075841887732120944640 }, { target := 375, numerator := 4474967724137600535899825766400 }, { target := 377, numerator := 1204394585934532778480925409280 }, { target := 382, numerator := 545931492244739609183215681536 }, { target := 384, numerator := 545931622404965793277811884032 }, { target := 386, numerator := 4425175910438092605314702508032 }, { target := 389, numerator := 16438425741072552854659866296320 }, { target := 391, numerator := 4424244415673435598926133592064 }, { target := 406, numerator := 94542007735066072201761390592 }, { target := 409, numerator := 351199998603204092690872401920 }, { target := 411, numerator := 94522106744229154766857437184 }, { target := 443, numerator := 106740976475074597647149957120 }, { target := 446, numerator := 396516127455230427231630131200 }, { target := 448, numerator := 106718507614452271510968074240 }, { target := 457, numerator := 109790718660076729008497098752 }, { target := 460, numerator := 407845159668237010866819563520 }, { target := 462, numerator := 109767607832008050696995733504 }, { target := 477, numerator := 106740976475074597647149957120 }, { target := 480, numerator := 396516127455230427231630131200 }, { target := 482, numerator := 106718507614452271510968074240 }]

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
  [{ target := 0, numerator := 224581582825831717427740672 }, { target := 1, numerator := 39389499674306337079344234496 }, { target := 6, numerator := 39389504396672819948989448192 }, { target := 14, numerator := 224576860459348847782526976 }, { target := 16, numerator := 544772197463842271851970560 }, { target := 17, numerator := 175482760714117386569326264320 }, { target := 19, numerator := 1866332955671192913536610205696 }, { target := 27, numerator := 175483289619163467969590198272 }, { target := 34, numerator := 544772197463842271851970560 }, { target := 35, numerator := 231060347116379125612189581312 }, { target := 37, numerator := 9042800359483463532930429616128 }, { target := 40, numerator := 9042803676075688318759298138112 }, { target := 47, numerator := 231063663708603911441058103296 }, { target := 126, numerator := 544772197463842271851970560 }, { target := 127, numerator := 175482760714117386569326264320 }, { target := 129, numerator := 1866332955671192913536610205696 }, { target := 137, numerator := 175483289619163467969590198272 }, { target := 144, numerator := 544772197463842271851970560 }, { target := 145, numerator := 841697543213470391694557970432 }, { target := 147, numerator := 32940757431276174759216082321408 }, { target := 150, numerator := 32940769512827865829296918495232 }, { target := 157, numerator := 841709624765161461775394144256 }, { target := 215, numerator := 20909580976054626205718020096 }, { target := 216, numerator := 231060502543643443302676561920 }, { target := 218, numerator := 9042806442300092115375861268480 }, { target := 221, numerator := 9042809758894547871870138449920 }, { target := 228, numerator := 231063819138099199796953743360 }, { target := 260, numerator := 15570964556636423770215546880 }, { target := 265, numerator := 16460733959872790842799292416 }, { target := 355, numerator := 21354465677672809742009892864 }, { target := 396, numerator := 13938313411373508146958975369216 }, { target := 398, numerator := 13938316734526782909624134664192 }, { target := 400, numerator := 286060863140492013835674189824 }, { target := 401, numerator := 892825461275251235851717312512 }, { target := 403, numerator := 892825674141454474423088185344 }, { target := 405, numerator := 517400907981947452707448029184 }, { target := 416, numerator := 494750414846795270822289211392 }, { target := 418, numerator := 494750532804500250158017019904 }, { target := 420, numerator := 15570964556636423770215546880 }, { target := 421, numerator := 870078315765053752135749992448 }, { target := 423, numerator := 870078523207914233036512690176 }, { target := 425, numerator := 286060863140492013835674189824 }, { target := 426, numerator := 16905618661490974379091165184 }, { target := 453, numerator := 28433931887746854644959150080 }, { target := 455, numerator := 28433938666925301733219368960 }, { target := 467, numerator := 892825461275251235851717312512 }, { target := 469, numerator := 892825674141454474423088185344 }, { target := 471, numerator := 16905618661490974379091165184 }, { target := 472, numerator := 28433931887746854644959150080 }, { target := 474, numerator := 28433938666925301733219368960 }, { target := 476, numerator := 16460733959872790842799292416 }, { target := 487, numerator := 870078315765053752135749992448 }, { target := 489, numerator := 870078523207914233036512690176 }, { target := 491, numerator := 16460733959872790842799292416 }, { target := 492, numerator := 909885820407899348638692802560 }, { target := 494, numerator := 909886037341609655463019806720 }, { target := 496, numerator := 517400907981947452707448029184 }, { target := 497, numerator := 16460733959872790842799292416 }, { target := 498, numerator := 34120718265296225573950980096 }, { target := 500, numerator := 34120726400310362079863242752 }, { target := 502, numerator := 20909580976054626205718020096 }, { target := 503, numerator := 21354465677672809742009892864 }]

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
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 993656743493016397639843840 }, { target := 1, numerator := 197076749542167827586220032000 }, { target := 6, numerator := 197076749542167827586220032000 }, { target := 14, numerator := 993656743493016397639843840 }, { target := 16, numerator := 8563177417751132524238602240 }, { target := 17, numerator := 1403339856790290191361035468800 }, { target := 19, numerator := 14447927182838183354126093516800 }, { target := 27, numerator := 1403339856790290191361035468800 }, { target := 34, numerator := 8563177417751132524238602240 }, { target := 35, numerator := 650658730895009119624639807488 }, { target := 37, numerator := 26013215338672074362944229474304 }, { target := 40, numerator := 26013208981509863186554083606528 }, { target := 47, numerator := 650658730895009119624639807488 }, { target := 86, numerator := 881203436574719047784342749184 }, { target := 89, numerator := 3172087495067826012462820360192 }, { target := 91, numerator := 881392421052481040331246141440 }, { target := 122, numerator := 8622098363286117381056757760 }, { target := 124, numerator := 8622104530293644820565983232 }, { target := 126, numerator := 8563183542615100550721568768 }, { target := 127, numerator := 1403340860537533116941766492160 }, { target := 129, numerator := 14447937516804688753903544565760 }, { target := 137, numerator := 1403340860537533116941766492160 }, { target := 144, numerator := 8563183542615100550721568768 }, { target := 145, numerator := 2332217796451129740177489002496 }, { target := 147, numerator := 93241634784973069450938069024768 }, { target := 150, numerator := 93241611998393654097522695602176 }, { target := 157, numerator := 2332217796451129740177489002496 }, { target := 161, numerator := 35035105294840006426042342309888 }, { target := 164, numerator := 126108240151754339759411022528512 }, { target := 166, numerator := 35042660727861854878205822894080 }, { target := 197, numerator := 1412995864979214206439207731200 }, { target := 199, numerator := 1412996875632974858572099747840 }, { target := 215, numerator := 993656743493016397639843840 }, { target := 216, numerator := 650847811213672401734813614080 }, { target := 218, numerator := 26020774734730476538642972016640 }, { target := 221, numerator := 26020768375720884854455774740480 }, { target := 228, numerator := 650847811213672401734813614080 }, { target := 232, numerator := 35035102267747277796417757773824 }, { target := 235, numerator := 126108229495327503025871018524672 }, { target := 237, numerator := 35042657698926437365696000163840 }, { target := 242, numerator := 14547339525839363514819621683200 }, { target := 244, numerator := 14547349930911143034320312074240 }, { target := 260, numerator := 197076749542167827586220032000 }, { target := 406, numerator := 881206758188279525946033176576 }, { target := 409, numerator := 3172099594911041217396163477504 }, { target := 411, numerator := 881395742668275866858065756160 }, { target := 416, numerator := 1412995864979214206439207731200 }, { target := 418, numerator := 1412996875632974858572099747840 }, { target := 420, numerator := 197076749542167827586220032000 }, { target := 498, numerator := 8622098363286117381056757760 }, { target := 500, numerator := 8622104530293644820565983232 }, { target := 502, numerator := 993656743493016397639843840 }]

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
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left3.expected,
    Slot16.Left11.expected,
    Slot16.Left18.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left6.expected,
    Slot17.Left14.expected,
    Slot18.Left0.expected,
    Slot19.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 20909580976054626205718020096 }, { target := 1, numerator := 15570964556636423770215546880 }, { target := 2, numerator := 16460733959872790842799292416 }, { target := 3, numerator := 21354465677672809742009892864 }, { target := 4, numerator := 286060863140492013835674189824 }, { target := 5, numerator := 517400907981947452707448029184 }, { target := 6, numerator := 15570964556636423770215546880 }, { target := 7, numerator := 286060863140492013835674189824 }, { target := 8, numerator := 16905618661490974379091165184 }, { target := 9, numerator := 16905618661490974379091165184 }, { target := 10, numerator := 16460733959872790842799292416 }, { target := 11, numerator := 16460733959872790842799292416 }, { target := 12, numerator := 517400907981947452707448029184 }, { target := 13, numerator := 16460733959872790842799292416 }, { target := 14, numerator := 20909580976054626205718020096 }, { target := 15, numerator := 21354465677672809742009892864 }, { target := 16, numerator := 34062689832872252401206165504 }, { target := 17, numerator := 493909002576647659817489399808 }, { target := 18, numerator := 874275705710387811630958247936 }, { target := 19, numerator := 28385574860726877001005137920 }, { target := 20, numerator := 545003037325956038419298648064 }, { target := 21, numerator := 28385574860726877001005137920 }, { target := 22, numerator := 868598590738242436230757220352 }, { target := 23, numerator := 908338395543260064032164413440 }, { target := 24, numerator := 545003037325956038419298648064 }, { target := 25, numerator := 13914608796728315105892718608384 }, { target := 26, numerator := 891307050626823937831561330688 }, { target := 27, numerator := 493909002576647659817489399808 }, { target := 28, numerator := 868598590738242436230757220352 }, { target := 29, numerator := 28385574860726877001005137920 }, { target := 30, numerator := 891307050626823937831561330688 }, { target := 31, numerator := 28385574860726877001005137920 }, { target := 32, numerator := 868598590738242436230757220352 }, { target := 33, numerator := 908338395543260064032164413440 }, { target := 34, numerator := 34062689832872252401206165504 }, { target := 122, numerator := 535044122509130802711756800 }, { target := 124, numerator := 535044122509130802711756800 }, { target := 197, numerator := 172349139987079576094874009600 }, { target := 199, numerator := 172349139987079576094874009600 }, { target := 215, numerator := 224581582825831717427740672 }, { target := 242, numerator := 1833005581462778754366313594880 }, { target := 244, numerator := 1833005581462778754366313594880 }, { target := 260, numerator := 39389499674306337079344234496 }, { target := 416, numerator := 172349659447392691755847516160 }, { target := 418, numerator := 172349659447392691755847516160 }, { target := 420, numerator := 39389504396672819948989448192 }, { target := 498, numerator := 535044122509130802711756800 }, { target := 500, numerator := 535044122509130802711756800 }, { target := 502, numerator := 224576860459348847782526976 }]

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
    Slot19.Left2.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 94542007735066072201761390592 }, { target := 36, numerator := 106740976475074597647149957120 }, { target := 37, numerator := 91492265550063940840414248960 }, { target := 38, numerator := 1204648163075841887732120944640 }, { target := 39, numerator := 106740976475074597647149957120 }, { target := 40, numerator := 91492265550063940840414248960 }, { target := 41, numerator := 106740976475074597647149957120 }, { target := 42, numerator := 106740976475074597647149957120 }, { target := 43, numerator := 4425175910438092605314702508032 }, { target := 44, numerator := 109790718660076729008497098752 }, { target := 45, numerator := 1204648163075841887732120944640 }, { target := 46, numerator := 4425175910438092605314702508032 }, { target := 47, numerator := 94542007735066072201761390592 }, { target := 48, numerator := 106740976475074597647149957120 }, { target := 49, numerator := 109790718660076729008497098752 }, { target := 50, numerator := 106740976475074597647149957120 }, { target := 126, numerator := 34062697954051330851836264448 }, { target := 127, numerator := 493909120333744297351625834496 }, { target := 128, numerator := 874275914153984158530464120832 }, { target := 129, numerator := 28385581628376109043196887040 }, { target := 130, numerator := 545003167264821293629380231168 }, { target := 131, numerator := 28385581628376109043196887040 }, { target := 132, numerator := 868598797828308936721824743424 }, { target := 133, numerator := 908338612108035489382300385280 }, { target := 134, numerator := 545003167264821293629380231168 }, { target := 135, numerator := 13914612114229968652975114027008 }, { target := 136, numerator := 891307263131009823956382253056 }, { target := 137, numerator := 493909120333744297351625834496 }, { target := 138, numerator := 868598797828308936721824743424 }, { target := 139, numerator := 28385581628376109043196887040 }, { target := 140, numerator := 891307263131009823956382253056 }, { target := 141, numerator := 28385581628376109043196887040 }, { target := 142, numerator := 868598797828308936721824743424 }, { target := 143, numerator := 908338612108035489382300385280 }, { target := 144, numerator := 34062697954051330851836264448 }, { target := 145, numerator := 351199998603204092690872401920 }, { target := 146, numerator := 396516127455230427231630131200 }, { target := 147, numerator := 339870966390197509055682969600 }, { target := 148, numerator := 4474967724137600535899825766400 }, { target := 149, numerator := 396516127455230427231630131200 }, { target := 150, numerator := 339870966390197509055682969600 }, { target := 151, numerator := 396516127455230427231630131200 }, { target := 152, numerator := 396516127455230427231630131200 }, { target := 153, numerator := 16438425741072552854659866296320 }, { target := 154, numerator := 407845159668237010866819563520 }, { target := 155, numerator := 4474967724137600535899825766400 }, { target := 156, numerator := 16438425741072552854659866296320 }, { target := 157, numerator := 351199998603204092690872401920 }, { target := 158, numerator := 396516127455230427231630131200 }, { target := 159, numerator := 407845159668237010866819563520 }, { target := 160, numerator := 396516127455230427231630131200 }]

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
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected,
    Slot21.Left5.expected,
    Slot21.Left12.expected,
    Slot22.Left0.expected,
    Slot22.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 485799801334600206290780160 }, { target := 87, numerator := 10141070852859779306320035840 }, { target := 88, numerator := 526283118112483556815011840 }, { target := 89, numerator := 10910253871639562966280437760 }, { target := 90, numerator := 16335018319875931936527482880 }, { target := 91, numerator := 506041459723541881552896000 }, { target := 92, numerator := 16335018319875931936527482880 }, { target := 93, numerator := 17023234705099948895439421440 }, { target := 94, numerator := 10141070852859779306320035840 }, { target := 95, numerator := 506041459723541881552896000 }, { target := 122, numerator := 69547730039259014407127040 }, { target := 123, numerator := 76090052292440843983257600 }, { target := 124, numerator := 69547730039259014407127040 }, { target := 125, numerator := 76090052292440843983257600 }, { target := 161, numerator := 19011755817410139123370426368 }, { target := 162, numerator := 396870402688436654200357650432 }, { target := 163, numerator := 20596068802194317383651295232 }, { target := 164, numerator := 426972349399336041145694158848 }, { target := 165, numerator := 639270289360415928023330586624 }, { target := 166, numerator := 19803912309802228253510860800 }, { target := 167, numerator := 639270289360415928023330586624 }, { target := 168, numerator := 666203610101746958448105357312 }, { target := 169, numerator := 396870402688436654200357650432 }, { target := 170, numerator := 19803912309802228253510860800 }, { target := 197, numerator := 8220095177976739326370775040 }, { target := 198, numerator := 8993355665066575745620377600 }, { target := 199, numerator := 8220095177976739326370775040 }, { target := 200, numerator := 8993355665066575745620377600 }, { target := 216, numerator := 94522106744229154766857437184 }, { target := 217, numerator := 106718507614452271510968074240 }, { target := 218, numerator := 91473006526673375580829777920 }, { target := 219, numerator := 1204394585934532778480925409280 }, { target := 220, numerator := 106718507614452271510968074240 }, { target := 221, numerator := 91473006526673375580829777920 }, { target := 222, numerator := 106718507614452271510968074240 }, { target := 223, numerator := 106718507614452271510968074240 }, { target := 224, numerator := 4424244415673435598926133592064 }, { target := 225, numerator := 109767607832008050696995733504 }, { target := 226, numerator := 1204394585934532778480925409280 }, { target := 227, numerator := 4424244415673435598926133592064 }, { target := 228, numerator := 94522106744229154766857437184 }, { target := 229, numerator := 106718507614452271510968074240 }, { target := 230, numerator := 109767607832008050696995733504 }, { target := 231, numerator := 106718507614452271510968074240 }, { target := 232, numerator := 19011755817410139123370426368 }, { target := 233, numerator := 396870402688436654200357650432 }, { target := 234, numerator := 20596068802194317383651295232 }, { target := 235, numerator := 426972349399336041145694158848 }, { target := 236, numerator := 639270289360415928023330586624 }, { target := 237, numerator := 19803912309802228253510860800 }, { target := 238, numerator := 639270289360415928023330586624 }, { target := 239, numerator := 666203610101746958448105357312 }, { target := 240, numerator := 396870402688436654200357650432 }, { target := 241, numerator := 19803912309802228253510860800 }, { target := 406, numerator := 485799801334600206290780160 }, { target := 407, numerator := 10141070852859779306320035840 }, { target := 408, numerator := 526283118112483556815011840 }, { target := 409, numerator := 10910253871639562966280437760 }, { target := 410, numerator := 16335018319875931936527482880 }, { target := 411, numerator := 506041459723541881552896000 }, { target := 412, numerator := 16335018319875931936527482880 }, { target := 413, numerator := 17023234705099948895439421440 }, { target := 414, numerator := 10141070852859779306320035840 }, { target := 415, numerator := 506041459723541881552896000 }]

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
    Slot22.Left3.expected,
    Slot22.Left11.expected,
    Slot22.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 242, numerator := 78007064672830432419973693440 }, { target := 243, numerator := 85345152556164174529010073600 }, { target := 244, numerator := 78007064672830432419973693440 }, { target := 245, numerator := 85345152556164174529010073600 }, { target := 416, numerator := 8220100815762896853852487680 }, { target := 417, numerator := 8993361833196625392251699200 }, { target := 418, numerator := 8220100815762896853852487680 }, { target := 419, numerator := 8993361833196625392251699200 }, { target := 498, numerator := 69547730039259014407127040 }, { target := 499, numerator := 76090052292440843983257600 }, { target := 500, numerator := 69547730039259014407127040 }, { target := 501, numerator := 76090052292440843983257600 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7.Parent1
