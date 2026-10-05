import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk15Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 64; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15.Parent2

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
    Slot0.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 12297042321392556136464384 }, { target := 87, numerator := 245940846427851122729287680 }, { target := 88, numerator := 12736222404299433141338112 }, { target := 89, numerator := 228812823194482919539212288 }, { target := 90, numerator := 342560464667364063801507840 }, { target := 91, numerator := 12297042321392556136464384 }, { target := 92, numerator := 342999644750270940806381568 }, { target := 93, numerator := 342999644750270940806381568 }, { target := 94, numerator := 245501666344944245724413952 }, { target := 95, numerator := 12736222404299433141338112 }, { target := 112, numerator := 13883757459636756928266240 }, { target := 113, numerator := 277675149192735138565324800 }, { target := 114, numerator := 14379605940338069675704320 }, { target := 115, numerator := 258337058445383941415239680 }, { target := 116, numerator := 386761814947023943001702400 }, { target := 117, numerator := 13883757459636756928266240 }, { target := 118, numerator := 387257663427725255749140480 }, { target := 119, numerator := 387257663427725255749140480 }, { target := 120, numerator := 277179300712033825817886720 }, { target := 121, numerator := 14379605940338069675704320 }, { target := 161, numerator := 11900363536831505938513920 }, { target := 162, numerator := 238007270736630118770278400 }, { target := 163, numerator := 12325376520289774007746560 }, { target := 164, numerator := 221431764381757664070205440 }, { target := 165, numerator := 331510127097449094001459200 }, { target := 166, numerator := 11900363536831505938513920 }, { target := 167, numerator := 331935140080907362070691840 }, { target := 168, numerator := 331935140080907362070691840 }, { target := 169, numerator := 237582257753171850701045760 }, { target := 170, numerator := 12325376520289774007746560 }, { target := 187, numerator := 156688119901614828190433280 }, { target := 188, numerator := 3133762398032296563808665600 }, { target := 189, numerator := 162284124183815357768663040 }, { target := 190, numerator := 2915518231026475910257704960 }, { target := 191, numerator := 4364883340116413071019212800 }, { target := 192, numerator := 156688119901614828190433280 }, { target := 193, numerator := 4370479344398613600597442560 }, { target := 194, numerator := 4370479344398613600597442560 }, { target := 195, numerator := 3128166393750096034230435840 }, { target := 196, numerator := 162284124183815357768663040 }, { target := 201, numerator := 13883757459636756928266240 }, { target := 202, numerator := 277675149192735138565324800 }, { target := 203, numerator := 14379605940338069675704320 }, { target := 204, numerator := 258337058445383941415239680 }, { target := 205, numerator := 386761814947023943001702400 }, { target := 206, numerator := 13883757459636756928266240 }, { target := 207, numerator := 387257663427725255749140480 }, { target := 208, numerator := 387257663427725255749140480 }, { target := 209, numerator := 277179300712033825817886720 }, { target := 210, numerator := 14379605940338069675704320 }, { target := 232, numerator := 11900363536831505938513920 }, { target := 233, numerator := 238007270736630118770278400 }, { target := 234, numerator := 12325376520289774007746560 }, { target := 235, numerator := 221431764381757664070205440 }, { target := 236, numerator := 331510127097449094001459200 }, { target := 237, numerator := 11900363536831505938513920 }, { target := 238, numerator := 331935140080907362070691840 }, { target := 239, numerator := 331935140080907362070691840 }, { target := 240, numerator := 237582257753171850701045760 }, { target := 241, numerator := 12325376520289774007746560 }]

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
    Slot0.Left6.expected,
    Slot0.Left7.expected,
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 246, numerator := 13883757459636756928266240 }, { target := 247, numerator := 277675149192735138565324800 }, { target := 248, numerator := 14379605940338069675704320 }, { target := 249, numerator := 258337058445383941415239680 }, { target := 250, numerator := 386761814947023943001702400 }, { target := 251, numerator := 13883757459636756928266240 }, { target := 252, numerator := 387257663427725255749140480 }, { target := 253, numerator := 387257663427725255749140480 }, { target := 254, numerator := 277179300712033825817886720 }, { target := 255, numerator := 14379605940338069675704320 }, { target := 301, numerator := 13883757459636756928266240 }, { target := 302, numerator := 277675149192735138565324800 }, { target := 303, numerator := 14379605940338069675704320 }, { target := 304, numerator := 258337058445383941415239680 }, { target := 305, numerator := 386761814947023943001702400 }, { target := 306, numerator := 13883757459636756928266240 }, { target := 307, numerator := 387257663427725255749140480 }, { target := 308, numerator := 387257663427725255749140480 }, { target := 309, numerator := 277179300712033825817886720 }, { target := 310, numerator := 14379605940338069675704320 }, { target := 327, numerator := 575580916398083837226123264 }, { target := 328, numerator := 11511618327961676744522465280 }, { target := 329, numerator := 596137377698015402841341952 }, { target := 330, numerator := 10709916337264345685528936448 }, { target := 331, numerator := 16034039813946621179870576640 }, { target := 332, numerator := 575580916398083837226123264 }, { target := 333, numerator := 16054596275246552745485795328 }, { target := 334, numerator := 16054596275246552745485795328 }, { target := 335, numerator := 11491061866661745178907246592 }, { target := 336, numerator := 596137377698015402841341952 }, { target := 341, numerator := 14280436244197807126216704 }, { target := 342, numerator := 285608724883956142524334080 }, { target := 343, numerator := 14790451824347728809295872 }, { target := 344, numerator := 265718117258109196884246528 }, { target := 345, numerator := 397812152516938912801751040 }, { target := 346, numerator := 14280436244197807126216704 }, { target := 347, numerator := 398322168097088834484830208 }, { target := 348, numerator := 398322168097088834484830208 }, { target := 349, numerator := 285098709303806220841254912 }, { target := 350, numerator := 14790451824347728809295872 }, { target := 372, numerator := 156688119901614828190433280 }, { target := 373, numerator := 3133762398032296563808665600 }, { target := 374, numerator := 162284124183815357768663040 }, { target := 375, numerator := 2915518231026475910257704960 }, { target := 376, numerator := 4364883340116413071019212800 }, { target := 377, numerator := 156688119901614828190433280 }, { target := 378, numerator := 4370479344398613600597442560 }, { target := 379, numerator := 4370479344398613600597442560 }, { target := 380, numerator := 3128166393750096034230435840 }, { target := 381, numerator := 162284124183815357768663040 }, { target := 386, numerator := 575580916398083837226123264 }, { target := 387, numerator := 11511618327961676744522465280 }, { target := 388, numerator := 596137377698015402841341952 }, { target := 389, numerator := 10709916337264345685528936448 }, { target := 390, numerator := 16034039813946621179870576640 }, { target := 391, numerator := 575580916398083837226123264 }, { target := 392, numerator := 16054596275246552745485795328 }, { target := 393, numerator := 16054596275246552745485795328 }, { target := 394, numerator := 11491061866661745178907246592 }, { target := 395, numerator := 596137377698015402841341952 }]

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
    Slot1.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 122, numerator := 580284393415022003858964480 }, { target := 124, numerator := 580284393415022003858964480 }, { target := 197, numerator := 8414123704517819055954984960 }, { target := 199, numerator := 8414123704517819055954984960 }, { target := 211, numerator := 14893966097652231432380088320 }, { target := 213, numerator := 14893966097652231432380088320 }, { target := 242, numerator := 483570327845851669882470400 }, { target := 244, numerator := 483570327845851669882470400 }, { target := 256, numerator := 9284550294640352061743431680 }, { target := 258, numerator := 9284550294640352061743431680 }, { target := 261, numerator := 483570327845851669882470400 }, { target := 263, numerator := 483570327845851669882470400 }, { target := 337, numerator := 14797252032083061098403594240 }, { target := 339, numerator := 14797252032083061098403594240 }, { target := 351, numerator := 15474250491067253436239052800 }, { target := 353, numerator := 15474250491067253436239052800 }, { target := 382, numerator := 9284550294640352061743431680 }, { target := 384, numerator := 9284550294640352061743431680 }, { target := 396, numerator := 237046174710036488576386990080 }, { target := 398, numerator := 237046174710036488576386990080 }, { target := 401, numerator := 15184108294359742434309570560 }, { target := 403, numerator := 15184108294359742434309570560 }, { target := 406, numerator := 12297042321392556136464384 }, { target := 407, numerator := 245940846427851122729287680 }, { target := 408, numerator := 12736222404299433141338112 }, { target := 409, numerator := 228812823194482919539212288 }, { target := 410, numerator := 342560464667364063801507840 }, { target := 411, numerator := 12297042321392556136464384 }, { target := 412, numerator := 342999644750270940806381568 }, { target := 413, numerator := 342999644750270940806381568 }, { target := 414, numerator := 245501666344944245724413952 }, { target := 415, numerator := 12736222404299433141338112 }, { target := 416, numerator := 8414123704517819055954984960 }, { target := 418, numerator := 8414123704517819055954984960 }, { target := 443, numerator := 13883757459636756928266240 }, { target := 444, numerator := 277675149192735138565324800 }, { target := 445, numerator := 14379605940338069675704320 }, { target := 446, numerator := 258337058445383941415239680 }, { target := 447, numerator := 386761814947023943001702400 }, { target := 448, numerator := 13883757459636756928266240 }, { target := 449, numerator := 387257663427725255749140480 }, { target := 450, numerator := 387257663427725255749140480 }, { target := 451, numerator := 277179300712033825817886720 }, { target := 452, numerator := 14379605940338069675704320 }, { target := 457, numerator := 14280436244197807126216704 }, { target := 458, numerator := 285608724883956142524334080 }, { target := 459, numerator := 14790451824347728809295872 }, { target := 460, numerator := 265718117258109196884246528 }, { target := 461, numerator := 397812152516938912801751040 }, { target := 462, numerator := 14280436244197807126216704 }, { target := 463, numerator := 398322168097088834484830208 }, { target := 464, numerator := 398322168097088834484830208 }, { target := 465, numerator := 285098709303806220841254912 }, { target := 466, numerator := 14790451824347728809295872 }, { target := 477, numerator := 13883757459636756928266240 }, { target := 478, numerator := 277675149192735138565324800 }, { target := 479, numerator := 14379605940338069675704320 }, { target := 480, numerator := 258337058445383941415239680 }, { target := 481, numerator := 386761814947023943001702400 }, { target := 482, numerator := 13883757459636756928266240 }, { target := 483, numerator := 387257663427725255749140480 }, { target := 484, numerator := 387257663427725255749140480 }, { target := 485, numerator := 277179300712033825817886720 }, { target := 486, numerator := 14379605940338069675704320 }]

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
    Slot3.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 7157452066536743006543806464 }, { target := 36, numerator := 8151542631333512868563779584 }, { target := 37, numerator := 6362179614699327116927827968 }, { target := 38, numerator := 85292970459562854161313693696 }, { target := 39, numerator := 7555088292455450951351795712 }, { target := 40, numerator := 6362179614699327116927827968 }, { target := 41, numerator := 7555088292455450951351795712 }, { target := 42, numerator := 7356270179496096978947801088 }, { target := 43, numerator := 277947721917176853420784484352 }, { target := 44, numerator := 7356270179496096978947801088 }, { target := 45, numerator := 85292970459562854161313693696 }, { target := 46, numerator := 277947721917176853420784484352 }, { target := 47, numerator := 7157452066536743006543806464 }, { target := 48, numerator := 7356270179496096978947801088 }, { target := 49, numerator := 7356270179496096978947801088 }, { target := 50, numerator := 8151542631333512868563779584 }, { target := 145, numerator := 26072884834011842217303343104 }, { target := 146, numerator := 29694118838735709191928807424 }, { target := 147, numerator := 23175897630232748637602971648 }, { target := 148, numerator := 310701877605307786422864838656 }, { target := 149, numerator := 27521378435901389007153528832 }, { target := 150, numerator := 23175897630232748637602971648 }, { target := 151, numerator := 27521378435901389007153528832 }, { target := 152, numerator := 26797131634956615612228435968 }, { target := 153, numerator := 1012497027720793206105279823872 }, { target := 154, numerator := 26797131634956615612228435968 }, { target := 155, numerator := 310701877605307786422864838656 }, { target := 156, numerator := 1012497027720793206105279823872 }, { target := 157, numerator := 26072884834011842217303343104 }, { target := 158, numerator := 26797131634956615612228435968 }, { target := 159, numerator := 26797131634956615612228435968 }, { target := 160, numerator := 29694118838735709191928807424 }, { target := 215, numerator := 2727336649050603418137133056 }, { target := 260, numerator := 2030995376952577013506375680 }, { target := 265, numerator := 2147052255635581414278168576 }, { target := 355, numerator := 2785365088392105618523029504 }, { target := 400, numerator := 37312286496585914848131416064 }, { target := 405, numerator := 67487074954167059048797569024 }, { target := 420, numerator := 2030995376952577013506375680 }, { target := 421, numerator := 14797252032083061098403594240 }, { target := 423, numerator := 14797252032083061098403594240 }, { target := 425, numerator := 37312286496585914848131416064 }, { target := 426, numerator := 2205080694977083614664065024 }, { target := 453, numerator := 483570327845851669882470400 }, { target := 455, numerator := 483570327845851669882470400 }, { target := 467, numerator := 15184108294359742434309570560 }, { target := 469, numerator := 15184108294359742434309570560 }, { target := 471, numerator := 2205080694977083614664065024 }, { target := 472, numerator := 483570327845851669882470400 }, { target := 474, numerator := 483570327845851669882470400 }, { target := 476, numerator := 2147052255635581414278168576 }, { target := 487, numerator := 14797252032083061098403594240 }, { target := 489, numerator := 14797252032083061098403594240 }, { target := 491, numerator := 2147052255635581414278168576 }, { target := 492, numerator := 15474250491067253436239052800 }, { target := 494, numerator := 15474250491067253436239052800 }, { target := 496, numerator := 67487074954167059048797569024 }, { target := 497, numerator := 2147052255635581414278168576 }, { target := 498, numerator := 580284393415022003858964480 }, { target := 500, numerator := 580284393415022003858964480 }, { target := 502, numerator := 2727336649050603418137133056 }, { target := 503, numerator := 2785365088392105618523029504 }]

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
    Slot3.Left5.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left5.expected,
    Slot4.Left12.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left3.expected,
    Slot5.Left11.expected,
    Slot5.Left18.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left6.expected,
    Slot6.Left14.expected,
    Slot7.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 6557211300547408273279549440 }, { target := 17, numerator := 98358169508211124099193241600 }, { target := 18, numerator := 172673230914415084529694801920 }, { target := 19, numerator := 6557211300547408273279549440 }, { target := 20, numerator := 109286855009123471221325824000 }, { target := 21, numerator := 6557211300547408273279549440 }, { target := 22, numerator := 172673230914415084529694801920 }, { target := 23, numerator := 171580362364323849817481543680 }, { target := 24, numerator := 109286855009123471221325824000 }, { target := 25, numerator := 2648020496871061707692724715520 }, { target := 26, numerator := 169394625264141380393055027200 }, { target := 27, numerator := 98358169508211124099193241600 }, { target := 28, numerator := 172673230914415084529694801920 }, { target := 29, numerator := 6557211300547408273279549440 }, { target := 30, numerator := 169394625264141380393055027200 }, { target := 31, numerator := 6557211300547408273279549440 }, { target := 32, numerator := 172673230914415084529694801920 }, { target := 33, numerator := 172673230914415084529694801920 }, { target := 34, numerator := 6557211300547408273279549440 }, { target := 86, numerator := 121250610779955674600160886784 }, { target := 89, numerator := 442870076551017543648254361600 }, { target := 91, numerator := 121250569928645346377733242880 }, { target := 122, numerator := 11116421041295434961121181696 }, { target := 124, numerator := 11116423691657060269217021952 }, { target := 161, numerator := 4847576922276713279396062953472 }, { target := 164, numerator := 17705863490879306322896800972800 }, { target := 166, numerator := 4847575289048905864570774487040 }, { target := 197, numerator := 1821767312653556759028847083520 }, { target := 199, numerator := 1821767746996782673309193994240 }, { target := 215, numerator := 11327686875820386933094219776 }, { target := 216, numerator := 7157456881136946244736778240 }, { target := 217, numerator := 8151548114628188778727997440 }, { target := 218, numerator := 6362183894343952217543802880 }, { target := 219, numerator := 85293027833548609416446607360 }, { target := 220, numerator := 7555093374533443258333265920 }, { target := 221, numerator := 6362183894343952217543802880 }, { target := 222, numerator := 7555093374533443258333265920 }, { target := 223, numerator := 7356275127835194751535022080 }, { target := 224, numerator := 277947908884151412503944888320 }, { target := 225, numerator := 7356275127835194751535022080 }, { target := 226, numerator := 85293027833548609416446607360 }, { target := 227, numerator := 277947908884151412503944888320 }, { target := 228, numerator := 7157456881136946244736778240 }, { target := 229, numerator := 7356275127835194751535022080 }, { target := 230, numerator := 7356275127835194751535022080 }, { target := 231, numerator := 8151548114628188778727997440 }, { target := 232, numerator := 4847575737616054269858497429504 }, { target := 235, numerator := 17705859163884552501298043289600 }, { target := 237, numerator := 4847574104388645986550184673280 }, { target := 242, numerator := 18755799851287673846773810462720 }, { target := 244, numerator := 18755804323019357376035306864640 }, { target := 260, numerator := 2246674944780713234482908364800 }, { target := 406, numerator := 121250610779955674600160886784 }, { target := 409, numerator := 442870076551017543648254361600 }, { target := 411, numerator := 121250569928645346377733242880 }, { target := 416, numerator := 1821767312653556759028847083520 }, { target := 418, numerator := 1821767746996782673309193994240 }, { target := 420, numerator := 2246674944780713234482908364800 }, { target := 498, numerator := 11116421041295434961121181696 }, { target := 500, numerator := 11116423691657060269217021952 }, { target := 502, numerator := 11327686875820386933094219776 }]

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
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
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
    Slot11.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 682819628050825787138778333184 }, { target := 37, numerator := 26633641942021756945336006344704 }, { target := 40, numerator := 26633632172894991087283950583808 }, { target := 47, numerator := 682822884426414406489463586816 }, { target := 86, numerator := 1819343447375276460305572429824 }, { target := 89, numerator := 6544124276713704378254147715072 }, { target := 91, numerator := 1819344054318155326926599749632 }, { target := 122, numerator := 23872698784709067803637841920 }, { target := 124, numerator := 23872693093014822736531292160 }, { target := 126, numerator := 6557215990632089013933047808 }, { target := 127, numerator := 98358239859481335208995717120 }, { target := 128, numerator := 172673354419978344033570258944 }, { target := 129, numerator := 6557215990632089013933047808 }, { target := 130, numerator := 109286933177201483565550796800 }, { target := 131, numerator := 6557215990632089013933047808 }, { target := 132, numerator := 172673354419978344033570258944 }, { target := 133, numerator := 171580485088206329197914750976 }, { target := 134, numerator := 109286933177201483565550796800 }, { target := 135, numerator := 2648022390883591946793295806464 }, { target := 136, numerator := 169394746424662299526603735040 }, { target := 137, numerator := 98358239859481335208995717120 }, { target := 138, numerator := 172673354419978344033570258944 }, { target := 139, numerator := 6557215990632089013933047808 }, { target := 140, numerator := 169394746424662299526603735040 }, { target := 141, numerator := 6557215990632089013933047808 }, { target := 142, numerator := 172673354419978344033570258944 }, { target := 143, numerator := 172673354419978344033570258944 }, { target := 144, numerator := 6557215990632089013933047808 }, { target := 145, numerator := 2447495150208384132458875977728 }, { target := 147, numerator := 95465488699502866488713247981568 }, { target := 150, numerator := 95465453683095313206190261927936 }, { target := 157, numerator := 2447506822344235226633204662272 }, { target := 161, numerator := 71202003222398895284262122029056 }, { target := 164, numerator := 256111488191286736359457258733568 }, { target := 166, numerator := 71202026975774806368701758046208 }, { target := 197, numerator := 7689906180858930156533962506240 }, { target := 199, numerator := 7689904347442643652077703659520 }, { target := 215, numerator := 25826882024970647504190177280 }, { target := 216, numerator := 683018054271409657006721597440 }, { target := 218, numerator := 26641381632994064556718964080640 }, { target := 221, numerator := 26641371861028407104282852065280 }, { target := 228, numerator := 683021311593295474485425602560 }, { target := 232, numerator := 71202029336876810184595995623424 }, { target := 235, numerator := 256111582124287205925174349135872 }, { target := 237, numerator := 71202053090261433201039803154432 }, { target := 242, numerator := 81785386057024951858122480156672 }, { target := 244, numerator := 81785366557871741349693285728256 }, { target := 260, numerator := 4529792462545228764124586967040 }, { target := 406, numerator := 1819369561853191360639446024192 }, { target := 409, numerator := 6544218209714173943971238117376 }, { target := 411, numerator := 1819370168804782159264644857856 }, { target := 416, numerator := 7689929358236391039124063125504 }, { target := 418, numerator := 7689927524814578617925020680192 }, { target := 420, numerator := 4529793005617374294133786542080 }, { target := 498, numerator := 23872698784709067803637841920 }, { target := 500, numerator := 23872693093014822736531292160 }, { target := 502, numerator := 25826338952825117494990602240 }]

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
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left3.expected,
    Slot16.Left11.expected,
    Slot16.Left18.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left2.expected,
    Slot17.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 19497555618744739329661206528 }, { target := 1, numerator := 14623166714058554497245904896 }, { target := 2, numerator := 15435564864839585302648455168 }, { target := 3, numerator := 19903754694135254732362481664 }, { target := 4, numerator := 266466593456178104172036489216 }, { target := 5, numerator := 465910339472921166898362580992 }, { target := 6, numerator := 14216967638668039094544629760 }, { target := 7, numerator := 266466593456178104172036489216 }, { target := 8, numerator := 15029365789449069899947180032 }, { target := 9, numerator := 15435564864839585302648455168 }, { target := 10, numerator := 15435564864839585302648455168 }, { target := 11, numerator := 15029365789449069899947180032 }, { target := 12, numerator := 465910339472921166898362580992 }, { target := 13, numerator := 15029365789449069899947180032 }, { target := 14, numerator := 19497555618744739329661206528 }, { target := 15, numerator := 19903754694135254732362481664 }, { target := 16, numerator := 37982329104260315303953563648 }, { target := 17, numerator := 4489267444703250087914659381248 }, { target := 19, numerator := 42602253174736853854897022435328 }, { target := 27, numerator := 4489270523685829875553708015616 }, { target := 34, numerator := 37982329104260315303953563648 }, { target := 35, numerator := 2492365807002547548161939865600 }, { target := 37, numerator := 97538636286428514998566130810880 }, { target := 40, numerator := 97538636286428514998566130810880 }, { target := 47, numerator := 2492365807002547548161939865600 }, { target := 86, numerator := 2488565942293326754949218959360 }, { target := 89, numerator := 9244402318031508801221925273600 }, { target := 91, numerator := 2488042101841858584248026398720 }, { target := 122, numerator := 37865818892284056668051865600 }, { target := 124, numerator := 37865827920199869694948147200 }, { target := 126, numerator := 37982338159954330832471064576 }, { target := 127, numerator := 4489268515028143053635925835776 }, { target := 129, numerator := 42602263331906733129692910452736 }, { target := 137, numerator := 4489271594011456928014235860992 }, { target := 144, numerator := 37982338159954330832471064576 }, { target := 145, numerator := 9258517868489358134483091456000 }, { target := 147, numerator := 362331726903305185484434361548800 }, { target := 150, numerator := 362331726903305185484434361548800 }, { target := 157, numerator := 9258517868489358134483091456000 }, { target := 161, numerator := 97389928732838672494756813078528 }, { target := 164, numerator := 361779315400056903150362458849280 }, { target := 166, numerator := 97369428257698018238352175661056 }, { target := 197, numerator := 4475496685670418032430258585600 }, { target := 199, numerator := 4475497752712105805005140787200 }, { target := 215, numerator := 20426010648208774535835549696 }, { target := 216, numerator := 2491841166683649317788660531200 }, { target := 218, numerator := 97518104508507940253985417461760 }, { target := 221, numerator := 97518104508507940253985417461760 }, { target := 228, numerator := 2491841166683649317788660531200 }, { target := 232, numerator := 97389928732838672494756813078528 }, { target := 235, numerator := 361779315400056903150362458849280 }, { target := 237, numerator := 97369428257698018238352175661056 }, { target := 242, numerator := 42471571416532139579268503961600 }, { target := 244, numerator := 42471581542545056034203054899200 }, { target := 260, numerator := 15319507986156580901876662272 }, { target := 265, numerator := 16170591763165279840869810176 }, { target := 355, numerator := 20851552536713124005332123648 }, { target := 406, numerator := 2488565942293326754949218959360 }, { target := 409, numerator := 9244402318031508801221925273600 }, { target := 411, numerator := 2488042101841858584248026398720 }, { target := 416, numerator := 4475499755208265980229923635200 }, { target := 418, numerator := 4475500822250685587744253542400 }, { target := 498, numerator := 37865818892284056668051865600 }, { target := 500, numerator := 37865827920199869694948147200 }]

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
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected,
    Slot21.Left5.expected,
    Slot21.Left12.expected,
    Slot22.Left0.expected,
    Slot22.Left1.expected,
    Slot22.Left2.expected,
    Slot22.Left3.expected,
    Slot22.Left4.expected,
    Slot22.Left5.expected,
    Slot22.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 24928555693667320634479214592 }, { target := 1, numerator := 4372234463848003415807210029056 }, { target := 6, numerator := 4372234988030683014337828749312 }, { target := 14, numerator := 24928031510987722103860494336 }, { target := 16, numerator := 23794874175793960818132910080 }, { target := 17, numerator := 7664837212054174068004104437760 }, { target := 19, numerator := 81518767031574177768935446806528 }, { target := 27, numerator := 7664860313873762217480626896896 }, { target := 34, numerator := 23794874175793960818132910080 }, { target := 35, numerator := 1811407956909841988975364931584 }, { target := 37, numerator := 70891439090867641015793400938496 }, { target := 40, numerator := 70891465091441174199493076189184 }, { target := 47, numerator := 1811433957483375172675040182272 }, { target := 86, numerator := 681578460199266249223958429696 }, { target := 89, numerator := 2443046314567911868390526943232 }, { target := 91, numerator := 681776525738587047918420623360 }, { target := 122, numerator := 6905381812080898978055454720 }, { target := 124, numerator := 6905386751196624713787899904 }, { target := 126, numerator := 23794868502654546215792803840 }, { target := 127, numerator := 7664835384614794773016325652480 }, { target := 129, numerator := 81518747595987888892155573305344 }, { target := 137, numerator := 7664858486428875020148573995008 }, { target := 144, numerator := 23794868502654546215792803840 }, { target := 145, numerator := 6515580553494540212603140964352 }, { target := 147, numerator := 254994398245701013461698648997888 }, { target := 150, numerator := 254994491768990809272403888177152 }, { target := 157, numerator := 6515674076784336023308380143616 }, { target := 161, numerator := 26585229713095724149018854424576 }, { target := 164, numerator := 95291960156034541361364249608192 }, { target := 166, numerator := 26592955335556786329791663964160 }, { target := 197, numerator := 103580727181213484670831820800 }, { target := 199, numerator := 103580801267949370706818498560 }, { target := 211, numerator := 181841721051463673088793640960 }, { target := 213, numerator := 181841851114844450796414697472 }, { target := 216, numerator := 1811408561205398034136864653312 }, { target := 218, numerator := 70891462740637667056247403184128 }, { target := 221, numerator := 70891488741219874172829394010112 }, { target := 228, numerator := 1811434561787605150718855479296 }, { target := 232, numerator := 26585219961726394635034927562752 }, { target := 235, numerator := 95291925203276651250219518787584 }, { target := 237, numerator := 26592945581353725502171717304320 }, { target := 242, numerator := 6905381812080898978055454720 }, { target := 244, numerator := 6905386751196624713787899904 }, { target := 256, numerator := 115089696868014982967590912000 }, { target := 258, numerator := 115089779186610411896464998400 }, { target := 261, numerator := 6905381812080898978055454720 }, { target := 263, numerator := 6905386751196624713787899904 }, { target := 337, numerator := 181841721051463673088793640960 }, { target := 339, numerator := 181841851114844450796414697472 }, { target := 400, numerator := 279155478858853251989752512512 }, { target := 405, numerator := 488096546114488841512570322944 }, { target := 406, numerator := 681581710655709420551934050304 }, { target := 409, numerator := 2443057965487208572105437216768 }, { target := 411, numerator := 681779777139607323791736176640 }, { target := 420, numerator := 14893966097652231432380088320 }, { target := 425, numerator := 279155478858853251989752512512 }, { target := 426, numerator := 15745049874660930371373236224 }, { target := 471, numerator := 16170591763165279840869810176 }, { target := 476, numerator := 16170591763165279840869810176 }, { target := 491, numerator := 15745049874660930371373236224 }, { target := 496, numerator := 488096546114488841512570322944 }, { target := 497, numerator := 15745049874660930371373236224 }, { target := 502, numerator := 20426010648208774535835549696 }, { target := 503, numerator := 20851552536713124005332123648 }]

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
    Slot22.Left7.expected,
    Slot22.Left8.expected,
    Slot22.Left9.expected,
    Slot22.Left10.expected,
    Slot22.Left11.expected,
    Slot22.Left12.expected,
    Slot22.Left13.expected,
    Slot22.Left14.expected,
    Slot22.Left15.expected,
    Slot22.Left16.expected,
    Slot22.Left17.expected,
    Slot22.Left18.expected,
    Slot23.Left0.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected,
    Slot25.Left0.expected,
    Slot25.Left3.expected,
    Slot25.Left5.expected,
    Slot26.Left0.expected,
    Slot26.Left1.expected,
    Slot26.Left2.expected,
    Slot26.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 10930224178423180374038282240 }, { target := 1, numerator := 2167844244963846103448420352000 }, { target := 6, numerator := 2167844244963846103448420352000 }, { target := 14, numerator := 10930224178423180374038282240 }, { target := 16, numerator := 11253903280322056948272857088 }, { target := 17, numerator := 1844298003799448803751818690560 }, { target := 19, numerator := 18987762040261196314843451228160 }, { target := 27, numerator := 1844298003799448803751818690560 }, { target := 34, numerator := 11253903280322056948272857088 }, { target := 35, numerator := 124157889176654188659685195776 }, { target := 37, numerator := 4963809373163460988493006635008 }, { target := 40, numerator := 4963808160097680394805739257856 }, { target := 47, numerator := 124157889176654188659685195776 }, { target := 86, numerator := 7280856412511514437691113472 }, { target := 89, numerator := 26522417331149977427946504192 }, { target := 91, numerator := 7280861310122066007577067520 }, { target := 112, numerator := 8292086469804780331814879232 }, { target := 115, numerator := 30206086404920807626272407552 }, { target := 117, numerator := 8292092047639019619740549120 }, { target := 126, numerator := 11253905963462006244278009856 }, { target := 127, numerator := 1844298443514410727572735262720 }, { target := 129, numerator := 18987766567296981937223022673920 }, { target := 137, numerator := 1844298443514410727572735262720 }, { target := 144, numerator := 11253905963462006244278009856 }, { target := 145, numerator := 453488964141098359222330982400 }, { target := 147, numerator := 18130404646513930028805468979200 }, { target := 150, numerator := 18130400215768949387788969574400 }, { target := 157, numerator := 453488964141098359222330982400 }, { target := 161, numerator := 6471872366676901722392100864 }, { target := 164, numerator := 23575482072133313269285781504 }, { target := 166, numerator := 6471876720108503117846282240 }, { target := 187, numerator := 86763538915762213715819102208 }, { target := 190, numerator := 316058806529537231016362508288 }, { target := 192, numerator := 86763597278954619923626721280 }, { target := 216, numerator := 124157847345834303907241656320 }, { target := 218, numerator := 4963807700775043240731145666560 }, { target := 221, numerator := 4963806487709671348710062161920 }, { target := 228, numerator := 124157847345834303907241656320 }, { target := 351, numerator := 180690824082783523259117731840 }, { target := 353, numerator := 180690953322978346677450047488 }, { target := 382, numerator := 115089696868014982967590912000 }, { target := 384, numerator := 115089779186610411896464998400 }, { target := 396, numerator := 2788623355112003037304727797760 }, { target := 398, numerator := 2788625349691570280251346911232 }, { target := 401, numerator := 178389030145423223599765913600 }, { target := 403, numerator := 178389157739246138439520747520 }, { target := 416, numerator := 103580727181213484670831820800 }, { target := 418, numerator := 103580801267949370706818498560 }, { target := 421, numerator := 181841721051463673088793640960 }, { target := 423, numerator := 181841851114844450796414697472 }, { target := 453, numerator := 6905381812080898978055454720 }, { target := 455, numerator := 6905386751196624713787899904 }, { target := 467, numerator := 178389030145423223599765913600 }, { target := 469, numerator := 178389157739246138439520747520 }, { target := 472, numerator := 6905381812080898978055454720 }, { target := 474, numerator := 6905386751196624713787899904 }, { target := 487, numerator := 181841721051463673088793640960 }, { target := 489, numerator := 181841851114844450796414697472 }, { target := 492, numerator := 181841721051463673088793640960 }, { target := 494, numerator := 181841851114844450796414697472 }, { target := 498, numerator := 6905381812080898978055454720 }, { target := 500, numerator := 6905386751196624713787899904 }]

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
    Slot26.Left4.expected,
    Slot26.Left5.expected,
    Slot26.Left6.expected,
    Slot26.Left7.expected,
    Slot26.Left8.expected,
    Slot26.Left9.expected,
    Slot26.Left10.expected,
    Slot26.Left11.expected,
    Slot26.Left12.expected,
    Slot26.Left13.expected,
    Slot26.Left14.expected,
    Slot26.Left15.expected,
    Slot27.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 2727336649050603418137133056 }, { target := 1, numerator := 2030995376952577013506375680 }, { target := 2, numerator := 2147052255635581414278168576 }, { target := 3, numerator := 2785365088392105618523029504 }, { target := 4, numerator := 37312286496585914848131416064 }, { target := 5, numerator := 67487074954167059048797569024 }, { target := 6, numerator := 2030995376952577013506375680 }, { target := 7, numerator := 37312286496585914848131416064 }, { target := 8, numerator := 2205080694977083614664065024 }, { target := 9, numerator := 2205080694977083614664065024 }, { target := 10, numerator := 2147052255635581414278168576 }, { target := 11, numerator := 2147052255635581414278168576 }, { target := 12, numerator := 67487074954167059048797569024 }, { target := 13, numerator := 2147052255635581414278168576 }, { target := 14, numerator := 2727336649050603418137133056 }, { target := 15, numerator := 2785365088392105618523029504 }, { target := 201, numerator := 7685348435428820795340619776 }, { target := 204, numerator := 27995884960658309507276865536 }, { target := 206, numerator := 7685353605128847452442460160 }, { target := 232, numerator := 6471872366676901722392100864 }, { target := 235, numerator := 23575482072133313269285781504 }, { target := 237, numerator := 6471876720108503117846282240 }, { target := 246, numerator := 7685348435428820795340619776 }, { target := 249, numerator := 27995884960658309507276865536 }, { target := 251, numerator := 7685353605128847452442460160 }, { target := 301, numerator := 7483102423970167616515866624 }, { target := 304, numerator := 27259151145904143467611684864 }, { target := 306, numerator := 7483107457625456730009763840 }, { target := 327, numerator := 282739924019197143997004906496 }, { target := 330, numerator := 1029953873026324123451922579456 }, { target := 332, numerator := 282740114209740229960909455360 }, { target := 341, numerator := 7483102423970167616515866624 }, { target := 344, numerator := 27259151145904143467611684864 }, { target := 346, numerator := 7483107457625456730009763840 }, { target := 372, numerator := 86763538915762213715819102208 }, { target := 375, numerator := 316058806529537231016362508288 }, { target := 377, numerator := 86763597278954619923626721280 }, { target := 386, numerator := 282739924019197143997004906496 }, { target := 389, numerator := 1029953873026324123451922579456 }, { target := 391, numerator := 282740114209740229960909455360 }, { target := 406, numerator := 7280856412511514437691113472 }, { target := 409, numerator := 26522417331149977427946504192 }, { target := 411, numerator := 7280861310122066007577067520 }, { target := 443, numerator := 7483102423970167616515866624 }, { target := 446, numerator := 27259151145904143467611684864 }, { target := 448, numerator := 7483107457625456730009763840 }, { target := 457, numerator := 7483102423970167616515866624 }, { target := 460, numerator := 27259151145904143467611684864 }, { target := 462, numerator := 7483107457625456730009763840 }, { target := 477, numerator := 8292086469804780331814879232 }, { target := 480, numerator := 30206086404920807626272407552 }, { target := 482, numerator := 8292092047639019619740549120 }]

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
    Slot28.Left0.expected,
    Slot28.Left2.expected,
    Slot29.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 580284393415022003858964480 }, { target := 17, numerator := 8414123704517819055954984960 }, { target := 18, numerator := 14893966097652231432380088320 }, { target := 19, numerator := 483570327845851669882470400 }, { target := 20, numerator := 9284550294640352061743431680 }, { target := 21, numerator := 483570327845851669882470400 }, { target := 22, numerator := 14797252032083061098403594240 }, { target := 23, numerator := 15474250491067253436239052800 }, { target := 24, numerator := 9284550294640352061743431680 }, { target := 25, numerator := 237046174710036488576386990080 }, { target := 26, numerator := 15184108294359742434309570560 }, { target := 27, numerator := 8414123704517819055954984960 }, { target := 28, numerator := 14797252032083061098403594240 }, { target := 29, numerator := 483570327845851669882470400 }, { target := 30, numerator := 15184108294359742434309570560 }, { target := 31, numerator := 483570327845851669882470400 }, { target := 32, numerator := 14797252032083061098403594240 }, { target := 33, numerator := 15474250491067253436239052800 }, { target := 34, numerator := 580284393415022003858964480 }, { target := 35, numerator := 12297042321392556136464384 }, { target := 36, numerator := 13883757459636756928266240 }, { target := 37, numerator := 11900363536831505938513920 }, { target := 38, numerator := 156688119901614828190433280 }, { target := 39, numerator := 13883757459636756928266240 }, { target := 40, numerator := 11900363536831505938513920 }, { target := 41, numerator := 13883757459636756928266240 }, { target := 42, numerator := 13883757459636756928266240 }, { target := 43, numerator := 575580916398083837226123264 }, { target := 44, numerator := 14280436244197807126216704 }, { target := 45, numerator := 156688119901614828190433280 }, { target := 46, numerator := 575580916398083837226123264 }, { target := 47, numerator := 12297042321392556136464384 }, { target := 48, numerator := 13883757459636756928266240 }, { target := 49, numerator := 14280436244197807126216704 }, { target := 50, numerator := 13883757459636756928266240 }, { target := 126, numerator := 580284393415022003858964480 }, { target := 127, numerator := 8414123704517819055954984960 }, { target := 128, numerator := 14893966097652231432380088320 }, { target := 129, numerator := 483570327845851669882470400 }, { target := 130, numerator := 9284550294640352061743431680 }, { target := 131, numerator := 483570327845851669882470400 }, { target := 132, numerator := 14797252032083061098403594240 }, { target := 133, numerator := 15474250491067253436239052800 }, { target := 134, numerator := 9284550294640352061743431680 }, { target := 135, numerator := 237046174710036488576386990080 }, { target := 136, numerator := 15184108294359742434309570560 }, { target := 137, numerator := 8414123704517819055954984960 }, { target := 138, numerator := 14797252032083061098403594240 }, { target := 139, numerator := 483570327845851669882470400 }, { target := 140, numerator := 15184108294359742434309570560 }, { target := 141, numerator := 483570327845851669882470400 }, { target := 142, numerator := 14797252032083061098403594240 }, { target := 143, numerator := 15474250491067253436239052800 }, { target := 144, numerator := 580284393415022003858964480 }]

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
    Slot29.Left1.expected,
    Slot29.Left2.expected,
    Slot29.Left3.expected,
    Slot29.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 70, numerator := 245940846427851122729287680 }, { target := 71, numerator := 277675149192735138565324800 }, { target := 72, numerator := 238007270736630118770278400 }, { target := 73, numerator := 3133762398032296563808665600 }, { target := 74, numerator := 277675149192735138565324800 }, { target := 75, numerator := 238007270736630118770278400 }, { target := 76, numerator := 277675149192735138565324800 }, { target := 77, numerator := 277675149192735138565324800 }, { target := 78, numerator := 11511618327961676744522465280 }, { target := 79, numerator := 285608724883956142524334080 }, { target := 80, numerator := 3133762398032296563808665600 }, { target := 81, numerator := 11511618327961676744522465280 }, { target := 82, numerator := 245940846427851122729287680 }, { target := 83, numerator := 277675149192735138565324800 }, { target := 84, numerator := 285608724883956142524334080 }, { target := 85, numerator := 277675149192735138565324800 }, { target := 96, numerator := 12736222404299433141338112 }, { target := 97, numerator := 14379605940338069675704320 }, { target := 98, numerator := 12325376520289774007746560 }, { target := 99, numerator := 162284124183815357768663040 }, { target := 100, numerator := 14379605940338069675704320 }, { target := 101, numerator := 12325376520289774007746560 }, { target := 102, numerator := 14379605940338069675704320 }, { target := 103, numerator := 14379605940338069675704320 }, { target := 104, numerator := 596137377698015402841341952 }, { target := 105, numerator := 14790451824347728809295872 }, { target := 106, numerator := 162284124183815357768663040 }, { target := 107, numerator := 596137377698015402841341952 }, { target := 108, numerator := 12736222404299433141338112 }, { target := 109, numerator := 14379605940338069675704320 }, { target := 110, numerator := 14790451824347728809295872 }, { target := 111, numerator := 14379605940338069675704320 }, { target := 145, numerator := 228812823194482919539212288 }, { target := 146, numerator := 258337058445383941415239680 }, { target := 147, numerator := 221431764381757664070205440 }, { target := 148, numerator := 2915518231026475910257704960 }, { target := 149, numerator := 258337058445383941415239680 }, { target := 150, numerator := 221431764381757664070205440 }, { target := 151, numerator := 258337058445383941415239680 }, { target := 152, numerator := 258337058445383941415239680 }, { target := 153, numerator := 10709916337264345685528936448 }, { target := 154, numerator := 265718117258109196884246528 }, { target := 155, numerator := 2915518231026475910257704960 }, { target := 156, numerator := 10709916337264345685528936448 }, { target := 157, numerator := 228812823194482919539212288 }, { target := 158, numerator := 258337058445383941415239680 }, { target := 159, numerator := 265718117258109196884246528 }, { target := 160, numerator := 258337058445383941415239680 }, { target := 171, numerator := 342560464667364063801507840 }, { target := 172, numerator := 386761814947023943001702400 }, { target := 173, numerator := 331510127097449094001459200 }, { target := 174, numerator := 4364883340116413071019212800 }, { target := 175, numerator := 386761814947023943001702400 }, { target := 176, numerator := 331510127097449094001459200 }, { target := 177, numerator := 386761814947023943001702400 }, { target := 178, numerator := 386761814947023943001702400 }, { target := 179, numerator := 16034039813946621179870576640 }, { target := 180, numerator := 397812152516938912801751040 }, { target := 181, numerator := 4364883340116413071019212800 }, { target := 182, numerator := 16034039813946621179870576640 }, { target := 183, numerator := 342560464667364063801507840 }, { target := 184, numerator := 386761814947023943001702400 }, { target := 185, numerator := 397812152516938912801751040 }, { target := 186, numerator := 386761814947023943001702400 }]

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
    Slot29.Left5.expected,
    Slot29.Left6.expected,
    Slot29.Left7.expected,
    Slot29.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 216, numerator := 12297042321392556136464384 }, { target := 217, numerator := 13883757459636756928266240 }, { target := 218, numerator := 11900363536831505938513920 }, { target := 219, numerator := 156688119901614828190433280 }, { target := 220, numerator := 13883757459636756928266240 }, { target := 221, numerator := 11900363536831505938513920 }, { target := 222, numerator := 13883757459636756928266240 }, { target := 223, numerator := 13883757459636756928266240 }, { target := 224, numerator := 575580916398083837226123264 }, { target := 225, numerator := 14280436244197807126216704 }, { target := 226, numerator := 156688119901614828190433280 }, { target := 227, numerator := 575580916398083837226123264 }, { target := 228, numerator := 12297042321392556136464384 }, { target := 229, numerator := 13883757459636756928266240 }, { target := 230, numerator := 14280436244197807126216704 }, { target := 231, numerator := 13883757459636756928266240 }, { target := 285, numerator := 342999644750270940806381568 }, { target := 286, numerator := 387257663427725255749140480 }, { target := 287, numerator := 331935140080907362070691840 }, { target := 288, numerator := 4370479344398613600597442560 }, { target := 289, numerator := 387257663427725255749140480 }, { target := 290, numerator := 331935140080907362070691840 }, { target := 291, numerator := 387257663427725255749140480 }, { target := 292, numerator := 387257663427725255749140480 }, { target := 293, numerator := 16054596275246552745485795328 }, { target := 294, numerator := 398322168097088834484830208 }, { target := 295, numerator := 4370479344398613600597442560 }, { target := 296, numerator := 16054596275246552745485795328 }, { target := 297, numerator := 342999644750270940806381568 }, { target := 298, numerator := 387257663427725255749140480 }, { target := 299, numerator := 398322168097088834484830208 }, { target := 300, numerator := 387257663427725255749140480 }, { target := 311, numerator := 342999644750270940806381568 }, { target := 312, numerator := 387257663427725255749140480 }, { target := 313, numerator := 331935140080907362070691840 }, { target := 314, numerator := 4370479344398613600597442560 }, { target := 315, numerator := 387257663427725255749140480 }, { target := 316, numerator := 331935140080907362070691840 }, { target := 317, numerator := 387257663427725255749140480 }, { target := 318, numerator := 387257663427725255749140480 }, { target := 319, numerator := 16054596275246552745485795328 }, { target := 320, numerator := 398322168097088834484830208 }, { target := 321, numerator := 4370479344398613600597442560 }, { target := 322, numerator := 16054596275246552745485795328 }, { target := 323, numerator := 342999644750270940806381568 }, { target := 324, numerator := 387257663427725255749140480 }, { target := 325, numerator := 398322168097088834484830208 }, { target := 326, numerator := 387257663427725255749140480 }, { target := 356, numerator := 245501666344944245724413952 }, { target := 357, numerator := 277179300712033825817886720 }, { target := 358, numerator := 237582257753171850701045760 }, { target := 359, numerator := 3128166393750096034230435840 }, { target := 360, numerator := 277179300712033825817886720 }, { target := 361, numerator := 237582257753171850701045760 }, { target := 362, numerator := 277179300712033825817886720 }, { target := 363, numerator := 277179300712033825817886720 }, { target := 364, numerator := 11491061866661745178907246592 }, { target := 365, numerator := 285098709303806220841254912 }, { target := 366, numerator := 3128166393750096034230435840 }, { target := 367, numerator := 11491061866661745178907246592 }, { target := 368, numerator := 245501666344944245724413952 }, { target := 369, numerator := 277179300712033825817886720 }, { target := 370, numerator := 285098709303806220841254912 }, { target := 371, numerator := 277179300712033825817886720 }]

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
    Slot29.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 427, numerator := 12736222404299433141338112 }, { target := 428, numerator := 14379605940338069675704320 }, { target := 429, numerator := 12325376520289774007746560 }, { target := 430, numerator := 162284124183815357768663040 }, { target := 431, numerator := 14379605940338069675704320 }, { target := 432, numerator := 12325376520289774007746560 }, { target := 433, numerator := 14379605940338069675704320 }, { target := 434, numerator := 14379605940338069675704320 }, { target := 435, numerator := 596137377698015402841341952 }, { target := 436, numerator := 14790451824347728809295872 }, { target := 437, numerator := 162284124183815357768663040 }, { target := 438, numerator := 596137377698015402841341952 }, { target := 439, numerator := 12736222404299433141338112 }, { target := 440, numerator := 14379605940338069675704320 }, { target := 441, numerator := 14790451824347728809295872 }, { target := 442, numerator := 14379605940338069675704320 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15.Parent2
