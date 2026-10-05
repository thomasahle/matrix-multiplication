import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk15Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 64; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent2

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
    Slot2.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 20400623205996867323166720 }, { target := 87, numerator := 363131093066744238352367616 }, { target := 88, numerator := 20400623205996867323166720 }, { target := 89, numerator := 323009867428283732616806400 }, { target := 90, numerator := 551496847335448646636273664 }, { target := 91, numerator := 20400623205996867323166720 }, { target := 92, numerator := 551496847335448646636273664 }, { target := 93, numerator := 551496847335448646636273664 }, { target := 94, numerator := 363131093066744238352367616 }, { target := 95, numerator := 20400623205996867323166720 }, { target := 122, numerator := 580284393415022003858964480 }, { target := 124, numerator := 580284393415022003858964480 }, { target := 197, numerator := 15474250491067253436239052800 }, { target := 199, numerator := 15474250491067253436239052800 }, { target := 211, numerator := 14797252032083061098403594240 }, { target := 213, numerator := 14797252032083061098403594240 }, { target := 215, numerator := 2030995376952577013506375680 }, { target := 242, numerator := 483570327845851669882470400 }, { target := 244, numerator := 483570327845851669882470400 }, { target := 256, numerator := 15184108294359742434309570560 }, { target := 258, numerator := 15184108294359742434309570560 }, { target := 260, numerator := 2089023816294079213892272128 }, { target := 261, numerator := 483570327845851669882470400 }, { target := 263, numerator := 483570327845851669882470400 }, { target := 265, numerator := 2030995376952577013506375680 }, { target := 337, numerator := 14797252032083061098403594240 }, { target := 339, numerator := 14797252032083061098403594240 }, { target := 351, numerator := 8414123704517819055954984960 }, { target := 353, numerator := 8414123704517819055954984960 }, { target := 355, numerator := 1798881619586568211962789888 }, { target := 382, numerator := 15184108294359742434309570560 }, { target := 384, numerator := 15184108294359742434309570560 }, { target := 396, numerator := 237046174710036488576386990080 }, { target := 398, numerator := 237046174710036488576386990080 }, { target := 400, numerator := 84199265484519692759935746048 }, { target := 401, numerator := 9284550294640352061743431680 }, { target := 403, numerator := 9284550294640352061743431680 }, { target := 405, numerator := 22921233539893369152429096960 }, { target := 416, numerator := 15474250491067253436239052800 }, { target := 418, numerator := 15474250491067253436239052800 }, { target := 420, numerator := 2089023816294079213892272128 }, { target := 421, numerator := 14797252032083061098403594240 }, { target := 423, numerator := 14797252032083061098403594240 }, { target := 425, numerator := 84199265484519692759935746048 }, { target := 426, numerator := 2030995376952577013506375680 }, { target := 453, numerator := 483570327845851669882470400 }, { target := 455, numerator := 483570327845851669882470400 }, { target := 467, numerator := 9284550294640352061743431680 }, { target := 469, numerator := 9284550294640352061743431680 }, { target := 471, numerator := 2030995376952577013506375680 }, { target := 472, numerator := 483570327845851669882470400 }, { target := 474, numerator := 483570327845851669882470400 }, { target := 476, numerator := 1740853180245066011576893440 }, { target := 487, numerator := 14893966097652231432380088320 }, { target := 489, numerator := 14893966097652231432380088320 }, { target := 491, numerator := 2030995376952577013506375680 }, { target := 492, numerator := 8414123704517819055954984960 }, { target := 494, numerator := 8414123704517819055954984960 }, { target := 496, numerator := 22921233539893369152429096960 }, { target := 497, numerator := 1740853180245066011576893440 }, { target := 498, numerator := 580284393415022003858964480 }, { target := 500, numerator := 580284393415022003858964480 }, { target := 502, numerator := 2030995376952577013506375680 }, { target := 503, numerator := 1798881619586568211962789888 }]

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
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 112, numerator := 19975610222538599253934080 }, { target := 113, numerator := 355565861961187066720026624 }, { target := 114, numerator := 19975610222538599253934080 }, { target := 115, numerator := 316280495190194488187289600 }, { target := 116, numerator := 540007329682626799831351296 }, { target := 117, numerator := 19975610222538599253934080 }, { target := 118, numerator := 540007329682626799831351296 }, { target := 119, numerator := 540007329682626799831351296 }, { target := 120, numerator := 355565861961187066720026624 }, { target := 121, numerator := 19975610222538599253934080 }, { target := 161, numerator := 15725480387955918561607680 }, { target := 162, numerator := 279913550905615350396616704 }, { target := 163, numerator := 15725480387955918561607680 }, { target := 164, numerator := 248986772809302043892121600 }, { target := 165, numerator := 425112153154408331782127616 }, { target := 166, numerator := 15725480387955918561607680 }, { target := 167, numerator := 425112153154408331782127616 }, { target := 168, numerator := 425112153154408331782127616 }, { target := 169, numerator := 279913550905615350396616704 }, { target := 170, numerator := 15725480387955918561607680 }, { target := 187, numerator := 494290099761965764517560320 }, { target := 188, numerator := 8798363775762990608412573696 }, { target := 189, numerator := 494290099761965764517560320 }, { target := 190, numerator := 7826259912897791271528038400 }, { target := 191, numerator := 13362309030231807834124713984 }, { target := 192, numerator := 494290099761965764517560320 }, { target := 193, numerator := 13362309030231807834124713984 }, { target := 194, numerator := 13362309030231807834124713984 }, { target := 195, numerator := 8798363775762990608412573696 }, { target := 196, numerator := 494290099761965764517560320 }, { target := 201, numerator := 15725480387955918561607680 }, { target := 202, numerator := 279913550905615350396616704 }, { target := 203, numerator := 15725480387955918561607680 }, { target := 204, numerator := 248986772809302043892121600 }, { target := 205, numerator := 425112153154408331782127616 }, { target := 206, numerator := 15725480387955918561607680 }, { target := 207, numerator := 425112153154408331782127616 }, { target := 208, numerator := 425112153154408331782127616 }, { target := 209, numerator := 279913550905615350396616704 }, { target := 210, numerator := 15725480387955918561607680 }, { target := 232, numerator := 15725480387955918561607680 }, { target := 233, numerator := 279913550905615350396616704 }, { target := 234, numerator := 15725480387955918561607680 }, { target := 235, numerator := 248986772809302043892121600 }, { target := 236, numerator := 425112153154408331782127616 }, { target := 237, numerator := 15725480387955918561607680 }, { target := 238, numerator := 425112153154408331782127616 }, { target := 239, numerator := 425112153154408331782127616 }, { target := 240, numerator := 279913550905615350396616704 }, { target := 241, numerator := 15725480387955918561607680 }, { target := 246, numerator := 16150493371414186630840320 }, { target := 247, numerator := 287478782011172522028957696 }, { target := 248, numerator := 16150493371414186630840320 }, { target := 249, numerator := 255716145047391288321638400 }, { target := 250, numerator := 436601670807230178587049984 }, { target := 251, numerator := 16150493371414186630840320 }, { target := 252, numerator := 436601670807230178587049984 }, { target := 253, numerator := 436601670807230178587049984 }, { target := 254, numerator := 287478782011172522028957696 }, { target := 255, numerator := 16150493371414186630840320 }]

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
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot2.Left10.expected,
    Slot2.Left11.expected,
    Slot2.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 301, numerator := 16150493371414186630840320 }, { target := 302, numerator := 287478782011172522028957696 }, { target := 303, numerator := 16150493371414186630840320 }, { target := 304, numerator := 255716145047391288321638400 }, { target := 305, numerator := 436601670807230178587049984 }, { target := 306, numerator := 16150493371414186630840320 }, { target := 307, numerator := 436601670807230178587049984 }, { target := 308, numerator := 436601670807230178587049984 }, { target := 309, numerator := 287478782011172522028957696 }, { target := 310, numerator := 16150493371414186630840320 }, { target := 327, numerator := 273283348363666368516587520 }, { target := 328, numerator := 4864443600873261359595257856 }, { target := 329, numerator := 273283348363666368516587520 }, { target := 330, numerator := 4326986349091384168179302400 }, { target := 331, numerator := 7387759850764447495565082624 }, { target := 332, numerator := 273283348363666368516587520 }, { target := 333, numerator := 7387759850764447495565082624 }, { target := 334, numerator := 7387759850764447495565082624 }, { target := 335, numerator := 4864443600873261359595257856 }, { target := 336, numerator := 273283348363666368516587520 }, { target := 341, numerator := 14875454421039382423142400 }, { target := 342, numerator := 264783088694501007131934720 }, { target := 343, numerator := 14875454421039382423142400 }, { target := 344, numerator := 235528028333123555033088000 }, { target := 345, numerator := 402133117848764638172282880 }, { target := 346, numerator := 14875454421039382423142400 }, { target := 347, numerator := 402133117848764638172282880 }, { target := 348, numerator := 402133117848764638172282880 }, { target := 349, numerator := 264783088694501007131934720 }, { target := 350, numerator := 14875454421039382423142400 }, { target := 372, numerator := 494290099761965764517560320 }, { target := 373, numerator := 8798363775762990608412573696 }, { target := 374, numerator := 494290099761965764517560320 }, { target := 375, numerator := 7826259912897791271528038400 }, { target := 376, numerator := 13362309030231807834124713984 }, { target := 377, numerator := 494290099761965764517560320 }, { target := 378, numerator := 13362309030231807834124713984 }, { target := 379, numerator := 13362309030231807834124713984 }, { target := 380, numerator := 8798363775762990608412573696 }, { target := 381, numerator := 494290099761965764517560320 }, { target := 386, numerator := 273283348363666368516587520 }, { target := 387, numerator := 4864443600873261359595257856 }, { target := 388, numerator := 273283348363666368516587520 }, { target := 389, numerator := 4326986349091384168179302400 }, { target := 390, numerator := 7387759850764447495565082624 }, { target := 391, numerator := 273283348363666368516587520 }, { target := 392, numerator := 7387759850764447495565082624 }, { target := 393, numerator := 7387759850764447495565082624 }, { target := 394, numerator := 4864443600873261359595257856 }, { target := 395, numerator := 273283348363666368516587520 }, { target := 406, numerator := 20400623205996867323166720 }, { target := 407, numerator := 363131093066744238352367616 }, { target := 408, numerator := 20400623205996867323166720 }, { target := 409, numerator := 323009867428283732616806400 }, { target := 410, numerator := 551496847335448646636273664 }, { target := 411, numerator := 20400623205996867323166720 }, { target := 412, numerator := 551496847335448646636273664 }, { target := 413, numerator := 551496847335448646636273664 }, { target := 414, numerator := 363131093066744238352367616 }, { target := 415, numerator := 20400623205996867323166720 }]

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
    Slot2.Left13.expected,
    Slot2.Left14.expected,
    Slot2.Left15.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left6.expected,
    Slot3.Left14.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left3.expected,
    Slot4.Left11.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 111675815677296301884470984704 }, { target := 89, numerator := 399512857160071875219054133248 }, { target := 91, numerator := 111675778551681933621577383936 }, { target := 122, numerator := 20931008713970647220875165696 }, { target := 124, numerator := 20931008713970647220875165696 }, { target := 161, numerator := 3908375117543653087524696358912 }, { target := 164, numerator := 13981953931504962917989135417344 }, { target := 166, numerator := 3908373818239712118514812715008 }, { target := 197, numerator := 2194578513180217463236663967744 }, { target := 199, numerator := 2194578513180217463236663967744 }, { target := 215, numerator := 27117197830917535014154403840 }, { target := 232, numerator := 3908377034453544429889114865664 }, { target := 235, numerator := 13981960789123534709484335136768 }, { target := 237, numerator := 3908375735148966201531958296576 }, { target := 242, numerator := 23655362893439413278707023872000 }, { target := 244, numerator := 23655362893439413278707023872000 }, { target := 260, numerator := 2270499515082748255198620155904 }, { target := 406, numerator := 111674857222350630702261731328 }, { target := 409, numerator := 399509428350785979471454273536 }, { target := 411, numerator := 111674820097054892113004593152 }, { target := 416, numerator := 2194580187259135640525892222976 }, { target := 418, numerator := 2194580187259135640525892222976 }, { target := 420, numerator := 2270500336774516274516887339008 }, { target := 443, numerator := 15725480387955918561607680 }, { target := 444, numerator := 279913550905615350396616704 }, { target := 445, numerator := 15725480387955918561607680 }, { target := 446, numerator := 248986772809302043892121600 }, { target := 447, numerator := 425112153154408331782127616 }, { target := 448, numerator := 15725480387955918561607680 }, { target := 449, numerator := 425112153154408331782127616 }, { target := 450, numerator := 425112153154408331782127616 }, { target := 451, numerator := 279913550905615350396616704 }, { target := 452, numerator := 15725480387955918561607680 }, { target := 457, numerator := 14875454421039382423142400 }, { target := 458, numerator := 264783088694501007131934720 }, { target := 459, numerator := 14875454421039382423142400 }, { target := 460, numerator := 235528028333123555033088000 }, { target := 461, numerator := 402133117848764638172282880 }, { target := 462, numerator := 14875454421039382423142400 }, { target := 463, numerator := 402133117848764638172282880 }, { target := 464, numerator := 402133117848764638172282880 }, { target := 465, numerator := 264783088694501007131934720 }, { target := 466, numerator := 14875454421039382423142400 }, { target := 477, numerator := 19975610222538599253934080 }, { target := 478, numerator := 355565861961187066720026624 }, { target := 479, numerator := 19975610222538599253934080 }, { target := 480, numerator := 316280495190194488187289600 }, { target := 481, numerator := 540007329682626799831351296 }, { target := 482, numerator := 19975610222538599253934080 }, { target := 483, numerator := 540007329682626799831351296 }, { target := 484, numerator := 540007329682626799831351296 }, { target := 485, numerator := 355565861961187066720026624 }, { target := 486, numerator := 19975610222538599253934080 }, { target := 498, numerator := 20931008713970647220875165696 }, { target := 500, numerator := 20931008713970647220875165696 }, { target := 502, numerator := 27116376139149515695887220736 }]

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
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
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
  [{ target := 35, numerator := 6510583523198367870002135040 }, { target := 36, numerator := 7731317933798061845627535360 }, { target := 37, numerator := 5900216317898520882189434880 }, { target := 38, numerator := 60833264794884749785332449280 }, { target := 39, numerator := 7324406463598163853752401920 }, { target := 40, numerator := 5900216317898520882189434880 }, { target := 41, numerator := 7324406463598163853752401920 }, { target := 42, numerator := 7324406463598163853752401920 }, { target := 43, numerator := 313728743524121351735727882240 }, { target := 44, numerator := 7324406463598163853752401920 }, { target := 45, numerator := 60833264794884749785332449280 }, { target := 46, numerator := 313728743524121351735727882240 }, { target := 47, numerator := 6510583523198367870002135040 }, { target := 48, numerator := 7324406463598163853752401920 }, { target := 49, numerator := 7324406463598163853752401920 }, { target := 50, numerator := 7731317933798061845627535360 }, { target := 122, numerator := 83054720599483845872912957440 }, { target := 124, numerator := 83054680995916342086781108224 }, { target := 145, numerator := 22260126176165426497509654528 }, { target := 146, numerator := 26433899834196443965792714752 }, { target := 147, numerator := 20173239347149917763368124416 }, { target := 148, numerator := 207993053958545703836105834496 }, { target := 149, numerator := 25042641948186104809698361344 }, { target := 150, numerator := 20173239347149917763368124416 }, { target := 151, numerator := 25042641948186104809698361344 }, { target := 152, numerator := 25042641948186104809698361344 }, { target := 153, numerator := 1072659830113971489348746477568 }, { target := 154, numerator := 25042641948186104809698361344 }, { target := 155, numerator := 207993053958545703836105834496 }, { target := 156, numerator := 1072659830113971489348746477568 }, { target := 157, numerator := 22260126176165426497509654528 }, { target := 158, numerator := 25042641948186104809698361344 }, { target := 159, numerator := 25042641948186104809698361344 }, { target := 160, numerator := 26433899834196443965792714752 }, { target := 197, numerator := 12266747591023657255504487383040 }, { target := 199, numerator := 12266741741783990124164608425984 }, { target := 215, numerator := 52608192095061113263230025728 }, { target := 216, numerator := 6510581420269543467113250816 }, { target := 217, numerator := 7731315436570082867196985344 }, { target := 218, numerator := 5900214412119273767071383552 }, { target := 219, numerator := 60833245145643546770839437312 }, { target := 220, numerator := 7324404097803236400502407168 }, { target := 221, numerator := 5900214412119273767071383552 }, { target := 222, numerator := 7324404097803236400502407168 }, { target := 223, numerator := 7324404097803236400502407168 }, { target := 224, numerator := 313728642189238625821519773696 }, { target := 225, numerator := 7324404097803236400502407168 }, { target := 226, numerator := 60833245145643546770839437312 }, { target := 227, numerator := 313728642189238625821519773696 }, { target := 228, numerator := 6510581420269543467113250816 }, { target := 229, numerator := 7324404097803236400502407168 }, { target := 230, numerator := 7324404097803236400502407168 }, { target := 231, numerator := 7731315436570082867196985344 }, { target := 242, numerator := 127854258669636350895621511577600 }, { target := 244, numerator := 127854197703989518041858661416960 }, { target := 260, numerator := 4423782989960873960772003168256 }, { target := 416, numerator := 12266747591023657255504487383040 }, { target := 418, numerator := 12266741741783990124164608425984 }, { target := 420, numerator := 4423781922706048832232184872960 }, { target := 498, numerator := 83054720599483845872912957440 }, { target := 500, numerator := 83054680995916342086781108224 }, { target := 502, numerator := 52609259349886241803048321024 }]

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
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 5561058770227294203648409600 }, { target := 17, numerator := 93425787339818542621293281280 }, { target := 18, numerator := 202422539236273509012802109440 }, { target := 19, numerator := 6673270524272753044378091520 }, { target := 20, numerator := 106772328388364048710049464320 }, { target := 21, numerator := 7785482278318211885107773440 }, { target := 22, numerator := 202422539236273509012802109440 }, { target := 23, numerator := 202422539236273509012802109440 }, { target := 24, numerator := 106772328388364048710049464320 }, { target := 25, numerator := 2498027599586100556278865592320 }, { target := 26, numerator := 200198115728182591331342745600 }, { target := 27, numerator := 93425787339818542621293281280 }, { target := 28, numerator := 202422539236273509012802109440 }, { target := 29, numerator := 7785482278318211885107773440 }, { target := 30, numerator := 200198115728182591331342745600 }, { target := 31, numerator := 7785482278318211885107773440 }, { target := 32, numerator := 202422539236273509012802109440 }, { target := 33, numerator := 202422539236273509012802109440 }, { target := 34, numerator := 6673270524272753044378091520 }, { target := 35, numerator := 475542715000685629328572022784 }, { target := 37, numerator := 17561159807048035142531253534720 }, { target := 40, numerator := 17561155506763048158106478444544 }, { target := 47, numerator := 475547015285672613753347112960 }, { target := 86, numerator := 1946815719050137371530741415936 }, { target := 89, numerator := 7080988425428068561816827985920 }, { target := 91, numerator := 1946815719050137371530741415936 }, { target := 126, numerator := 5561058770227294203648409600 }, { target := 127, numerator := 93425787339818542621293281280 }, { target := 128, numerator := 202422539236273509012802109440 }, { target := 129, numerator := 6673270524272753044378091520 }, { target := 130, numerator := 106772328388364048710049464320 }, { target := 131, numerator := 7785482278318211885107773440 }, { target := 132, numerator := 202422539236273509012802109440 }, { target := 133, numerator := 202422539236273509012802109440 }, { target := 134, numerator := 106772328388364048710049464320 }, { target := 135, numerator := 2498027599586100556278865592320 }, { target := 136, numerator := 200198115728182591331342745600 }, { target := 137, numerator := 93425787339818542621293281280 }, { target := 138, numerator := 202422539236273509012802109440 }, { target := 139, numerator := 7785482278318211885107773440 }, { target := 140, numerator := 200198115728182591331342745600 }, { target := 141, numerator := 7785482278318211885107773440 }, { target := 142, numerator := 202422539236273509012802109440 }, { target := 143, numerator := 202422539236273509012802109440 }, { target := 144, numerator := 6673270524272753044378091520 }, { target := 145, numerator := 1611961373593880543039003295744 }, { target := 147, numerator := 59527588987311020140519772651520 }, { target := 150, numerator := 59527574410506296185150614011904 }, { target := 157, numerator := 1611975950398604498408161935360 }, { target := 161, numerator := 70553246056661651685905019174912 }, { target := 164, numerator := 256617364352980938799608118640640 }, { target := 166, numerator := 70553246056661651685905019174912 }, { target := 215, numerator := 18278958392573193121557381120 }, { target := 216, numerator := 475542715000685629328572022784 }, { target := 218, numerator := 17561159807048035142531253534720 }, { target := 221, numerator := 17561155506763048158106478444544 }, { target := 228, numerator := 475547015285672613753347112960 }, { target := 232, numerator := 70553271984704221696968496250880 }, { target := 235, numerator := 256617458658860810075870173593600 }, { target := 237, numerator := 70553271984704221696968496250880 }, { target := 260, numerator := 14216967638668039094544629760 }, { target := 406, numerator := 1946789791007567360467264339968 }, { target := 409, numerator := 7080894119548197285554773032960 }, { target := 411, numerator := 1946789791007567360467264339968 }]

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
    Slot12.Left2.expected,
    Slot12.Left3.expected,
    Slot12.Left4.expected,
    Slot12.Left5.expected,
    Slot12.Left6.expected,
    Slot12.Left7.expected,
    Slot12.Left8.expected,
    Slot12.Left9.expected,
    Slot12.Left10.expected,
    Slot12.Left11.expected,
    Slot12.Left12.expected,
    Slot12.Left13.expected,
    Slot12.Left14.expected,
    Slot12.Left15.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 26901432906315220924340633600 }, { target := 17, numerator := 4294738252853163934944015155200 }, { target := 19, numerator := 42855029332291074989336245043200 }, { target := 27, numerator := 4294738252853163934944015155200 }, { target := 34, numerator := 26898363368101355654951731200 }, { target := 35, numerator := 2723635563245265046770297077760 }, { target := 37, numerator := 102333984932458795785034997432320 }, { target := 40, numerator := 102326245196680661306752777584640 }, { target := 47, numerator := 2731375299023399525052516925440 }, { target := 86, numerator := 2727794362689420781850040729600 }, { target := 89, numerator := 9364041090309264265084749742080 }, { target := 91, numerator := 2727794362689420781850040729600 }, { target := 122, numerator := 26984206546026960065646297088 }, { target := 124, numerator := 26984206546026960065646297088 }, { target := 126, numerator := 26901432906315220924340633600 }, { target := 127, numerator := 4294738252853163934944015155200 }, { target := 129, numerator := 42855029332291074989336245043200 }, { target := 137, numerator := 4294738252853163934944015155200 }, { target := 144, numerator := 26898363368101355654951731200 }, { target := 145, numerator := 9349764658986547438069374517248 }, { target := 147, numerator := 351294677102365618922210654683136 }, { target := 150, numerator := 351268107942737643024563434422272 }, { target := 157, numerator := 9376333818614523335716594778112 }, { target := 161, numerator := 102490241711228513546505761587200 }, { target := 164, numerator := 351831079302272062815623247298560 }, { target := 166, numerator := 102490241711228513546505761587200 }, { target := 197, numerator := 4307952832092712131666919817216 }, { target := 199, numerator := 4307952832092712131666919817216 }, { target := 216, numerator := 2723635563245265046770297077760 }, { target := 218, numerator := 102333984932458795785034997432320 }, { target := 221, numerator := 102326245196680661306752777584640 }, { target := 228, numerator := 2731375299023399525052516925440 }, { target := 232, numerator := 102482490157419624004472694374400 }, { target := 235, numerator := 351804469573410895949781396357120 }, { target := 237, numerator := 102482490157419624004472694374400 }, { target := 242, numerator := 42986890961005816758534202720256 }, { target := 244, numerator := 42986890961005816758534202720256 }, { target := 265, numerator := 16247963015620616108051005440 }, { target := 355, numerator := 19091356543354223926959931392 }, { target := 400, numerator := 225440486841736048499207700480 }, { target := 405, numerator := 506936446087363222571191369728 }, { target := 406, numerator := 2735545916498310323883107942400 }, { target := 409, numerator := 9390650819170431130926600683520 }, { target := 411, numerator := 2735545916498310323883107942400 }, { target := 416, numerator := 4307952832092712131666919817216 }, { target := 418, numerator := 4307952832092712131666919817216 }, { target := 420, numerator := 14216967638668039094544629760 }, { target := 425, numerator := 225440486841736048499207700480 }, { target := 426, numerator := 16247963015620616108051005440 }, { target := 471, numerator := 15841763940230100705349730304 }, { target := 476, numerator := 15841763940230100705349730304 }, { target := 491, numerator := 15841763940230100705349730304 }, { target := 496, numerator := 506936446087363222571191369728 }, { target := 497, numerator := 15841763940230100705349730304 }, { target := 498, numerator := 26981127563080129056966967296 }, { target := 500, numerator := 26981127563080129056966967296 }, { target := 502, numerator := 18278958392573193121557381120 }, { target := 503, numerator := 19091356543354223926959931392 }]

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
    Slot18.Left15.expected,
    Slot18.Left16.expected,
    Slot18.Left17.expected,
    Slot18.Left18.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot19.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 19149384982695726127345827840 }, { target := 1, numerator := 14893966097652231432380088320 }, { target := 2, numerator := 17021675540173978779862958080 }, { target := 3, numerator := 20000468759704425066338975744 }, { target := 4, numerator := 236175748119913955570598543360 }, { target := 5, numerator := 531076276853428137931724292096 }, { target := 6, numerator := 14893966097652231432380088320 }, { target := 7, numerator := 236175748119913955570598543360 }, { target := 8, numerator := 17021675540173978779862958080 }, { target := 9, numerator := 16596133651669629310366384128 }, { target := 10, numerator := 16596133651669629310366384128 }, { target := 11, numerator := 16596133651669629310366384128 }, { target := 12, numerator := 531076276853428137931724292096 }, { target := 13, numerator := 16596133651669629310366384128 }, { target := 14, numerator := 19149384982695726127345827840 }, { target := 15, numerator := 20000468759704425066338975744 }, { target := 86, numerator := 473992453501090892150646767616 }, { target := 89, numerator := 1606706405790803507853872070656 }, { target := 91, numerator := 473992453501090892150646767616 }, { target := 122, numerator := 5367630639088953535695421440 }, { target := 124, numerator := 5367630639088953535695421440 }, { target := 161, numerator := 17503910712322532175481436897280 }, { target := 164, numerator := 59333530017507235233786211860480 }, { target := 166, numerator := 17503910712322532175481436897280 }, { target := 197, numerator := 90176194736694419399683080192 }, { target := 199, numerator := 90176194736694419399683080192 }, { target := 211, numerator := 195381755262837908699313340416 }, { target := 213, numerator := 195381755262837908699313340416 }, { target := 232, numerator := 17503906426056404154331070201856 }, { target := 235, numerator := 59333515488222657077782559850496 }, { target := 237, numerator := 17503906426056404154331070201856 }, { target := 242, numerator := 6441156766906744242834505728 }, { target := 244, numerator := 6441156766906744242834505728 }, { target := 256, numerator := 103058508270507907885352091648 }, { target := 258, numerator := 103058508270507907885352091648 }, { target := 261, numerator := 7514682894724534949973590016 }, { target := 263, numerator := 7514682894724534949973590016 }, { target := 337, numerator := 195381755262837908699313340416 }, { target := 339, numerator := 195381755262837908699313340416 }, { target := 351, numerator := 195381755262837908699313340416 }, { target := 353, numerator := 195381755262837908699313340416 }, { target := 382, numerator := 103058508270507907885352091648 }, { target := 384, numerator := 103058508270507907885352091648 }, { target := 396, numerator := 2411139683078757928234383310848 }, { target := 398, numerator := 2411139683078757928234383310848 }, { target := 401, numerator := 193234703007202327285035171840 }, { target := 403, numerator := 193234703007202327285035171840 }, { target := 416, numerator := 90176194736694419399683080192 }, { target := 418, numerator := 90176194736694419399683080192 }, { target := 421, numerator := 195381755262837908699313340416 }, { target := 423, numerator := 195381755262837908699313340416 }, { target := 453, numerator := 7514682894724534949973590016 }, { target := 455, numerator := 7514682894724534949973590016 }, { target := 467, numerator := 193234703007202327285035171840 }, { target := 469, numerator := 193234703007202327285035171840 }, { target := 472, numerator := 7514682894724534949973590016 }, { target := 474, numerator := 7514682894724534949973590016 }, { target := 487, numerator := 195381755262837908699313340416 }, { target := 489, numerator := 195381755262837908699313340416 }, { target := 492, numerator := 195381755262837908699313340416 }, { target := 494, numerator := 195381755262837908699313340416 }, { target := 498, numerator := 6441156766906744242834505728 }, { target := 500, numerator := 6441156766906744242834505728 }]

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
    Slot19.Left12.expected,
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
    Slot23.Left8.expected,
    Slot23.Left9.expected,
    Slot23.Left10.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 55401547427542234321454628864 }, { target := 1, numerator := 4658674122171185852494410416128 }, { target := 6, numerator := 4658672998247962929518849556480 }, { target := 14, numerator := 55402671350765157297015488512 }, { target := 16, numerator := 82903751229399092063224463360 }, { target := 17, numerator := 12244450205114240064959555829760 }, { target := 19, numerator := 127621856745282298842578314854400 }, { target := 27, numerator := 12244450205114240064959555829760 }, { target := 34, numerator := 82903751229399092063224463360 }, { target := 35, numerator := 1938324228562858493783442456576 }, { target := 37, numerator := 70245511630709361841389585825792 }, { target := 40, numerator := 70245537445660731343535949742080 }, { target := 47, numerator := 1938298413611488991637078540288 }, { target := 86, numerator := 6282141996068600576317849600 }, { target := 89, numerator := 21479069117352604515140894720 }, { target := 91, numerator := 6282139966926752468267171840 }, { target := 112, numerator := 7460043620331463184377446400 }, { target := 115, numerator := 25506394576856217861729812480 }, { target := 117, numerator := 7460041210725518556067266560 }, { target := 126, numerator := 82903711697819376520796307456 }, { target := 127, numerator := 12244444366506792531105882832896 }, { target := 129, numerator := 127621795890453312737705711370240 }, { target := 137, numerator := 12244444366506792531105882832896 }, { target := 144, numerator := 82903711697819376520796307456 }, { target := 145, numerator := 7050103044101688501209892126720 }, { target := 147, numerator := 255498067910615508708885780234240 }, { target := 150, numerator := 255498161805158305815579957657600 }, { target := 157, numerator := 7050009149558891394515714703360 }, { target := 161, numerator := 5693191183937169272288051200 }, { target := 164, numerator := 19465406387600797841846435840 }, { target := 166, numerator := 5693189345027369424367124480 }, { target := 187, numerator := 58698764275765986634969907200 }, { target := 190, numerator := 200695052065263398438347735040 }, { target := 192, numerator := 58698745315971843375371386880 }, { target := 201, numerator := 7067409745577175648357580800 }, { target := 204, numerator := 24163952757021680079533506560 }, { target := 206, numerator := 7067407462792596526800568320 }, { target := 216, numerator := 1938324228562858493783442456576 }, { target := 218, numerator := 70245511630709361841389585825792 }, { target := 221, numerator := 70245537445660731343535949742080 }, { target := 228, numerator := 1938298413611488991637078540288 }, { target := 232, numerator := 5693191183937169272288051200 }, { target := 235, numerator := 19465406387600797841846435840 }, { target := 237, numerator := 5693189345027369424367124480 }, { target := 246, numerator := 7067409745577175648357580800 }, { target := 249, numerator := 24163952757021680079533506560 }, { target := 251, numerator := 7067407462792596526800568320 }, { target := 301, numerator := 7067409745577175648357580800 }, { target := 304, numerator := 24163952757021680079533506560 }, { target := 306, numerator := 7067407462792596526800568320 }, { target := 327, numerator := 302720717435555690271316377600 }, { target := 330, numerator := 1035022643092428630073351864320 }, { target := 332, numerator := 302720619656282884564624343040 }, { target := 341, numerator := 7067409745577175648357580800 }, { target := 344, numerator := 24163952757021680079533506560 }, { target := 346, numerator := 7067407462792596526800568320 }, { target := 372, numerator := 58698764275765986634969907200 }, { target := 375, numerator := 200695052065263398438347735040 }, { target := 377, numerator := 58698745315971843375371386880 }, { target := 406, numerator := 473996739767218913301013463040 }, { target := 409, numerator := 1606720935075381663857524080640 }, { target := 411, numerator := 473996739767218913301013463040 }]

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
    Slot23.Left11.expected,
    Slot23.Left12.expected,
    Slot23.Left13.expected,
    Slot23.Left14.expected,
    Slot23.Left15.expected,
    Slot24.Left0.expected,
    Slot24.Left3.expected,
    Slot24.Left5.expected,
    Slot25.Left0.expected,
    Slot25.Left2.expected,
    Slot26.Left0.expected,
    Slot27.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 27584735724554044238536376320 }, { target := 1, numerator := 2309646058446243914771010158592 }, { target := 6, numerator := 2309646894305111382698212982784 }, { target := 14, numerator := 27583899865686576311333552128 }, { target := 16, numerator := 21432880573120860200783314944 }, { target := 17, numerator := 2247198872452521690140787081216 }, { target := 19, numerator := 24222557772407636164092100608000 }, { target := 27, numerator := 2247200586671554971821999652864 }, { target := 34, numerator := 21432880573120860200783314944 }, { target := 35, numerator := 113077365964355786584287608832 }, { target := 36, numerator := 19975610222538599253934080 }, { target := 37, numerator := 3956727637763980215903810748416 }, { target := 38, numerator := 494290099761965764517560320 }, { target := 39, numerator := 15725480387955918561607680 }, { target := 40, numerator := 3956729578381237705611958812672 }, { target := 41, numerator := 16150493371414186630840320 }, { target := 42, numerator := 16150493371414186630840320 }, { target := 43, numerator := 273283348363666368516587520 }, { target := 44, numerator := 14875454421039382423142400 }, { target := 45, numerator := 494290099761965764517560320 }, { target := 46, numerator := 273283348363666368516587520 }, { target := 47, numerator := 113076395655727041730213576704 }, { target := 48, numerator := 15725480387955918561607680 }, { target := 49, numerator := 14875454421039382423142400 }, { target := 50, numerator := 19975610222538599253934080 }, { target := 126, numerator := 21432880573120860200783314944 }, { target := 127, numerator := 2247198872452521690140787081216 }, { target := 129, numerator := 24222557772407636164092100608000 }, { target := 137, numerator := 2247200586671554971821999652864 }, { target := 144, numerator := 21432880573120860200783314944 }, { target := 145, numerator := 404453828891733541520349855744 }, { target := 147, numerator := 14154875623237356452310555820032 }, { target := 150, numerator := 14154882565667465350767710306304 }, { target := 157, numerator := 404450357676679092291772612608 }, { target := 216, numerator := 113056927756384713719370743808 }, { target := 218, numerator := 3956710596910521278991144321024 }, { target := 221, numerator := 3956712537527133628052671561728 }, { target := 228, numerator := 113055957448078539188607123456 }, { target := 386, numerator := 302720717435555690271316377600 }, { target := 389, numerator := 1035022643092428630073351864320 }, { target := 391, numerator := 302720619656282884564624343040 }, { target := 406, numerator := 6282141996068600576317849600 }, { target := 409, numerator := 21479069117352604515140894720 }, { target := 411, numerator := 6282139966926752468267171840 }, { target := 443, numerator := 7067409745577175648357580800 }, { target := 446, numerator := 24163952757021680079533506560 }, { target := 448, numerator := 7067407462792596526800568320 }, { target := 457, numerator := 7067409745577175648357580800 }, { target := 460, numerator := 24163952757021680079533506560 }, { target := 462, numerator := 7067407462792596526800568320 }, { target := 477, numerator := 7460043620331463184377446400 }, { target := 480, numerator := 25506394576856217861729812480 }, { target := 482, numerator := 7460041210725518556067266560 }]

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
    Slot27.Left1.expected,
    Slot27.Left2.expected,
    Slot27.Left3.expected,
    Slot27.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 70, numerator := 363131093066744238352367616 }, { target := 71, numerator := 355565861961187066720026624 }, { target := 72, numerator := 279913550905615350396616704 }, { target := 73, numerator := 8798363775762990608412573696 }, { target := 74, numerator := 279913550905615350396616704 }, { target := 75, numerator := 279913550905615350396616704 }, { target := 76, numerator := 287478782011172522028957696 }, { target := 77, numerator := 287478782011172522028957696 }, { target := 78, numerator := 4864443600873261359595257856 }, { target := 79, numerator := 264783088694501007131934720 }, { target := 80, numerator := 8798363775762990608412573696 }, { target := 81, numerator := 4864443600873261359595257856 }, { target := 82, numerator := 363131093066744238352367616 }, { target := 83, numerator := 279913550905615350396616704 }, { target := 84, numerator := 264783088694501007131934720 }, { target := 85, numerator := 355565861961187066720026624 }, { target := 96, numerator := 20400623205996867323166720 }, { target := 97, numerator := 19975610222538599253934080 }, { target := 98, numerator := 15725480387955918561607680 }, { target := 99, numerator := 494290099761965764517560320 }, { target := 100, numerator := 15725480387955918561607680 }, { target := 101, numerator := 15725480387955918561607680 }, { target := 102, numerator := 16150493371414186630840320 }, { target := 103, numerator := 16150493371414186630840320 }, { target := 104, numerator := 273283348363666368516587520 }, { target := 105, numerator := 14875454421039382423142400 }, { target := 106, numerator := 494290099761965764517560320 }, { target := 107, numerator := 273283348363666368516587520 }, { target := 108, numerator := 20400623205996867323166720 }, { target := 109, numerator := 15725480387955918561607680 }, { target := 110, numerator := 14875454421039382423142400 }, { target := 111, numerator := 19975610222538599253934080 }, { target := 145, numerator := 323009867428283732616806400 }, { target := 146, numerator := 316280495190194488187289600 }, { target := 147, numerator := 248986772809302043892121600 }, { target := 148, numerator := 7826259912897791271528038400 }, { target := 149, numerator := 248986772809302043892121600 }, { target := 150, numerator := 248986772809302043892121600 }, { target := 151, numerator := 255716145047391288321638400 }, { target := 152, numerator := 255716145047391288321638400 }, { target := 153, numerator := 4326986349091384168179302400 }, { target := 154, numerator := 235528028333123555033088000 }, { target := 155, numerator := 7826259912897791271528038400 }, { target := 156, numerator := 4326986349091384168179302400 }, { target := 157, numerator := 323009867428283732616806400 }, { target := 158, numerator := 248986772809302043892121600 }, { target := 159, numerator := 235528028333123555033088000 }, { target := 160, numerator := 316280495190194488187289600 }, { target := 171, numerator := 551496847335448646636273664 }, { target := 172, numerator := 540007329682626799831351296 }, { target := 173, numerator := 425112153154408331782127616 }, { target := 174, numerator := 13362309030231807834124713984 }, { target := 175, numerator := 425112153154408331782127616 }, { target := 176, numerator := 425112153154408331782127616 }, { target := 177, numerator := 436601670807230178587049984 }, { target := 178, numerator := 436601670807230178587049984 }, { target := 179, numerator := 7387759850764447495565082624 }, { target := 180, numerator := 402133117848764638172282880 }, { target := 181, numerator := 13362309030231807834124713984 }, { target := 182, numerator := 7387759850764447495565082624 }, { target := 183, numerator := 551496847335448646636273664 }, { target := 184, numerator := 425112153154408331782127616 }, { target := 185, numerator := 402133117848764638172282880 }, { target := 186, numerator := 540007329682626799831351296 }]

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
    Slot27.Left5.expected,
    Slot27.Left6.expected,
    Slot27.Left7.expected,
    Slot27.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 216, numerator := 20400623205996867323166720 }, { target := 217, numerator := 19975610222538599253934080 }, { target := 218, numerator := 15725480387955918561607680 }, { target := 219, numerator := 494290099761965764517560320 }, { target := 220, numerator := 15725480387955918561607680 }, { target := 221, numerator := 15725480387955918561607680 }, { target := 222, numerator := 16150493371414186630840320 }, { target := 223, numerator := 16150493371414186630840320 }, { target := 224, numerator := 273283348363666368516587520 }, { target := 225, numerator := 14875454421039382423142400 }, { target := 226, numerator := 494290099761965764517560320 }, { target := 227, numerator := 273283348363666368516587520 }, { target := 228, numerator := 20400623205996867323166720 }, { target := 229, numerator := 15725480387955918561607680 }, { target := 230, numerator := 14875454421039382423142400 }, { target := 231, numerator := 19975610222538599253934080 }, { target := 285, numerator := 551496847335448646636273664 }, { target := 286, numerator := 540007329682626799831351296 }, { target := 287, numerator := 425112153154408331782127616 }, { target := 288, numerator := 13362309030231807834124713984 }, { target := 289, numerator := 425112153154408331782127616 }, { target := 290, numerator := 425112153154408331782127616 }, { target := 291, numerator := 436601670807230178587049984 }, { target := 292, numerator := 436601670807230178587049984 }, { target := 293, numerator := 7387759850764447495565082624 }, { target := 294, numerator := 402133117848764638172282880 }, { target := 295, numerator := 13362309030231807834124713984 }, { target := 296, numerator := 7387759850764447495565082624 }, { target := 297, numerator := 551496847335448646636273664 }, { target := 298, numerator := 425112153154408331782127616 }, { target := 299, numerator := 402133117848764638172282880 }, { target := 300, numerator := 540007329682626799831351296 }, { target := 311, numerator := 551496847335448646636273664 }, { target := 312, numerator := 540007329682626799831351296 }, { target := 313, numerator := 425112153154408331782127616 }, { target := 314, numerator := 13362309030231807834124713984 }, { target := 315, numerator := 425112153154408331782127616 }, { target := 316, numerator := 425112153154408331782127616 }, { target := 317, numerator := 436601670807230178587049984 }, { target := 318, numerator := 436601670807230178587049984 }, { target := 319, numerator := 7387759850764447495565082624 }, { target := 320, numerator := 402133117848764638172282880 }, { target := 321, numerator := 13362309030231807834124713984 }, { target := 322, numerator := 7387759850764447495565082624 }, { target := 323, numerator := 551496847335448646636273664 }, { target := 324, numerator := 425112153154408331782127616 }, { target := 325, numerator := 402133117848764638172282880 }, { target := 326, numerator := 540007329682626799831351296 }, { target := 356, numerator := 363131093066744238352367616 }, { target := 357, numerator := 355565861961187066720026624 }, { target := 358, numerator := 279913550905615350396616704 }, { target := 359, numerator := 8798363775762990608412573696 }, { target := 360, numerator := 279913550905615350396616704 }, { target := 361, numerator := 279913550905615350396616704 }, { target := 362, numerator := 287478782011172522028957696 }, { target := 363, numerator := 287478782011172522028957696 }, { target := 364, numerator := 4864443600873261359595257856 }, { target := 365, numerator := 264783088694501007131934720 }, { target := 366, numerator := 8798363775762990608412573696 }, { target := 367, numerator := 4864443600873261359595257856 }, { target := 368, numerator := 363131093066744238352367616 }, { target := 369, numerator := 279913550905615350396616704 }, { target := 370, numerator := 264783088694501007131934720 }, { target := 371, numerator := 355565861961187066720026624 }]

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
    Slot27.Left9.expected,
    Slot28.Left0.expected,
    Slot28.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 580284393415022003858964480 }, { target := 17, numerator := 15474250491067253436239052800 }, { target := 18, numerator := 14797252032083061098403594240 }, { target := 19, numerator := 483570327845851669882470400 }, { target := 20, numerator := 15184108294359742434309570560 }, { target := 21, numerator := 483570327845851669882470400 }, { target := 22, numerator := 14797252032083061098403594240 }, { target := 23, numerator := 8414123704517819055954984960 }, { target := 24, numerator := 15184108294359742434309570560 }, { target := 25, numerator := 237046174710036488576386990080 }, { target := 26, numerator := 9284550294640352061743431680 }, { target := 27, numerator := 15474250491067253436239052800 }, { target := 28, numerator := 14797252032083061098403594240 }, { target := 29, numerator := 483570327845851669882470400 }, { target := 30, numerator := 9284550294640352061743431680 }, { target := 31, numerator := 483570327845851669882470400 }, { target := 32, numerator := 14893966097652231432380088320 }, { target := 33, numerator := 8414123704517819055954984960 }, { target := 34, numerator := 580284393415022003858964480 }, { target := 126, numerator := 580284393415022003858964480 }, { target := 127, numerator := 15474250491067253436239052800 }, { target := 128, numerator := 14797252032083061098403594240 }, { target := 129, numerator := 483570327845851669882470400 }, { target := 130, numerator := 15184108294359742434309570560 }, { target := 131, numerator := 483570327845851669882470400 }, { target := 132, numerator := 14797252032083061098403594240 }, { target := 133, numerator := 8414123704517819055954984960 }, { target := 134, numerator := 15184108294359742434309570560 }, { target := 135, numerator := 237046174710036488576386990080 }, { target := 136, numerator := 9284550294640352061743431680 }, { target := 137, numerator := 15474250491067253436239052800 }, { target := 138, numerator := 14797252032083061098403594240 }, { target := 139, numerator := 483570327845851669882470400 }, { target := 140, numerator := 9284550294640352061743431680 }, { target := 141, numerator := 483570327845851669882470400 }, { target := 142, numerator := 14893966097652231432380088320 }, { target := 143, numerator := 8414123704517819055954984960 }, { target := 144, numerator := 580284393415022003858964480 }, { target := 427, numerator := 20400623205996867323166720 }, { target := 428, numerator := 19975610222538599253934080 }, { target := 429, numerator := 15725480387955918561607680 }, { target := 430, numerator := 494290099761965764517560320 }, { target := 431, numerator := 15725480387955918561607680 }, { target := 432, numerator := 15725480387955918561607680 }, { target := 433, numerator := 16150493371414186630840320 }, { target := 434, numerator := 16150493371414186630840320 }, { target := 435, numerator := 273283348363666368516587520 }, { target := 436, numerator := 14875454421039382423142400 }, { target := 437, numerator := 494290099761965764517560320 }, { target := 438, numerator := 273283348363666368516587520 }, { target := 439, numerator := 20400623205996867323166720 }, { target := 440, numerator := 15725480387955918561607680 }, { target := 441, numerator := 14875454421039382423142400 }, { target := 442, numerator := 19975610222538599253934080 }]

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
  [{ target := 0, numerator := 2030995376952577013506375680 }, { target := 1, numerator := 2089023816294079213892272128 }, { target := 2, numerator := 2030995376952577013506375680 }, { target := 3, numerator := 1798881619586568211962789888 }, { target := 4, numerator := 84199265484519692759935746048 }, { target := 5, numerator := 22921233539893369152429096960 }, { target := 6, numerator := 2089023816294079213892272128 }, { target := 7, numerator := 84199265484519692759935746048 }, { target := 8, numerator := 2030995376952577013506375680 }, { target := 9, numerator := 2030995376952577013506375680 }, { target := 10, numerator := 1740853180245066011576893440 }, { target := 11, numerator := 2030995376952577013506375680 }, { target := 12, numerator := 22921233539893369152429096960 }, { target := 13, numerator := 1740853180245066011576893440 }, { target := 14, numerator := 2030995376952577013506375680 }, { target := 15, numerator := 1798881619586568211962789888 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent2
