import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk2Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 33; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk2.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
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
    Slot2.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 4799428909159071472418816 }, { target := 112, numerator := 159614502158096074604019712 }, { target := 115, numerator := 159614502158096074604019712 }, { target := 122, numerator := 4799389709827914839621632 }, { target := 206, numerator := 38395431273272571779350528 }, { target := 208, numerator := 1276916017264768596832157696 }, { target := 211, numerator := 1276916017264768596832157696 }, { target := 218, numerator := 38395117678623318716973056 }, { target := 241, numerator := 38677750620870164218904576 }, { target := 243, numerator := 1286305105627009542397100032 }, { target := 246, numerator := 1286305105627009542397100032 }, { target := 253, numerator := 38677434720377901942833152 }, { target := 302, numerator := 5364067604354256351526912 }, { target := 304, numerator := 178392678882577965733904384 }, { target := 307, numerator := 178392678882577965733904384 }, { target := 314, numerator := 5364023793337081291341824 }, { target := 337, numerator := 34442960406906277625593856 }, { target := 339, numerator := 1145468780193395358922964992 }, { target := 342, numerator := 1145468780193395358922964992 }, { target := 349, numerator := 34442679094059153554931712 }, { target := 363, numerator := 5364067604354256351526912 }, { target := 365, numerator := 178392678882577965733904384 }, { target := 368, numerator := 178392678882577965733904384 }, { target := 375, numerator := 5364023793337081291341824 }, { target := 473, numerator := 38395431273272571779350528 }, { target := 475, numerator := 1276916017264768596832157696 }, { target := 478, numerator := 1276916017264768596832157696 }, { target := 485, numerator := 38395117678623318716973056 }, { target := 508, numerator := 38677750620870164218904576 }, { target := 510, numerator := 1286305105627009542397100032 }, { target := 513, numerator := 1286305105627009542397100032 }, { target := 520, numerator := 38677434720377901942833152 }, { target := 569, numerator := 34442960406906277625593856 }, { target := 571, numerator := 1145468780193395358922964992 }, { target := 574, numerator := 1145468780193395358922964992 }, { target := 581, numerator := 34442679094059153554931712 }, { target := 604, numerator := 678978030972209817127485440 }, { target := 606, numerator := 22580757511189474083686318080 }, { target := 609, numerator := 22580757511189474083686318080 }, { target := 616, numerator := 678972485419772658193530880 }, { target := 630, numerator := 34442960406906277625593856 }, { target := 632, numerator := 1145468780193395358922964992 }, { target := 635, numerator := 1145468780193395358922964992 }, { target := 642, numerator := 34442679094059153554931712 }, { target := 679, numerator := 38395431273272571779350528 }, { target := 681, numerator := 1276916017264768596832157696 }, { target := 684, numerator := 1276916017264768596832157696 }, { target := 691, numerator := 38395117678623318716973056 }, { target := 705, numerator := 38395431273272571779350528 }, { target := 707, numerator := 1276916017264768596832157696 }, { target := 710, numerator := 1276916017264768596832157696 }, { target := 717, numerator := 38395117678623318716973056 }, { target := 785, numerator := 5364067604354256351526912 }, { target := 787, numerator := 178392678882577965733904384 }, { target := 790, numerator := 178392678882577965733904384 }, { target := 797, numerator := 5364023793337081291341824 }, { target := 820, numerator := 34442960406906277625593856 }, { target := 822, numerator := 1145468780193395358922964992 }, { target := 825, numerator := 1145468780193395358922964992 }, { target := 832, numerator := 34442679094059153554931712 }, { target := 846, numerator := 5364067604354256351526912 }, { target := 848, numerator := 178392678882577965733904384 }, { target := 851, numerator := 178392678882577965733904384 }, { target := 858, numerator := 5364023793337081291341824 }]

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
    Slot2.Left16.expected,
    Slot2.Left17.expected,
    Slot2.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left6.expected,
    Slot10.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 5074503526579395574628352 }, { target := 57, numerator := 249275399087889798521683968 }, { target := 59, numerator := 2782091115384540559809970176 }, { target := 67, numerator := 249275791380690740069793792 }, { target := 74, numerator := 5073718940977512478408704 }, { target := 110, numerator := 11986037053618472374763520 }, { target := 112, numerator := 440971550067030722409922560 }, { target := 115, numerator := 440972036037800138008166400 }, { target := 122, numerator := 11985551082849056776519680 }, { target := 152, numerator := 178184186159840430963818496 }, { target := 153, numerator := 8752961522934538651633188864 }, { target := 155, numerator := 97689288936502817556422197248 }, { target := 163, numerator := 8752975297754697117902831616 }, { target := 170, numerator := 178156636519523498424532992 }, { target := 206, numerator := 405933244684360983951441920 }, { target := 208, numerator := 14934461768425952358705397760 }, { target := 211, numerator := 14934478226884270829758054400 }, { target := 218, numerator := 405916786226042512898785280 }, { target := 257, numerator := 127327329972374529762131968 }, { target := 260, numerator := 410945865561259972919033856 }, { target := 262, numerator := 127075185337318420412104704 }, { target := 283, numerator := 178174683098785592761122816 }, { target := 284, numerator := 8752494703013221505112735744 }, { target := 286, numerator := 97684078893472766949649809408 }, { target := 294, numerator := 8752508477098730282167566336 }, { target := 301, numerator := 178147134927768038651461632 }, { target := 302, numerator := 4405448596817217056921354240 }, { target := 304, numerator := 162078382353459980767298846720 }, { target := 307, numerator := 162078560971232864241503436800 }, { target := 314, numerator := 4405269979044333582716764160 }, { target := 353, numerator := 7453596199407372933623971840 }, { target := 356, numerator := 24056300735860456499215073280 }, { target := 358, numerator := 7438835940993386440839659520 }, { target := 660, numerator := 5083657049756354671017984 }, { target := 661, numerator := 249725048621296429308051456 }, { target := 663, numerator := 2787109524647968615528660992 }, { target := 671, numerator := 249725441621725462306750464 }, { target := 678, numerator := 5082871048898288673619968 }, { target := 679, numerator := 405932619874651930938572800 }, { target := 681, numerator := 14934438781403247063492198400 }, { target := 684, numerator := 14934455239836232786640896000 }, { target := 691, numerator := 405916161441666207789875200 }, { target := 695, numerator := 7456070575206485462014230528 }, { target := 698, numerator := 24064286723666144005378277376 }, { target := 700, numerator := 7441305416818683494881296384 }, { target := 895, numerator := 38677750620870164218904576 }, { target := 897, numerator := 1286305105627009542397100032 }, { target := 900, numerator := 1286305105627009542397100032 }, { target := 907, numerator := 38677434720377901942833152 }, { target := 921, numerator := 38677750620870164218904576 }, { target := 923, numerator := 1286305105627009542397100032 }, { target := 926, numerator := 1286305105627009542397100032 }, { target := 933, numerator := 38677434720377901942833152 }, { target := 966, numerator := 17064973666684397728825344 }, { target := 968, numerator := 609871698985193914119487488 }, { target := 971, numerator := 609872184841965964149915648 }, { target := 978, numerator := 17064446304738181851906048 }, { target := 982, numerator := 124852954173262001371873280 }, { target := 985, numerator := 402959877755572466755829760 }, { target := 987, numerator := 124605709512021366370467840 }]

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
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left3.expected,
    Slot17.Left11.expected,
    Slot17.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 127327329972374529762131968 }, { target := 15, numerator := 7453596199407372933623971840 }, { target := 20, numerator := 7456070575206485462014230528 }, { target := 28, numerator := 124852954173262001371873280 }, { target := 56, numerator := 11986037053618472374763520 }, { target := 57, numerator := 405933244684360983951441920 }, { target := 59, numerator := 4405448596817217056921354240 }, { target := 67, numerator := 405932619874651930938572800 }, { target := 74, numerator := 11983225409927733816852480 }, { target := 110, numerator := 5074503526579395574628352 }, { target := 112, numerator := 178184186159840430963818496 }, { target := 115, numerator := 178174683098785592761122816 }, { target := 122, numerator := 5083657049756354671017984 }, { target := 136, numerator := 410945865561259972919033856 }, { target := 137, numerator := 24056300735860456499215073280 }, { target := 142, numerator := 24064286723666144005378277376 }, { target := 150, numerator := 402959877755572466755829760 }, { target := 152, numerator := 440971550067030722409922560 }, { target := 153, numerator := 14934461768425952358705397760 }, { target := 155, numerator := 162078382353459980767298846720 }, { target := 163, numerator := 14934438781403247063492198400 }, { target := 170, numerator := 440868108464856893950525440 }, { target := 206, numerator := 249275399087889798521683968 }, { target := 208, numerator := 8752961522934538651633188864 }, { target := 211, numerator := 8752494703013221505112735744 }, { target := 218, numerator := 249725048621296429308051456 }, { target := 267, numerator := 127075185337318420412104704 }, { target := 268, numerator := 7438835940993386440839659520 }, { target := 273, numerator := 7441305416818683494881296384 }, { target := 281, numerator := 124605709512021366370467840 }, { target := 283, numerator := 440972036037800138008166400 }, { target := 284, numerator := 14934478226884270829758054400 }, { target := 286, numerator := 162078560971232864241503436800 }, { target := 294, numerator := 14934455239836232786640896000 }, { target := 301, numerator := 440868594321628943980953600 }, { target := 302, numerator := 2782091115384540559809970176 }, { target := 304, numerator := 97689288936502817556422197248 }, { target := 307, numerator := 97684078893472766949649809408 }, { target := 314, numerator := 2787109524647968615528660992 }, { target := 660, numerator := 11985551082849056776519680 }, { target := 661, numerator := 405916786226042512898785280 }, { target := 663, numerator := 4405269979044333582716764160 }, { target := 671, numerator := 405916161441666207789875200 }, { target := 678, numerator := 11982739553155683786424320 }, { target := 679, numerator := 249275791380690740069793792 }, { target := 681, numerator := 8752975297754697117902831616 }, { target := 684, numerator := 8752508477098730282167566336 }, { target := 691, numerator := 249725441621725462306750464 }, { target := 966, numerator := 5073718940977512478408704 }, { target := 968, numerator := 178156636519523498424532992 }, { target := 971, numerator := 178147134927768038651461632 }, { target := 978, numerator := 5082871048898288673619968 }]

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
    Slot23.Left0.expected,
    Slot23.Left2.expected,
    Slot23.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 4799428909159071472418816 }, { target := 57, numerator := 38395431273272571779350528 }, { target := 58, numerator := 38677750620870164218904576 }, { target := 59, numerator := 5364067604354256351526912 }, { target := 60, numerator := 34442960406906277625593856 }, { target := 61, numerator := 5364067604354256351526912 }, { target := 62, numerator := 38395431273272571779350528 }, { target := 63, numerator := 38677750620870164218904576 }, { target := 64, numerator := 34442960406906277625593856 }, { target := 65, numerator := 678978030972209817127485440 }, { target := 66, numerator := 34442960406906277625593856 }, { target := 67, numerator := 38395431273272571779350528 }, { target := 68, numerator := 38395431273272571779350528 }, { target := 69, numerator := 5364067604354256351526912 }, { target := 70, numerator := 34442960406906277625593856 }, { target := 71, numerator := 5364067604354256351526912 }, { target := 72, numerator := 38677750620870164218904576 }, { target := 73, numerator := 38677750620870164218904576 }, { target := 74, numerator := 5081748256756663911972864 }, { target := 152, numerator := 159614502158096074604019712 }, { target := 153, numerator := 1276916017264768596832157696 }, { target := 154, numerator := 1286305105627009542397100032 }, { target := 155, numerator := 178392678882577965733904384 }, { target := 156, numerator := 1145468780193395358922964992 }, { target := 157, numerator := 178392678882577965733904384 }, { target := 158, numerator := 1276916017264768596832157696 }, { target := 159, numerator := 1286305105627009542397100032 }, { target := 160, numerator := 1145468780193395358922964992 }, { target := 161, numerator := 22580757511189474083686318080 }, { target := 162, numerator := 1145468780193395358922964992 }, { target := 163, numerator := 1276916017264768596832157696 }, { target := 164, numerator := 1276916017264768596832157696 }, { target := 165, numerator := 178392678882577965733904384 }, { target := 166, numerator := 1145468780193395358922964992 }, { target := 167, numerator := 178392678882577965733904384 }, { target := 168, numerator := 1286305105627009542397100032 }, { target := 169, numerator := 1286305105627009542397100032 }, { target := 170, numerator := 169003590520337020168962048 }, { target := 283, numerator := 159614502158096074604019712 }, { target := 284, numerator := 1276916017264768596832157696 }, { target := 285, numerator := 1286305105627009542397100032 }, { target := 286, numerator := 178392678882577965733904384 }, { target := 287, numerator := 1145468780193395358922964992 }, { target := 288, numerator := 178392678882577965733904384 }, { target := 289, numerator := 1276916017264768596832157696 }, { target := 290, numerator := 1286305105627009542397100032 }, { target := 291, numerator := 1145468780193395358922964992 }, { target := 292, numerator := 22580757511189474083686318080 }, { target := 293, numerator := 1145468780193395358922964992 }, { target := 294, numerator := 1276916017264768596832157696 }, { target := 295, numerator := 1276916017264768596832157696 }, { target := 296, numerator := 178392678882577965733904384 }, { target := 297, numerator := 1145468780193395358922964992 }, { target := 298, numerator := 178392678882577965733904384 }, { target := 299, numerator := 1286305105627009542397100032 }, { target := 300, numerator := 1286305105627009542397100032 }, { target := 301, numerator := 169003590520337020168962048 }]

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
    Slot23.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 660, numerator := 4799389709827914839621632 }, { target := 661, numerator := 38395117678623318716973056 }, { target := 662, numerator := 38677434720377901942833152 }, { target := 663, numerator := 5364023793337081291341824 }, { target := 664, numerator := 34442679094059153554931712 }, { target := 665, numerator := 5364023793337081291341824 }, { target := 666, numerator := 38395117678623318716973056 }, { target := 667, numerator := 38677434720377901942833152 }, { target := 668, numerator := 34442679094059153554931712 }, { target := 669, numerator := 678972485419772658193530880 }, { target := 670, numerator := 34442679094059153554931712 }, { target := 671, numerator := 38395117678623318716973056 }, { target := 672, numerator := 38395117678623318716973056 }, { target := 673, numerator := 5364023793337081291341824 }, { target := 674, numerator := 34442679094059153554931712 }, { target := 675, numerator := 5364023793337081291341824 }, { target := 676, numerator := 38677434720377901942833152 }, { target := 677, numerator := 38677434720377901942833152 }, { target := 678, numerator := 5081706751582498065481728 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk2.Parent0
