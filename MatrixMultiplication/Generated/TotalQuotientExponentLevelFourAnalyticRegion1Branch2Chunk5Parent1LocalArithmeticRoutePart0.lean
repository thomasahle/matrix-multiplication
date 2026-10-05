import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk5Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 23; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5.Parent1

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
    Slot0.Left16.expected,
    Slot0.Left17.expected,
    Slot0.Left18.expected,
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
    Slot2.Left2.expected,
    Slot2.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 4895161248232011020913082368 }, { target := 38, numerator := 16593274590805645066961420288 }, { target := 40, numerator := 4895161248232011020913082368 }, { target := 61, numerator := 120010404795365431480449761280 }, { target := 64, numerator := 406802860935880330673892884480 }, { target := 66, numerator := 120010404795365431480449761280 }, { target := 71, numerator := 23211375736600880154358579200 }, { target := 73, numerator := 23211375736600880154358579200 }, { target := 75, numerator := 4895161248232011020913082368 }, { target := 78, numerator := 16593274590805645066961420288 }, { target := 80, numerator := 4895161248232011020913082368 }, { target := 85, numerator := 22727805408755028484476108800 }, { target := 87, numerator := 22727805408755028484476108800 }, { target := 89, numerator := 696341272098026404630757376 }, { target := 106, numerator := 100587668229799710332955918336 }, { target := 109, numerator := 340965029494941803472723378176 }, { target := 111, numerator := 100587668229799710332955918336 }, { target := 116, numerator := 17892102130296511785651404800 }, { target := 118, numerator := 17892102130296511785651404800 }, { target := 130, numerator := 562392291284725492073313075200 }, { target := 132, numerator := 562392291284725492073313075200 }, { target := 134, numerator := 18569100589280704123486863360 }, { target := 135, numerator := 17892102130296511785651404800 }, { target := 137, numerator := 17892102130296511785651404800 }, { target := 139, numerator := 17756702438499673318084313088 }, { target := 150, numerator := 17892102130296511785651404800 }, { target := 152, numerator := 17892102130296511785651404800 }, { target := 154, numerator := 580284393415022003858964480 }, { target := 155, numerator := 18375672458142363455533875200 }, { target := 157, numerator := 18375672458142363455533875200 }, { target := 159, numerator := 18220929953231690921171484672 }, { target := 160, numerator := 580284393415022003858964480 }, { target := 187, numerator := 18375672458142363455533875200 }, { target := 189, numerator := 18375672458142363455533875200 }, { target := 201, numerator := 310935720804882623734428467200 }, { target := 203, numerator := 310935720804882623734428467200 }, { target := 205, numerator := 17756702438499673318084313088 }, { target := 206, numerator := 16924961474604808445886464000 }, { target := 208, numerator := 16924961474604808445886464000 }, { target := 210, numerator := 10096948445421382867145981952 }, { target := 221, numerator := 562392291284725492073313075200 }, { target := 223, numerator := 562392291284725492073313075200 }, { target := 225, numerator := 18220929953231690921171484672 }, { target := 226, numerator := 310935720804882623734428467200 }, { target := 228, numerator := 310935720804882623734428467200 }, { target := 230, numerator := 284455409652043786291664388096 }, { target := 231, numerator := 11141460353568422474092118016 }, { target := 232, numerator := 23211375736600880154358579200 }, { target := 234, numerator := 23211375736600880154358579200 }, { target := 236, numerator := 18569100589280704123486863360 }, { target := 237, numerator := 17756702438499673318084313088 }, { target := 248, numerator := 17892102130296511785651404800 }, { target := 250, numerator := 17892102130296511785651404800 }, { target := 252, numerator := 580284393415022003858964480 }, { target := 253, numerator := 16924961474604808445886464000 }, { target := 255, numerator := 16924961474604808445886464000 }, { target := 257, numerator := 11141460353568422474092118016 }, { target := 258, numerator := 580284393415022003858964480 }, { target := 259, numerator := 22727805408755028484476108800 }, { target := 261, numerator := 22727805408755028484476108800 }, { target := 263, numerator := 17872759317182677718856105984 }, { target := 264, numerator := 10096948445421382867145981952 }, { target := 265, numerator := 696341272098026404630757376 }]

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
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot4.Left0.expected,
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
  [{ target := 0, numerator := 215670477272656696909496320 }, { target := 1, numerator := 31853400847581988288326533120 }, { target := 3, numerator := 332002669921612397997247692800 }, { target := 11, numerator := 31853400847581988288326533120 }, { target := 18, numerator := 215670477272656696909496320 }, { target := 19, numerator := 3460535631835917966324531200 }, { target := 21, numerator := 125410956739083552057353830400 }, { target := 24, numerator := 125411002827120698716061696000 }, { target := 31, numerator := 3460489543798771307616665600 }, { target := 35, numerator := 294074232125326172677891686400 }, { target := 38, numerator := 1005459723993048605172149780480 }, { target := 40, numerator := 294074137138881862891533762560 }, { target := 45, numerator := 3436902705569721453383778304 }, { target := 47, numerator := 124554491668670298531108487168 }, { target := 50, numerator := 124554537441959874432147128320 }, { target := 57, numerator := 3436856932280145552345137152 }, { target := 71, numerator := 19262531545007699209381478400 }, { target := 73, numerator := 19253821456081971948531220480 }, { target := 89, numerator := 295218740676595870534205440 }, { target := 90, numerator := 3460535631835917966324531200 }, { target := 92, numerator := 125410956739083552057353830400 }, { target := 95, numerator := 125411002827120698716061696000 }, { target := 102, numerator := 3460489543798771307616665600 }, { target := 106, numerator := 1005459723993048605172149780480 }, { target := 109, numerator := 3437734919057237632651242766336 }, { target := 111, numerator := 1005459399227959911181075873792 }, { target := 116, numerator := 674140578556018338483614515200 }, { target := 118, numerator := 673835747159690997807909437440 }, { target := 120, numerator := 98850675528814158035212566528 }, { target := 123, numerator := 335077093349817219739285454848 }, { target := 125, numerator := 98850675528814158035212566528 }, { target := 134, numerator := 30953152513120133473013596160 }, { target := 140, numerator := 298969298387113873912446844928 }, { target := 143, numerator := 1022052673818765556248037294080 }, { target := 145, numerator := 298969203400700244898550382592 }, { target := 150, numerator := 674140909196426263673595494400 }, { target := 152, numerator := 673836077650590674368258375680 }, { target := 154, numerator := 333644046451895814932398080000 }, { target := 161, numerator := 3470664028807145043299139584 }, { target := 163, numerator := 125778013197832089282887548928 }, { target := 166, numerator := 125778059420761051980596510720 }, { target := 173, numerator := 3470617805878182345590177792 }, { target := 177, numerator := 99008583956176480971371053056 }, { target := 180, numerator := 335612360272101272805961629696 }, { target := 182, numerator := 99008583956176480971371053056 }, { target := 191, numerator := 88744536177625490121069428736 }, { target := 194, numerator := 300820010323637823472010264576 }, { target := 196, numerator := 88744536177625490121069428736 }, { target := 211, numerator := 120010404795365431480449761280 }, { target := 214, numerator := 406802860935880330673892884480 }, { target := 216, numerator := 120010404795365431480449761280 }, { target := 232, numerator := 19262366224803736614390988800 }, { target := 234, numerator := 19253656210632133668356751360 }, { target := 236, numerator := 30953176124952547821239664640 }, { target := 238, numerator := 4895161248232011020913082368 }, { target := 241, numerator := 16593274590805645066961420288 }, { target := 243, numerator := 4895161248232011020913082368 }, { target := 265, numerator := 295218740676595870534205440 }]

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
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot9.Left0.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 295218740676595870534205440 }, { target := 1, numerator := 30953152513120133473013596160 }, { target := 3, numerator := 333644046451895814932398080000 }, { target := 11, numerator := 30953176124952547821239664640 }, { target := 18, numerator := 295218740676595870534205440 }, { target := 19, numerator := 19812889589150776329649520640 }, { target := 21, numerator := 693401737943333148154574929920 }, { target := 24, numerator := 693402078030609871207126794240 }, { target := 31, numerator := 19812719545512414803373588480 }, { target := 35, numerator := 4783907583499465315892330496 }, { target := 36, numerator := 117282895595470762583166812160 }, { target := 37, numerator := 4783907583499465315892330496 }, { target := 38, numerator := 98301584860940626007206920192 }, { target := 39, numerator := 96604069266795654443503190016 }, { target := 40, numerator := 4783907583499465315892330496 }, { target := 41, numerator := 96758388866263379131112620032 }, { target := 42, numerator := 86727614900861274436499668992 }, { target := 43, numerator := 117282895595470762583166812160 }, { target := 44, numerator := 4783907583499465315892330496 }, { target := 71, numerator := 3726730680438680886811033600 }, { target := 72, numerator := 3701279836767392334413299712 }, { target := 73, numerator := 3726730680438680886811033600 }, { target := 74, numerator := 3737638184869233123552919552 }, { target := 89, numerator := 215670477272656696909496320 }, { target := 90, numerator := 19803930640541456861346398208 }, { target := 92, numerator := 693088197078539312030992564224 }, { target := 95, numerator := 693088537012036122207351472128 }, { target := 102, numerator := 19803760673793051773166944256 }, { target := 106, numerator := 16216154713741880406348660736 }, { target := 107, numerator := 397557341369155777704031682560 }, { target := 108, numerator := 16216154713741880406348660736 }, { target := 109, numerator := 333215824279147671575616028672 }, { target := 110, numerator := 327461704864594101108847149056 }, { target := 111, numerator := 16216154713741880406348660736 }, { target := 112, numerator := 327984806629553516605826138112 }, { target := 113, numerator := 293983191907191509302191849472 }, { target := 114, numerator := 397557341369155777704031682560 }, { target := 115, numerator := 16216154713741880406348660736 }, { target := 116, numerator := 135057953411320748369457971200 }, { target := 117, numerator := 134135606412414167648886063104 }, { target := 118, numerator := 135057953411320748369457971200 }, { target := 119, numerator := 135453244982280711535417360384 }, { target := 134, numerator := 31853400847581988288326533120 }, { target := 140, numerator := 4783907583499465315892330496 }, { target := 141, numerator := 117282895595470762583166812160 }, { target := 142, numerator := 4783907583499465315892330496 }, { target := 143, numerator := 98301584860940626007206920192 }, { target := 144, numerator := 96604069266795654443503190016 }, { target := 145, numerator := 4783907583499465315892330496 }, { target := 146, numerator := 96758388866263379131112620032 }, { target := 147, numerator := 86727614900861274436499668992 }, { target := 148, numerator := 117282895595470762583166812160 }, { target := 149, numerator := 4783907583499465315892330496 }, { target := 150, numerator := 135058003044591521694220288000 }, { target := 151, numerator := 134135655706726018619235368960 }, { target := 152, numerator := 135058003044591521694220288000 }, { target := 153, numerator := 135453294760819594440642396160 }, { target := 154, numerator := 332002669921612397997247692800 }, { target := 232, numerator := 3726681047167907562048716800 }, { target := 233, numerator := 3701230542455541364063993856 }, { target := 234, numerator := 3726681047167907562048716800 }, { target := 235, numerator := 3737588406330350218327883776 }, { target := 236, numerator := 31853400847581988288326533120 }, { target := 265, numerator := 215670477272656696909496320 }]

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
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 696341272098026404630757376 }, { target := 1, numerator := 18569100589280704123486863360 }, { target := 2, numerator := 17756702438499673318084313088 }, { target := 3, numerator := 580284393415022003858964480 }, { target := 4, numerator := 18220929953231690921171484672 }, { target := 5, numerator := 580284393415022003858964480 }, { target := 6, numerator := 17756702438499673318084313088 }, { target := 7, numerator := 10096948445421382867145981952 }, { target := 8, numerator := 18220929953231690921171484672 }, { target := 9, numerator := 284455409652043786291664388096 }, { target := 10, numerator := 11141460353568422474092118016 }, { target := 11, numerator := 18569100589280704123486863360 }, { target := 12, numerator := 17756702438499673318084313088 }, { target := 13, numerator := 580284393415022003858964480 }, { target := 14, numerator := 11141460353568422474092118016 }, { target := 15, numerator := 580284393415022003858964480 }, { target := 16, numerator := 17872759317182677718856105984 }, { target := 17, numerator := 10096948445421382867145981952 }, { target := 18, numerator := 696341272098026404630757376 }, { target := 19, numerator := 23211375736600880154358579200 }, { target := 20, numerator := 22727805408755028484476108800 }, { target := 21, numerator := 17892102130296511785651404800 }, { target := 22, numerator := 562392291284725492073313075200 }, { target := 23, numerator := 17892102130296511785651404800 }, { target := 24, numerator := 17892102130296511785651404800 }, { target := 25, numerator := 18375672458142363455533875200 }, { target := 26, numerator := 18375672458142363455533875200 }, { target := 27, numerator := 310935720804882623734428467200 }, { target := 28, numerator := 16924961474604808445886464000 }, { target := 29, numerator := 562392291284725492073313075200 }, { target := 30, numerator := 310935720804882623734428467200 }, { target := 31, numerator := 23211375736600880154358579200 }, { target := 32, numerator := 17892102130296511785651404800 }, { target := 33, numerator := 16924961474604808445886464000 }, { target := 34, numerator := 22727805408755028484476108800 }, { target := 90, numerator := 23211375736600880154358579200 }, { target := 91, numerator := 22727805408755028484476108800 }, { target := 92, numerator := 17892102130296511785651404800 }, { target := 93, numerator := 562392291284725492073313075200 }, { target := 94, numerator := 17892102130296511785651404800 }, { target := 95, numerator := 17892102130296511785651404800 }, { target := 96, numerator := 18375672458142363455533875200 }, { target := 97, numerator := 18375672458142363455533875200 }, { target := 98, numerator := 310935720804882623734428467200 }, { target := 99, numerator := 16924961474604808445886464000 }, { target := 100, numerator := 562392291284725492073313075200 }, { target := 101, numerator := 310935720804882623734428467200 }, { target := 102, numerator := 23211375736600880154358579200 }, { target := 103, numerator := 17892102130296511785651404800 }, { target := 104, numerator := 16924961474604808445886464000 }, { target := 105, numerator := 22727805408755028484476108800 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5.Parent1
