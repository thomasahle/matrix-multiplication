import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk12Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 50; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent0

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
    Slot1.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 411, numerator := 161693828373456652116951040 }, { target := 412, numerator := 192011421193479774388879360 }, { target := 413, numerator := 146535031963445090980986880 }, { target := 414, numerator := 1510826708864485593217761280 }, { target := 415, numerator := 181905556920138733631569920 }, { target := 416, numerator := 146535031963445090980986880 }, { target := 417, numerator := 181905556920138733631569920 }, { target := 418, numerator := 181905556920138733631569920 }, { target := 419, numerator := 7791621354745942423885578240 }, { target := 420, numerator := 181905556920138733631569920 }, { target := 421, numerator := 1510826708864485593217761280 }, { target := 422, numerator := 7791621354745942423885578240 }, { target := 423, numerator := 161693828373456652116951040 }, { target := 424, numerator := 181905556920138733631569920 }, { target := 425, numerator := 181905556920138733631569920 }, { target := 426, numerator := 192011421193479774388879360 }, { target := 627, numerator := 147791181447888416607830016 }, { target := 628, numerator := 175502027969367494721798144 }, { target := 629, numerator := 133935758187148877550845952 }, { target := 630, numerator := 1380923851653707392679411712 }, { target := 631, numerator := 166265079128874468683808768 }, { target := 632, numerator := 133935758187148877550845952 }, { target := 633, numerator := 166265079128874468683808768 }, { target := 634, numerator := 166265079128874468683808768 }, { target := 635, numerator := 7121687556020123075289808896 }, { target := 636, numerator := 166265079128874468683808768 }, { target := 637, numerator := 1380923851653707392679411712 }, { target := 638, numerator := 7121687556020123075289808896 }, { target := 639, numerator := 147791181447888416607830016 }, { target := 640, numerator := 166265079128874468683808768 }, { target := 641, numerator := 166265079128874468683808768 }, { target := 642, numerator := 175502027969367494721798144 }, { target := 723, numerator := 161693828373456652116951040 }, { target := 724, numerator := 192011421193479774388879360 }, { target := 725, numerator := 146535031963445090980986880 }, { target := 726, numerator := 1510826708864485593217761280 }, { target := 727, numerator := 181905556920138733631569920 }, { target := 728, numerator := 146535031963445090980986880 }, { target := 729, numerator := 181905556920138733631569920 }, { target := 730, numerator := 181905556920138733631569920 }, { target := 731, numerator := 7791621354745942423885578240 }, { target := 732, numerator := 181905556920138733631569920 }, { target := 733, numerator := 1510826708864485593217761280 }, { target := 734, numerator := 7791621354745942423885578240 }, { target := 735, numerator := 161693828373456652116951040 }, { target := 736, numerator := 181905556920138733631569920 }, { target := 737, numerator := 181905556920138733631569920 }, { target := 738, numerator := 192011421193479774388879360 }, { target := 774, numerator := 14205128665895484893993893888 }, { target := 777, numerator := 50817909904839850675201376256 }, { target := 779, numerator := 14205123943529002024348680192 }]

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
    Slot1.Left3.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot3.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 142, numerator := 82760106719118066135859200 }, { target := 143, numerator := 1390369792881183511082434560 }, { target := 144, numerator := 3012467884575897607345274880 }, { target := 145, numerator := 99312128062941679363031040 }, { target := 146, numerator := 1588994049007066869808496640 }, { target := 147, numerator := 115864149406765292590202880 }, { target := 148, numerator := 3012467884575897607345274880 }, { target := 149, numerator := 3012467884575897607345274880 }, { target := 150, numerator := 1588994049007066869808496640 }, { target := 151, numerator := 37175839938227835308227952640 }, { target := 152, numerator := 2979363841888250380890931200 }, { target := 153, numerator := 1390369792881183511082434560 }, { target := 154, numerator := 3012467884575897607345274880 }, { target := 155, numerator := 115864149406765292590202880 }, { target := 156, numerator := 2979363841888250380890931200 }, { target := 157, numerator := 115864149406765292590202880 }, { target := 158, numerator := 3012467884575897607345274880 }, { target := 159, numerator := 3012467884575897607345274880 }, { target := 160, numerator := 99312128062941679363031040 }, { target := 411, numerator := 1044436350283313692622716928 }, { target := 413, numerator := 38569644906848855104149258240 }, { target := 416, numerator := 38569635462115889364858830848 }, { target := 423, numerator := 1044445795016279431913144320 }, { target := 627, numerator := 1044436350283313692622716928 }, { target := 629, numerator := 38569644906848855104149258240 }, { target := 632, numerator := 38569635462115889364858830848 }, { target := 639, numerator := 1044445795016279431913144320 }, { target := 723, numerator := 1044436350283313692622716928 }, { target := 725, numerator := 38569644906848855104149258240 }, { target := 728, numerator := 38569635462115889364858830848 }, { target := 735, numerator := 1044445795016279431913144320 }, { target := 758, numerator := 1192227531731202109230546944 }, { target := 759, numerator := 175502027969367494721798144 }, { target := 760, numerator := 38703580665036003981700104192 }, { target := 761, numerator := 1380923851653707392679411712 }, { target := 762, numerator := 166265079128874468683808768 }, { target := 763, numerator := 38703571220303038242409676800 }, { target := 764, numerator := 166265079128874468683808768 }, { target := 765, numerator := 166265079128874468683808768 }, { target := 766, numerator := 7121687556020123075289808896 }, { target := 767, numerator := 166265079128874468683808768 }, { target := 768, numerator := 1380923851653707392679411712 }, { target := 769, numerator := 7121687556020123075289808896 }, { target := 770, numerator := 1192236976464167848520974336 }, { target := 771, numerator := 166265079128874468683808768 }, { target := 772, numerator := 166265079128874468683808768 }, { target := 773, numerator := 175502027969367494721798144 }]

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
    Slot3.Left2.expected,
    Slot3.Left7.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot4.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 142, numerator := 8457218803555378573344768 }, { target := 143, numerator := 1350171243103252033333886976 }, { target := 145, numerator := 13472678617460798439781564416 }, { target := 153, numerator := 1350171243103252033333886976 }, { target := 160, numerator := 8456253808256022642425856 }, { target := 282, numerator := 202427624265744867787800576 }, { target := 283, numerator := 32317002012342355120443359232 }, { target := 285, numerator := 322475081746964917494126477312 }, { target := 293, numerator := 32317002012342355120443359232 }, { target := 300, numerator := 202404526636321574215483392 }, { target := 357, numerator := 953031940188087694854717440 }, { target := 358, numerator := 37639644072513245166541209600 }, { target := 359, numerator := 29178984098026206352753295360 }, { target := 360, numerator := 242166352036857164974113423360 }, { target := 361, numerator := 15391112491266570383869870080 }, { target := 362, numerator := 1122268619154854090490511360 }, { target := 363, numerator := 29178984098026206352753295360 }, { target := 364, numerator := 29178984098026206352753295360 }, { target := 365, numerator := 15391112491266570383869870080 }, { target := 366, numerator := 360087902660257469605955502080 }, { target := 367, numerator := 28858335921124819469756006400 }, { target := 368, numerator := 37639644072513245166541209600 }, { target := 369, numerator := 29178984098026206352753295360 }, { target := 370, numerator := 1122268619154854090490511360 }, { target := 371, numerator := 28858335921124819469756006400 }, { target := 372, numerator := 1122268619154854090490511360 }, { target := 373, numerator := 29178984098026206352753295360 }, { target := 374, numerator := 29178984098026206352753295360 }, { target := 375, numerator := 1113338752110034602751426560 }, { target := 392, numerator := 175691900306118187136581632 }, { target := 393, numerator := 28048718727693364821516877824 }, { target := 395, numerator := 279884033214346909523204112384 }, { target := 403, numerator := 28048718727693364821516877824 }, { target := 410, numerator := 175671853306996083281362944 }, { target := 498, numerator := 8457218803555378573344768 }, { target := 499, numerator := 1350171243103252033333886976 }, { target := 501, numerator := 13472678617460798439781564416 }, { target := 509, numerator := 1350171243103252033333886976 }, { target := 516, numerator := 8456253808256022642425856 }, { target := 669, numerator := 82760106719118066135859200 }, { target := 670, numerator := 1390369792881183511082434560 }, { target := 671, numerator := 3012467884575897607345274880 }, { target := 672, numerator := 99312128062941679363031040 }, { target := 673, numerator := 1588994049007066869808496640 }, { target := 674, numerator := 115864149406765292590202880 }, { target := 675, numerator := 3012467884575897607345274880 }, { target := 676, numerator := 3012467884575897607345274880 }, { target := 677, numerator := 1588994049007066869808496640 }, { target := 678, numerator := 37175839938227835308227952640 }, { target := 679, numerator := 2979363841888250380890931200 }, { target := 680, numerator := 1390369792881183511082434560 }, { target := 681, numerator := 3012467884575897607345274880 }, { target := 682, numerator := 115864149406765292590202880 }, { target := 683, numerator := 2979363841888250380890931200 }, { target := 684, numerator := 115864149406765292590202880 }, { target := 685, numerator := 3012467884575897607345274880 }, { target := 686, numerator := 3012467884575897607345274880 }, { target := 687, numerator := 99312128062941679363031040 }]

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
    Slot4.Left5.expected,
    Slot4.Left6.expected,
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 55, numerator := 265968891520419241383690240 }, { target := 56, numerator := 206864693404770521076203520 }, { target := 57, numerator := 236416792462594881229946880 }, { target := 58, numerator := 277789731143548985445187584 }, { target := 59, numerator := 3280282995418503977065512960 }, { target := 60, numerator := 7376203924832960294374342656 }, { target := 61, numerator := 206864693404770521076203520 }, { target := 62, numerator := 3280282995418503977065512960 }, { target := 63, numerator := 236416792462594881229946880 }, { target := 64, numerator := 230506372651030009199198208 }, { target := 65, numerator := 230506372651030009199198208 }, { target := 66, numerator := 230506372651030009199198208 }, { target := 67, numerator := 7376203924832960294374342656 }, { target := 68, numerator := 230506372651030009199198208 }, { target := 69, numerator := 265968891520419241383690240 }, { target := 70, numerator := 277789731143548985445187584 }, { target := 100, numerator := 22365122451665438909115924480 }, { target := 101, numerator := 17395095240184230262645719040 }, { target := 102, numerator := 19880108845924834585880821760 }, { target := 103, numerator := 23359127893961680638409965568 }, { target := 104, numerator := 275836510237207079879096401920 }, { target := 105, numerator := 620259395992854839079481638912 }, { target := 106, numerator := 17395095240184230262645719040 }, { target := 107, numerator := 275836510237207079879096401920 }, { target := 108, numerator := 19880108845924834585880821760 }, { target := 109, numerator := 19383106124776713721233801216 }, { target := 110, numerator := 19383106124776713721233801216 }, { target := 111, numerator := 19383106124776713721233801216 }, { target := 112, numerator := 620259395992854839079481638912 }, { target := 113, numerator := 19383106124776713721233801216 }, { target := 114, numerator := 22365122451665438909115924480 }, { target := 115, numerator := 23359127893961680638409965568 }, { target := 573, numerator := 175419086796326078150344704 }, { target := 574, numerator := 28005164816625517981731913728 }, { target := 576, numerator := 279449430678299786992888578048 }, { target := 584, numerator := 28005164816625517981731913728 }, { target := 591, numerator := 175399070926084598679994368 }, { target := 608, numerator := 176237527325702405109055488 }, { target := 609, numerator := 28135826549829058501086806016 }, { target := 611, numerator := 280753238286441154583835181056 }, { target := 619, numerator := 28135826549829058501086806016 }, { target := 626, numerator := 176217418068819052484100096 }, { target := 669, numerator := 8457218803555378573344768 }, { target := 670, numerator := 1350171243103252033333886976 }, { target := 672, numerator := 13472678617460798439781564416 }, { target := 680, numerator := 1350171243103252033333886976 }, { target := 687, numerator := 8456253808256022642425856 }, { target := 704, numerator := 202427624265744867787800576 }, { target := 705, numerator := 32317002012342355120443359232 }, { target := 707, numerator := 322475081746964917494126477312 }, { target := 715, numerator := 32317002012342355120443359232 }, { target := 722, numerator := 202404526636321574215483392 }, { target := 739, numerator := 8457218803555378573344768 }, { target := 740, numerator := 1350171243103252033333886976 }, { target := 742, numerator := 13472678617460798439781564416 }, { target := 750, numerator := 1350171243103252033333886976 }, { target := 757, numerator := 8456253808256022642425856 }]

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
    Slot5.Left6.expected,
    Slot5.Left14.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot6.Left4.expected,
    Slot6.Left5.expected,
    Slot6.Left6.expected,
    Slot6.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 55, numerator := 255739318769633885945856000 }, { target := 56, numerator := 21504925434293691258765312000 }, { target := 61, numerator := 21504920246146920527953920000 }, { target := 69, numerator := 255744506916404616757248000 }, { target := 100, numerator := 198908359043048577957888000 }, { target := 101, numerator := 16726053115561759867928576000 }, { target := 106, numerator := 16726049080336493743964160000 }, { target := 114, numerator := 198912394268314701922304000 }, { target := 126, numerator := 227323838906341231951872000 }, { target := 127, numerator := 19115489274927725563346944000 }, { target := 132, numerator := 19115484663241707135959040000 }, { target := 140, numerator := 227328450592359659339776000 }, { target := 195, numerator := 267105510714950947543449600 }, { target := 196, numerator := 22460699898040077536932659200 }, { target := 201, numerator := 22460694479309005884751872000 }, { target := 209, numerator := 267110929446022599724236800 }, { target := 240, numerator := 3154118264825484593332224000 }, { target := 241, numerator := 265227413689622192191438848000 }, { target := 246, numerator := 265227349702478686511431680000 }, { target := 254, numerator := 3154182251968990273339392000 }, { target := 266, numerator := 7092503773877846436898406400 }, { target := 267, numerator := 596403265377745037576424652800 }, { target := 272, numerator := 596403121493141262641922048000 }, { target := 280, numerator := 7092647658481621371401011200 }, { target := 315, numerator := 22564025415035845927029964800 }, { target := 316, numerator := 34121144159111713361651302400 }, { target := 317, numerator := 19880104049771375421397401600 }, { target := 318, numerator := 23359122258481366120141946880 }, { target := 319, numerator := 275836443690577833971888947200 }, { target := 320, numerator := 620259246352866913147598929920 }, { target := 321, numerator := 34121140123886447237686886400 }, { target := 322, numerator := 275836443690577833971888947200 }, { target := 323, numerator := 19880104049771375421397401600 }, { target := 324, numerator := 19383101448527091035862466560 }, { target := 325, numerator := 19383101448527091035862466560 }, { target := 326, numerator := 19383101448527091035862466560 }, { target := 327, numerator := 620259246352866913147598929920 }, { target := 328, numerator := 19383101448527091035862466560 }, { target := 329, numerator := 22564029450261112050994380800 }, { target := 330, numerator := 23359122258481366120141946880 }, { target := 341, numerator := 3154118264825484593332224000 }, { target := 342, numerator := 265227413689622192191438848000 }, { target := 347, numerator := 265227349702478686511431680000 }, { target := 355, numerator := 3154182251968990273339392000 }, { target := 653, numerator := 265974287193060801427537920 }, { target := 654, numerator := 206868890039047289999196160 }, { target := 655, numerator := 236421588616054045713367040 }, { target := 656, numerator := 277795366623863503713206272 }, { target := 657, numerator := 3280349542047749884272967680 }, { target := 658, numerator := 7376353564820886226257051648 }, { target := 659, numerator := 206868890039047289999196160 }, { target := 660, numerator := 3280349542047749884272967680 }, { target := 661, numerator := 236421588616054045713367040 }, { target := 662, numerator := 230511048900652694570532864 }, { target := 663, numerator := 230511048900652694570532864 }, { target := 664, numerator := 230511048900652694570532864 }, { target := 665, numerator := 7376353564820886226257051648 }, { target := 666, numerator := 230511048900652694570532864 }, { target := 667, numerator := 265974287193060801427537920 }, { target := 668, numerator := 277795366623863503713206272 }]

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
    Slot6.Left8.expected,
    Slot6.Left9.expected,
    Slot6.Left10.expected,
    Slot6.Left11.expected,
    Slot6.Left12.expected,
    Slot6.Left13.expected,
    Slot6.Left14.expected,
    Slot6.Left15.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 11, numerator := 8457218803555378573344768 }, { target := 12, numerator := 202427624265744867787800576 }, { target := 13, numerator := 151411497934620487361495040 }, { target := 14, numerator := 175691900306118187136581632 }, { target := 15, numerator := 8457218803555378573344768 }, { target := 16, numerator := 175419086796326078150344704 }, { target := 17, numerator := 176237527325702405109055488 }, { target := 18, numerator := 8457218803555378573344768 }, { target := 19, numerator := 202427624265744867787800576 }, { target := 20, numerator := 8457218803555378573344768 }, { target := 31, numerator := 1350171243103252033333886976 }, { target := 32, numerator := 32317002012342355120443359232 }, { target := 33, numerator := 24172420642654996080655073280 }, { target := 34, numerator := 28048718727693364821516877824 }, { target := 35, numerator := 1350171243103252033333886976 }, { target := 36, numerator := 28005164816625517981731913728 }, { target := 37, numerator := 28135826549829058501086806016 }, { target := 38, numerator := 1350171243103252033333886976 }, { target := 39, numerator := 32317002012342355120443359232 }, { target := 40, numerator := 1350171243103252033333886976 }, { target := 76, numerator := 13472678617460798439781564416 }, { target := 77, numerator := 322475081746964917494126477312 }, { target := 78, numerator := 241204407506153004325121556480 }, { target := 79, numerator := 279884033214346909523204112384 }, { target := 80, numerator := 13472678617460798439781564416 }, { target := 81, numerator := 279449430678299786992888578048 }, { target := 82, numerator := 280753238286441154583835181056 }, { target := 83, numerator := 13472678617460798439781564416 }, { target := 84, numerator := 322475081746964917494126477312 }, { target := 85, numerator := 13472678617460798439781564416 }, { target := 376, numerator := 227323838906341231951872000 }, { target := 377, numerator := 19115489274927725563346944000 }, { target := 382, numerator := 19115484663241707135959040000 }, { target := 390, numerator := 227328450592359659339776000 }, { target := 456, numerator := 221640742933682701153075200 }, { target := 457, numerator := 18637602043054532424263270400 }, { target := 462, numerator := 18637597546660664457560064000 }, { target := 470, numerator := 221645239327550667856281600 }, { target := 482, numerator := 221640742933682701153075200 }, { target := 483, numerator := 18637602043054532424263270400 }, { target := 488, numerator := 18637597546660664457560064000 }, { target := 496, numerator := 221645239327550667856281600 }, { target := 531, numerator := 221640742933682701153075200 }, { target := 532, numerator := 18637602043054532424263270400 }, { target := 537, numerator := 18637597546660664457560064000 }, { target := 545, numerator := 221645239327550667856281600 }, { target := 557, numerator := 7092503773877846436898406400 }, { target := 558, numerator := 596403265377745037576424652800 }, { target := 563, numerator := 596403121493141262641922048000 }, { target := 571, numerator := 7092647658481621371401011200 }, { target := 592, numerator := 221640742933682701153075200 }, { target := 593, numerator := 18637602043054532424263270400 }, { target := 598, numerator := 18637597546660664457560064000 }, { target := 606, numerator := 221645239327550667856281600 }, { target := 653, numerator := 255739318769633885945856000 }, { target := 654, numerator := 21504925434293691258765312000 }, { target := 659, numerator := 21504920246146920527953920000 }, { target := 667, numerator := 255744506916404616757248000 }, { target := 688, numerator := 267105510714950947543449600 }, { target := 689, numerator := 22460699898040077536932659200 }, { target := 694, numerator := 22460694479309005884751872000 }, { target := 702, numerator := 267110929446022599724236800 }]

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
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot8.Left4.expected,
    Slot8.Left5.expected,
    Slot8.Left6.expected,
    Slot8.Left7.expected,
    Slot8.Left8.expected,
    Slot8.Left9.expected,
    Slot8.Left10.expected,
    Slot8.Left11.expected,
    Slot8.Left12.expected,
    Slot8.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 11, numerator := 82760106719118066135859200 }, { target := 13, numerator := 801620442253467207493222400 }, { target := 18, numerator := 82760106719118066135859200 }, { target := 31, numerator := 1390369792881183511082434560 }, { target := 33, numerator := 13467223429858249085886136320 }, { target := 38, numerator := 1390369792881183511082434560 }, { target := 45, numerator := 3012467884575897607345274880 }, { target := 47, numerator := 29178984098026206352753295360 }, { target := 52, numerator := 3012467884575897607345274880 }, { target := 76, numerator := 99312128062941679363031040 }, { target := 78, numerator := 961944530704160648991866880 }, { target := 83, numerator := 99312128062941679363031040 }, { target := 90, numerator := 1588994049007066869808496640 }, { target := 92, numerator := 15391112491266570383869870080 }, { target := 97, numerator := 1588994049007066869808496640 }, { target := 116, numerator := 115864149406765292590202880 }, { target := 118, numerator := 1122268619154854090490511360 }, { target := 123, numerator := 115864149406765292590202880 }, { target := 171, numerator := 3012467884575897607345274880 }, { target := 173, numerator := 29178984098026206352753295360 }, { target := 178, numerator := 3012467884575897607345274880 }, { target := 185, numerator := 3012467884575897607345274880 }, { target := 187, numerator := 29178984098026206352753295360 }, { target := 192, numerator := 3012467884575897607345274880 }, { target := 216, numerator := 1588994049007066869808496640 }, { target := 218, numerator := 15391112491266570383869870080 }, { target := 223, numerator := 1588994049007066869808496640 }, { target := 230, numerator := 37175839938227835308227952640 }, { target := 232, numerator := 360087902660257469605955502080 }, { target := 237, numerator := 37175839938227835308227952640 }, { target := 256, numerator := 2979363841888250380890931200 }, { target := 258, numerator := 28858335921124819469756006400 }, { target := 263, numerator := 2979363841888250380890931200 }, { target := 305, numerator := 2740541035984435544416321536 }, { target := 306, numerator := 32317002012342355120443359232 }, { target := 307, numerator := 37639644072513245166541209600 }, { target := 308, numerator := 28048718727693364821516877824 }, { target := 309, numerator := 1350171243103252033333886976 }, { target := 310, numerator := 28005164816625517981731913728 }, { target := 311, numerator := 28135826549829058501086806016 }, { target := 312, numerator := 2740541035984435544416321536 }, { target := 313, numerator := 32317002012342355120443359232 }, { target := 314, numerator := 1350171243103252033333886976 }, { target := 331, numerator := 3012467884575897607345274880 }, { target := 333, numerator := 29178984098026206352753295360 }, { target := 338, numerator := 3012467884575897607345274880 }, { target := 432, numerator := 115864149406765292590202880 }, { target := 434, numerator := 1122268619154854090490511360 }, { target := 439, numerator := 115864149406765292590202880 }, { target := 643, numerator := 8456253808256022642425856 }, { target := 644, numerator := 202404526636321574215483392 }, { target := 645, numerator := 151394221405873953759559680 }, { target := 646, numerator := 175671853306996083281362944 }, { target := 647, numerator := 8456253808256022642425856 }, { target := 648, numerator := 175399070926084598679994368 }, { target := 649, numerator := 176217418068819052484100096 }, { target := 650, numerator := 8456253808256022642425856 }, { target := 651, numerator := 202404526636321574215483392 }, { target := 652, numerator := 8456253808256022642425856 }]

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
    Slot8.Left14.expected,
    Slot8.Left15.expected,
    Slot8.Left16.expected,
    Slot8.Left17.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected,
    Slot10.Left4.expected,
    Slot10.Left5.expected,
    Slot10.Left6.expected,
    Slot10.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 1206130178656770344739667968 }, { target := 3, numerator := 1192227531731202109230546944 }, { target := 4, numerator := 1206130178656770344739667968 }, { target := 5, numerator := 1192227531731202109230546944 }, { target := 7, numerator := 192011421193479774388879360 }, { target := 8, numerator := 175502027969367494721798144 }, { target := 9, numerator := 192011421193479774388879360 }, { target := 10, numerator := 175502027969367494721798144 }, { target := 22, numerator := 38716179938812300195130245120 }, { target := 23, numerator := 38703580665036003981700104192 }, { target := 24, numerator := 38716179938812300195130245120 }, { target := 25, numerator := 38703580665036003981700104192 }, { target := 27, numerator := 1510826708864485593217761280 }, { target := 28, numerator := 1380923851653707392679411712 }, { target := 29, numerator := 1510826708864485593217761280 }, { target := 30, numerator := 1380923851653707392679411712 }, { target := 41, numerator := 181905556920138733631569920 }, { target := 42, numerator := 166265079128874468683808768 }, { target := 43, numerator := 181905556920138733631569920 }, { target := 44, numerator := 166265079128874468683808768 }, { target := 72, numerator := 38716170494079334455839817728 }, { target := 73, numerator := 38703571220303038242409676800 }, { target := 74, numerator := 38716170494079334455839817728 }, { target := 75, numerator := 38703571220303038242409676800 }, { target := 86, numerator := 181905556920138733631569920 }, { target := 87, numerator := 166265079128874468683808768 }, { target := 88, numerator := 181905556920138733631569920 }, { target := 89, numerator := 166265079128874468683808768 }, { target := 162, numerator := 181905556920138733631569920 }, { target := 163, numerator := 166265079128874468683808768 }, { target := 164, numerator := 181905556920138733631569920 }, { target := 165, numerator := 166265079128874468683808768 }, { target := 301, numerator := 1044445795016279431913144320 }, { target := 302, numerator := 1044445795016279431913144320 }, { target := 303, numerator := 1044445795016279431913144320 }, { target := 304, numerator := 1044445795016279431913144320 }, { target := 446, numerator := 2979363841888250380890931200 }, { target := 448, numerator := 28858335921124819469756006400 }, { target := 453, numerator := 2979363841888250380890931200 }, { target := 472, numerator := 115864149406765292590202880 }, { target := 474, numerator := 1122268619154854090490511360 }, { target := 479, numerator := 115864149406765292590202880 }, { target := 521, numerator := 3012467884575897607345274880 }, { target := 523, numerator := 29178984098026206352753295360 }, { target := 528, numerator := 3012467884575897607345274880 }, { target := 547, numerator := 3012467884575897607345274880 }, { target := 549, numerator := 29178984098026206352753295360 }, { target := 554, numerator := 3012467884575897607345274880 }, { target := 643, numerator := 99312128062941679363031040 }, { target := 645, numerator := 961944530704160648991866880 }, { target := 650, numerator := 99312128062941679363031040 }]

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
    Slot10.Left8.expected,
    Slot10.Left9.expected,
    Slot10.Left10.expected,
    Slot10.Left11.expected,
    Slot10.Left12.expected,
    Slot10.Left13.expected,
    Slot10.Left14.expected,
    Slot10.Left15.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 14205128665895484893993893888 }, { target := 21, numerator := 50817909904839850675201376256 }, { target := 71, numerator := 14205123943529002024348680192 }, { target := 167, numerator := 7791621354745942423885578240 }, { target := 168, numerator := 7121687556020123075289808896 }, { target := 169, numerator := 7791621354745942423885578240 }, { target := 170, numerator := 7121687556020123075289808896 }, { target := 181, numerator := 181905556920138733631569920 }, { target := 182, numerator := 166265079128874468683808768 }, { target := 183, numerator := 181905556920138733631569920 }, { target := 184, numerator := 166265079128874468683808768 }, { target := 212, numerator := 1510826708864485593217761280 }, { target := 213, numerator := 1380923851653707392679411712 }, { target := 214, numerator := 1510826708864485593217761280 }, { target := 215, numerator := 1380923851653707392679411712 }, { target := 226, numerator := 7791621354745942423885578240 }, { target := 227, numerator := 7121687556020123075289808896 }, { target := 228, numerator := 7791621354745942423885578240 }, { target := 229, numerator := 7121687556020123075289808896 }, { target := 301, numerator := 161693828373456652116951040 }, { target := 302, numerator := 147791181447888416607830016 }, { target := 303, numerator := 161693828373456652116951040 }, { target := 304, numerator := 147791181447888416607830016 }, { target := 428, numerator := 181905556920138733631569920 }, { target := 429, numerator := 166265079128874468683808768 }, { target := 430, numerator := 181905556920138733631569920 }, { target := 431, numerator := 166265079128874468683808768 }, { target := 442, numerator := 181905556920138733631569920 }, { target := 443, numerator := 166265079128874468683808768 }, { target := 444, numerator := 181905556920138733631569920 }, { target := 445, numerator := 166265079128874468683808768 }, { target := 517, numerator := 192011421193479774388879360 }, { target := 518, numerator := 175502027969367494721798144 }, { target := 519, numerator := 192011421193479774388879360 }, { target := 520, numerator := 175502027969367494721798144 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent0
