import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk19Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 81; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19.Parent3

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
    Slot1.Left3.expected,
    Slot1.Left11.expected,
    Slot1.Left18.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left6.expected,
    Slot2.Left14.expected,
    Slot3.Left0.expected,
    Slot3.Left2.expected,
    Slot3.Left5.expected,
    Slot3.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 620726371039436171278024704 }, { target := 87, numerator := 12414527420788723425560494080 }, { target := 88, numerator := 642895170005130320252239872 }, { target := 89, numerator := 11549944261126651615566102528 }, { target := 90, numerator := 17291663193241436199887831040 }, { target := 91, numerator := 620726371039436171278024704 }, { target := 92, numerator := 17313831992207130348862046208 }, { target := 93, numerator := 17313831992207130348862046208 }, { target := 94, numerator := 12392358621823029276586278912 }, { target := 95, numerator := 642895170005130320252239872 }, { target := 122, numerator := 46799205247560395354275840 }, { target := 123, numerator := 51402405763713876864532480 }, { target := 124, numerator := 46799205247560395354275840 }, { target := 125, numerator := 51402405763713876864532480 }, { target := 161, numerator := 24292808009801454259353419776 }, { target := 162, numerator := 485856160196029085187068395520 }, { target := 163, numerator := 25160408295865791911473184768 }, { target := 164, numerator := 452019749039519916754397560832 }, { target := 165, numerator := 676728223130183368653416693760 }, { target := 166, numerator := 24292808009801454259353419776 }, { target := 167, numerator := 677595823416247706305536458752 }, { target := 168, numerator := 677595823416247706305536458752 }, { target := 169, numerator := 484988559909964747534948630528 }, { target := 170, numerator := 25160408295865791911473184768 }, { target := 197, numerator := 7669488413712963276164300800 }, { target := 198, numerator := 8423864323258500647590297600 }, { target := 199, numerator := 7669488413712963276164300800 }, { target := 200, numerator := 8423864323258500647590297600 }, { target := 215, numerator := 198731348698603279527968768 }, { target := 232, numerator := 24292816919578841861066850304 }, { target := 233, numerator := 485856338391576837221337006080 }, { target := 234, numerator := 25160417523849514784676380672 }, { target := 235, numerator := 452019914825020593200565321728 }, { target := 236, numerator := 676728471331124880415433687040 }, { target := 237, numerator := 24292816919578841861066850304 }, { target := 238, numerator := 677596071935395553339043217408 }, { target := 239, numerator := 677596071935395553339043217408 }, { target := 240, numerator := 484988737787306164297727475712 }, { target := 241, numerator := 25160417523849514784676380672 }, { target := 242, numerator := 78960352757589198618021068800 }, { target := 243, numerator := 86726944832106168973891993600 }, { target := 244, numerator := 78960352757589198618021068800 }, { target := 245, numerator := 86726944832106168973891993600 }, { target := 260, numerator := 39415349908433565517244006400 }, { target := 406, numerator := 620735280816823772991455232 }, { target := 407, numerator := 12414705616336475459829104640 }, { target := 408, numerator := 642904397988853193455435776 }, { target := 409, numerator := 11550110046627328061733863424 }, { target := 410, numerator := 17291911394182947961904824320 }, { target := 411, numerator := 620735280816823772991455232 }, { target := 412, numerator := 17314080511354977382368804864 }, { target := 413, numerator := 17314080511354977382368804864 }, { target := 414, numerator := 12392536499164446039365124096 }, { target := 415, numerator := 642904397988853193455435776 }, { target := 416, numerator := 7669488413712963276164300800 }, { target := 417, numerator := 8423864323258500647590297600 }, { target := 418, numerator := 7669488413712963276164300800 }, { target := 419, numerator := 8423864323258500647590297600 }, { target := 420, numerator := 39415349908433565517244006400 }, { target := 498, numerator := 46799205247560395354275840 }, { target := 499, numerator := 51402405763713876864532480 }, { target := 500, numerator := 46799205247560395354275840 }, { target := 501, numerator := 51402405763713876864532480 }, { target := 502, numerator := 198731348698603279527968768 }]

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
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left3.expected,
    Slot4.Left11.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left6.expected,
    Slot5.Left14.expected,
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 100407938042067951945617768448 }, { target := 36, numerator := 114353484992355167493620236288 }, { target := 37, numerator := 89251500481838179507215794176 }, { target := 38, numerator := 1196527928334643094018611740672 }, { target := 39, numerator := 105986156822182838164818755584 }, { target := 40, numerator := 89251500481838179507215794176 }, { target := 41, numerator := 105986156822182838164818755584 }, { target := 42, numerator := 103197047432125395055218262016 }, { target := 43, numerator := 3899174927300305467221490008064 }, { target := 44, numerator := 103197047432125395055218262016 }, { target := 45, numerator := 1196527928334643094018611740672 }, { target := 46, numerator := 3899174927300305467221490008064 }, { target := 47, numerator := 100407938042067951945617768448 }, { target := 48, numerator := 103197047432125395055218262016 }, { target := 49, numerator := 103197047432125395055218262016 }, { target := 50, numerator := 114353484992355167493620236288 }, { target := 122, numerator := 612868722146822555833466880 }, { target := 124, numerator := 612868722146822555833466880 }, { target := 145, numerator := 372990467887488675864882708480 }, { target := 146, numerator := 424794699538528769735005306880 }, { target := 147, numerator := 331547082566656600768784629760 }, { target := 148, numerator := 4444803075659240054056518942720 }, { target := 149, numerator := 393712160547904713412931747840 }, { target := 150, numerator := 331547082566656600768784629760 }, { target := 151, numerator := 393712160547904713412931747840 }, { target := 152, numerator := 383351314217696694638907228160 }, { target := 153, numerator := 14484463169630810246086278512640 }, { target := 154, numerator := 383351314217696694638907228160 }, { target := 155, numerator := 4444803075659240054056518942720 }, { target := 156, numerator := 14484463169630810246086278512640 }, { target := 157, numerator := 372990467887488675864882708480 }, { target := 158, numerator := 383351314217696694638907228160 }, { target := 159, numerator := 383351314217696694638907228160 }, { target := 160, numerator := 424794699538528769735005306880 }, { target := 197, numerator := 197418105803382059890492047360 }, { target := 199, numerator := 197418105803382059890492047360 }, { target := 215, numerator := 1347489496954990304566444032 }, { target := 216, numerator := 100386802279217129605243600896 }, { target := 217, numerator := 114329413706886175383749656576 }, { target := 218, numerator := 89232713137081892982438756352 }, { target := 219, numerator := 1196276060494004127795819577344 }, { target := 220, numerator := 105963846850284747916646023168 }, { target := 221, numerator := 89232713137081892982438756352 }, { target := 222, numerator := 105963846850284747916646023168 }, { target := 223, numerator := 103175324564750938760944812032 }, { target := 224, numerator := 3898354155176265199670293168128 }, { target := 225, numerator := 103175324564750938760944812032 }, { target := 226, numerator := 1196276060494004127795819577344 }, { target := 227, numerator := 3898354155176265199670293168128 }, { target := 228, numerator := 100386802279217129605243600896 }, { target := 229, numerator := 103175324564750938760944812032 }, { target := 230, numerator := 103175324564750938760944812032 }, { target := 231, numerator := 114329413706886175383749656576 }, { target := 242, numerator := 2099624575130092027728686481408 }, { target := 244, numerator := 2099624575130092027728686481408 }, { target := 260, numerator := 236336998045838022476065406976 }, { target := 416, numerator := 197418700821558901465788973056 }, { target := 418, numerator := 197418700821558901465788973056 }, { target := 420, numerator := 236337026380036919693936689152 }, { target := 498, numerator := 612868722146822555833466880 }, { target := 500, numerator := 612868722146822555833466880 }, { target := 502, numerator := 1347461162756093086695161856 }]

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
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left2.expected,
    Slot9.Left3.expected,
    Slot9.Left4.expected,
    Slot9.Left5.expected,
    Slot9.Left6.expected,
    Slot9.Left7.expected,
    Slot9.Left8.expected,
    Slot9.Left9.expected,
    Slot9.Left10.expected,
    Slot9.Left11.expected,
    Slot9.Left12.expected,
    Slot9.Left13.expected,
    Slot9.Left14.expected,
    Slot9.Left15.expected,
    Slot10.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 27099284402967583488598867968 }, { target := 17, numerator := 406489266044513752328983019520 }, { target := 18, numerator := 713614489278146365199770189824 }, { target := 19, numerator := 27099284402967583488598867968 }, { target := 20, numerator := 451654740049459724809981132800 }, { target := 21, numerator := 27099284402967583488598867968 }, { target := 22, numerator := 713614489278146365199770189824 }, { target := 23, numerator := 709097941877651767951670378496 }, { target := 24, numerator := 451654740049459724809981132800 }, { target := 25, numerator := 10943594351398409132145842847744 }, { target := 26, numerator := 700064847076662573455470755840 }, { target := 27, numerator := 406489266044513752328983019520 }, { target := 28, numerator := 713614489278146365199770189824 }, { target := 29, numerator := 27099284402967583488598867968 }, { target := 30, numerator := 700064847076662573455470755840 }, { target := 31, numerator := 27099284402967583488598867968 }, { target := 32, numerator := 713614489278146365199770189824 }, { target := 33, numerator := 713614489278146365199770189824 }, { target := 34, numerator := 27099284402967583488598867968 }, { target := 86, numerator := 279909941266821061249628897280 }, { target := 89, numerator := 1022376186963675971240067072000 }, { target := 91, numerator := 279909846960591994932009369600 }, { target := 122, numerator := 14301628520085747556933435392 }, { target := 124, numerator := 14301631929860104630938107904 }, { target := 161, numerator := 10954264369007258116622850719744 }, { target := 164, numerator := 40010651232647768274261088665600 }, { target := 166, numerator := 10954260678336751162919831470080 }, { target := 197, numerator := 1690360671280134810710197665792 }, { target := 199, numerator := 1690361074293572269428864712704 }, { target := 215, numerator := 20426010648208774535835549696 }, { target := 232, numerator := 10954264369007258116622850719744 }, { target := 235, numerator := 40010651232647768274261088665600 }, { target := 237, numerator := 10954260678336751162919831470080 }, { target := 242, numerator := 16041185819628677333400642650112 }, { target := 244, numerator := 16041189644145863471379769196544 }, { target := 260, numerator := 15319507986156580901876662272 }, { target := 265, numerator := 16170591763165279840869810176 }, { target := 355, numerator := 20851552536713124005332123648 }, { target := 400, numerator := 279155478858853251989752512512 }, { target := 405, numerator := 488096546114488841512570322944 }, { target := 406, numerator := 279909941266821061249628897280 }, { target := 409, numerator := 1022376186963675971240067072000 }, { target := 411, numerator := 279909846960591994932009369600 }, { target := 416, numerator := 1690361830620968150994532696064 }, { target := 418, numerator := 1690362233634682018140329607168 }, { target := 420, numerator := 14893966097652231432380088320 }, { target := 425, numerator := 279155478858853251989752512512 }, { target := 426, numerator := 15745049874660930371373236224 }, { target := 471, numerator := 16170591763165279840869810176 }, { target := 476, numerator := 16170591763165279840869810176 }, { target := 491, numerator := 15745049874660930371373236224 }, { target := 496, numerator := 488096546114488841512570322944 }, { target := 497, numerator := 15745049874660930371373236224 }, { target := 498, numerator := 14301628520085747556933435392 }, { target := 500, numerator := 14301631929860104630938107904 }, { target := 502, numerator := 20426010648208774535835549696 }, { target := 503, numerator := 20851552536713124005332123648 }]

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
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left2.expected,
    Slot13.Left3.expected,
    Slot13.Left4.expected,
    Slot13.Left5.expected,
    Slot13.Left6.expected,
    Slot13.Left7.expected,
    Slot13.Left8.expected,
    Slot13.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 601706635338836973175246422016 }, { target := 37, numerator := 23469798496419859954677365866496 }, { target := 40, numerator := 23469789887779810659723842158592 }, { target := 47, numerator := 601709504885520071493087657984 }, { target := 86, numerator := 603829681391193939855076753408 }, { target := 89, numerator := 2171957407323615195346631655424 }, { target := 91, numerator := 603829882832063005787835858944 }, { target := 122, numerator := 26518999940377271208329084928 }, { target := 124, numerator := 26518993617755739944380268544 }, { target := 126, numerator := 27099277941995471671828414464 }, { target := 127, numerator := 406489169129932075077426216960 }, { target := 128, numerator := 713614319139214087358148247552 }, { target := 129, numerator := 27099277941995471671828414464 }, { target := 130, numerator := 451654632366591194530473574400 }, { target := 131, numerator := 27099277941995471671828414464 }, { target := 132, numerator := 713614319139214087358148247552 }, { target := 133, numerator := 709097772815548175412843511808 }, { target := 134, numerator := 451654632366591194530473574400 }, { target := 135, numerator := 10943591742242504643473374707712 }, { target := 136, numerator := 700064680168216351522234040320 }, { target := 137, numerator := 406489169129932075077426216960 }, { target := 138, numerator := 713614319139214087358148247552 }, { target := 139, numerator := 27099277941995471671828414464 }, { target := 140, numerator := 700064680168216351522234040320 }, { target := 141, numerator := 27099277941995471671828414464 }, { target := 142, numerator := 713614319139214087358148247552 }, { target := 143, numerator := 713614319139214087358148247552 }, { target := 144, numerator := 27099277941995471671828414464 }, { target := 145, numerator := 2164320873808267002453528936448 }, { target := 147, numerator := 84420167248564092043098626981888 }, { target := 150, numerator := 84420136283541837803202937880576 }, { target := 157, numerator := 2164331195482351749085425303552 }, { target := 161, numerator := 23552608723399289040080520347648 }, { target := 164, numerator := 84718033172404953291118969094144 }, { target := 166, numerator := 23552616580677783665292831883264 }, { target := 197, numerator := 397784999105659068124936273920 }, { target := 199, numerator := 397784904266336099165704028160 }, { target := 211, numerator := 698333665096601475152665903104 }, { target := 213, numerator := 698333498600901151868680404992 }, { target := 216, numerator := 601706836071446317809677631488 }, { target := 218, numerator := 23469806326072412026270413488128 }, { target := 221, numerator := 23469797717429490842129510957056 }, { target := 228, numerator := 601709705619086712523311808512 }, { target := 232, numerator := 23552600084384737954024543748096 }, { target := 235, numerator := 84718002098126519383220119666688 }, { target := 237, numerator := 23552607941660350556950314876928 }, { target := 242, numerator := 26518999940377271208329084928 }, { target := 244, numerator := 26518993617755739944380268544 }, { target := 256, numerator := 441983332339621186805484748800 }, { target := 258, numerator := 441983226962595665739671142400 }, { target := 261, numerator := 26518999940377271208329084928 }, { target := 263, numerator := 26518993617755739944380268544 }, { target := 337, numerator := 698333665096601475152665903104 }, { target := 339, numerator := 698333498600901151868680404992 }, { target := 351, numerator := 693913831773205263284611055616 }, { target := 353, numerator := 693913666331275195211283693568 }, { target := 382, numerator := 441983332339621186805484748800 }, { target := 384, numerator := 441983226962595665739671142400 }, { target := 396, numerator := 10709256142589021356296895463424 }, { target := 398, numerator := 10709253589303692980872231780352 }, { target := 406, numerator := 603832561062710968540402286592 }, { target := 409, numerator := 2171967765416426497979581464576 }, { target := 411, numerator := 603832762504540708568674861056 }]

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
    Slot13.Left10.expected,
    Slot13.Left11.expected,
    Slot13.Left12.expected,
    Slot13.Left13.expected,
    Slot13.Left14.expected,
    Slot13.Left15.expected,
    Slot13.Left16.expected,
    Slot13.Left17.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 20426010648208774535835549696 }, { target := 1, numerator := 15319507986156580901876662272 }, { target := 2, numerator := 16170591763165279840869810176 }, { target := 3, numerator := 20851552536713124005332123648 }, { target := 4, numerator := 279155478858853251989752512512 }, { target := 5, numerator := 488096546114488841512570322944 }, { target := 6, numerator := 14893966097652231432380088320 }, { target := 7, numerator := 279155478858853251989752512512 }, { target := 8, numerator := 15745049874660930371373236224 }, { target := 9, numerator := 16170591763165279840869810176 }, { target := 10, numerator := 16170591763165279840869810176 }, { target := 11, numerator := 15745049874660930371373236224 }, { target := 12, numerator := 488096546114488841512570322944 }, { target := 13, numerator := 15745049874660930371373236224 }, { target := 14, numerator := 20426010648208774535835549696 }, { target := 15, numerator := 20851552536713124005332123648 }, { target := 16, numerator := 14155990755115424262056312832 }, { target := 17, numerator := 1673147222489094741354696671232 }, { target := 19, numerator := 15877833621872784488864994557952 }, { target := 27, numerator := 1673148370024013281839802220544 }, { target := 34, numerator := 14155990755115424262056312832 }, { target := 35, numerator := 276766847727954698740275609600 }, { target := 37, numerator := 10831259528931069316810491822080 }, { target := 40, numerator := 10831259528931069316810491822080 }, { target := 47, numerator := 276766847727954698740275609600 }, { target := 86, numerator := 102845023916875426507404607488 }, { target := 89, numerator := 382043634583786944696554618880 }, { target := 91, numerator := 102823375150071914304399998976 }, { target := 112, numerator := 117129055016441457966766358528 }, { target := 115, numerator := 435105250498201798126631649280 }, { target := 117, numerator := 117104399476470791291122221056 }, { target := 126, numerator := 14155994130167028209034461184 }, { target := 127, numerator := 1673147621398525708640383401984 }, { target := 129, numerator := 15877837407443767102017449754624 }, { target := 137, numerator := 1673148768933717842802851708928 }, { target := 144, numerator := 14155994130167028209034461184 }, { target := 145, numerator := 1010895980247926646547415040000 }, { target := 147, numerator := 39561373801463950539428462592000 }, { target := 150, numerator := 39561373801463950539428462592000 }, { target := 157, numerator := 1010895980247926646547415040000 }, { target := 216, numerator := 276766754480685160303951872000 }, { target := 218, numerator := 10831255879702901181052983705600 }, { target := 221, numerator := 10831255879702901181052983705600 }, { target := 228, numerator := 276766754480685160303951872000 }, { target := 401, numerator := 685074165126412839548501360640 }, { target := 403, numerator := 685074001792023281896490270720 }, { target := 416, numerator := 397784999105659068124936273920 }, { target := 418, numerator := 397784904266336099165704028160 }, { target := 421, numerator := 698333665096601475152665903104 }, { target := 423, numerator := 698333498600901151868680404992 }, { target := 453, numerator := 26518999940377271208329084928 }, { target := 455, numerator := 26518993617755739944380268544 }, { target := 467, numerator := 685074165126412839548501360640 }, { target := 469, numerator := 685074001792023281896490270720 }, { target := 472, numerator := 26518999940377271208329084928 }, { target := 474, numerator := 26518993617755739944380268544 }, { target := 487, numerator := 698333665096601475152665903104 }, { target := 489, numerator := 698333498600901151868680404992 }, { target := 492, numerator := 698333665096601475152665903104 }, { target := 494, numerator := 698333498600901151868680404992 }, { target := 498, numerator := 26518999940377271208329084928 }, { target := 500, numerator := 26518993617755739944380268544 }]

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
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot20.Left0.expected,
    Slot20.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1572071079780822021994184704 }, { target := 1, numerator := 275726497720144359555409641472 }, { target := 6, numerator := 275726530776709739642926137344 }, { target := 14, numerator := 1572038023215441934477688832 }, { target := 16, numerator := 603140647192111086693253120 }, { target := 17, numerator := 194284485076344249416039792640 }, { target := 19, numerator := 2066297200921677868558389870592 }, { target := 27, numerator := 194285070649788125252046290944 }, { target := 34, numerator := 603140647192111086693253120 }, { target := 35, numerator := 607232319495100602337198080 }, { target := 37, numerator := 23764703487849248731976171520 }, { target := 40, numerator := 23764712203935823559739310080 }, { target := 47, numerator := 607241035581675430100336640 }, { target := 70, numerator := 12144646389902012046743961600 }, { target := 72, numerator := 475294069756984974639523430400 }, { target := 75, numerator := 475294244078716471194786201600 }, { target := 82, numerator := 12144820711633508602006732800 }, { target := 126, numerator := 603140647192111086693253120 }, { target := 127, numerator := 194284485076344249416039792640 }, { target := 129, numerator := 2066297200921677868558389870592 }, { target := 137, numerator := 194285070649788125252046290944 }, { target := 144, numerator := 603140647192111086693253120 }, { target := 161, numerator := 91417799037222601339915206656 }, { target := 164, numerator := 339594341852255061952492994560 }, { target := 166, numerator := 91398555688952812715022221312 }, { target := 187, numerator := 1225569868342765499213238239232 }, { target := 190, numerator := 4552686645456794424300609208320 }, { target := 192, numerator := 1225311887205023645460766654464 }, { target := 201, numerator := 108558636356701839091149307904 }, { target := 204, numerator := 403268280949552886068585431040 }, { target := 206, numerator := 108535784880631465099088887808 }, { target := 232, numerator := 91417799037222601339915206656 }, { target := 235, numerator := 339594341852255061952492994560 }, { target := 237, numerator := 91398555688952812715022221312 }, { target := 246, numerator := 108558636356701839091149307904 }, { target := 249, numerator := 403268280949552886068585431040 }, { target := 251, numerator := 108535784880631465099088887808 }, { target := 301, numerator := 105701830136788632799276957696 }, { target := 304, numerator := 392655957766669915382570024960 }, { target := 306, numerator := 105679580015351689701744443392 }, { target := 327, numerator := 3993815095438662396037545590784 }, { target := 330, numerator := 14836027809670393019049537699840 }, { target := 332, numerator := 3992974401661126005487533293568 }, { target := 341, numerator := 105701830136788632799276957696 }, { target := 344, numerator := 392655957766669915382570024960 }, { target := 346, numerator := 105679580015351689701744443392 }, { target := 372, numerator := 1225569868342765499213238239232 }, { target := 375, numerator := 4552686645456794424300609208320 }, { target := 377, numerator := 1225311887205023645460766654464 }, { target := 386, numerator := 3993815095438662396037545590784 }, { target := 389, numerator := 14836027809670393019049537699840 }, { target := 391, numerator := 3992974401661126005487533293568 }, { target := 406, numerator := 102845023916875426507404607488 }, { target := 409, numerator := 382043634583786944696554618880 }, { target := 411, numerator := 102823375150071914304399998976 }, { target := 443, numerator := 105701830136788632799276957696 }, { target := 446, numerator := 392655957766669915382570024960 }, { target := 448, numerator := 105679580015351689701744443392 }, { target := 457, numerator := 105701830136788632799276957696 }, { target := 460, numerator := 392655957766669915382570024960 }, { target := 462, numerator := 105679580015351689701744443392 }, { target := 477, numerator := 117129055016441457966766358528 }, { target := 480, numerator := 435105250498201798126631649280 }, { target := 482, numerator := 117104399476470791291122221056 }]

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
    Slot20.Left2.expected,
    Slot20.Left3.expected,
    Slot20.Left4.expected,
    Slot20.Left5.expected,
    Slot20.Left6.expected,
    Slot20.Left7.expected,
    Slot20.Left8.expected,
    Slot20.Left9.expected,
    Slot21.Left0.expected,
    Slot22.Left0.expected,
    Slot22.Left1.expected,
    Slot22.Left2.expected,
    Slot22.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 198731348698603279527968768 }, { target := 1, numerator := 39415349908433565517244006400 }, { target := 6, numerator := 39415349908433565517244006400 }, { target := 14, numerator := 198731348698603279527968768 }, { target := 16, numerator := 46799205247560395354275840 }, { target := 17, numerator := 7669488413712963276164300800 }, { target := 19, numerator := 78960352757589198618021068800 }, { target := 27, numerator := 7669488413712963276164300800 }, { target := 34, numerator := 46799205247560395354275840 }, { target := 51, numerator := 51402405763713876864532480 }, { target := 52, numerator := 8423864323258500647590297600 }, { target := 54, numerator := 86726944832106168973891993600 }, { target := 62, numerator := 8423864323258500647590297600 }, { target := 69, numerator := 51402405763713876864532480 }, { target := 96, numerator := 628919188048497052420669440 }, { target := 98, numerator := 24613442898129579043832463360 }, { target := 101, numerator := 24613451925504960115444285440 }, { target := 108, numerator := 628928215423878124032491520 }, { target := 126, numerator := 46799205247560395354275840 }, { target := 127, numerator := 7669488413712963276164300800 }, { target := 129, numerator := 78960352757589198618021068800 }, { target := 137, numerator := 7669488413712963276164300800 }, { target := 144, numerator := 46799205247560395354275840 }, { target := 145, numerator := 11298858516319550493488578560 }, { target := 147, numerator := 442193232756052092477128048640 }, { target := 150, numerator := 442193394937520145522292162560 }, { target := 157, numerator := 11299020697787603538652692480 }, { target := 171, numerator := 16915757471649231065107660800 }, { target := 173, numerator := 662016740018657643247907635200 }, { target := 176, numerator := 662016982823926513449880780800 }, { target := 183, numerator := 16916000276918101267080806400 }, { target := 216, numerator := 607232319495100602337198080 }, { target := 218, numerator := 23764703487849248731976171520 }, { target := 221, numerator := 23764712203935823559739310080 }, { target := 228, numerator := 607241035581675430100336640 }, { target := 266, numerator := 51402405763713876864532480 }, { target := 267, numerator := 8423864323258500647590297600 }, { target := 269, numerator := 86726944832106168973891993600 }, { target := 277, numerator := 8423864323258500647590297600 }, { target := 284, numerator := 51402405763713876864532480 }, { target := 285, numerator := 16937444340202627515191132160 }, { target := 287, numerator := 662865479428937973559763927040 }, { target := 290, numerator := 662865722545495650005585756160 }, { target := 297, numerator := 16937687456760303961012961280 }, { target := 311, numerator := 16937444340202627515191132160 }, { target := 313, numerator := 662865479428937973559763927040 }, { target := 316, numerator := 662865722545495650005585756160 }, { target := 323, numerator := 16937687456760303961012961280 }, { target := 356, numerator := 12122959521348615596660490240 }, { target := 358, numerator := 474445330346704644327667138560 }, { target := 361, numerator := 474445504357147334639081226240 }, { target := 368, numerator := 12123133531791305908074577920 }, { target := 427, numerator := 628919188048497052420669440 }, { target := 429, numerator := 24613442898129579043832463360 }, { target := 432, numerator := 24613451925504960115444285440 }, { target := 439, numerator := 628928215423878124032491520 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19.Parent3
