import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk6Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 28; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6.Parent2

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
    Slot2.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 61, numerator := 15937986879685052596224000 }, { target := 62, numerator := 12396212017532818685952000 }, { target := 63, numerator := 14167099448608935641088000 }, { target := 64, numerator := 16646341852115499378278400 }, { target := 65, numerator := 196568504849448982020096000 }, { target := 66, numerator := 442013502796598792001945600 }, { target := 67, numerator := 12396212017532818685952000 }, { target := 68, numerator := 196568504849448982020096000 }, { target := 69, numerator := 14167099448608935641088000 }, { target := 70, numerator := 13812921962393712250060800 }, { target := 71, numerator := 13812921962393712250060800 }, { target := 72, numerator := 13812921962393712250060800 }, { target := 73, numerator := 442013502796598792001945600 }, { target := 74, numerator := 13812921962393712250060800 }, { target := 75, numerator := 15937986879685052596224000 }, { target := 76, numerator := 16646341852115499378278400 }, { target := 132, numerator := 319397257068888454028328960 }, { target := 133, numerator := 248420088831357686466478080 }, { target := 134, numerator := 283908672950123070247403520 }, { target := 135, numerator := 333592690716394607540699136 }, { target := 136, numerator := 3939232837182957599682723840 }, { target := 137, numerator := 8857950596043839791718989824 }, { target := 138, numerator := 248420088831357686466478080 }, { target := 139, numerator := 3939232837182957599682723840 }, { target := 140, numerator := 283908672950123070247403520 }, { target := 141, numerator := 276810956126369993491218432 }, { target := 142, numerator := 276810956126369993491218432 }, { target := 143, numerator := 276810956126369993491218432 }, { target := 144, numerator := 8857950596043839791718989824 }, { target := 145, numerator := 276810956126369993491218432 }, { target := 146, numerator := 319397257068888454028328960 }, { target := 147, numerator := 333592690716394607540699136 }, { target := 219, numerator := 54057491755103076902502400 }, { target := 220, numerator := 8630126822702984920353996800 }, { target := 222, numerator := 86115687698226131006966988800 }, { target := 230, numerator := 8630126822702984920353996800 }, { target := 237, numerator := 54051323625053430271180800 }, { target := 359, numerator := 49409557884570849729576960 }, { target := 360, numerator := 7888097226732260983276830720 }, { target := 362, numerator := 78711348195201080490480107520 }, { target := 370, numerator := 7888097226732260983276830720 }, { target := 377, numerator := 49403920098413322247864320 }, { target := 434, numerator := 54057491755103076902502400 }, { target := 435, numerator := 8630126822702984920353996800 }, { target := 437, numerator := 86115687698226131006966988800 }, { target := 445, numerator := 8630126822702984920353996800 }, { target := 452, numerator := 54051323625053430271180800 }, { target := 469, numerator := 49409557884570849729576960 }, { target := 470, numerator := 7888097226732260983276830720 }, { target := 472, numerator := 78711348195201080490480107520 }, { target := 480, numerator := 7888097226732260983276830720 }, { target := 487, numerator := 49403920098413322247864320 }, { target := 488, numerator := 8216010985828471699950010368 }, { target := 490, numerator := 308696639071228878674225790976 }, { target := 493, numerator := 308673291691337571148289277952 }, { target := 500, numerator := 8239358365719779225886523392 }]

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
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 177, numerator := 536153878632605169336975360 }, { target := 178, numerator := 417008572269804020595425280 }, { target := 179, numerator := 476581225451204594966200320 }, { target := 180, numerator := 559982939905165399085285376 }, { target := 181, numerator := 6612564503135463755156029440 }, { target := 182, numerator := 14869334234077583362945449984 }, { target := 183, numerator := 417008572269804020595425280 }, { target := 184, numerator := 6612564503135463755156029440 }, { target := 185, numerator := 476581225451204594966200320 }, { target := 186, numerator := 464666694814924480092045312 }, { target := 187, numerator := 464666694814924480092045312 }, { target := 188, numerator := 464666694814924480092045312 }, { target := 189, numerator := 14869334234077583362945449984 }, { target := 190, numerator := 464666694814924480092045312 }, { target := 191, numerator := 536153878632605169336975360 }, { target := 192, numerator := 559982939905165399085285376 }, { target := 203, numerator := 514478216476233497806110720 }, { target := 204, numerator := 400149723925959387182530560 }, { target := 205, numerator := 457313970201096442494320640 }, { target := 206, numerator := 537343914986288319930826752 }, { target := 207, numerator := 6345231336540213139608698880 }, { target := 208, numerator := 14268195870274209005822803968 }, { target := 209, numerator := 400149723925959387182530560 }, { target := 210, numerator := 6345231336540213139608698880 }, { target := 211, numerator := 457313970201096442494320640 }, { target := 212, numerator := 445881120946069031431962624 }, { target := 213, numerator := 445881120946069031431962624 }, { target := 214, numerator := 445881120946069031431962624 }, { target := 215, numerator := 14268195870274209005822803968 }, { target := 216, numerator := 445881120946069031431962624 }, { target := 217, numerator := 514478216476233497806110720 }, { target := 218, numerator := 537343914986288319930826752 }, { target := 272, numerator := 15937986879685052596224000 }, { target := 273, numerator := 12396212017532818685952000 }, { target := 274, numerator := 14167099448608935641088000 }, { target := 275, numerator := 16646341852115499378278400 }, { target := 276, numerator := 196568504849448982020096000 }, { target := 277, numerator := 442013502796598792001945600 }, { target := 278, numerator := 12396212017532818685952000 }, { target := 279, numerator := 196568504849448982020096000 }, { target := 280, numerator := 14167099448608935641088000 }, { target := 281, numerator := 13812921962393712250060800 }, { target := 282, numerator := 13812921962393712250060800 }, { target := 283, numerator := 13812921962393712250060800 }, { target := 284, numerator := 442013502796598792001945600 }, { target := 285, numerator := 13812921962393712250060800 }, { target := 286, numerator := 15937986879685052596224000 }, { target := 287, numerator := 16646341852115499378278400 }, { target := 317, numerator := 514478216476233497806110720 }, { target := 318, numerator := 400149723925959387182530560 }, { target := 319, numerator := 457313970201096442494320640 }, { target := 320, numerator := 537343914986288319930826752 }, { target := 321, numerator := 6345231336540213139608698880 }, { target := 322, numerator := 14268195870274209005822803968 }, { target := 323, numerator := 400149723925959387182530560 }, { target := 324, numerator := 6345231336540213139608698880 }, { target := 325, numerator := 457313970201096442494320640 }, { target := 326, numerator := 445881120946069031431962624 }, { target := 327, numerator := 445881120946069031431962624 }, { target := 328, numerator := 445881120946069031431962624 }, { target := 329, numerator := 14268195870274209005822803968 }, { target := 330, numerator := 445881120946069031431962624 }, { target := 331, numerator := 514478216476233497806110720 }, { target := 332, numerator := 537343914986288319930826752 }]

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
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 343, numerator := 343622997126009733974589440 }, { target := 344, numerator := 267262331098007570869125120 }, { target := 345, numerator := 305442664112008652421857280 }, { target := 346, numerator := 358895130331610166595682304 }, { target := 347, numerator := 4238016964554120052353269760 }, { target := 348, numerator := 9529811120294669955561947136 }, { target := 349, numerator := 267262331098007570869125120 }, { target := 350, numerator := 4238016964554120052353269760 }, { target := 351, numerator := 305442664112008652421857280 }, { target := 352, numerator := 297806597509208436111310848 }, { target := 353, numerator := 297806597509208436111310848 }, { target := 354, numerator := 297806597509208436111310848 }, { target := 355, numerator := 9529811120294669955561947136 }, { target := 356, numerator := 297806597509208436111310848 }, { target := 357, numerator := 343622997126009733974589440 }, { target := 358, numerator := 358895130331610166595682304 }, { target := 392, numerator := 16575506354872454700072960 }, { target := 393, numerator := 12892060498234131433390080 }, { target := 394, numerator := 14733783426553293066731520 }, { target := 395, numerator := 17312195526200119353409536 }, { target := 396, numerator := 204431245043426941300899840 }, { target := 397, numerator := 459694042908462743682023424 }, { target := 398, numerator := 12892060498234131433390080 }, { target := 399, numerator := 204431245043426941300899840 }, { target := 400, numerator := 14733783426553293066731520 }, { target := 401, numerator := 14365438840889460740063232 }, { target := 402, numerator := 14365438840889460740063232 }, { target := 403, numerator := 14365438840889460740063232 }, { target := 404, numerator := 459694042908462743682023424 }, { target := 405, numerator := 14365438840889460740063232 }, { target := 406, numerator := 16575506354872454700072960 }, { target := 407, numerator := 17312195526200119353409536 }, { target := 418, numerator := 319397257068888454028328960 }, { target := 419, numerator := 248420088831357686466478080 }, { target := 420, numerator := 283908672950123070247403520 }, { target := 421, numerator := 333592690716394607540699136 }, { target := 422, numerator := 3939232837182957599682723840 }, { target := 423, numerator := 8857950596043839791718989824 }, { target := 424, numerator := 248420088831357686466478080 }, { target := 425, numerator := 3939232837182957599682723840 }, { target := 426, numerator := 283908672950123070247403520 }, { target := 427, numerator := 276810956126369993491218432 }, { target := 428, numerator := 276810956126369993491218432 }, { target := 429, numerator := 276810956126369993491218432 }, { target := 430, numerator := 8857950596043839791718989824 }, { target := 431, numerator := 276810956126369993491218432 }, { target := 432, numerator := 319397257068888454028328960 }, { target := 433, numerator := 333592690716394607540699136 }, { target := 453, numerator := 15300467404497650492375040 }, { target := 454, numerator := 11900363536831505938513920 }, { target := 455, numerator := 13600415470664578215444480 }, { target := 456, numerator := 15980488178030879403147264 }, { target := 457, numerator := 188705764655471022739292160 }, { target := 458, numerator := 424332962684734840321867776 }, { target := 459, numerator := 11900363536831505938513920 }, { target := 460, numerator := 188705764655471022739292160 }, { target := 461, numerator := 13600415470664578215444480 }, { target := 462, numerator := 13260405083897963760058368 }, { target := 463, numerator := 13260405083897963760058368 }, { target := 464, numerator := 13260405083897963760058368 }, { target := 465, numerator := 424332962684734840321867776 }, { target := 466, numerator := 13260405083897963760058368 }, { target := 467, numerator := 15300467404497650492375040 }, { target := 468, numerator := 15980488178030879403147264 }]

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
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left7.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 17, numerator := 24769463603301392014376960 }, { target := 18, numerator := 592869096569342995957022720 }, { target := 19, numerator := 443453299994589437676748800 }, { target := 20, numerator := 514565630984712788943831040 }, { target := 21, numerator := 24769463603301392014376960 }, { target := 22, numerator := 513766616029767582749818880 }, { target := 23, numerator := 516163660894603201331855360 }, { target := 24, numerator := 24769463603301392014376960 }, { target := 25, numerator := 592869096569342995957022720 }, { target := 26, numerator := 24769463603301392014376960 }, { target := 37, numerator := 2073925759247694855275544576 }, { target := 38, numerator := 49640416560057728471434002432 }, { target := 39, numerator := 37129961173628085312191201280 }, { target := 40, numerator := 43084135127597273767659700224 }, { target := 41, numerator := 2073925759247694855275544576 }, { target := 42, numerator := 43017234296653799740070166528 }, { target := 43, numerator := 43217936789484221822838767616 }, { target := 44, numerator := 2073925759247694855275544576 }, { target := 45, numerator := 49640416560057728471434002432 }, { target := 46, numerator := 2073925759247694855275544576 }, { target := 61, numerator := 358549272114740053772599296 }, { target := 62, numerator := 30150136468820943846550536192 }, { target := 67, numerator := 30150129194983439236564254720 }, { target := 75, numerator := 358556545952244663758880768 }, { target := 153, numerator := 2073926509799594354332925952 }, { target := 154, numerator := 49640434524880613255323582464 }, { target := 155, numerator := 37129974610928221504992706560 }, { target := 156, numerator := 43084150719707702070658203648 }, { target := 157, numerator := 2073926509799594354332925952 }, { target := 158, numerator := 43017249864552876446324883456 }, { target := 159, numerator := 43217952430017353319324844032 }, { target := 160, numerator := 2073926509799594354332925952 }, { target := 161, numerator := 49640434524880613255323582464 }, { target := 162, numerator := 2073926509799594354332925952 }, { target := 177, numerator := 3472934454492201479791706112 }, { target := 178, numerator := 292036425377825949890509799424 }, { target := 183, numerator := 292036354922904267456868515840 }, { target := 191, numerator := 3473004909413883913432989696 }, { target := 219, numerator := 86268190909062678763798528 }, { target := 220, numerator := 12741360339032795315330613248 }, { target := 222, numerator := 132801067968644959198899077120 }, { target := 230, numerator := 12741360339032795315330613248 }, { target := 237, numerator := 86268190909062678763798528 }, { target := 359, numerator := 86268190909062678763798528 }, { target := 360, numerator := 12741360339032795315330613248 }, { target := 362, numerator := 132801067968644959198899077120 }, { target := 370, numerator := 12741360339032795315330613248 }, { target := 377, numerator := 86268190909062678763798528 }, { target := 392, numerator := 358549272114740053772599296 }, { target := 393, numerator := 30150136468820943846550536192 }, { target := 398, numerator := 30150129194983439236564254720 }, { target := 406, numerator := 358556545952244663758880768 }, { target := 434, numerator := 86268190909062678763798528 }, { target := 435, numerator := 12741360339032795315330613248 }, { target := 437, numerator := 132801067968644959198899077120 }, { target := 445, numerator := 12741360339032795315330613248 }, { target := 452, numerator := 86268190909062678763798528 }, { target := 469, numerator := 86268190909062678763798528 }, { target := 470, numerator := 12741360339032795315330613248 }, { target := 472, numerator := 132801067968644959198899077120 }, { target := 480, numerator := 12741360339032795315330613248 }, { target := 487, numerator := 86268190909062678763798528 }]

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
    Slot5.Left14.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot6.Left4.expected,
    Slot6.Left5.expected,
    Slot6.Left6.expected,
    Slot6.Left7.expected,
    Slot6.Left8.expected,
    Slot6.Left9.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 17, numerator := 318710464101991158908977152 }, { target := 19, numerator := 3087052848437512426481516544 }, { target := 24, numerator := 318710464101991158908977152 }, { target := 37, numerator := 26800121305618616752489365504 }, { target := 39, numerator := 259587933669178622124897599488 }, { target := 44, numerator := 26800121305618616752489365504 }, { target := 61, numerator := 24769463603301392014376960 }, { target := 62, numerator := 2073925759247694855275544576 }, { target := 67, numerator := 2073926509799594354332925952 }, { target := 75, numerator := 24768713051401892956995584 }, { target := 132, numerator := 592869096569342995957022720 }, { target := 133, numerator := 49640416560057728471434002432 }, { target := 138, numerator := 49640434524880613255323582464 }, { target := 146, numerator := 592851131746458212067442688 }, { target := 153, numerator := 26800114839985279321390448640 }, { target := 155, numerator := 259587871042581571072772014080 }, { target := 160, numerator := 26800114839985279321390448640 }, { target := 177, numerator := 443453299994589437676748800 }, { target := 178, numerator := 37129961173628085312191201280 }, { target := 183, numerator := 37129974610928221504992706560 }, { target := 191, numerator := 443439862694453244875243520 }, { target := 203, numerator := 514565630984712788943831040 }, { target := 204, numerator := 43084135127597273767659700224 }, { target := 209, numerator := 43084150719707702070658203648 }, { target := 217, numerator := 514550038874284485945327616 }, { target := 272, numerator := 24769463603301392014376960 }, { target := 273, numerator := 2073925759247694855275544576 }, { target := 278, numerator := 2073926509799594354332925952 }, { target := 286, numerator := 24768713051401892956995584 }, { target := 317, numerator := 513766616029767582749818880 }, { target := 318, numerator := 43017234296653799740070166528 }, { target := 323, numerator := 43017249864552876446324883456 }, { target := 331, numerator := 513751048130690876495101952 }, { target := 343, numerator := 516163660894603201331855360 }, { target := 344, numerator := 43217936789484221822838767616 }, { target := 349, numerator := 43217952430017353319324844032 }, { target := 357, numerator := 516148020361471704845778944 }, { target := 382, numerator := 343485642786730482964889600 }, { target := 383, numerator := 592851131746458212067442688 }, { target := 384, numerator := 3530555337729016723482345472 }, { target := 385, numerator := 514550038874284485945327616 }, { target := 386, numerator := 24768713051401892956995584 }, { target := 387, numerator := 513751048130690876495101952 }, { target := 388, numerator := 516148020361471704845778944 }, { target := 389, numerator := 343485642786730482964889600 }, { target := 390, numerator := 592851131746458212067442688 }, { target := 391, numerator := 24768713051401892956995584 }, { target := 392, numerator := 24769463603301392014376960 }, { target := 393, numerator := 2073925759247694855275544576 }, { target := 398, numerator := 2073926509799594354332925952 }, { target := 406, numerator := 24768713051401892956995584 }, { target := 418, numerator := 592869096569342995957022720 }, { target := 419, numerator := 49640416560057728471434002432 }, { target := 424, numerator := 49640434524880613255323582464 }, { target := 432, numerator := 592851131746458212067442688 }, { target := 453, numerator := 24769463603301392014376960 }, { target := 454, numerator := 2073925759247694855275544576 }, { target := 459, numerator := 2073926509799594354332925952 }, { target := 467, numerator := 24768713051401892956995584 }]

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
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left2.expected,
    Slot9.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 86268190909062678763798528 }, { target := 3, numerator := 86268190909062678763798528 }, { target := 4, numerator := 86268190909062678763798528 }, { target := 5, numerator := 86268190909062678763798528 }, { target := 8, numerator := 12741360339032795315330613248 }, { target := 9, numerator := 12741360339032795315330613248 }, { target := 10, numerator := 12741360339032795315330613248 }, { target := 11, numerator := 12741360339032795315330613248 }, { target := 17, numerator := 15937986879685052596224000 }, { target := 18, numerator := 319397257068888454028328960 }, { target := 19, numerator := 536153878632605169336975360 }, { target := 20, numerator := 514478216476233497806110720 }, { target := 21, numerator := 15937986879685052596224000 }, { target := 22, numerator := 514478216476233497806110720 }, { target := 23, numerator := 343622997126009733974589440 }, { target := 24, numerator := 16575506354872454700072960 }, { target := 25, numerator := 319397257068888454028328960 }, { target := 26, numerator := 15300467404497650492375040 }, { target := 28, numerator := 132801067968644959198899077120 }, { target := 29, numerator := 132801067968644959198899077120 }, { target := 30, numerator := 132801067968644959198899077120 }, { target := 31, numerator := 132801067968644959198899077120 }, { target := 37, numerator := 12396212017532818685952000 }, { target := 38, numerator := 248420088831357686466478080 }, { target := 39, numerator := 417008572269804020595425280 }, { target := 40, numerator := 400149723925959387182530560 }, { target := 41, numerator := 12396212017532818685952000 }, { target := 42, numerator := 400149723925959387182530560 }, { target := 43, numerator := 267262331098007570869125120 }, { target := 44, numerator := 12892060498234131433390080 }, { target := 45, numerator := 248420088831357686466478080 }, { target := 46, numerator := 11900363536831505938513920 }, { target := 51, numerator := 14167099448608935641088000 }, { target := 52, numerator := 283908672950123070247403520 }, { target := 53, numerator := 476581225451204594966200320 }, { target := 54, numerator := 457313970201096442494320640 }, { target := 55, numerator := 14167099448608935641088000 }, { target := 56, numerator := 457313970201096442494320640 }, { target := 57, numerator := 305442664112008652421857280 }, { target := 58, numerator := 14733783426553293066731520 }, { target := 59, numerator := 283908672950123070247403520 }, { target := 60, numerator := 13600415470664578215444480 }, { target := 88, numerator := 16646341852115499378278400 }, { target := 89, numerator := 333592690716394607540699136 }, { target := 90, numerator := 559982939905165399085285376 }, { target := 91, numerator := 537343914986288319930826752 }, { target := 92, numerator := 16646341852115499378278400 }, { target := 93, numerator := 537343914986288319930826752 }, { target := 94, numerator := 358895130331610166595682304 }, { target := 95, numerator := 17312195526200119353409536 }, { target := 96, numerator := 333592690716394607540699136 }, { target := 97, numerator := 15980488178030879403147264 }, { target := 149, numerator := 12741360339032795315330613248 }, { target := 150, numerator := 12741360339032795315330613248 }, { target := 151, numerator := 12741360339032795315330613248 }, { target := 152, numerator := 12741360339032795315330613248 }, { target := 378, numerator := 86268190909062678763798528 }, { target := 379, numerator := 86268190909062678763798528 }, { target := 380, numerator := 86268190909062678763798528 }, { target := 381, numerator := 86268190909062678763798528 }]

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
    Slot9.Left4.expected,
    Slot9.Left5.expected,
    Slot9.Left6.expected,
    Slot9.Left7.expected,
    Slot9.Left8.expected,
    Slot9.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 108, numerator := 196568504849448982020096000 }, { target := 109, numerator := 3939232837182957599682723840 }, { target := 110, numerator := 6612564503135463755156029440 }, { target := 111, numerator := 6345231336540213139608698880 }, { target := 112, numerator := 196568504849448982020096000 }, { target := 113, numerator := 6345231336540213139608698880 }, { target := 114, numerator := 4238016964554120052353269760 }, { target := 115, numerator := 204431245043426941300899840 }, { target := 116, numerator := 3939232837182957599682723840 }, { target := 117, numerator := 188705764655471022739292160 }, { target := 122, numerator := 442013502796598792001945600 }, { target := 123, numerator := 8857950596043839791718989824 }, { target := 124, numerator := 14869334234077583362945449984 }, { target := 125, numerator := 14268195870274209005822803968 }, { target := 126, numerator := 442013502796598792001945600 }, { target := 127, numerator := 14268195870274209005822803968 }, { target := 128, numerator := 9529811120294669955561947136 }, { target := 129, numerator := 459694042908462743682023424 }, { target := 130, numerator := 8857950596043839791718989824 }, { target := 131, numerator := 424332962684734840321867776 }, { target := 153, numerator := 12396212017532818685952000 }, { target := 154, numerator := 248420088831357686466478080 }, { target := 155, numerator := 417008572269804020595425280 }, { target := 156, numerator := 400149723925959387182530560 }, { target := 157, numerator := 12396212017532818685952000 }, { target := 158, numerator := 400149723925959387182530560 }, { target := 159, numerator := 267262331098007570869125120 }, { target := 160, numerator := 12892060498234131433390080 }, { target := 161, numerator := 248420088831357686466478080 }, { target := 162, numerator := 11900363536831505938513920 }, { target := 167, numerator := 196568504849448982020096000 }, { target := 168, numerator := 3939232837182957599682723840 }, { target := 169, numerator := 6612564503135463755156029440 }, { target := 170, numerator := 6345231336540213139608698880 }, { target := 171, numerator := 196568504849448982020096000 }, { target := 172, numerator := 6345231336540213139608698880 }, { target := 173, numerator := 4238016964554120052353269760 }, { target := 174, numerator := 204431245043426941300899840 }, { target := 175, numerator := 3939232837182957599682723840 }, { target := 176, numerator := 188705764655471022739292160 }, { target := 193, numerator := 14167099448608935641088000 }, { target := 194, numerator := 283908672950123070247403520 }, { target := 195, numerator := 476581225451204594966200320 }, { target := 196, numerator := 457313970201096442494320640 }, { target := 197, numerator := 14167099448608935641088000 }, { target := 198, numerator := 457313970201096442494320640 }, { target := 199, numerator := 305442664112008652421857280 }, { target := 200, numerator := 14733783426553293066731520 }, { target := 201, numerator := 283908672950123070247403520 }, { target := 202, numerator := 13600415470664578215444480 }, { target := 248, numerator := 13812921962393712250060800 }, { target := 249, numerator := 276810956126369993491218432 }, { target := 250, numerator := 464666694814924480092045312 }, { target := 251, numerator := 445881120946069031431962624 }, { target := 252, numerator := 13812921962393712250060800 }, { target := 253, numerator := 445881120946069031431962624 }, { target := 254, numerator := 297806597509208436111310848 }, { target := 255, numerator := 14365438840889460740063232 }, { target := 256, numerator := 276810956126369993491218432 }, { target := 257, numerator := 13260405083897963760058368 }]

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
  [{ target := 2, numerator := 54057491755103076902502400 }, { target := 3, numerator := 49409557884570849729576960 }, { target := 4, numerator := 54057491755103076902502400 }, { target := 5, numerator := 49409557884570849729576960 }, { target := 262, numerator := 13812921962393712250060800 }, { target := 263, numerator := 276810956126369993491218432 }, { target := 264, numerator := 464666694814924480092045312 }, { target := 265, numerator := 445881120946069031431962624 }, { target := 266, numerator := 13812921962393712250060800 }, { target := 267, numerator := 445881120946069031431962624 }, { target := 268, numerator := 297806597509208436111310848 }, { target := 269, numerator := 14365438840889460740063232 }, { target := 270, numerator := 276810956126369993491218432 }, { target := 271, numerator := 13260405083897963760058368 }, { target := 293, numerator := 13812921962393712250060800 }, { target := 294, numerator := 276810956126369993491218432 }, { target := 295, numerator := 464666694814924480092045312 }, { target := 296, numerator := 445881120946069031431962624 }, { target := 297, numerator := 13812921962393712250060800 }, { target := 298, numerator := 445881120946069031431962624 }, { target := 299, numerator := 297806597509208436111310848 }, { target := 300, numerator := 14365438840889460740063232 }, { target := 301, numerator := 276810956126369993491218432 }, { target := 302, numerator := 13260405083897963760058368 }, { target := 307, numerator := 442013502796598792001945600 }, { target := 308, numerator := 8857950596043839791718989824 }, { target := 309, numerator := 14869334234077583362945449984 }, { target := 310, numerator := 14268195870274209005822803968 }, { target := 311, numerator := 442013502796598792001945600 }, { target := 312, numerator := 14268195870274209005822803968 }, { target := 313, numerator := 9529811120294669955561947136 }, { target := 314, numerator := 459694042908462743682023424 }, { target := 315, numerator := 8857950596043839791718989824 }, { target := 316, numerator := 424332962684734840321867776 }, { target := 333, numerator := 13812921962393712250060800 }, { target := 334, numerator := 276810956126369993491218432 }, { target := 335, numerator := 464666694814924480092045312 }, { target := 336, numerator := 445881120946069031431962624 }, { target := 337, numerator := 13812921962393712250060800 }, { target := 338, numerator := 445881120946069031431962624 }, { target := 339, numerator := 297806597509208436111310848 }, { target := 340, numerator := 14365438840889460740063232 }, { target := 341, numerator := 276810956126369993491218432 }, { target := 342, numerator := 13260405083897963760058368 }, { target := 382, numerator := 15937986879685052596224000 }, { target := 383, numerator := 319397257068888454028328960 }, { target := 384, numerator := 536153878632605169336975360 }, { target := 385, numerator := 514478216476233497806110720 }, { target := 386, numerator := 15937986879685052596224000 }, { target := 387, numerator := 514478216476233497806110720 }, { target := 388, numerator := 343622997126009733974589440 }, { target := 389, numerator := 16575506354872454700072960 }, { target := 390, numerator := 319397257068888454028328960 }, { target := 391, numerator := 15300467404497650492375040 }, { target := 408, numerator := 16646341852115499378278400 }, { target := 409, numerator := 333592690716394607540699136 }, { target := 410, numerator := 559982939905165399085285376 }, { target := 411, numerator := 537343914986288319930826752 }, { target := 412, numerator := 16646341852115499378278400 }, { target := 413, numerator := 537343914986288319930826752 }, { target := 414, numerator := 358895130331610166595682304 }, { target := 415, numerator := 17312195526200119353409536 }, { target := 416, numerator := 333592690716394607540699136 }, { target := 417, numerator := 15980488178030879403147264 }]

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
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 9243012359057030662443761664 }, { target := 6, numerator := 347283718955132488508504014848 }, { target := 8, numerator := 8630126822702984920353996800 }, { target := 9, numerator := 7888097226732260983276830720 }, { target := 10, numerator := 8630126822702984920353996800 }, { target := 11, numerator := 7888097226732260983276830720 }, { target := 27, numerator := 347257453152754767541825437696 }, { target := 28, numerator := 86115687698226131006966988800 }, { target := 29, numerator := 78711348195201080490480107520 }, { target := 30, numerator := 86115687698226131006966988800 }, { target := 31, numerator := 78711348195201080490480107520 }, { target := 148, numerator := 9269278161434751629122338816 }, { target := 149, numerator := 8630126822702984920353996800 }, { target := 150, numerator := 7888097226732260983276830720 }, { target := 151, numerator := 8630126822702984920353996800 }, { target := 152, numerator := 7888097226732260983276830720 }, { target := 378, numerator := 54051323625053430271180800 }, { target := 379, numerator := 49403920098413322247864320 }, { target := 380, numerator := 54051323625053430271180800 }, { target := 381, numerator := 49403920098413322247864320 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6.Parent2
