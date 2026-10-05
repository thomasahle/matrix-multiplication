import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk19Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 78; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19.Parent0

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
    Slot2.Left6.expected,
    Slot2.Left14.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left6.expected,
    Slot4.Left14.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left3.expected,
    Slot5.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 14532483331848937584721920 }, { target := 132, numerator := 258678203306911089008050176 }, { target := 133, numerator := 14532483331848937584721920 }, { target := 134, numerator := 230097652754274845091430400 }, { target := 135, numerator := 392861466070982946040315904 }, { target := 136, numerator := 14532483331848937584721920 }, { target := 137, numerator := 392861466070982946040315904 }, { target := 138, numerator := 392861466070982946040315904 }, { target := 139, numerator := 258678203306911089008050176 }, { target := 140, numerator := 14532483331848937584721920 }, { target := 227, numerator := 2146371736799958195209502720 }, { target := 228, numerator := 38205416915039255874729148416 }, { target := 229, numerator := 2146371736799958195209502720 }, { target := 230, numerator := 33984219165999338090817126400 }, { target := 231, numerator := 58023582618158869877163556864 }, { target := 232, numerator := 2146371736799958195209502720 }, { target := 233, numerator := 58023582618158869877163556864 }, { target := 234, numerator := 58023582618158869877163556864 }, { target := 235, numerator := 38205416915039255874729148416 }, { target := 236, numerator := 2146371736799958195209502720 }, { target := 263, numerator := 2205280563143279248442130432 }, { target := 264, numerator := 123504883035816157417308160 }, { target := 265, numerator := 2205280563143279248442130432 }, { target := 266, numerator := 123504883035816157417308160 }, { target := 302, numerator := 22371273656827397911923916800 }, { target := 303, numerator := 398208671091527682832245719040 }, { target := 304, numerator := 22371273656827397911923916800 }, { target := 305, numerator := 354211832899767133605462016000 }, { target := 306, numerator := 604770097856233990219009884160 }, { target := 307, numerator := 22371273656827397911923916800 }, { target := 308, numerator := 604770097856233990219009884160 }, { target := 309, numerator := 604770097856233990219009884160 }, { target := 310, numerator := 398208671091527682832245719040 }, { target := 311, numerator := 22371273656827397911923916800 }, { target := 338, numerator := 185400663827933334599161085952 }, { target := 339, numerator := 10340957011548413978839351296 }, { target := 340, numerator := 185400663827933334599161085952 }, { target := 341, numerator := 10340957011548413978839351296 }, { target := 589, numerator := 2146371736799958195209502720 }, { target := 590, numerator := 38205416915039255874729148416 }, { target := 591, numerator := 2146371736799958195209502720 }, { target := 592, numerator := 33984219165999338090817126400 }, { target := 593, numerator := 58023582618158869877163556864 }, { target := 594, numerator := 2146371736799958195209502720 }, { target := 595, numerator := 58023582618158869877163556864 }, { target := 596, numerator := 58023582618158869877163556864 }, { target := 597, numerator := 38205416915039255874729148416 }, { target := 598, numerator := 2146371736799958195209502720 }, { target := 599, numerator := 185400624667801509122996699136 }, { target := 600, numerator := 10340960753931617932664635392 }, { target := 601, numerator := 185400624667801509122996699136 }, { target := 602, numerator := 10340960753931617932664635392 }, { target := 773, numerator := 2205319723275104724606517248 }, { target := 774, numerator := 123501140652612203592024064 }, { target := 775, numerator := 2205319723275104724606517248 }, { target := 776, numerator := 123501140652612203592024064 }]

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
    Slot5.Left18.expected,
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
    Slot6.Left10.expected,
    Slot6.Left11.expected,
    Slot6.Left12.expected,
    Slot6.Left13.expected,
    Slot6.Left14.expected,
    Slot6.Left15.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 4326096467201136425923772416 }, { target := 134, numerator := 15476324479741310543899656192 }, { target := 136, numerator := 4326095029029512720777478144 }, { target := 227, numerator := 690649157906382431316567130112 }, { target := 230, numerator := 2470751762115597348799191711744 }, { target := 232, numerator := 690648928306319564610950135808 }, { target := 263, numerator := 23066304638247124653393838080 }, { target := 265, numerator := 23066304638247124653393838080 }, { target := 302, numerator := 6891639997091131411334684475392 }, { target := 305, numerator := 24654387067228317530628349231104 }, { target := 307, numerator := 6891637706027776779241629155328 }, { target := 338, numerator := 17940459163081096952639651840 }, { target := 340, numerator := 17940459163081096952639651840 }, { target := 352, numerator := 20503381900664110803016744960 }, { target := 354, numerator := 20503381900664110803016744960 }, { target := 479, numerator := 24091473733280330193544675328 }, { target := 481, numerator := 24091473733280330193544675328 }, { target := 554, numerator := 284484423871714537391857336320 }, { target := 556, numerator := 284484423871714537391857336320 }, { target := 568, numerator := 639705515300720257054122442752 }, { target := 570, numerator := 639705515300720257054122442752 }, { target := 589, numerator := 690649157906382431316567130112 }, { target := 592, numerator := 2470751762115597348799191711744 }, { target := 594, numerator := 690648928306319564610950135808 }, { target := 599, numerator := 17940459163081096952639651840 }, { target := 601, numerator := 17940459163081096952639651840 }, { target := 613, numerator := 284484423871714537391857336320 }, { target := 615, numerator := 284484423871714537391857336320 }, { target := 618, numerator := 20503381900664110803016744960 }, { target := 620, numerator := 20503381900664110803016744960 }, { target := 694, numerator := 19990797353147508032941326336 }, { target := 696, numerator := 19990797353147508032941326336 }, { target := 708, numerator := 19990797353147508032941326336 }, { target := 710, numerator := 19990797353147508032941326336 }, { target := 739, numerator := 19990797353147508032941326336 }, { target := 741, numerator := 19990797353147508032941326336 }, { target := 753, numerator := 639705515300720257054122442752 }, { target := 755, numerator := 639705515300720257054122442752 }, { target := 758, numerator := 19990797353147508032941326336 }, { target := 760, numerator := 19990797353147508032941326336 }, { target := 763, numerator := 4340135329302131742282350592 }, { target := 764, numerator := 258678203306911089008050176 }, { target := 765, numerator := 14532483331848937584721920 }, { target := 766, numerator := 15704656235133679716861476864 }, { target := 767, numerator := 392861466070982946040315904 }, { target := 768, numerator := 4340133891294607948558368768 }, { target := 769, numerator := 392861466070982946040315904 }, { target := 770, numerator := 392861466070982946040315904 }, { target := 771, numerator := 258678203306911089008050176 }, { target := 772, numerator := 14532483331848937584721920 }, { target := 773, numerator := 23066304638247124653393838080 }, { target := 775, numerator := 23066304638247124653393838080 }, { target := 778, numerator := 24091473733280330193544675328 }, { target := 780, numerator := 24091473733280330193544675328 }]

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
    Slot8.Left5.expected,
    Slot8.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 6442828927363537866269392896 }, { target := 81, numerator := 7650859351244201216194904064 }, { target := 82, numerator := 5838813715423206191306637312 }, { target := 83, numerator := 60200182790053056937954639872 }, { target := 84, numerator := 7248182543283980099553067008 }, { target := 85, numerator := 5838813715423206191306637312 }, { target := 86, numerator := 7248182543283980099553067008 }, { target := 87, numerator := 7248182543283980099553067008 }, { target := 88, numerator := 310463818937330480930856370176 }, { target := 89, numerator := 7248182543283980099553067008 }, { target := 90, numerator := 60200182790053056937954639872 }, { target := 91, numerator := 310463818937330480930856370176 }, { target := 92, numerator := 6442828927363537866269392896 }, { target := 93, numerator := 7248182543283980099553067008 }, { target := 94, numerator := 7248182543283980099553067008 }, { target := 95, numerator := 7650859351244201216194904064 }, { target := 176, numerator := 242073633959176552319729795072 }, { target := 177, numerator := 287462440326522155879679131648 }, { target := 178, numerator := 219379230775503750539755126784 }, { target := 179, numerator := 2261875517306055910737475272704 }, { target := 180, numerator := 272332838204073621359696019456 }, { target := 181, numerator := 219379230775503750539755126784 }, { target := 182, numerator := 272332838204073621359696019456 }, { target := 183, numerator := 272332838204073621359696019456 }, { target := 184, numerator := 11664923236407820114906979500032 }, { target := 185, numerator := 272332838204073621359696019456 }, { target := 186, numerator := 2261875517306055910737475272704 }, { target := 187, numerator := 11664923236407820114906979500032 }, { target := 188, numerator := 242073633959176552319729795072 }, { target := 189, numerator := 272332838204073621359696019456 }, { target := 190, numerator := 272332838204073621359696019456 }, { target := 191, numerator := 287462440326522155879679131648 }, { target := 286, numerator := 242055325418109443000074502144 }, { target := 287, numerator := 287440698934004963562588471296 }, { target := 288, numerator := 219362638660161682718817517568 }, { target := 289, numerator := 2261704446875460108031946129408 }, { target := 290, numerator := 272312241095373123375083814912 }, { target := 291, numerator := 219362638660161682718817517568 }, { target := 292, numerator := 272312241095373123375083814912 }, { target := 293, numerator := 272312241095373123375083814912 }, { target := 294, numerator := 11664040993585148784566090072064 }, { target := 295, numerator := 272312241095373123375083814912 }, { target := 296, numerator := 2261704446875460108031946129408 }, { target := 297, numerator := 11664040993585148784566090072064 }, { target := 298, numerator := 242055325418109443000074502144 }, { target := 299, numerator := 272312241095373123375083814912 }, { target := 300, numerator := 272312241095373123375083814912 }, { target := 301, numerator := 287440698934004963562588471296 }, { target := 573, numerator := 6461137468430647185924685824 }, { target := 574, numerator := 7672600743761393533285564416 }, { target := 575, numerator := 5855405830765274012244246528 }, { target := 576, numerator := 60371253220648859643483783168 }, { target := 577, numerator := 7268779651984478084165271552 }, { target := 578, numerator := 5855405830765274012244246528 }, { target := 579, numerator := 7268779651984478084165271552 }, { target := 580, numerator := 7268779651984478084165271552 }, { target := 581, numerator := 311346061760001811271745798144 }, { target := 582, numerator := 7268779651984478084165271552 }, { target := 583, numerator := 60371253220648859643483783168 }, { target := 584, numerator := 311346061760001811271745798144 }, { target := 585, numerator := 6461137468430647185924685824 }, { target := 586, numerator := 7268779651984478084165271552 }, { target := 587, numerator := 7268779651984478084165271552 }, { target := 588, numerator := 7672600743761393533285564416 }]

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
    Slot9.Left16.expected,
    Slot9.Left17.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 34944271501898126840008015872 }, { target := 82, numerator := 1290445457007626949098219765760 }, { target := 85, numerator := 1290445141010091122051568893952 }, { target := 92, numerator := 34944587499433953886658887680 }, { target := 131, numerator := 13502050577145213998522695680 }, { target := 134, numerator := 49109868448646624842455449600 }, { target := 136, numerator := 13502050577145213998522695680 }, { target := 227, numerator := 226834449696039595175181287424 }, { target := 230, numerator := 825045789937263297353251553280 }, { target := 232, numerator := 226834449696039595175181287424 }, { target := 253, numerator := 491474641008085789546226122752 }, { target := 256, numerator := 1787599211530737144265378365440 }, { target := 258, numerator := 491474641008085789546226122752 }, { target := 302, numerator := 16202460692574256798227234816 }, { target := 305, numerator := 58931842138375949810946539520 }, { target := 307, numerator := 16202460692574256798227234816 }, { target := 328, numerator := 259239371081188108771635757056 }, { target := 331, numerator := 942909474214015196975144632320 }, { target := 333, numerator := 259239371081188108771635757056 }, { target := 342, numerator := 18902870808003299597931773952 }, { target := 345, numerator := 68753815828105274779437629440 }, { target := 347, numerator := 18902870808003299597931773952 }, { target := 443, numerator := 491474641008085789546226122752 }, { target := 446, numerator := 1787599211530737144265378365440 }, { target := 448, numerator := 491474641008085789546226122752 }, { target := 469, numerator := 491474641008085789546226122752 }, { target := 472, numerator := 1787599211530737144265378365440 }, { target := 474, numerator := 491474641008085789546226122752 }, { target := 518, numerator := 259239371081188108771635757056 }, { target := 521, numerator := 942909474214015196975144632320 }, { target := 523, numerator := 259239371081188108771635757056 }, { target := 544, numerator := 6065121119253630128136394899456 }, { target := 547, numerator := 22060152907132063879230987960320 }, { target := 549, numerator := 6065121119253630128136394899456 }, { target := 558, numerator := 486073820777227703946817044480 }, { target := 561, numerator := 1767955264151278494328396185600 }, { target := 563, numerator := 486073820777227703946817044480 }, { target := 589, numerator := 226834449696039595175181287424 }, { target := 592, numerator := 825045789937263297353251553280 }, { target := 594, numerator := 226834449696039595175181287424 }, { target := 603, numerator := 491474641008085789546226122752 }, { target := 606, numerator := 1787599211530737144265378365440 }, { target := 608, numerator := 491474641008085789546226122752 }, { target := 658, numerator := 18902870808003299597931773952 }, { target := 661, numerator := 68753815828105274779437629440 }, { target := 663, numerator := 18902870808003299597931773952 }, { target := 684, numerator := 486073820777227703946817044480 }, { target := 687, numerator := 1767955264151278494328396185600 }, { target := 689, numerator := 486073820777227703946817044480 }, { target := 698, numerator := 18902870808003299597931773952 }, { target := 701, numerator := 68753815828105274779437629440 }, { target := 703, numerator := 18902870808003299597931773952 }, { target := 729, numerator := 491474641008085789546226122752 }, { target := 732, numerator := 1787599211530737144265378365440 }, { target := 734, numerator := 491474641008085789546226122752 }, { target := 743, numerator := 491474641008085789546226122752 }, { target := 746, numerator := 1787599211530737144265378365440 }, { target := 748, numerator := 491474641008085789546226122752 }, { target := 763, numerator := 16202460692574256798227234816 }, { target := 766, numerator := 58931842138375949810946539520 }, { target := 768, numerator := 16202460692574256798227234816 }]

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
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 13364799745357206740596162560 }, { target := 27, numerator := 224528635722001073242015531008 }, { target := 28, numerator := 486478710731002325357700317184 }, { target := 29, numerator := 16037759694428648088715395072 }, { target := 30, numerator := 256604155110858369419446321152 }, { target := 31, numerator := 18710719643500089436834627584 }, { target := 32, numerator := 486478710731002325357700317184 }, { target := 33, numerator := 486478710731002325357700317184 }, { target := 34, numerator := 256604155110858369419446321152 }, { target := 35, numerator := 6003468045614457267875796221952 }, { target := 36, numerator := 481132790832859442661461852160 }, { target := 37, numerator := 224528635722001073242015531008 }, { target := 38, numerator := 486478710731002325357700317184 }, { target := 39, numerator := 18710719643500089436834627584 }, { target := 40, numerator := 481132790832859442661461852160 }, { target := 41, numerator := 18710719643500089436834627584 }, { target := 42, numerator := 486478710731002325357700317184 }, { target := 43, numerator := 486478710731002325357700317184 }, { target := 44, numerator := 16037759694428648088715395072 }, { target := 157, numerator := 48610657587669276686496563200 }, { target := 158, numerator := 816659047472843848333142261760 }, { target := 159, numerator := 1769427936191161671388474900480 }, { target := 160, numerator := 58332789105203132023795875840 }, { target := 161, numerator := 933324625683250112380734013440 }, { target := 162, numerator := 68054920622736987361095188480 }, { target := 163, numerator := 1769427936191161671388474900480 }, { target := 164, numerator := 1769427936191161671388474900480 }, { target := 165, numerator := 933324625683250112380734013440 }, { target := 166, numerator := 21835907388381039087574256189440 }, { target := 167, numerator := 1749983673156093960713876275200 }, { target := 168, numerator := 816659047472843848333142261760 }, { target := 169, numerator := 1769427936191161671388474900480 }, { target := 170, numerator := 68054920622736987361095188480 }, { target := 171, numerator := 1749983673156093960713876275200 }, { target := 172, numerator := 68054920622736987361095188480 }, { target := 173, numerator := 1769427936191161671388474900480 }, { target := 174, numerator := 1769427936191161671388474900480 }, { target := 175, numerator := 58332789105203132023795875840 }, { target := 176, numerator := 1290445457007626949098219765760 }, { target := 178, numerator := 47654433929783570178067188940800 }, { target := 181, numerator := 47654422260414972481954287452160 }, { target := 188, numerator := 1290457126376224645211121254400 }, { target := 286, numerator := 1290445141010091122051568893952 }, { target := 288, numerator := 47654422260414972481954287452160 }, { target := 291, numerator := 47654410591049232319804952543232 }, { target := 298, numerator := 1290456810375831284200903802880 }, { target := 573, numerator := 34944587499433953886658887680 }, { target := 575, numerator := 1290457126376224645211121254400 }, { target := 578, numerator := 1290456810375831284200903802880 }, { target := 585, numerator := 34944903499827314896876339200 }]

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
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left2.expected,
    Slot12.Left3.expected,
    Slot12.Left4.expected,
    Slot12.Left5.expected,
    Slot12.Left6.expected,
    Slot12.Left7.expected,
    Slot12.Left8.expected,
    Slot12.Left9.expected,
    Slot12.Left10.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 6434805479135189749374910464 }, { target := 82, numerator := 241772172397583555367899496448 }, { target := 85, numerator := 241753886656692121153250000896 }, { target := 92, numerator := 6453091220026623964024406016 }, { target := 115, numerator := 7641331506473037827382706176 }, { target := 117, numerator := 287104454722130471999380652032 }, { target := 120, numerator := 287082740404821893869484376064 }, { target := 127, numerator := 7663045823781615957278982144 }, { target := 176, numerator := 5831542465466265710371012608 }, { target := 178, numerator := 219106031235310097052158918656 }, { target := 181, numerator := 219089459782627234795132813312 }, { target := 188, numerator := 5848113918149127967397117952 }, { target := 211, numerator := 60125213695669429220721819648 }, { target := 213, numerator := 2259058735839921345468810919936 }, { target := 216, numerator := 2258887878448467007025679695872 }, { target := 223, numerator := 60296071087123767663853043712 }, { target := 237, numerator := 7239156164027088468046774272 }, { target := 239, numerator := 271993693947281499788886933504 }, { target := 242, numerator := 271973122488778636297406251008 }, { target := 249, numerator := 7259727622529951959527456768 }, { target := 267, numerator := 13364799745357206740596162560 }, { target := 268, numerator := 224528635722001073242015531008 }, { target := 269, numerator := 486478710731002325357700317184 }, { target := 270, numerator := 16037759694428648088715395072 }, { target := 271, numerator := 256604155110858369419446321152 }, { target := 272, numerator := 18710719643500089436834627584 }, { target := 273, numerator := 486478710731002325357700317184 }, { target := 274, numerator := 486478710731002325357700317184 }, { target := 275, numerator := 256604155110858369419446321152 }, { target := 276, numerator := 6003468045614457267875796221952 }, { target := 277, numerator := 481132790832859442661461852160 }, { target := 278, numerator := 224528635722001073242015531008 }, { target := 279, numerator := 486478710731002325357700317184 }, { target := 280, numerator := 18710719643500089436834627584 }, { target := 281, numerator := 481132790832859442661461852160 }, { target := 282, numerator := 18710719643500089436834627584 }, { target := 283, numerator := 486478710731002325357700317184 }, { target := 284, numerator := 486478710731002325357700317184 }, { target := 285, numerator := 16037759694428648088715395072 }, { target := 286, numerator := 5831542465466265710371012608 }, { target := 288, numerator := 219106031235310097052158918656 }, { target := 291, numerator := 219089459782627234795132813312 }, { target := 298, numerator := 5848113918149127967397117952 }, { target := 312, numerator := 7239156164027088468046774272 }, { target := 314, numerator := 271993693947281499788886933504 }, { target := 317, numerator := 271973122488778636297406251008 }, { target := 324, numerator := 7259727622529951959527456768 }, { target := 392, numerator := 7239156164027088468046774272 }, { target := 394, numerator := 271993693947281499788886933504 }, { target := 397, numerator := 271973122488778636297406251008 }, { target := 404, numerator := 7259727622529951959527456768 }, { target := 427, numerator := 310077189025826956048003497984 }, { target := 429, numerator := 11650396557408557574290656985088 }, { target := 432, numerator := 11649515413269351588072234418176 }, { target := 439, numerator := 310958333165032942266426064896 }, { target := 453, numerator := 7239156164027088468046774272 }, { target := 455, numerator := 271993693947281499788886933504 }, { target := 458, numerator := 271973122488778636297406251008 }, { target := 465, numerator := 7259727622529951959527456768 }, { target := 502, numerator := 60125213695669429220721819648 }, { target := 504, numerator := 2259058735839921345468810919936 }, { target := 507, numerator := 2258887878448467007025679695872 }, { target := 514, numerator := 60296071087123767663853043712 }]

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
    Slot12.Left11.expected,
    Slot12.Left12.expected,
    Slot12.Left13.expected,
    Slot12.Left14.expected,
    Slot12.Left15.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 23501517933308391156288061440 }, { target := 11, numerator := 18278958392573193121557381120 }, { target := 12, numerator := 20890238162940792138922721280 }, { target := 13, numerator := 24546029841455430763234197504 }, { target := 14, numerator := 289852054510803490927552757760 }, { target := 15, numerator := 651775430683752714734388903936 }, { target := 16, numerator := 18278958392573193121557381120 }, { target := 17, numerator := 289852054510803490927552757760 }, { target := 18, numerator := 20890238162940792138922721280 }, { target := 19, numerator := 20367982208867272335449653248 }, { target := 20, numerator := 20367982208867272335449653248 }, { target := 21, numerator := 20367982208867272335449653248 }, { target := 22, numerator := 651775430683752714734388903936 }, { target := 23, numerator := 20367982208867272335449653248 }, { target := 24, numerator := 23501517933308391156288061440 }, { target := 25, numerator := 24546029841455430763234197504 }, { target := 26, numerator := 4326096467201136425923772416 }, { target := 27, numerator := 690649157906382431316567130112 }, { target := 29, numerator := 6891639997091131411334684475392 }, { target := 37, numerator := 690649157906382431316567130112 }, { target := 44, numerator := 4325602845970282804697628672 }, { target := 157, numerator := 15476324479741310543899656192 }, { target := 158, numerator := 2470751762115597348799191711744 }, { target := 160, numerator := 24654387067228317530628349231104 }, { target := 168, numerator := 2470751762115597348799191711744 }, { target := 175, numerator := 15474558582379404871770046464 }, { target := 267, numerator := 4326095029029512720777478144 }, { target := 268, numerator := 690648928306319564610950135808 }, { target := 270, numerator := 6891637706027776779241629155328 }, { target := 278, numerator := 690648928306319564610950135808 }, { target := 285, numerator := 4325601407962759010973646848 }, { target := 528, numerator := 310077189025826956048003497984 }, { target := 530, numerator := 11650396557408557574290656985088 }, { target := 533, numerator := 11649515413269351588072234418176 }, { target := 540, numerator := 310958333165032942266426064896 }, { target := 573, numerator := 6434805479135189749374910464 }, { target := 575, numerator := 241772172397583555367899496448 }, { target := 578, numerator := 241753886656692121153250000896 }, { target := 585, numerator := 6453091220026623964024406016 }, { target := 642, numerator := 7239156164027088468046774272 }, { target := 644, numerator := 271993693947281499788886933504 }, { target := 647, numerator := 271973122488778636297406251008 }, { target := 654, numerator := 7259727622529951959527456768 }, { target := 668, numerator := 7239156164027088468046774272 }, { target := 670, numerator := 271993693947281499788886933504 }, { target := 673, numerator := 271973122488778636297406251008 }, { target := 680, numerator := 7259727622529951959527456768 }, { target := 713, numerator := 7641331506473037827382706176 }, { target := 715, numerator := 287104454722130471999380652032 }, { target := 718, numerator := 287082740404821893869484376064 }, { target := 725, numerator := 7663045823781615957278982144 }]

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
    Slot14.Left2.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left2.expected,
    Slot15.Left3.expected,
    Slot15.Left4.expected,
    Slot15.Left5.expected,
    Slot15.Left6.expected,
    Slot15.Left7.expected,
    Slot15.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 14848406882541305793085440 }, { target := 27, numerator := 2193031991947783373366231040 }, { target := 29, numerator := 22857605692845384823052697600 }, { target := 37, numerator := 2193031991947783373366231040 }, { target := 44, numerator := 14848406882541305793085440 }, { target := 61, numerator := 264301642509235243116920832 }, { target := 62, numerator := 39035969456670544045918912512 }, { target := 64, numerator := 406865381332647849850338017280 }, { target := 72, numerator := 39035969456670544045918912512 }, { target := 79, numerator := 264301642509235243116920832 }, { target := 96, numerator := 14848406882541305793085440 }, { target := 97, numerator := 2193031991947783373366231040 }, { target := 99, numerator := 22857605692845384823052697600 }, { target := 107, numerator := 2193031991947783373366231040 }, { target := 114, numerator := 14848406882541305793085440 }, { target := 141, numerator := 23501517933308391156288061440 }, { target := 142, numerator := 18278958392573193121557381120 }, { target := 143, numerator := 20890238162940792138922721280 }, { target := 144, numerator := 24546029841455430763234197504 }, { target := 145, numerator := 289852054510803490927552757760 }, { target := 146, numerator := 651775430683752714734388903936 }, { target := 147, numerator := 18278958392573193121557381120 }, { target := 148, numerator := 289852054510803490927552757760 }, { target := 149, numerator := 20890238162940792138922721280 }, { target := 150, numerator := 20367982208867272335449653248 }, { target := 151, numerator := 20367982208867272335449653248 }, { target := 152, numerator := 20367982208867272335449653248 }, { target := 153, numerator := 651775430683752714734388903936 }, { target := 154, numerator := 20367982208867272335449653248 }, { target := 155, numerator := 23501517933308391156288061440 }, { target := 156, numerator := 24546029841455430763234197504 }, { target := 157, numerator := 235099775640237341723852800 }, { target := 158, numerator := 34723006539173236744965324800 }, { target := 160, numerator := 361912090136718593031667712000 }, { target := 168, numerator := 34723006539173236744965324800 }, { target := 175, numerator := 235099775640237341723852800 }, { target := 192, numerator := 401401932724699966606409728 }, { target := 193, numerator := 59284964848988410526667112448 }, { target := 195, numerator := 617917273896586903049857925120 }, { target := 203, numerator := 59284964848988410526667112448 }, { target := 210, numerator := 401401932724699966606409728 }, { target := 267, numerator := 14848406882541305793085440 }, { target := 268, numerator := 2193031991947783373366231040 }, { target := 270, numerator := 22857605692845384823052697600 }, { target := 278, numerator := 2193031991947783373366231040 }, { target := 285, numerator := 14848406882541305793085440 }, { target := 373, numerator := 401401932724699966606409728 }, { target := 374, numerator := 59284964848988410526667112448 }, { target := 376, numerator := 617917273896586903049857925120 }, { target := 384, numerator := 59284964848988410526667112448 }, { target := 391, numerator := 401401932724699966606409728 }, { target := 408, numerator := 401401932724699966606409728 }, { target := 409, numerator := 59284964848988410526667112448 }, { target := 411, numerator := 617917273896586903049857925120 }, { target := 419, numerator := 59284964848988410526667112448 }, { target := 426, numerator := 401401932724699966606409728 }, { target := 483, numerator := 264301642509235243116920832 }, { target := 484, numerator := 39035969456670544045918912512 }, { target := 486, numerator := 406865381332647849850338017280 }, { target := 494, numerator := 39035969456670544045918912512 }, { target := 501, numerator := 264301642509235243116920832 }]

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
    Slot15.Left9.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left2.expected,
    Slot18.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 2205280563143279248442130432 }, { target := 11, numerator := 185400663827933334599161085952 }, { target := 16, numerator := 185400624667801509122996699136 }, { target := 24, numerator := 2205319723275104724606517248 }, { target := 45, numerator := 123504883035816157417308160 }, { target := 46, numerator := 10340957011548413978839351296 }, { target := 51, numerator := 10340960753931617932664635392 }, { target := 59, numerator := 123501140652612203592024064 }, { target := 141, numerator := 2205280563143279248442130432 }, { target := 142, numerator := 185400663827933334599161085952 }, { target := 147, numerator := 185400624667801509122996699136 }, { target := 155, numerator := 2205319723275104724606517248 }, { target := 357, numerator := 123504883035816157417308160 }, { target := 358, numerator := 10340957011548413978839351296 }, { target := 363, numerator := 10340960753931617932664635392 }, { target := 371, numerator := 123501140652612203592024064 }, { target := 623, numerator := 14848406882541305793085440 }, { target := 624, numerator := 2193031991947783373366231040 }, { target := 626, numerator := 22857605692845384823052697600 }, { target := 634, numerator := 2193031991947783373366231040 }, { target := 641, numerator := 14848406882541305793085440 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19.Parent0
