import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk20Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 84; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk20.Parent2

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
    Slot3.Left11.expected,
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot4.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 8487531415754501794037760 }, { target := 132, numerator := 151078059200430131933872128 }, { target := 133, numerator := 8487531415754501794037760 }, { target := 134, numerator := 134385914082779611738931200 }, { target := 135, numerator := 229446265939230031832154112 }, { target := 136, numerator := 8487531415754501794037760 }, { target := 137, numerator := 229446265939230031832154112 }, { target := 138, numerator := 229446265939230031832154112 }, { target := 139, numerator := 151078059200430131933872128 }, { target := 140, numerator := 8487531415754501794037760 }, { target := 263, numerator := 1850650594436828826609647616 }, { target := 264, numerator := 122982196848330606485962752 }, { target := 265, numerator := 1850650594436828826609647616 }, { target := 266, numerator := 122982196848330606485962752 }, { target := 338, numerator := 10586778237758476122767491072 }, { target := 339, numerator := 10341479697735899529770696704 }, { target := 340, numerator := 10586778237758476122767491072 }, { target := 341, numerator := 10341479697735899529770696704 }, { target := 352, numerator := 1547425049106725343623905280 }, { target := 354, numerator := 1547425049106725343623905280 }, { target := 479, numerator := 1818224432700402278758088704 }, { target := 481, numerator := 1818224432700402278758088704 }, { target := 554, numerator := 21470522556355814142781685760 }, { target := 556, numerator := 21470522556355814142781685760 }, { target := 568, numerator := 48279661532129830721065844736 }, { target := 570, numerator := 48279661532129830721065844736 }, { target := 599, numerator := 10586776010314129222339133440 }, { target := 600, numerator := 10341477202813763560553840640 }, { target := 601, numerator := 10586776010314129222339133440 }, { target := 602, numerator := 10341477202813763560553840640 }, { target := 613, numerator := 21470522556355814142781685760 }, { target := 615, numerator := 21470522556355814142781685760 }, { target := 618, numerator := 1547425049106725343623905280 }, { target := 620, numerator := 1547425049106725343623905280 }, { target := 694, numerator := 1508739422879057210033307648 }, { target := 696, numerator := 1508739422879057210033307648 }, { target := 708, numerator := 1508739422879057210033307648 }, { target := 710, numerator := 1508739422879057210033307648 }, { target := 739, numerator := 1508739422879057210033307648 }, { target := 741, numerator := 1508739422879057210033307648 }, { target := 753, numerator := 48279661532129830721065844736 }, { target := 755, numerator := 48279661532129830721065844736 }, { target := 758, numerator := 1508739422879057210033307648 }, { target := 760, numerator := 1508739422879057210033307648 }, { target := 773, numerator := 1850652821881175727038005248 }, { target := 774, numerator := 122984691770466575702818816 }, { target := 775, numerator := 1850652821881175727038005248 }, { target := 776, numerator := 122984691770466575702818816 }, { target := 778, numerator := 1818224432700402278758088704 }, { target := 780, numerator := 1818224432700402278758088704 }]

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
    Slot4.Left1.expected,
    Slot4.Left3.expected,
    Slot4.Left11.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 2236891598999655214020034560 }, { target := 134, numerator := 8002332004058033126343966720 }, { target := 136, numerator := 2236890855365284742603735040 }, { target := 227, numerator := 38934789429749442611068796928 }, { target := 228, numerator := 24119188084683183276473450496 }, { target := 229, numerator := 1355010566555235015532216320 }, { target := 230, numerator := 155893511638632844268505399296 }, { target := 231, numerator := 36630452315876519919887581184 }, { target := 232, numerator := 38934776936692018691274964992 }, { target := 233, numerator := 36630452315876519919887581184 }, { target := 234, numerator := 36630452315876519919887581184 }, { target := 235, numerator := 24119188084683183276473450496 }, { target := 236, numerator := 1355010566555235015532216320 }, { target := 253, numerator := 81422854203587449790329257984 }, { target := 256, numerator := 291284884947712405798920388608 }, { target := 258, numerator := 81422827135296364630775955456 }, { target := 302, numerator := 16205237706932287199973998592 }, { target := 303, numerator := 240673226628762076788069236736 }, { target := 304, numerator := 13520967788132700943149957120 }, { target := 305, numerator := 223684788383637404684820414464 }, { target := 306, numerator := 365516829205854015496487174144 }, { target := 307, numerator := 16205236814571042634274439168 }, { target := 308, numerator := 365516829205854015496487174144 }, { target := 309, numerator := 365516829205854015496487174144 }, { target := 310, numerator := 240673226628762076788069236736 }, { target := 311, numerator := 13520967788132700943149957120 }, { target := 328, numerator := 42948318700793380109184663552 }, { target := 331, numerator := 153644774477914236025804161024 }, { target := 333, numerator := 42948304423013467057991712768 }, { target := 342, numerator := 3131648238599517299628048384 }, { target := 345, numerator := 11203264805681246376881553408 }, { target := 347, numerator := 3131647197511398639645229056 }, { target := 443, numerator := 81422854203587449790329257984 }, { target := 446, numerator := 291284884947712405798920388608 }, { target := 448, numerator := 81422827135296364630775955456 }, { target := 469, numerator := 81422854203587449790329257984 }, { target := 472, numerator := 291284884947712405798920388608 }, { target := 474, numerator := 81422827135296364630775955456 }, { target := 589, numerator := 1355010566555235015532216320 }, { target := 590, numerator := 24119188084683183276473450496 }, { target := 591, numerator := 1355010566555235015532216320 }, { target := 592, numerator := 21454333970457887745926758400 }, { target := 593, numerator := 36630452315876519919887581184 }, { target := 594, numerator := 1355010566555235015532216320 }, { target := 595, numerator := 36630452315876519919887581184 }, { target := 596, numerator := 36630452315876519919887581184 }, { target := 597, numerator := 24119188084683183276473450496 }, { target := 598, numerator := 1355010566555235015532216320 }, { target := 763, numerator := 8486562961690632042577920 }, { target := 764, numerator := 151060820718093250357886976 }, { target := 765, numerator := 8486562961690632042577920 }, { target := 766, numerator := 134370580226768340674150400 }, { target := 767, numerator := 229420085397703419551023104 }, { target := 768, numerator := 8486562961690632042577920 }, { target := 769, numerator := 229420085397703419551023104 }, { target := 770, numerator := 229420085397703419551023104 }, { target := 771, numerator := 151060820718093250357886976 }, { target := 772, numerator := 8486562961690632042577920 }]

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
    Slot5.Left8.expected,
    Slot5.Left9.expected,
    Slot5.Left10.expected,
    Slot5.Left11.expected,
    Slot5.Left12.expected,
    Slot5.Left13.expected,
    Slot5.Left14.expected,
    Slot5.Left15.expected,
    Slot5.Left16.expected,
    Slot5.Left17.expected,
    Slot5.Left18.expected,
    Slot6.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 1893040884888506067878674432 }, { target := 81, numerator := 2247986050805100955605925888 }, { target := 82, numerator := 1715568301930208624015048704 }, { target := 83, numerator := 17688100768176978571741364224 }, { target := 84, numerator := 2129670995499569326363508736 }, { target := 85, numerator := 1715568301930208624015048704 }, { target := 86, numerator := 2129670995499569326363508736 }, { target := 87, numerator := 2129670995499569326363508736 }, { target := 88, numerator := 91220907640564886145903624192 }, { target := 89, numerator := 2129670995499569326363508736 }, { target := 90, numerator := 17688100768176978571741364224 }, { target := 91, numerator := 91220907640564886145903624192 }, { target := 92, numerator := 1893040884888506067878674432 }, { target := 93, numerator := 2129670995499569326363508736 }, { target := 94, numerator := 2129670995499569326363508736 }, { target := 95, numerator := 2247986050805100955605925888 }, { target := 518, numerator := 42948318700793380109184663552 }, { target := 521, numerator := 153644774477914236025804161024 }, { target := 523, numerator := 42948304423013467057991712768 }, { target := 544, numerator := 1004811706270645122137799524352 }, { target := 547, numerator := 3594647536222868480353709850624 }, { target := 549, numerator := 1004811372230085906377597779968 }, { target := 558, numerator := 80528097563987587704721244160 }, { target := 561, numerator := 288083952146089192548382801920 }, { target := 563, numerator := 80528070793150250733734461440 }, { target := 589, numerator := 37579778863194207595536580608 }, { target := 592, numerator := 134439177668174956522578640896 }, { target := 594, numerator := 37579766370136783675742748672 }, { target := 603, numerator := 81422854203587449790329257984 }, { target := 606, numerator := 291284884947712405798920388608 }, { target := 608, numerator := 81422827135296364630775955456 }, { target := 658, numerator := 3131648238599517299628048384 }, { target := 661, numerator := 11203264805681246376881553408 }, { target := 663, numerator := 3131647197511398639645229056 }, { target := 684, numerator := 80528097563987587704721244160 }, { target := 687, numerator := 288083952146089192548382801920 }, { target := 689, numerator := 80528070793150250733734461440 }, { target := 698, numerator := 3131648238599517299628048384 }, { target := 701, numerator := 11203264805681246376881553408 }, { target := 703, numerator := 3131647197511398639645229056 }, { target := 729, numerator := 81422854203587449790329257984 }, { target := 732, numerator := 291284884947712405798920388608 }, { target := 734, numerator := 81422827135296364630775955456 }, { target := 743, numerator := 81422854203587449790329257984 }, { target := 746, numerator := 291284884947712405798920388608 }, { target := 748, numerator := 81422827135296364630775955456 }, { target := 763, numerator := 2684269918799586256824041472 }, { target := 766, numerator := 9602798404869639751612760064 }, { target := 768, numerator := 2684269026438341691124482048 }]

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
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left2.expected,
    Slot7.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 1852242589955564126760599552 }, { target := 82, numerator := 68400854639489766473764700160 }, { target := 85, numerator := 68400837889846147545491832832 }, { target := 92, numerator := 1852259339599183055033466880 }, { target := 115, numerator := 2199538075572232400528211968 }, { target := 117, numerator := 81226014884394097687595581440 }, { target := 120, numerator := 81225994994192300210271551488 }, { target := 127, numerator := 2199557965774029877852241920 }, { target := 176, numerator := 71586076240810779866147323904 }, { target := 177, numerator := 83015134154975465478071255040 }, { target := 178, numerator := 125341929530045192942219427840 }, { target := 179, numerator := 653198029272043794156402769920 }, { target := 180, numerator := 78645916567871493610804346880 }, { target := 181, numerator := 125341914350680663288472141824 }, { target := 182, numerator := 78645916567871493610804346880 }, { target := 183, numerator := 78645916567871493610804346880 }, { target := 184, numerator := 3368666759657162309662786191360 }, { target := 185, numerator := 78645916567871493610804346880 }, { target := 186, numerator := 653198029272043794156402769920 }, { target := 187, numerator := 3368666759657162309662786191360 }, { target := 188, numerator := 71586091420175309519894609920 }, { target := 189, numerator := 78645916567871493610804346880 }, { target := 190, numerator := 78645916567871493610804346880 }, { target := 191, numerator := 83015134154975465478071255040 }, { target := 211, numerator := 17306891699897302309419352064 }, { target := 213, numerator := 639120485537732505489238917120 }, { target := 216, numerator := 639120329033249941128189313024 }, { target := 223, numerator := 17307048204379866670468956160 }, { target := 286, numerator := 69907464275085049473806630912 }, { target := 287, numerator := 83015113826663496250145374208 }, { target := 288, numerator := 63353639499295826085637259264 }, { target := 289, numerator := 653197869320325931020880707584 }, { target := 290, numerator := 78645897309470680658032459776 }, { target := 291, numerator := 63353639499295826085637259264 }, { target := 292, numerator := 78645897309470680658032459776 }, { target := 293, numerator := 78645897309470680658032459776 }, { target := 294, numerator := 3368665934755660821519057027072 }, { target := 295, numerator := 78645897309470680658032459776 }, { target := 296, numerator := 653197869320325931020880707584 }, { target := 297, numerator := 3368665934755660821519057027072 }, { target := 298, numerator := 69907464275085049473806630912 }, { target := 299, numerator := 78645897309470680658032459776 }, { target := 300, numerator := 78645897309470680658032459776 }, { target := 301, numerator := 83015113826663496250145374208 }, { target := 573, numerator := 1893058003467006470342574080 }, { target := 574, numerator := 2248006379117070183531806720 }, { target := 575, numerator := 1715583815641974613747957760 }, { target := 576, numerator := 17688260719894841707263426560 }, { target := 577, numerator := 2129690253900382279135395840 }, { target := 578, numerator := 1715583815641974613747957760 }, { target := 579, numerator := 2129690253900382279135395840 }, { target := 580, numerator := 2129690253900382279135395840 }, { target := 581, numerator := 91221732542066374289632788480 }, { target := 582, numerator := 2129690253900382279135395840 }, { target := 583, numerator := 17688260719894841707263426560 }, { target := 584, numerator := 91221732542066374289632788480 }, { target := 585, numerator := 1893058003467006470342574080 }, { target := 586, numerator := 2129690253900382279135395840 }, { target := 587, numerator := 2129690253900382279135395840 }, { target := 588, numerator := 2248006379117070183531806720 }]

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
    Slot7.Left4.expected,
    Slot7.Left5.expected,
    Slot7.Left6.expected,
    Slot7.Left7.expected,
    Slot7.Left8.expected,
    Slot7.Left9.expected,
    Slot7.Left10.expected,
    Slot7.Left11.expected,
    Slot7.Left12.expected,
    Slot7.Left13.expected,
    Slot7.Left14.expected,
    Slot7.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 237, numerator := 2083772913700009642605674496 }, { target := 239, numerator := 76950961469425987282985287680 }, { target := 242, numerator := 76950942626076915988678311936 }, { target := 249, numerator := 2083791757049080936912650240 }, { target := 286, numerator := 1678594847147229989876793344 }, { target := 288, numerator := 61988274517037600866849259520 }, { target := 291, numerator := 61988259337673071213101973504 }, { target := 298, numerator := 1678610026511759643624079360 }, { target := 312, numerator := 2083772913700009642605674496 }, { target := 314, numerator := 76950961469425987282985287680 }, { target := 317, numerator := 76950942626076915988678311936 }, { target := 324, numerator := 2083791757049080936912650240 }, { target := 392, numerator := 2083772913700009642605674496 }, { target := 394, numerator := 76950961469425987282985287680 }, { target := 397, numerator := 76950942626076915988678311936 }, { target := 404, numerator := 2083791757049080936912650240 }, { target := 427, numerator := 89254939803483746358276390912 }, { target := 429, numerator := 3296066182940413121954536488960 }, { target := 432, numerator := 3296065375816961234848387694592 }, { target := 439, numerator := 89255746926935633464425185280 }, { target := 453, numerator := 2083772913700009642605674496 }, { target := 455, numerator := 76950961469425987282985287680 }, { target := 458, numerator := 76950942626076915988678311936 }, { target := 465, numerator := 2083791757049080936912650240 }, { target := 502, numerator := 17306891699897302309419352064 }, { target := 504, numerator := 639120485537732505489238917120 }, { target := 507, numerator := 639120329033249941128189313024 }, { target := 514, numerator := 17307048204379866670468956160 }, { target := 528, numerator := 89254939803483746358276390912 }, { target := 530, numerator := 3296066182940413121954536488960 }, { target := 533, numerator := 3296065375816961234848387694592 }, { target := 540, numerator := 89255746926935633464425185280 }, { target := 573, numerator := 1852242589955564126760599552 }, { target := 575, numerator := 68400854639489766473764700160 }, { target := 578, numerator := 68400837889846147545491832832 }, { target := 585, numerator := 1852259339599183055033466880 }, { target := 642, numerator := 2083772913700009642605674496 }, { target := 644, numerator := 76950961469425987282985287680 }, { target := 647, numerator := 76950942626076915988678311936 }, { target := 654, numerator := 2083791757049080936912650240 }, { target := 668, numerator := 2083772913700009642605674496 }, { target := 670, numerator := 76950961469425987282985287680 }, { target := 673, numerator := 76950942626076915988678311936 }, { target := 680, numerator := 2083791757049080936912650240 }, { target := 713, numerator := 2199538075572232400528211968 }, { target := 715, numerator := 81226014884394097687595581440 }, { target := 718, numerator := 81225994994192300210271551488 }, { target := 725, numerator := 2199557965774029877852241920 }]

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
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 2245379130415409715814072320 }, { target := 27, numerator := 38934789429749442611068796928 }, { target := 28, numerator := 81422854203587449790329257984 }, { target := 29, numerator := 16205237706932287199973998592 }, { target := 30, numerator := 42948318700793380109184663552 }, { target := 31, numerator := 3131648238599517299628048384 }, { target := 32, numerator := 81422854203587449790329257984 }, { target := 33, numerator := 81422854203587449790329257984 }, { target := 34, numerator := 42948318700793380109184663552 }, { target := 35, numerator := 1004811706270645122137799524352 }, { target := 36, numerator := 80528097563987587704721244160 }, { target := 37, numerator := 38934789429749442611068796928 }, { target := 38, numerator := 81422854203587449790329257984 }, { target := 39, numerator := 3131648238599517299628048384 }, { target := 40, numerator := 80528097563987587704721244160 }, { target := 41, numerator := 3131648238599517299628048384 }, { target := 42, numerator := 81422854203587449790329257984 }, { target := 43, numerator := 81422854203587449790329257984 }, { target := 44, numerator := 2692756481761276888866619392 }, { target := 157, numerator := 8002332004058033126343966720 }, { target := 158, numerator := 134439177668174956522578640896 }, { target := 159, numerator := 291284884947712405798920388608 }, { target := 160, numerator := 9602798404869639751612760064 }, { target := 161, numerator := 153644774477914236025804161024 }, { target := 162, numerator := 11203264805681246376881553408 }, { target := 163, numerator := 291284884947712405798920388608 }, { target := 164, numerator := 291284884947712405798920388608 }, { target := 165, numerator := 153644774477914236025804161024 }, { target := 166, numerator := 3594647536222868480353709850624 }, { target := 167, numerator := 288083952146089192548382801920 }, { target := 168, numerator := 134439177668174956522578640896 }, { target := 169, numerator := 291284884947712405798920388608 }, { target := 170, numerator := 11203264805681246376881553408 }, { target := 171, numerator := 288083952146089192548382801920 }, { target := 172, numerator := 11203264805681246376881553408 }, { target := 173, numerator := 291284884947712405798920388608 }, { target := 174, numerator := 291284884947712405798920388608 }, { target := 175, numerator := 9602798404869639751612760064 }, { target := 267, numerator := 2236890855365284742603735040 }, { target := 268, numerator := 37579766370136783675742748672 }, { target := 269, numerator := 81422827135296364630775955456 }, { target := 270, numerator := 2684269026438341691124482048 }, { target := 271, numerator := 42948304423013467057991712768 }, { target := 272, numerator := 3131647197511398639645229056 }, { target := 273, numerator := 81422827135296364630775955456 }, { target := 274, numerator := 81422827135296364630775955456 }, { target := 275, numerator := 42948304423013467057991712768 }, { target := 276, numerator := 1004811372230085906377597779968 }, { target := 277, numerator := 80528070793150250733734461440 }, { target := 278, numerator := 37579766370136783675742748672 }, { target := 279, numerator := 81422827135296364630775955456 }, { target := 280, numerator := 3131647197511398639645229056 }, { target := 281, numerator := 80528070793150250733734461440 }, { target := 282, numerator := 3131647197511398639645229056 }, { target := 283, numerator := 81422827135296364630775955456 }, { target := 284, numerator := 81422827135296364630775955456 }, { target := 285, numerator := 2684269026438341691124482048 }]

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
    Slot9.Left1.expected,
    Slot9.Left2.expected,
    Slot9.Left3.expected,
    Slot9.Left4.expected,
    Slot9.Left5.expected,
    Slot9.Left6.expected,
    Slot9.Left7.expected,
    Slot9.Left8.expected,
    Slot9.Left9.expected,
    Slot10.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 1305639885183799508682670080 }, { target := 11, numerator := 1015497688476288506753187840 }, { target := 12, numerator := 1160568786830044007717928960 }, { target := 13, numerator := 1363668324525301709068566528 }, { target := 14, numerator := 16102891917266860607086264320 }, { target := 15, numerator := 36209746149097373040799383552 }, { target := 16, numerator := 1015497688476288506753187840 }, { target := 17, numerator := 16102891917266860607086264320 }, { target := 18, numerator := 1160568786830044007717928960 }, { target := 19, numerator := 1131554567159292907524980736 }, { target := 20, numerator := 1131554567159292907524980736 }, { target := 21, numerator := 1131554567159292907524980736 }, { target := 22, numerator := 36209746149097373040799383552 }, { target := 23, numerator := 1131554567159292907524980736 }, { target := 24, numerator := 1305639885183799508682670080 }, { target := 25, numerator := 1363668324525301709068566528 }, { target := 61, numerator := 151078059200430131933872128 }, { target := 62, numerator := 24119188084683183276473450496 }, { target := 64, numerator := 240673226628762076788069236736 }, { target := 72, numerator := 24119188084683183276473450496 }, { target := 79, numerator := 151060820718093250357886976 }, { target := 96, numerator := 8487531415754501794037760 }, { target := 97, numerator := 1355010566555235015532216320 }, { target := 99, numerator := 13520967788132700943149957120 }, { target := 107, numerator := 1355010566555235015532216320 }, { target := 114, numerator := 8486562961690632042577920 }, { target := 157, numerator := 134385914082779611738931200 }, { target := 158, numerator := 21454333970457887745926758400 }, { target := 160, numerator := 214081989978767764933207654400 }, { target := 168, numerator := 21454333970457887745926758400 }, { target := 175, numerator := 134370580226768340674150400 }, { target := 192, numerator := 229446265939230031832154112 }, { target := 193, numerator := 36630452315876519919887581184 }, { target := 195, numerator := 365516829205854015496487174144 }, { target := 203, numerator := 36630452315876519919887581184 }, { target := 210, numerator := 229420085397703419551023104 }, { target := 267, numerator := 8487531415754501794037760 }, { target := 268, numerator := 1355010566555235015532216320 }, { target := 270, numerator := 13520967788132700943149957120 }, { target := 278, numerator := 1355010566555235015532216320 }, { target := 285, numerator := 8486562961690632042577920 }, { target := 373, numerator := 229446265939230031832154112 }, { target := 374, numerator := 36630452315876519919887581184 }, { target := 376, numerator := 365516829205854015496487174144 }, { target := 384, numerator := 36630452315876519919887581184 }, { target := 391, numerator := 229420085397703419551023104 }, { target := 408, numerator := 229446265939230031832154112 }, { target := 409, numerator := 36630452315876519919887581184 }, { target := 411, numerator := 365516829205854015496487174144 }, { target := 419, numerator := 36630452315876519919887581184 }, { target := 426, numerator := 229420085397703419551023104 }, { target := 483, numerator := 151078059200430131933872128 }, { target := 484, numerator := 24119188084683183276473450496 }, { target := 486, numerator := 240673226628762076788069236736 }, { target := 494, numerator := 24119188084683183276473450496 }, { target := 501, numerator := 151060820718093250357886976 }, { target := 623, numerator := 8487531415754501794037760 }, { target := 624, numerator := 1355010566555235015532216320 }, { target := 626, numerator := 13520967788132700943149957120 }, { target := 634, numerator := 1355010566555235015532216320 }, { target := 641, numerator := 8486562961690632042577920 }]

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
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left2.expected,
    Slot11.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 109797414191762815032754176 }, { target := 11, numerator := 9232781319790091447096573952 }, { target := 16, numerator := 9232779092345744546668216320 }, { target := 24, numerator := 109799641636109715461111808 }, { target := 45, numerator := 122982196848330606485962752 }, { target := 46, numerator := 10341479697735899529770696704 }, { target := 51, numerator := 10341477202813763560553840640 }, { target := 59, numerator := 122984691770466575702818816 }, { target := 141, numerator := 1415437299375562323715424256 }, { target := 142, numerator := 10248279008266379953849761792 }, { target := 143, numerator := 1160568786830044007717928960 }, { target := 144, numerator := 1363668324525301709068566528 }, { target := 145, numerator := 16102891917266860607086264320 }, { target := 146, numerator := 36209746149097373040799383552 }, { target := 147, numerator := 10248276780822033053421404160 }, { target := 148, numerator := 16102891917266860607086264320 }, { target := 149, numerator := 1160568786830044007717928960 }, { target := 150, numerator := 1131554567159292907524980736 }, { target := 151, numerator := 1131554567159292907524980736 }, { target := 152, numerator := 1131554567159292907524980736 }, { target := 153, numerator := 36209746149097373040799383552 }, { target := 154, numerator := 1131554567159292907524980736 }, { target := 155, numerator := 1415439526819909224143781888 }, { target := 156, numerator := 1363668324525301709068566528 }, { target := 357, numerator := 122982196848330606485962752 }, { target := 358, numerator := 10341479697735899529770696704 }, { target := 363, numerator := 10341477202813763560553840640 }, { target := 371, numerator := 122984691770466575702818816 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk20.Parent2
