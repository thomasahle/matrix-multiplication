import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk12Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 53; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent3

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
    Slot2.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 257, numerator := 6797376021766394138727546880 }, { target := 260, numerator := 24317163919308131670750658560 }, { target := 262, numerator := 6797373762040245109307473920 }, { target := 353, numerator := 6991586765245433971262619648 }, { target := 356, numerator := 25011940031288364004200677376 }, { target := 358, numerator := 6991584440955680683859116032 }, { target := 379, numerator := 6797376021766394138727546880 }, { target := 382, numerator := 24317163919308131670750658560 }, { target := 384, numerator := 6797373762040245109307473920 }, { target := 389, numerator := 1692496147460480844588646400 }, { target := 391, numerator := 1692496147460480844588646400 }, { target := 524, numerator := 6020533047850234808587255808 }, { target := 527, numerator := 21538059471387202336950583296 }, { target := 529, numerator := 6020531046378502811100905472 }, { target := 620, numerator := 281799788788086797008390586368 }, { target := 623, numerator := 1008120138483317115835977302016 }, { target := 625, numerator := 281799695106297018674432704512 }, { target := 646, numerator := 76713243674220733851353743360 }, { target := 649, numerator := 274436564232191771712757432320 }, { target := 651, numerator := 76713218171597051947898634240 }, { target := 656, numerator := 33917622795108036125556473856 }, { target := 658, numerator := 33917622795108036125556473856 }, { target := 695, numerator := 6991586765245433971262619648 }, { target := 698, numerator := 25011940031288364004200677376 }, { target := 700, numerator := 6991584440955680683859116032 }, { target := 721, numerator := 281799788788086797008390586368 }, { target := 724, numerator := 1008120138483317115835977302016 }, { target := 726, numerator := 281799695106297018674432704512 }, { target := 731, numerator := 56935570400570575611962064896 }, { target := 733, numerator := 56935570400570575611962064896 }, { target := 735, numerator := 6797376021766394138727546880 }, { target := 738, numerator := 24317163919308131670750658560 }, { target := 740, numerator := 6797373762040245109307473920 }, { target := 745, numerator := 54633775640024321663321505792 }, { target := 747, numerator := 54633775640024321663321505792 }, { target := 749, numerator := 20696810031802451470969733120 }, { target := 836, numerator := 6797376021766394138727546880 }, { target := 839, numerator := 24317163919308131670750658560 }, { target := 841, numerator := 6797373762040245109307473920 }, { target := 862, numerator := 5826322304371194976052183040 }, { target := 865, numerator := 20843283359406970003500564480 }, { target := 867, numerator := 5826320367463067236549263360 }, { target := 872, numerator := 1692496147460480844588646400 }, { target := 874, numerator := 1692496147460480844588646400 }, { target := 911, numerator := 6797376021766394138727546880 }, { target := 914, numerator := 24317163919308131670750658560 }, { target := 916, numerator := 6797373762040245109307473920 }, { target := 937, numerator := 76713243674220733851353743360 }, { target := 940, numerator := 274436564232191771712757432320 }, { target := 942, numerator := 76713218171597051947898634240 }, { target := 947, numerator := 54633775640024321663321505792 }, { target := 949, numerator := 54633775640024321663321505792 }, { target := 961, numerator := 36490216939247967009331216384 }, { target := 963, numerator := 36490216939247967009331216384 }, { target := 965, numerator := 18917271225329717325802242048 }, { target := 992, numerator := 1760195993358900078372192256 }, { target := 994, numerator := 1760195993358900078372192256 }, { target := 1006, numerator := 33917622795108036125556473856 }, { target := 1008, numerator := 33917622795108036125556473856 }, { target := 1010, numerator := 20696810031802451470969733120 }, { target := 1011, numerator := 1624796301562061610805100544 }, { target := 1013, numerator := 1624796301562061610805100544 }, { target := 1015, numerator := 18917271225329717325802242048 }]

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
    Slot2.Left13.expected,
    Slot2.Left14.expected,
    Slot2.Left15.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 60748522435635116028985344 }, { target := 111, numerator := 72138870392316700284420096 }, { target := 112, numerator := 55053348457294323901267968 }, { target := 113, numerator := 567619006507965615395831808 }, { target := 114, numerator := 68342087740089505532608512 }, { target := 115, numerator := 55053348457294323901267968 }, { target := 116, numerator := 68342087740089505532608512 }, { target := 117, numerator := 68342087740089505532608512 }, { target := 118, numerator := 2927319424867167153646731264 }, { target := 119, numerator := 68342087740089505532608512 }, { target := 120, numerator := 567619006507965615395831808 }, { target := 121, numerator := 2927319424867167153646731264 }, { target := 122, numerator := 60748522435635116028985344 }, { target := 123, numerator := 68342087740089505532608512 }, { target := 124, numerator := 68342087740089505532608512 }, { target := 125, numerator := 72138870392316700284420096 }, { target := 206, numerator := 1619960598283603094106275840 }, { target := 207, numerator := 1923703210461778674251202560 }, { target := 208, numerator := 1468089292194515304033812480 }, { target := 209, numerator := 15136506840212416410555514880 }, { target := 210, numerator := 1822455673069053480869560320 }, { target := 211, numerator := 1468089292194515304033812480 }, { target := 212, numerator := 1822455673069053480869560320 }, { target := 213, numerator := 1822455673069053480869560320 }, { target := 214, numerator := 78061851329791124097246167040 }, { target := 215, numerator := 1822455673069053480869560320 }, { target := 216, numerator := 15136506840212416410555514880 }, { target := 217, numerator := 78061851329791124097246167040 }, { target := 218, numerator := 1619960598283603094106275840 }, { target := 219, numerator := 1822455673069053480869560320 }, { target := 220, numerator := 1822455673069053480869560320 }, { target := 221, numerator := 1923703210461778674251202560 }, { target := 241, numerator := 1549087322108695458739126272 }, { target := 242, numerator := 1839541195004075857252712448 }, { target := 243, numerator := 1403860385661005259482333184 }, { target := 244, numerator := 14474284665953123192593711104 }, { target := 245, numerator := 1742723237372282391081517056 }, { target := 246, numerator := 1403860385661005259482333184 }, { target := 247, numerator := 1742723237372282391081517056 }, { target := 248, numerator := 1742723237372282391081517056 }, { target := 249, numerator := 74646645334112762417991647232 }, { target := 250, numerator := 1742723237372282391081517056 }, { target := 251, numerator := 14474284665953123192593711104 }, { target := 252, numerator := 74646645334112762417991647232 }, { target := 253, numerator := 1549087322108695458739126272 }, { target := 254, numerator := 1742723237372282391081517056 }, { target := 255, numerator := 1742723237372282391081517056 }, { target := 256, numerator := 1839541195004075857252712448 }, { target := 951, numerator := 5826322304371194976052183040 }, { target := 954, numerator := 20843283359406970003500564480 }, { target := 956, numerator := 5826320367463067236549263360 }, { target := 982, numerator := 6797376021766394138727546880 }, { target := 985, numerator := 24317163919308131670750658560 }, { target := 987, numerator := 6797373762040245109307473920 }, { target := 996, numerator := 6020533047850234808587255808 }, { target := 999, numerator := 21538059471387202336950583296 }, { target := 1001, numerator := 6020531046378502811100905472 }]

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
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected,
    Slot3.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 302, numerator := 50623768696362596690821120 }, { target := 303, numerator := 60115725326930583570350080 }, { target := 304, numerator := 45877790381078603251056640 }, { target := 305, numerator := 473015838756638012829859840 }, { target := 306, numerator := 56951739783407921277173760 }, { target := 307, numerator := 45877790381078603251056640 }, { target := 308, numerator := 56951739783407921277173760 }, { target := 309, numerator := 56951739783407921277173760 }, { target := 310, numerator := 2439432854055972628038942720 }, { target := 311, numerator := 56951739783407921277173760 }, { target := 312, numerator := 473015838756638012829859840 }, { target := 313, numerator := 2439432854055972628038942720 }, { target := 314, numerator := 50623768696362596690821120 }, { target := 315, numerator := 56951739783407921277173760 }, { target := 316, numerator := 56951739783407921277173760 }, { target := 317, numerator := 60115725326930583570350080 }, { target := 337, numerator := 1589586337065785536091783168 }, { target := 338, numerator := 1887633775265620324108992512 }, { target := 339, numerator := 1440562617965868142083178496 }, { target := 340, numerator := 14852697336958433602857598976 }, { target := 341, numerator := 1788284629199008728103256064 }, { target := 342, numerator := 1440562617965868142083178496 }, { target := 343, numerator := 1788284629199008728103256064 }, { target := 344, numerator := 1788284629199008728103256064 }, { target := 345, numerator := 76598191617357540520422801408 }, { target := 346, numerator := 1788284629199008728103256064 }, { target := 347, numerator := 14852697336958433602857598976 }, { target := 348, numerator := 76598191617357540520422801408 }, { target := 349, numerator := 1589586337065785536091783168 }, { target := 350, numerator := 1788284629199008728103256064 }, { target := 351, numerator := 1788284629199008728103256064 }, { target := 352, numerator := 1887633775265620324108992512 }, { target := 363, numerator := 50623768696362596690821120 }, { target := 364, numerator := 60115725326930583570350080 }, { target := 365, numerator := 45877790381078603251056640 }, { target := 366, numerator := 473015838756638012829859840 }, { target := 367, numerator := 56951739783407921277173760 }, { target := 368, numerator := 45877790381078603251056640 }, { target := 369, numerator := 56951739783407921277173760 }, { target := 370, numerator := 56951739783407921277173760 }, { target := 371, numerator := 2439432854055972628038942720 }, { target := 372, numerator := 56951739783407921277173760 }, { target := 373, numerator := 473015838756638012829859840 }, { target := 374, numerator := 2439432854055972628038942720 }, { target := 375, numerator := 50623768696362596690821120 }, { target := 376, numerator := 56951739783407921277173760 }, { target := 377, numerator := 56951739783407921277173760 }, { target := 378, numerator := 60115725326930583570350080 }, { target := 473, numerator := 1549087322108695458739126272 }, { target := 474, numerator := 1839541195004075857252712448 }, { target := 475, numerator := 1403860385661005259482333184 }, { target := 476, numerator := 14474284665953123192593711104 }, { target := 477, numerator := 1742723237372282391081517056 }, { target := 478, numerator := 1403860385661005259482333184 }, { target := 479, numerator := 1742723237372282391081517056 }, { target := 480, numerator := 1742723237372282391081517056 }, { target := 481, numerator := 74646645334112762417991647232 }, { target := 482, numerator := 1742723237372282391081517056 }, { target := 483, numerator := 14474284665953123192593711104 }, { target := 484, numerator := 74646645334112762417991647232 }, { target := 485, numerator := 1549087322108695458739126272 }, { target := 486, numerator := 1742723237372282391081517056 }, { target := 487, numerator := 1742723237372282391081517056 }, { target := 488, numerator := 1839541195004075857252712448 }]

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
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot3.Left10.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 508, numerator := 880853575316709182420287488 }, { target := 509, numerator := 1046013620688592154124091392 }, { target := 510, numerator := 798273552630767696568385536 }, { target := 511, numerator := 8230475594365501423239561216 }, { target := 512, numerator := 990960272231297830222823424 }, { target := 513, numerator := 798273552630767696568385536 }, { target := 514, numerator := 990960272231297830222823424 }, { target := 515, numerator := 990960272231297830222823424 }, { target := 516, numerator := 42446131660573923727877603328 }, { target := 517, numerator := 990960272231297830222823424 }, { target := 518, numerator := 8230475594365501423239561216 }, { target := 519, numerator := 42446131660573923727877603328 }, { target := 520, numerator := 880853575316709182420287488 }, { target := 521, numerator := 990960272231297830222823424 }, { target := 522, numerator := 990960272231297830222823424 }, { target := 523, numerator := 1046013620688592154124091392 }, { target := 569, numerator := 1589586337065785536091783168 }, { target := 570, numerator := 1887633775265620324108992512 }, { target := 571, numerator := 1440562617965868142083178496 }, { target := 572, numerator := 14852697336958433602857598976 }, { target := 573, numerator := 1788284629199008728103256064 }, { target := 574, numerator := 1440562617965868142083178496 }, { target := 575, numerator := 1788284629199008728103256064 }, { target := 576, numerator := 1788284629199008728103256064 }, { target := 577, numerator := 76598191617357540520422801408 }, { target := 578, numerator := 1788284629199008728103256064 }, { target := 579, numerator := 14852697336958433602857598976 }, { target := 580, numerator := 76598191617357540520422801408 }, { target := 581, numerator := 1589586337065785536091783168 }, { target := 582, numerator := 1788284629199008728103256064 }, { target := 583, numerator := 1788284629199008728103256064 }, { target := 584, numerator := 1887633775265620324108992512 }, { target := 604, numerator := 24815771414956944897840513024 }, { target := 605, numerator := 29468728555261372066185609216 }, { target := 606, numerator := 22489292844804731313667964928 }, { target := 607, numerator := 231872364158503953889197293568 }, { target := 608, numerator := 27917742841826563010070577152 }, { target := 609, numerator := 22489292844804731313667964928 }, { target := 610, numerator := 27917742841826563010070577152 }, { target := 611, numerator := 27917742841826563010070577152 }, { target := 612, numerator := 1195809985058237782264689721344 }, { target := 613, numerator := 27917742841826563010070577152 }, { target := 614, numerator := 231872364158503953889197293568 }, { target := 615, numerator := 1195809985058237782264689721344 }, { target := 616, numerator := 24815771414956944897840513024 }, { target := 617, numerator := 27917742841826563010070577152 }, { target := 618, numerator := 27917742841826563010070577152 }, { target := 619, numerator := 29468728555261372066185609216 }, { target := 630, numerator := 971976358970161856463765504 }, { target := 631, numerator := 1154221926277067204550721536 }, { target := 632, numerator := 880853575316709182420287488 }, { target := 633, numerator := 9081904104127449846333308928 }, { target := 634, numerator := 1093473403841432088521736192 }, { target := 635, numerator := 880853575316709182420287488 }, { target := 636, numerator := 1093473403841432088521736192 }, { target := 637, numerator := 1093473403841432088521736192 }, { target := 638, numerator := 46837110797874674458347700224 }, { target := 639, numerator := 1093473403841432088521736192 }, { target := 640, numerator := 9081904104127449846333308928 }, { target := 641, numerator := 46837110797874674458347700224 }, { target := 642, numerator := 971976358970161856463765504 }, { target := 643, numerator := 1093473403841432088521736192 }, { target := 644, numerator := 1093473403841432088521736192 }, { target := 645, numerator := 1154221926277067204550721536 }]

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
    Slot3.Left11.expected,
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 679, numerator := 1619960598283603094106275840 }, { target := 680, numerator := 1923703210461778674251202560 }, { target := 681, numerator := 1468089292194515304033812480 }, { target := 682, numerator := 15136506840212416410555514880 }, { target := 683, numerator := 1822455673069053480869560320 }, { target := 684, numerator := 1468089292194515304033812480 }, { target := 685, numerator := 1822455673069053480869560320 }, { target := 686, numerator := 1822455673069053480869560320 }, { target := 687, numerator := 78061851329791124097246167040 }, { target := 688, numerator := 1822455673069053480869560320 }, { target := 689, numerator := 15136506840212416410555514880 }, { target := 690, numerator := 78061851329791124097246167040 }, { target := 691, numerator := 1619960598283603094106275840 }, { target := 692, numerator := 1822455673069053480869560320 }, { target := 693, numerator := 1822455673069053480869560320 }, { target := 694, numerator := 1923703210461778674251202560 }, { target := 705, numerator := 1549087322108695458739126272 }, { target := 706, numerator := 1839541195004075857252712448 }, { target := 707, numerator := 1403860385661005259482333184 }, { target := 708, numerator := 14474284665953123192593711104 }, { target := 709, numerator := 1742723237372282391081517056 }, { target := 710, numerator := 1403860385661005259482333184 }, { target := 711, numerator := 1742723237372282391081517056 }, { target := 712, numerator := 1742723237372282391081517056 }, { target := 713, numerator := 74646645334112762417991647232 }, { target := 714, numerator := 1742723237372282391081517056 }, { target := 715, numerator := 14474284665953123192593711104 }, { target := 716, numerator := 74646645334112762417991647232 }, { target := 717, numerator := 1549087322108695458739126272 }, { target := 718, numerator := 1742723237372282391081517056 }, { target := 719, numerator := 1742723237372282391081517056 }, { target := 720, numerator := 1839541195004075857252712448 }, { target := 785, numerator := 50623768696362596690821120 }, { target := 786, numerator := 60115725326930583570350080 }, { target := 787, numerator := 45877790381078603251056640 }, { target := 788, numerator := 473015838756638012829859840 }, { target := 789, numerator := 56951739783407921277173760 }, { target := 790, numerator := 45877790381078603251056640 }, { target := 791, numerator := 56951739783407921277173760 }, { target := 792, numerator := 56951739783407921277173760 }, { target := 793, numerator := 2439432854055972628038942720 }, { target := 794, numerator := 56951739783407921277173760 }, { target := 795, numerator := 473015838756638012829859840 }, { target := 796, numerator := 2439432854055972628038942720 }, { target := 797, numerator := 50623768696362596690821120 }, { target := 798, numerator := 56951739783407921277173760 }, { target := 799, numerator := 56951739783407921277173760 }, { target := 800, numerator := 60115725326930583570350080 }, { target := 820, numerator := 971976358970161856463765504 }, { target := 821, numerator := 1154221926277067204550721536 }, { target := 822, numerator := 880853575316709182420287488 }, { target := 823, numerator := 9081904104127449846333308928 }, { target := 824, numerator := 1093473403841432088521736192 }, { target := 825, numerator := 880853575316709182420287488 }, { target := 826, numerator := 1093473403841432088521736192 }, { target := 827, numerator := 1093473403841432088521736192 }, { target := 828, numerator := 46837110797874674458347700224 }, { target := 829, numerator := 1093473403841432088521736192 }, { target := 830, numerator := 9081904104127449846333308928 }, { target := 831, numerator := 46837110797874674458347700224 }, { target := 832, numerator := 971976358970161856463765504 }, { target := 833, numerator := 1093473403841432088521736192 }, { target := 834, numerator := 1093473403841432088521736192 }, { target := 835, numerator := 1154221926277067204550721536 }]

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
    Slot3.Left15.expected,
    Slot3.Left16.expected,
    Slot3.Left17.expected,
    Slot3.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 846, numerator := 50623768696362596690821120 }, { target := 847, numerator := 60115725326930583570350080 }, { target := 848, numerator := 45877790381078603251056640 }, { target := 849, numerator := 473015838756638012829859840 }, { target := 850, numerator := 56951739783407921277173760 }, { target := 851, numerator := 45877790381078603251056640 }, { target := 852, numerator := 56951739783407921277173760 }, { target := 853, numerator := 56951739783407921277173760 }, { target := 854, numerator := 2439432854055972628038942720 }, { target := 855, numerator := 56951739783407921277173760 }, { target := 856, numerator := 473015838756638012829859840 }, { target := 857, numerator := 2439432854055972628038942720 }, { target := 858, numerator := 50623768696362596690821120 }, { target := 859, numerator := 56951739783407921277173760 }, { target := 860, numerator := 56951739783407921277173760 }, { target := 861, numerator := 60115725326930583570350080 }, { target := 895, numerator := 1559212075847967978077290496 }, { target := 896, numerator := 1851564340069461973966782464 }, { target := 897, numerator := 1413035943737220980132544512 }, { target := 898, numerator := 14568887833704450795159683072 }, { target := 899, numerator := 1754113585328963975336951808 }, { target := 900, numerator := 1413035943737220980132544512 }, { target := 901, numerator := 1754113585328963975336951808 }, { target := 902, numerator := 1754113585328963975336951808 }, { target := 903, numerator := 75134531904923956943599435776 }, { target := 904, numerator := 1754113585328963975336951808 }, { target := 905, numerator := 14568887833704450795159683072 }, { target := 906, numerator := 75134531904923956943599435776 }, { target := 907, numerator := 1559212075847967978077290496 }, { target := 908, numerator := 1754113585328963975336951808 }, { target := 909, numerator := 1754113585328963975336951808 }, { target := 910, numerator := 1851564340069461973966782464 }, { target := 921, numerator := 880853575316709182420287488 }, { target := 922, numerator := 1046013620688592154124091392 }, { target := 923, numerator := 798273552630767696568385536 }, { target := 924, numerator := 8230475594365501423239561216 }, { target := 925, numerator := 990960272231297830222823424 }, { target := 926, numerator := 798273552630767696568385536 }, { target := 927, numerator := 990960272231297830222823424 }, { target := 928, numerator := 990960272231297830222823424 }, { target := 929, numerator := 42446131660573923727877603328 }, { target := 930, numerator := 990960272231297830222823424 }, { target := 931, numerator := 8230475594365501423239561216 }, { target := 932, numerator := 42446131660573923727877603328 }, { target := 933, numerator := 880853575316709182420287488 }, { target := 934, numerator := 990960272231297830222823424 }, { target := 935, numerator := 990960272231297830222823424 }, { target := 936, numerator := 1046013620688592154124091392 }, { target := 966, numerator := 60748522435635116028985344 }, { target := 967, numerator := 72138870392316700284420096 }, { target := 968, numerator := 55053348457294323901267968 }, { target := 969, numerator := 567619006507965615395831808 }, { target := 970, numerator := 68342087740089505532608512 }, { target := 971, numerator := 55053348457294323901267968 }, { target := 972, numerator := 68342087740089505532608512 }, { target := 973, numerator := 68342087740089505532608512 }, { target := 974, numerator := 2927319424867167153646731264 }, { target := 975, numerator := 68342087740089505532608512 }, { target := 976, numerator := 567619006507965615395831808 }, { target := 977, numerator := 2927319424867167153646731264 }, { target := 978, numerator := 60748522435635116028985344 }, { target := 979, numerator := 68342087740089505532608512 }, { target := 980, numerator := 68342087740089505532608512 }, { target := 981, numerator := 72138870392316700284420096 }]

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
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left7.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left6.expected,
    Slot6.Left14.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 887950241828971562338877440 }, { target := 57, numerator := 14917564062726722247293140992 }, { target := 58, numerator := 32321388802574564869135138816 }, { target := 59, numerator := 1065540290194765874806652928 }, { target := 60, numerator := 17048644643116253996906446848 }, { target := 61, numerator := 1243130338560560187274428416 }, { target := 62, numerator := 32321388802574564869135138816 }, { target := 63, numerator := 32321388802574564869135138816 }, { target := 64, numerator := 17048644643116253996906446848 }, { target := 65, numerator := 398867248629574025802623746048 }, { target := 66, numerator := 31966208705842976244199587840 }, { target := 67, numerator := 14917564062726722247293140992 }, { target := 68, numerator := 32321388802574564869135138816 }, { target := 69, numerator := 1243130338560560187274428416 }, { target := 70, numerator := 31966208705842976244199587840 }, { target := 71, numerator := 1243130338560560187274428416 }, { target := 72, numerator := 32321388802574564869135138816 }, { target := 73, numerator := 32321388802574564869135138816 }, { target := 74, numerator := 1065540290194765874806652928 }, { target := 110, numerator := 2124902271457129722827243520 }, { target := 112, numerator := 78469813933253542933010841600 }, { target := 115, numerator := 78469794717975822312218296320 }, { target := 122, numerator := 2124921486734850343619788800 }, { target := 206, numerator := 222792170758359283760659169280 }, { target := 208, numerator := 8227418465323437154372052582400 }, { target := 211, numerator := 8227416450636224190839500308480 }, { target := 218, numerator := 222794185445572247293211443200 }, { target := 257, numerator := 84762365786117157346061844480 }, { target := 260, numerator := 308298995724278112626252185600 }, { target := 262, numerator := 84762365786117157346061844480 }, { target := 302, numerator := 2401476920262420171734384640000 }, { target := 304, numerator := 88683347761105137304810291200000 }, { target := 307, numerator := 88683326044790659058226954240000 }, { target := 314, numerator := 2401498636576898418317721600000 }, { target := 353, numerator := 7097079558685865823820880805888 }, { target := 356, numerator := 25813608200120832435340821135360 }, { target := 358, numerator := 7097079558685865823820880805888 }, { target := 389, numerator := 128814481617931240376861982720 }, { target := 391, numerator := 128814420194414534781422272512 }, { target := 679, numerator := 222792340709752665919318917120 }, { target := 681, numerator := 8227424741402292889279109529600 }, { target := 684, numerator := 8227422726713543072373717073920 }, { target := 691, numerator := 222794355398502482824711372800 }, { target := 695, numerator := 7097082127112686270782873010176 }, { target := 698, numerator := 25813617542042828019749061918720 }, { target := 700, numerator := 7097082127112686270782873010176 }, { target := 731, numerator := 1247706483435012631616647331840 }, { target := 733, numerator := 1247705888482340646621454270464 }, { target := 749, numerator := 19807040628566084398385987584 }, { target := 965, numerator := 19807040628566084398385987584 }, { target := 966, numerator := 2124902271457129722827243520 }, { target := 968, numerator := 78469813933253542933010841600 }, { target := 971, numerator := 78469794717975822312218296320 }, { target := 978, numerator := 2124921486734850343619788800 }, { target := 982, numerator := 84759797359296710384069640192 }, { target := 985, numerator := 308289653802282528218011402240 }, { target := 987, numerator := 84759797359296710384069640192 }, { target := 992, numerator := 128814481617931240376861982720 }, { target := 994, numerator := 128814420194414534781422272512 }, { target := 1010, numerator := 19807040628566084398385987584 }, { target := 1015, numerator := 19807040628566084398385987584 }]

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
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 152, numerator := 31076044618376251091263160320 }, { target := 153, numerator := 522077549588721018333221093376 }, { target := 154, numerator := 1131168024108895539721979035648 }, { target := 155, numerator := 37291253542051501309515792384 }, { target := 156, numerator := 596660056672824020952252678144 }, { target := 157, numerator := 43506462465726751527768424448 }, { target := 158, numerator := 1131168024108895539721979035648 }, { target := 159, numerator := 1131168024108895539721979035648 }, { target := 160, numerator := 596660056672824020952252678144 }, { target := 161, numerator := 13959359242574611990195411615744 }, { target := 162, numerator := 1118737606261545039285473771520 }, { target := 163, numerator := 522077549588721018333221093376 }, { target := 164, numerator := 1131168024108895539721979035648 }, { target := 165, numerator := 43506462465726751527768424448 }, { target := 166, numerator := 1118737606261545039285473771520 }, { target := 167, numerator := 43506462465726751527768424448 }, { target := 168, numerator := 1131168024108895539721979035648 }, { target := 169, numerator := 1131168024108895539721979035648 }, { target := 170, numerator := 37291253542051501309515792384 }, { target := 283, numerator := 31076059859998541993780183040 }, { target := 284, numerator := 522077805647975505495507075072 }, { target := 285, numerator := 1131168578903946928573598662656 }, { target := 286, numerator := 37291271831998250392536219648 }, { target := 287, numerator := 596660349311972006280579514368 }, { target := 288, numerator := 43506483803997958791292256256 }, { target := 289, numerator := 1131168578903946928573598662656 }, { target := 290, numerator := 1131168578903946928573598662656 }, { target := 291, numerator := 596660349311972006280579514368 }, { target := 292, numerator := 13959366089111345063606058221568 }, { target := 293, numerator := 1118738154959947511776086589440 }, { target := 294, numerator := 522077805647975505495507075072 }, { target := 295, numerator := 1131168578903946928573598662656 }, { target := 296, numerator := 43506483803997958791292256256 }, { target := 297, numerator := 1118738154959947511776086589440 }, { target := 298, numerator := 43506483803997958791292256256 }, { target := 299, numerator := 1131168578903946928573598662656 }, { target := 300, numerator := 1131168578903946928573598662656 }, { target := 301, numerator := 37291271831998250392536219648 }, { target := 389, numerator := 8094967288139556953832554496 }, { target := 391, numerator := 8094967288139556953832554496 }, { target := 656, numerator := 193756958961275847088508239872 }, { target := 658, numerator := 193756958961275847088508239872 }, { target := 660, numerator := 887942621017826111080366080 }, { target := 661, numerator := 14917436033099478666150150144 }, { target := 662, numerator := 32321111405048870443325325312 }, { target := 663, numerator := 1065531145221391333296439296 }, { target := 664, numerator := 17048498323542261332743028736 }, { target := 665, numerator := 1243119669424956555512512512 }, { target := 666, numerator := 32321111405048870443325325312 }, { target := 667, numerator := 32321111405048870443325325312 }, { target := 668, numerator := 17048498323542261332743028736 }, { target := 669, numerator := 398863825361207489097300443136 }, { target := 670, numerator := 31965934356641739998893178880 }, { target := 671, numerator := 14917436033099478666150150144 }, { target := 672, numerator := 32321111405048870443325325312 }, { target := 673, numerator := 1243119669424956555512512512 }, { target := 674, numerator := 31965934356641739998893178880 }, { target := 675, numerator := 1243119669424956555512512512 }, { target := 676, numerator := 32321111405048870443325325312 }, { target := 677, numerator := 32321111405048870443325325312 }, { target := 678, numerator := 1065531145221391333296439296 }, { target := 731, numerator := 144926027255401745463776378880 }, { target := 733, numerator := 144926027255401745463776378880 }]

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
    Slot9.Left3.expected,
    Slot9.Left4.expected,
    Slot9.Left5.expected,
    Slot9.Left6.expected,
    Slot9.Left7.expected,
    Slot9.Left8.expected,
    Slot9.Left9.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left6.expected,
    Slot10.Left14.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 2703344374039919553633320960 }, { target := 57, numerator := 431581341196851365087511838720 }, { target := 59, numerator := 4306532772741934570590982635520 }, { target := 67, numerator := 431581341196851365087511838720 }, { target := 74, numerator := 2703035913933342657289912320 }, { target := 110, numerator := 5339124265657196049277648896 }, { target := 112, numerator := 200604614482002683829600387072 }, { target := 115, numerator := 200589442330610455964647686144 }, { target := 122, numerator := 5354296417049423914230349824 }, { target := 152, numerator := 97970094925362811059379896320 }, { target := 153, numerator := 15640650658903642899145283338240 }, { target := 155, numerator := 156070173151562742216425042083840 }, { target := 163, numerator := 15640650658903642899145283338240 }, { target := 170, numerator := 97958916228999807543740989440 }, { target := 206, numerator := 788560713360986028804654759936 }, { target := 208, numerator := 29628251755995054587718351716352 }, { target := 211, numerator := 29626010908633244137986881224704 }, { target := 218, numerator := 790801560722796478536125251584 }, { target := 257, numerator := 92120793506922518506635264000 }, { target := 260, numerator := 316234576722355819251970867200 }, { target := 262, numerator := 92120793506922518506635264000 }, { target := 283, numerator := 97970130928990337605881036800 }, { target := 284, numerator := 15640656406781717581080926617600 }, { target := 286, numerator := 156070230506742263409217739161600 }, { target := 294, numerator := 15640656406781717581080926617600 }, { target := 301, numerator := 97958952228519206805150105600 }, { target := 302, numerator := 8219036437706223083144966307840 }, { target := 304, numerator := 308810313070441455764426855546880 }, { target := 307, numerator := 308786957093145099173973731573760 }, { target := 314, numerator := 8242392415002579673598090280960 }, { target := 353, numerator := 7746367687398259699302268928000 }, { target := 356, numerator := 26591925812884361201660094054400 }, { target := 358, numerator := 7746367687398259699302268928000 }, { target := 679, numerator := 788560713360986028804654759936 }, { target := 681, numerator := 29628251755995054587718351716352 }, { target := 684, numerator := 29626010908633244137986881224704 }, { target := 691, numerator := 790801560722796478536125251584 }, { target := 695, numerator := 7746365818556973777923604480000 }, { target := 698, numerator := 26591919397478994874680213504000 }, { target := 700, numerator := 7746365818556973777923604480000 }, { target := 745, numerator := 168166417211673376718327906304 }, { target := 747, numerator := 168166417211673376718327906304 }, { target := 872, numerator := 8094967288139556953832554496 }, { target := 874, numerator := 8094967288139556953832554496 }, { target := 947, numerator := 167905289234636616816591372288 }, { target := 949, numerator := 167905289234636616816591372288 }, { target := 961, numerator := 168688673165746896521800974336 }, { target := 963, numerator := 168688673165746896521800974336 }, { target := 966, numerator := 5339124265657196049277648896 }, { target := 968, numerator := 200604614482002683829600387072 }, { target := 971, numerator := 200589442330610455964647686144 }, { target := 978, numerator := 5354296417049423914230349824 }, { target := 982, numerator := 92122662348208439885299712000 }, { target := 985, numerator := 316240992127722146231851417600 }, { target := 987, numerator := 92122662348208439885299712000 }, { target := 992, numerator := 8094967288139556953832554496 }, { target := 994, numerator := 8094967288139556953832554496 }, { target := 1006, numerator := 193756958961275847088508239872 }, { target := 1008, numerator := 193756958961275847088508239872 }, { target := 1011, numerator := 8094967288139556953832554496 }, { target := 1013, numerator := 8094967288139556953832554496 }]

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
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 52325110703242463845243944960 }, { target := 15, numerator := 40697308324744138546300846080 }, { target := 16, numerator := 46511209513993301195772395520 }, { target := 17, numerator := 54650671178942128905032564736 }, { target := 18, numerator := 645343032006657054091341987840 }, { target := 19, numerator := 1451149736836590997308098740224 }, { target := 20, numerator := 40697308324744138546300846080 }, { target := 21, numerator := 645343032006657054091341987840 }, { target := 22, numerator := 46511209513993301195772395520 }, { target := 23, numerator := 45348429276143468665878085632 }, { target := 24, numerator := 45348429276143468665878085632 }, { target := 25, numerator := 45348429276143468665878085632 }, { target := 26, numerator := 1451149736836590997308098740224 }, { target := 27, numerator := 45348429276143468665878085632 }, { target := 28, numerator := 52325110703242463845243944960 }, { target := 29, numerator := 54650671178942128905032564736 }, { target := 136, numerator := 177367993793215766184968847360 }, { target := 137, numerator := 137952884061390040366086881280 }, { target := 138, numerator := 157660438927302903275527864320 }, { target := 139, numerator := 185251015739580911348745240576 }, { target := 140, numerator := 2187538590116327782947949117440 }, { target := 141, numerator := 4919005694531850582196469366784 }, { target := 142, numerator := 137952884061390040366086881280 }, { target := 143, numerator := 2187538590116327782947949117440 }, { target := 144, numerator := 157660438927302903275527864320 }, { target := 145, numerator := 153718927954120330693639667712 }, { target := 146, numerator := 153718927954120330693639667712 }, { target := 147, numerator := 153718927954120330693639667712 }, { target := 148, numerator := 4919005694531850582196469366784 }, { target := 149, numerator := 153718927954120330693639667712 }, { target := 150, numerator := 177367993793215766184968847360 }, { target := 151, numerator := 185251015739580911348745240576 }, { target := 257, numerator := 52809602469013227399366574080 }, { target := 260, numerator := 179010290032041838094088929280 }, { target := 262, numerator := 52809602469013227399366574080 }, { target := 267, numerator := 52325110703242463845243944960 }, { target := 268, numerator := 40697308324744138546300846080 }, { target := 269, numerator := 46511209513993301195772395520 }, { target := 270, numerator := 54650671178942128905032564736 }, { target := 271, numerator := 645343032006657054091341987840 }, { target := 272, numerator := 1451149736836590997308098740224 }, { target := 273, numerator := 40697308324744138546300846080 }, { target := 274, numerator := 645343032006657054091341987840 }, { target := 275, numerator := 46511209513993301195772395520 }, { target := 276, numerator := 45348429276143468665878085632 }, { target := 277, numerator := 45348429276143468665878085632 }, { target := 278, numerator := 45348429276143468665878085632 }, { target := 279, numerator := 1451149736836590997308098740224 }, { target := 280, numerator := 45348429276143468665878085632 }, { target := 281, numerator := 52325110703242463845243944960 }, { target := 282, numerator := 54650671178942128905032564736 }, { target := 353, numerator := 41074135253676954643951779840 }, { target := 356, numerator := 139230225580476985184291389440 }, { target := 358, numerator := 41074135253676954643951779840 }, { target := 379, numerator := 46941868861345091021659176960 }, { target := 382, numerator := 159120257806259411639190159360 }, { target := 384, numerator := 46941868861345091021659176960 }, { target := 660, numerator := 2703308370412393007132180480 }, { target := 661, numerator := 431575593318776683151868559360 }, { target := 663, numerator := 4306475417562413377798285557760 }, { target := 671, numerator := 431575593318776683151868559360 }, { target := 678, numerator := 2702999914413943395880796160 }]

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
    Slot14.Left3.expected,
    Slot14.Left4.expected,
    Slot14.Left5.expected,
    Slot14.Left6.expected,
    Slot14.Left7.expected,
    Slot14.Left8.expected,
    Slot14.Left9.expected,
    Slot14.Left10.expected,
    Slot14.Left11.expected,
    Slot14.Left12.expected,
    Slot14.Left13.expected,
    Slot14.Left14.expected,
    Slot14.Left15.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected,
    Slot16.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 5345833815472662208309100544 }, { target := 57, numerator := 789551678756350133144968495104 }, { target := 59, numerator := 8229365104294606649696200949760 }, { target := 67, numerator := 789551678756350133144968495104 }, { target := 74, numerator := 5345833815472662208309100544 }, { target := 110, numerator := 2711123782310538027168956416 }, { target := 112, numerator := 98252023256083279580414083072 }, { target := 115, numerator := 98252059363318367354387169280 }, { target := 122, numerator := 2711087675075450253195870208 }, { target := 206, numerator := 432823301890943023692080218112 }, { target := 208, numerator := 15685659725547969929070881275904 }, { target := 211, numerator := 15685665489966700941026483240960 }, { target := 218, numerator := 432817537472212011736478253056 }, { target := 302, numerator := 4318925672807378986621460283392 }, { target := 304, numerator := 156519295951998893992587416305664 }, { target := 307, numerator := 156519353472229291505359372943360 }, { target := 314, numerator := 4318868152576981473849503645696 }, { target := 524, numerator := 55156695912080481950449532928 }, { target := 527, numerator := 186966302922354808676048437248 }, { target := 529, numerator := 55156695912080481950449532928 }, { target := 620, numerator := 651318430451163137925521080320 }, { target := 623, numerator := 2207793577061849336493763461120 }, { target := 625, numerator := 651318430451163137925521080320 }, { target := 646, numerator := 1464586308473966839875766321152 }, { target := 649, numerator := 4964552043555293643142732972032 }, { target := 651, numerator := 1464586308473966839875766321152 }, { target := 679, numerator := 432823301890943023692080218112 }, { target := 681, numerator := 15685659725547969929070881275904 }, { target := 684, numerator := 15685665489966700941026483240960 }, { target := 691, numerator := 432817537472212011736478253056 }, { target := 695, numerator := 41074135253676954643951779840 }, { target := 698, numerator := 139230225580476985184291389440 }, { target := 700, numerator := 41074135253676954643951779840 }, { target := 721, numerator := 651318430451163137925521080320 }, { target := 724, numerator := 2207793577061849336493763461120 }, { target := 726, numerator := 651318430451163137925521080320 }, { target := 735, numerator := 46941868861345091021659176960 }, { target := 738, numerator := 159120257806259411639190159360 }, { target := 740, numerator := 46941868861345091021659176960 }, { target := 836, numerator := 45768322139811463746117697536 }, { target := 839, numerator := 155142251361102926348210405376 }, { target := 841, numerator := 45768322139811463746117697536 }, { target := 862, numerator := 45768322139811463746117697536 }, { target := 865, numerator := 155142251361102926348210405376 }, { target := 867, numerator := 45768322139811463746117697536 }, { target := 911, numerator := 45768322139811463746117697536 }, { target := 914, numerator := 155142251361102926348210405376 }, { target := 916, numerator := 45768322139811463746117697536 }, { target := 937, numerator := 1464586308473966839875766321152 }, { target := 940, numerator := 4964552043555293643142732972032 }, { target := 942, numerator := 1464586308473966839875766321152 }, { target := 951, numerator := 45768322139811463746117697536 }, { target := 954, numerator := 155142251361102926348210405376 }, { target := 956, numerator := 45768322139811463746117697536 }, { target := 966, numerator := 2710814434548978175728156672 }, { target := 968, numerator := 98240812390809878932356071424 }, { target := 971, numerator := 98240848493925017472215285760 }, { target := 978, numerator := 2710778331433839635868942336 }, { target := 982, numerator := 52809602469013227399366574080 }, { target := 985, numerator := 179010290032041838094088929280 }, { target := 987, numerator := 52809602469013227399366574080 }, { target := 996, numerator := 55156695912080481950449532928 }, { target := 999, numerator := 186966302922354808676048437248 }, { target := 1001, numerator := 55156695912080481950449532928 }]

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
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left2.expected,
    Slot19.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 7795153684875128918505422848 }, { target := 5, numerator := 186580775296043408307452379136 }, { target := 6, numerator := 139558396616312791928080957440 }, { target := 7, numerator := 161938031389018807210241687552 }, { target := 8, numerator := 7795153684875128918505422848 }, { target := 9, numerator := 161686574818538964341902802944 }, { target := 10, numerator := 162440944529978492946919456768 }, { target := 11, numerator := 7795153684875128918505422848 }, { target := 12, numerator := 186580775296043408307452379136 }, { target := 13, numerator := 7795153684875128918505422848 }, { target := 14, numerator := 91606630938511788170784276480 }, { target := 15, numerator := 7703132146817432203306163240960 }, { target := 20, numerator := 7703130288406888342884030873600 }, { target := 28, numerator := 91608489349055648592916643840 }, { target := 110, numerator := 885263554259141088625295360 }, { target := 112, numerator := 30982017251906126277068718080 }, { target := 115, numerator := 30982032447411556995311861760 }, { target := 122, numerator := 885255956506425729503723520 }, { target := 126, numerator := 7795153684875128918505422848 }, { target := 127, numerator := 186580775296043408307452379136 }, { target := 128, numerator := 139558396616312791928080957440 }, { target := 129, numerator := 161938031389018807210241687552 }, { target := 130, numerator := 7795153684875128918505422848 }, { target := 131, numerator := 161686574818538964341902802944 }, { target := 132, numerator := 162440944529978492946919456768 }, { target := 133, numerator := 7795153684875128918505422848 }, { target := 134, numerator := 186580775296043408307452379136 }, { target := 135, numerator := 7795153684875128918505422848 }, { target := 136, numerator := 314469546526696158865448239104 }, { target := 137, numerator := 26443505761835704301929898180608 }, { target := 142, numerator := 26443499382237251647472696033280 }, { target := 150, numerator := 314475926125148813322650386432 }, { target := 152, numerator := 200856709504914405706860331008 }, { target := 153, numerator := 29665484871616788869324029820928 }, { target := 155, numerator := 309198387607759007075472318136320 }, { target := 163, numerator := 29665484871616788869324029820928 }, { target := 170, numerator := 200856709504914405706860331008 }, { target := 206, numerator := 14872427711553570288904962048 }, { target := 208, numerator := 520497889832022921454754463744 }, { target := 211, numerator := 520498145116514157521239277568 }, { target := 218, numerator := 14872300069307952255662555136 }, { target := 241, numerator := 32223593375032735625960751104 }, { target := 243, numerator := 1127745427969382996485301338112 }, { target := 246, numerator := 1127745981085780674629351768064 }, { target := 253, numerator := 32223316816833896553935536128 }, { target := 267, numerator := 91606630938511788170784276480 }, { target := 268, numerator := 7703132146817432203306163240960 }, { target := 273, numerator := 7703130288406888342884030873600 }, { target := 281, numerator := 91608489349055648592916643840 }, { target := 283, numerator := 200841518287042263009529430016 }, { target := 284, numerator := 29663241208235673599674580729856 }, { target := 286, numerator := 309175002279564382993231002992640 }, { target := 294, numerator := 29663241208235673599674580729856 }, { target := 301, numerator := 200841518287042263009529430016 }, { target := 302, numerator := 1062316265110969306350354432 }, { target := 304, numerator := 37178420702287351532482461696 }, { target := 307, numerator := 37178438936893868394374234112 }, { target := 314, numerator := 1062307147807710875404468224 }, { target := 660, numerator := 5361025033344804905640001536 }, { target := 661, numerator := 791795342137465402794417586176 }, { target := 663, numerator := 8252750432489230731937516093440 }, { target := 671, numerator := 791795342137465402794417586176 }, { target := 678, numerator := 5361025033344804905640001536 }]

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
    Slot19.Left4.expected,
    Slot19.Left5.expected,
    Slot19.Left6.expected,
    Slot19.Left7.expected,
    Slot19.Left8.expected,
    Slot19.Left9.expected,
    Slot19.Left10.expected,
    Slot19.Left11.expected,
    Slot19.Left12.expected,
    Slot19.Left13.expected,
    Slot19.Left14.expected,
    Slot19.Left15.expected,
    Slot19.Left16.expected,
    Slot19.Left17.expected,
    Slot19.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 337, numerator := 16997060241775508901605670912 }, { target := 339, numerator := 594854731236597624519719387136 }, { target := 342, numerator := 594855022990301894309987745792 }, { target := 349, numerator := 16996914364923374006471491584 }, { target := 363, numerator := 1239368975962797524075413504 }, { target := 365, numerator := 43374824152668576787896205312 }, { target := 368, numerator := 43374845426376179793436606464 }, { target := 375, numerator := 1239358339108996021305212928 }, { target := 473, numerator := 32223593375032735625960751104 }, { target := 475, numerator := 1127745427969382996485301338112 }, { target := 478, numerator := 1127745981085780674629351768064 }, { target := 485, numerator := 32223316816833896553935536128 }, { target := 508, numerator := 32223593375032735625960751104 }, { target := 510, numerator := 1127745427969382996485301338112 }, { target := 513, numerator := 1127745981085780674629351768064 }, { target := 520, numerator := 32223316816833896553935536128 }, { target := 569, numerator := 16997060241775508901605670912 }, { target := 571, numerator := 594854731236597624519719387136 }, { target := 574, numerator := 594855022990301894309987745792 }, { target := 581, numerator := 16996914364923374006471491584 }, { target := 604, numerator := 397660388573206177010482675712 }, { target := 606, numerator := 13917122149556231923659268161536 }, { target := 609, numerator := 13917128975377271402294088302592 }, { target := 616, numerator := 397656975662686437693072605184 }, { target := 630, numerator := 31869487953329079190510632960 }, { target := 632, numerator := 1115352621068620545974473850880 }, { target := 635, numerator := 1115353168106816051831227023360 }, { target := 642, numerator := 31869214434231326262134046720 }, { target := 679, numerator := 14872427711553570288904962048 }, { target := 681, numerator := 520497889832022921454754463744 }, { target := 684, numerator := 520498145116514157521239277568 }, { target := 691, numerator := 14872300069307952255662555136 }, { target := 705, numerator := 32223593375032735625960751104 }, { target := 707, numerator := 1127745427969382996485301338112 }, { target := 710, numerator := 1127745981085780674629351768064 }, { target := 717, numerator := 32223316816833896553935536128 }, { target := 785, numerator := 1239368975962797524075413504 }, { target := 787, numerator := 43374824152668576787896205312 }, { target := 790, numerator := 43374845426376179793436606464 }, { target := 797, numerator := 1239358339108996021305212928 }, { target := 820, numerator := 31869487953329079190510632960 }, { target := 822, numerator := 1115352621068620545974473850880 }, { target := 825, numerator := 1115353168106816051831227023360 }, { target := 832, numerator := 31869214434231326262134046720 }, { target := 846, numerator := 1239368975962797524075413504 }, { target := 848, numerator := 43374824152668576787896205312 }, { target := 851, numerator := 43374845426376179793436606464 }, { target := 858, numerator := 1239358339108996021305212928 }, { target := 895, numerator := 32223593375032735625960751104 }, { target := 897, numerator := 1127745427969382996485301338112 }, { target := 900, numerator := 1127745981085780674629351768064 }, { target := 907, numerator := 32223316816833896553935536128 }, { target := 921, numerator := 32223593375032735625960751104 }, { target := 923, numerator := 1127745427969382996485301338112 }, { target := 926, numerator := 1127745981085780674629351768064 }, { target := 933, numerator := 32223316816833896553935536128 }, { target := 966, numerator := 1062316265110969306350354432 }, { target := 968, numerator := 37178420702287351532482461696 }, { target := 971, numerator := 37178438936893868394374234112 }, { target := 978, numerator := 1062307147807710875404468224 }]

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
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot23.Left0.expected,
    Slot24.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 19807040628566084398385987584 }, { target := 1, numerator := 19807040628566084398385987584 }, { target := 2, numerator := 19807040628566084398385987584 }, { target := 3, numerator := 19807040628566084398385987584 }, { target := 4, numerator := 122034772059092754041237667840 }, { target := 6, numerator := 1182037721148959335215771156480 }, { target := 11, numerator := 122034772059092754041237667840 }, { target := 14, numerator := 84845303521720011707457208320 }, { target := 15, numerator := 7104023863537808941065323937792 }, { target := 20, numerator := 7104026434477767177114363101184 }, { target := 28, numerator := 84842732581761775658418044928 }, { target := 56, numerator := 2190705934428059435513413632 }, { target := 57, numerator := 224729493467092686895094693888 }, { target := 58, numerator := 1618449441009084807637893120 }, { target := 59, numerator := 2404168796393690311949497139200 }, { target := 60, numerator := 1660761844695596828752609280 }, { target := 61, numerator := 52890504608140026393395200 }, { target := 62, numerator := 1618449441009084807637893120 }, { target := 63, numerator := 920294780181636459245076480 }, { target := 64, numerator := 1660761844695596828752609280 }, { target := 65, numerator := 25926925358910240938042327040 }, { target := 66, numerator := 1015497688476288506753187840 }, { target := 67, numerator := 224729663605245842001181540352 }, { target := 68, numerator := 1618449441009084807637893120 }, { target := 69, numerator := 52890504608140026393395200 }, { target := 70, numerator := 1015497688476288506753187840 }, { target := 71, numerator := 52890504608140026393395200 }, { target := 72, numerator := 1629027541930712812916572160 }, { target := 73, numerator := 920294780181636459245076480 }, { target := 74, numerator := 2190705934428059435513413632 }, { target := 126, numerator := 122034713868392717161347416064 }, { target := 128, numerator := 1182037157509585875746640887808 }, { target := 133, numerator := 122034713868392717161347416064 }, { target := 136, numerator := 308600658146708913127843430400 }, { target := 137, numerator := 25838866133780441860424324874240 }, { target := 142, numerator := 25838875484843261315267407380480 }, { target := 150, numerator := 308591307083889458284760924160 }, { target := 152, numerator := 78556044498015360013157007360 }, { target := 153, numerator := 8236459584516100272124109783040 }, { target := 155, numerator := 88780801989414044049101291520000 }, { target := 163, numerator := 8236465867491745958388207452160 }, { target := 170, numerator := 78556044498015360013157007360 }, { target := 267, numerator := 84845303521720011707457208320 }, { target := 268, numerator := 7104023863537808941065323937792 }, { target := 273, numerator := 7104026434477767177114363101184 }, { target := 281, numerator := 84842732581761775658418044928 }, { target := 283, numerator := 78556025261621949589484470272 }, { target := 284, numerator := 8236457567614945316323939319808 }, { target := 286, numerator := 88780780249235483958290939904000 }, { target := 294, numerator := 8236463850589052460365336543232 }, { target := 301, numerator := 78556025261621949589484470272 }, { target := 660, numerator := 2127256565291701827513876480 }, { target := 661, numerator := 223039014220787161850676510720 }, { target := 663, numerator := 2404137646067642262733455360000 }, { target := 671, numerator := 223039184360478859179463802880 }, { target := 678, numerator := 2127256565291701827513876480 }]

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

namespace RouteChunk14

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot24.Left1.expected,
    Slot24.Left2.expected,
    Slot24.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 91, numerator := 75368969066599537610588160 }, { target := 92, numerator := 2009839175109321002949017600 }, { target := 93, numerator := 1921908711198288209069998080 }, { target := 94, numerator := 62807474222166281342156800 }, { target := 95, numerator := 1972154690576021234143723520 }, { target := 96, numerator := 62807474222166281342156800 }, { target := 97, numerator := 1921908711198288209069998080 }, { target := 98, numerator := 1092850051465693295353528320 }, { target := 99, numerator := 1972154690576021234143723520 }, { target := 100, numerator := 30788223863705911113925263360 }, { target := 101, numerator := 1205903505065592601769410560 }, { target := 102, numerator := 2009839175109321002949017600 }, { target := 103, numerator := 1921908711198288209069998080 }, { target := 104, numerator := 62807474222166281342156800 }, { target := 105, numerator := 1205903505065592601769410560 }, { target := 106, numerator := 62807474222166281342156800 }, { target := 107, numerator := 1934470206042721465338429440 }, { target := 108, numerator := 1092850051465693295353528320 }, { target := 109, numerator := 75368969066599537610588160 }, { target := 152, numerator := 57518423761352278702817280 }, { target := 153, numerator := 1533824633636060765408460800 }, { target := 154, numerator := 1466719805914483106921840640 }, { target := 155, numerator := 47932019801126898919014400 }, { target := 156, numerator := 1505065421755384626057052160 }, { target := 157, numerator := 47932019801126898919014400 }, { target := 158, numerator := 1466719805914483106921840640 }, { target := 159, numerator := 834017144539608041190850560 }, { target := 160, numerator := 1505065421755384626057052160 }, { target := 161, numerator := 23496276106512405850100858880 }, { target := 162, numerator := 920294780181636459245076480 }, { target := 163, numerator := 1533824633636060765408460800 }, { target := 164, numerator := 1466719805914483106921840640 }, { target := 165, numerator := 47932019801126898919014400 }, { target := 166, numerator := 920294780181636459245076480 }, { target := 167, numerator := 47932019801126898919014400 }, { target := 168, numerator := 1476306209874708486705643520 }, { target := 169, numerator := 834017144539608041190850560 }, { target := 170, numerator := 57518423761352278702817280 }, { target := 187, numerator := 593034782918770045935943680 }, { target := 188, numerator := 15814260877833867891625164800 }, { target := 189, numerator := 15122386964428636171366563840 }, { target := 190, numerator := 494195652432308371613286400 }, { target := 191, numerator := 15517743486374482868657192960 }, { target := 192, numerator := 494195652432308371613286400 }, { target := 193, numerator := 15122386964428636171366563840 }, { target := 194, numerator := 8599004352322165666071183360 }, { target := 195, numerator := 15517743486374482868657192960 }, { target := 196, numerator := 242254708822317563764832993280 }, { target := 197, numerator := 9488556526700320734975098880 }, { target := 198, numerator := 15814260877833867891625164800 }, { target := 199, numerator := 15122386964428636171366563840 }, { target := 200, numerator := 494195652432308371613286400 }, { target := 201, numerator := 9488556526700320734975098880 }, { target := 202, numerator := 494195652432308371613286400 }, { target := 203, numerator := 15221226094915097845689221120 }, { target := 204, numerator := 8599004352322165666071183360 }, { target := 205, numerator := 593034782918770045935943680 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk14

namespace RouteChunk15

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot24.Left4.expected,
    Slot24.Left5.expected,
    Slot24.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 222, numerator := 71402181220989035631083520 }, { target := 223, numerator := 1904058165893040950162227200 }, { target := 224, numerator := 1820755621135220408592629760 }, { target := 225, numerator := 59501817684157529692569600 }, { target := 226, numerator := 1868357075282546432346685440 }, { target := 227, numerator := 59501817684157529692569600 }, { target := 228, numerator := 1820755621135220408592629760 }, { target := 229, numerator := 1035331627704341016650711040 }, { target := 230, numerator := 1868357075282546432346685440 }, { target := 231, numerator := 29167791028774021055297617920 }, { target := 232, numerator := 1142434899535824570097336320 }, { target := 233, numerator := 1904058165893040950162227200 }, { target := 234, numerator := 1820755621135220408592629760 }, { target := 235, numerator := 59501817684157529692569600 }, { target := 236, numerator := 1142434899535824570097336320 }, { target := 237, numerator := 59501817684157529692569600 }, { target := 238, numerator := 1832655984672051914531143680 }, { target := 239, numerator := 1035331627704341016650711040 }, { target := 240, numerator := 71402181220989035631083520 }, { target := 283, numerator := 57518423761352278702817280 }, { target := 284, numerator := 1533824633636060765408460800 }, { target := 285, numerator := 1466719805914483106921840640 }, { target := 286, numerator := 47932019801126898919014400 }, { target := 287, numerator := 1505065421755384626057052160 }, { target := 288, numerator := 47932019801126898919014400 }, { target := 289, numerator := 1466719805914483106921840640 }, { target := 290, numerator := 834017144539608041190850560 }, { target := 291, numerator := 1505065421755384626057052160 }, { target := 292, numerator := 23496276106512405850100858880 }, { target := 293, numerator := 920294780181636459245076480 }, { target := 294, numerator := 1533824633636060765408460800 }, { target := 295, numerator := 1466719805914483106921840640 }, { target := 296, numerator := 47932019801126898919014400 }, { target := 297, numerator := 920294780181636459245076480 }, { target := 298, numerator := 47932019801126898919014400 }, { target := 299, numerator := 1476306209874708486705643520 }, { target := 300, numerator := 834017144539608041190850560 }, { target := 301, numerator := 57518423761352278702817280 }, { target := 318, numerator := 71402181220989035631083520 }, { target := 319, numerator := 1904058165893040950162227200 }, { target := 320, numerator := 1820755621135220408592629760 }, { target := 321, numerator := 59501817684157529692569600 }, { target := 322, numerator := 1868357075282546432346685440 }, { target := 323, numerator := 59501817684157529692569600 }, { target := 324, numerator := 1820755621135220408592629760 }, { target := 325, numerator := 1035331627704341016650711040 }, { target := 326, numerator := 1868357075282546432346685440 }, { target := 327, numerator := 29167791028774021055297617920 }, { target := 328, numerator := 1142434899535824570097336320 }, { target := 329, numerator := 1904058165893040950162227200 }, { target := 330, numerator := 1820755621135220408592629760 }, { target := 331, numerator := 59501817684157529692569600 }, { target := 332, numerator := 1142434899535824570097336320 }, { target := 333, numerator := 59501817684157529692569600 }, { target := 334, numerator := 1832655984672051914531143680 }, { target := 335, numerator := 1035331627704341016650711040 }, { target := 336, numerator := 71402181220989035631083520 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk15

namespace RouteChunk16

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot24.Left7.expected,
    Slot24.Left8.expected,
    Slot24.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 419, numerator := 71402181220989035631083520 }, { target := 420, numerator := 1904058165893040950162227200 }, { target := 421, numerator := 1820755621135220408592629760 }, { target := 422, numerator := 59501817684157529692569600 }, { target := 423, numerator := 1868357075282546432346685440 }, { target := 424, numerator := 59501817684157529692569600 }, { target := 425, numerator := 1820755621135220408592629760 }, { target := 426, numerator := 1035331627704341016650711040 }, { target := 427, numerator := 1868357075282546432346685440 }, { target := 428, numerator := 29167791028774021055297617920 }, { target := 429, numerator := 1142434899535824570097336320 }, { target := 430, numerator := 1904058165893040950162227200 }, { target := 431, numerator := 1820755621135220408592629760 }, { target := 432, numerator := 59501817684157529692569600 }, { target := 433, numerator := 1142434899535824570097336320 }, { target := 434, numerator := 59501817684157529692569600 }, { target := 435, numerator := 1832655984672051914531143680 }, { target := 436, numerator := 1035331627704341016650711040 }, { target := 437, numerator := 71402181220989035631083520 }, { target := 454, numerator := 3058393428965697026198077440 }, { target := 455, numerator := 81557158105751920698615398400 }, { target := 456, numerator := 77989032438625274168050974720 }, { target := 457, numerator := 2548661190804747521831731200 }, { target := 458, numerator := 80027961391269072185516359680 }, { target := 459, numerator := 2548661190804747521831731200 }, { target := 460, numerator := 77989032438625274168050974720 }, { target := 461, numerator := 44346704720002606879872122880 }, { target := 462, numerator := 80027961391269072185516359680 }, { target := 463, numerator := 1249353715732487235201914634240 }, { target := 464, numerator := 48934294863451152419169239040 }, { target := 465, numerator := 81557158105751920698615398400 }, { target := 466, numerator := 77989032438625274168050974720 }, { target := 467, numerator := 2548661190804747521831731200 }, { target := 468, numerator := 48934294863451152419169239040 }, { target := 469, numerator := 2548661190804747521831731200 }, { target := 470, numerator := 78498764676786223672417320960 }, { target := 471, numerator := 44346704720002606879872122880 }, { target := 472, numerator := 3058393428965697026198077440 }, { target := 489, numerator := 71402181220989035631083520 }, { target := 490, numerator := 1904058165893040950162227200 }, { target := 491, numerator := 1820755621135220408592629760 }, { target := 492, numerator := 59501817684157529692569600 }, { target := 493, numerator := 1868357075282546432346685440 }, { target := 494, numerator := 59501817684157529692569600 }, { target := 495, numerator := 1820755621135220408592629760 }, { target := 496, numerator := 1035331627704341016650711040 }, { target := 497, numerator := 1868357075282546432346685440 }, { target := 498, numerator := 29167791028774021055297617920 }, { target := 499, numerator := 1142434899535824570097336320 }, { target := 500, numerator := 1904058165893040950162227200 }, { target := 501, numerator := 1820755621135220408592629760 }, { target := 502, numerator := 59501817684157529692569600 }, { target := 503, numerator := 1142434899535824570097336320 }, { target := 504, numerator := 59501817684157529692569600 }, { target := 505, numerator := 1832655984672051914531143680 }, { target := 506, numerator := 1035331627704341016650711040 }, { target := 507, numerator := 71402181220989035631083520 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk16

namespace RouteChunk17

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot24.Left10.expected,
    Slot24.Left11.expected,
    Slot24.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 550, numerator := 593034782918770045935943680 }, { target := 551, numerator := 15814260877833867891625164800 }, { target := 552, numerator := 15122386964428636171366563840 }, { target := 553, numerator := 494195652432308371613286400 }, { target := 554, numerator := 15517743486374482868657192960 }, { target := 555, numerator := 494195652432308371613286400 }, { target := 556, numerator := 15122386964428636171366563840 }, { target := 557, numerator := 8599004352322165666071183360 }, { target := 558, numerator := 15517743486374482868657192960 }, { target := 559, numerator := 242254708822317563764832993280 }, { target := 560, numerator := 9488556526700320734975098880 }, { target := 561, numerator := 15814260877833867891625164800 }, { target := 562, numerator := 15122386964428636171366563840 }, { target := 563, numerator := 494195652432308371613286400 }, { target := 564, numerator := 9488556526700320734975098880 }, { target := 565, numerator := 494195652432308371613286400 }, { target := 566, numerator := 15221226094915097845689221120 }, { target := 567, numerator := 8599004352322165666071183360 }, { target := 568, numerator := 593034782918770045935943680 }, { target := 585, numerator := 3058393428965697026198077440 }, { target := 586, numerator := 81557158105751920698615398400 }, { target := 587, numerator := 77989032438625274168050974720 }, { target := 588, numerator := 2548661190804747521831731200 }, { target := 589, numerator := 80027961391269072185516359680 }, { target := 590, numerator := 2548661190804747521831731200 }, { target := 591, numerator := 77989032438625274168050974720 }, { target := 592, numerator := 44346704720002606879872122880 }, { target := 593, numerator := 80027961391269072185516359680 }, { target := 594, numerator := 1249353715732487235201914634240 }, { target := 595, numerator := 48934294863451152419169239040 }, { target := 596, numerator := 81557158105751920698615398400 }, { target := 597, numerator := 77989032438625274168050974720 }, { target := 598, numerator := 2548661190804747521831731200 }, { target := 599, numerator := 48934294863451152419169239040 }, { target := 600, numerator := 2548661190804747521831731200 }, { target := 601, numerator := 78498764676786223672417320960 }, { target := 602, numerator := 44346704720002606879872122880 }, { target := 603, numerator := 3058393428965697026198077440 }, { target := 660, numerator := 63468605529768031672074240 }, { target := 661, numerator := 1692496147460480844588646400 }, { target := 662, numerator := 1618449441009084807637893120 }, { target := 663, numerator := 52890504608140026393395200 }, { target := 664, numerator := 1660761844695596828752609280 }, { target := 665, numerator := 52890504608140026393395200 }, { target := 666, numerator := 1618449441009084807637893120 }, { target := 667, numerator := 920294780181636459245076480 }, { target := 668, numerator := 1660761844695596828752609280 }, { target := 669, numerator := 25926925358910240938042327040 }, { target := 670, numerator := 1015497688476288506753187840 }, { target := 671, numerator := 1692496147460480844588646400 }, { target := 672, numerator := 1618449441009084807637893120 }, { target := 673, numerator := 52890504608140026393395200 }, { target := 674, numerator := 1015497688476288506753187840 }, { target := 675, numerator := 52890504608140026393395200 }, { target := 676, numerator := 1629027541930712812916572160 }, { target := 677, numerator := 920294780181636459245076480 }, { target := 678, numerator := 63468605529768031672074240 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk17

namespace RouteChunk18

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot24.Left13.expected,
    Slot24.Left14.expected,
    Slot24.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 766, numerator := 71402181220989035631083520 }, { target := 767, numerator := 1904058165893040950162227200 }, { target := 768, numerator := 1820755621135220408592629760 }, { target := 769, numerator := 59501817684157529692569600 }, { target := 770, numerator := 1868357075282546432346685440 }, { target := 771, numerator := 59501817684157529692569600 }, { target := 772, numerator := 1820755621135220408592629760 }, { target := 773, numerator := 1035331627704341016650711040 }, { target := 774, numerator := 1868357075282546432346685440 }, { target := 775, numerator := 29167791028774021055297617920 }, { target := 776, numerator := 1142434899535824570097336320 }, { target := 777, numerator := 1904058165893040950162227200 }, { target := 778, numerator := 1820755621135220408592629760 }, { target := 779, numerator := 59501817684157529692569600 }, { target := 780, numerator := 1142434899535824570097336320 }, { target := 781, numerator := 59501817684157529692569600 }, { target := 782, numerator := 1832655984672051914531143680 }, { target := 783, numerator := 1035331627704341016650711040 }, { target := 784, numerator := 71402181220989035631083520 }, { target := 801, numerator := 71402181220989035631083520 }, { target := 802, numerator := 1904058165893040950162227200 }, { target := 803, numerator := 1820755621135220408592629760 }, { target := 804, numerator := 59501817684157529692569600 }, { target := 805, numerator := 1868357075282546432346685440 }, { target := 806, numerator := 59501817684157529692569600 }, { target := 807, numerator := 1820755621135220408592629760 }, { target := 808, numerator := 1035331627704341016650711040 }, { target := 809, numerator := 1868357075282546432346685440 }, { target := 810, numerator := 29167791028774021055297617920 }, { target := 811, numerator := 1142434899535824570097336320 }, { target := 812, numerator := 1904058165893040950162227200 }, { target := 813, numerator := 1820755621135220408592629760 }, { target := 814, numerator := 59501817684157529692569600 }, { target := 815, numerator := 1142434899535824570097336320 }, { target := 816, numerator := 59501817684157529692569600 }, { target := 817, numerator := 1832655984672051914531143680 }, { target := 818, numerator := 1035331627704341016650711040 }, { target := 819, numerator := 71402181220989035631083520 }, { target := 876, numerator := 75368969066599537610588160 }, { target := 877, numerator := 2009839175109321002949017600 }, { target := 878, numerator := 1921908711198288209069998080 }, { target := 879, numerator := 62807474222166281342156800 }, { target := 880, numerator := 1972154690576021234143723520 }, { target := 881, numerator := 62807474222166281342156800 }, { target := 882, numerator := 1921908711198288209069998080 }, { target := 883, numerator := 1092850051465693295353528320 }, { target := 884, numerator := 1972154690576021234143723520 }, { target := 885, numerator := 30788223863705911113925263360 }, { target := 886, numerator := 1205903505065592601769410560 }, { target := 887, numerator := 2009839175109321002949017600 }, { target := 888, numerator := 1921908711198288209069998080 }, { target := 889, numerator := 62807474222166281342156800 }, { target := 890, numerator := 1205903505065592601769410560 }, { target := 891, numerator := 62807474222166281342156800 }, { target := 892, numerator := 1934470206042721465338429440 }, { target := 893, numerator := 1092850051465693295353528320 }, { target := 894, numerator := 75368969066599537610588160 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk18

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent3
