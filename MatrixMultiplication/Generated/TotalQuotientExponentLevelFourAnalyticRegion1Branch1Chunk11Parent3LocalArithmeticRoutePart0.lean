import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk11Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 49; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent3

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
    Slot0.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 219, numerator := 29127556466339971678076928 }, { target := 220, numerator := 436913346995099575171153920 }, { target := 221, numerator := 767025653613619254189359104 }, { target := 222, numerator := 29127556466339971678076928 }, { target := 223, numerator := 485459274438999527967948800 }, { target := 224, numerator := 29127556466339971678076928 }, { target := 225, numerator := 767025653613619254189359104 }, { target := 226, numerator := 762171060869229258909679616 }, { target := 227, numerator := 485459274438999527967948800 }, { target := 228, numerator := 11762678219656958562663399424 }, { target := 229, numerator := 752461875380449268350320640 }, { target := 230, numerator := 436913346995099575171153920 }, { target := 231, numerator := 767025653613619254189359104 }, { target := 232, numerator := 29127556466339971678076928 }, { target := 233, numerator := 752461875380449268350320640 }, { target := 234, numerator := 29127556466339971678076928 }, { target := 235, numerator := 767025653613619254189359104 }, { target := 236, numerator := 767025653613619254189359104 }, { target := 237, numerator := 29127556466339971678076928 }, { target := 359, numerator := 29042553869648318064230400 }, { target := 360, numerator := 435638308044724770963456000 }, { target := 361, numerator := 764787251900739042358067200 }, { target := 362, numerator := 29042553869648318064230400 }, { target := 363, numerator := 484042564494138634403840000 }, { target := 364, numerator := 29042553869648318064230400 }, { target := 365, numerator := 764787251900739042358067200 }, { target := 366, numerator := 759946826255797656014028800 }, { target := 367, numerator := 484042564494138634403840000 }, { target := 368, numerator := 11728351337692979111605043200 }, { target := 369, numerator := 750265974965914883325952000 }, { target := 370, numerator := 435638308044724770963456000 }, { target := 371, numerator := 764787251900739042358067200 }, { target := 372, numerator := 29042553869648318064230400 }, { target := 373, numerator := 750265974965914883325952000 }, { target := 374, numerator := 29042553869648318064230400 }, { target := 375, numerator := 764787251900739042358067200 }, { target := 376, numerator := 764787251900739042358067200 }, { target := 377, numerator := 29042553869648318064230400 }, { target := 434, numerator := 28844214477367792965255168 }, { target := 435, numerator := 432663217160516894478827520 }, { target := 436, numerator := 759564314570685214751719424 }, { target := 437, numerator := 28844214477367792965255168 }, { target := 438, numerator := 480736907956129882754252800 }, { target := 439, numerator := 28844214477367792965255168 }, { target := 440, numerator := 759564314570685214751719424 }, { target := 441, numerator := 754756945491123915924176896 }, { target := 442, numerator := 480736907956129882754252800 }, { target := 443, numerator := 11648255279777027059135545344 }, { target := 444, numerator := 745142207332001318269091840 }, { target := 445, numerator := 432663217160516894478827520 }, { target := 446, numerator := 759564314570685214751719424 }, { target := 447, numerator := 28844214477367792965255168 }, { target := 448, numerator := 745142207332001318269091840 }, { target := 449, numerator := 28844214477367792965255168 }, { target := 450, numerator := 759564314570685214751719424 }, { target := 451, numerator := 759564314570685214751719424 }, { target := 452, numerator := 28844214477367792965255168 }]

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
    Slot0.Left3.expected,
    Slot1.Left0.expected,
    Slot2.Left0.expected,
    Slot2.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 61, numerator := 59007574070190629676122112 }, { target := 62, numerator := 44255680552642972257091584 }, { target := 63, numerator := 46714329472234248493596672 }, { target := 64, numerator := 60236898529986267794374656 }, { target := 65, numerator := 806436845625938605573668864 }, { target := 66, numerator := 1410035155385596921635667968 }, { target := 67, numerator := 43026356092847334138839040 }, { target := 68, numerator := 806436845625938605573668864 }, { target := 69, numerator := 45485005012438610375344128 }, { target := 70, numerator := 46714329472234248493596672 }, { target := 71, numerator := 46714329472234248493596672 }, { target := 72, numerator := 45485005012438610375344128 }, { target := 73, numerator := 1410035155385596921635667968 }, { target := 74, numerator := 45485005012438610375344128 }, { target := 75, numerator := 59007574070190629676122112 }, { target := 76, numerator := 60236898529986267794374656 }, { target := 177, numerator := 2667034998990153915996045312 }, { target := 178, numerator := 2000276249242615436997033984 }, { target := 179, numerator := 2111402707533871850163535872 }, { target := 180, numerator := 2722598228135782122579296256 }, { target := 181, numerator := 36449478319532103518612619264 }, { target := 182, numerator := 63731023830035552950988832768 }, { target := 183, numerator := 1944713020096987230413783040 }, { target := 184, numerator := 36449478319532103518612619264 }, { target := 185, numerator := 2055839478388243643580284928 }, { target := 186, numerator := 2111402707533871850163535872 }, { target := 187, numerator := 2111402707533871850163535872 }, { target := 188, numerator := 2055839478388243643580284928 }, { target := 189, numerator := 63731023830035552950988832768 }, { target := 190, numerator := 2055839478388243643580284928 }, { target := 191, numerator := 2667034998990153915996045312 }, { target := 192, numerator := 2722598228135782122579296256 }, { target := 469, numerator := 29042553869648318064230400 }, { target := 470, numerator := 435638308044724770963456000 }, { target := 471, numerator := 764787251900739042358067200 }, { target := 472, numerator := 29042553869648318064230400 }, { target := 473, numerator := 484042564494138634403840000 }, { target := 474, numerator := 29042553869648318064230400 }, { target := 475, numerator := 764787251900739042358067200 }, { target := 476, numerator := 759946826255797656014028800 }, { target := 477, numerator := 484042564494138634403840000 }, { target := 478, numerator := 11728351337692979111605043200 }, { target := 479, numerator := 750265974965914883325952000 }, { target := 480, numerator := 435638308044724770963456000 }, { target := 481, numerator := 764787251900739042358067200 }, { target := 482, numerator := 29042553869648318064230400 }, { target := 483, numerator := 750265974965914883325952000 }, { target := 484, numerator := 29042553869648318064230400 }, { target := 485, numerator := 764787251900739042358067200 }, { target := 486, numerator := 764787251900739042358067200 }, { target := 487, numerator := 29042553869648318064230400 }, { target := 488, numerator := 2970656582080461887772819456 }, { target := 490, numerator := 115871601356415493111478747136 }, { target := 493, numerator := 115871558855117147284671823872 }, { target := 500, numerator := 2970670749179910496708460544 }]

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
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 17, numerator := 11897998894825557295366144 }, { target := 18, numerator := 288238618387548178349031424 }, { target := 19, numerator := 218385850682443293582688256 }, { target := 20, numerator := 243333267719980752427810816 }, { target := 21, numerator := 11897998894825557295366144 }, { target := 22, numerator := 243333267719980752427810816 }, { target := 23, numerator := 242949461304018637676347392 }, { target := 24, numerator := 11897998894825557295366144 }, { target := 25, numerator := 288238618387548178349031424 }, { target := 26, numerator := 11897998894825557295366144 }, { target := 37, numerator := 2086797223956170689994555392 }, { target := 38, numerator := 50554345651325296393093906432 }, { target := 39, numerator := 38302826465518100729254903808 }, { target := 40, numerator := 42678369031877813466340261888 }, { target := 41, numerator := 2086797223956170689994555392 }, { target := 42, numerator := 42678369031877813466340261888 }, { target := 43, numerator := 42611052992395356347308179456 }, { target := 44, numerator := 2086797223956170689994555392 }, { target := 45, numerator := 50554345651325296393093906432 }, { target := 46, numerator := 2086797223956170689994555392 }, { target := 219, numerator := 72818891165849929195192320 }, { target := 220, numerator := 8606725421521657535995576320 }, { target := 222, numerator := 81676108614497303474491883520 }, { target := 230, numerator := 8606731324479761123052093440 }, { target := 237, numerator := 72818891165849929195192320 }, { target := 359, numerator := 72818891165849929195192320 }, { target := 360, numerator := 8606725421521657535995576320 }, { target := 362, numerator := 81676108614497303474491883520 }, { target := 370, numerator := 8606731324479761123052093440 }, { target := 377, numerator := 72818891165849929195192320 }, { target := 392, numerator := 59322515331761072850862080 }, { target := 393, numerator := 44491886498820804638146560 }, { target := 394, numerator := 46963657970977516006932480 }, { target := 395, numerator := 60558401067839428535255040 }, { target := 396, numerator := 810741042867401328961781760 }, { target := 397, numerator := 1417560939281873969998725120 }, { target := 398, numerator := 43256000762742448953753600 }, { target := 399, numerator := 810741042867401328961781760 }, { target := 400, numerator := 45727772234899160322539520 }, { target := 401, numerator := 46963657970977516006932480 }, { target := 402, numerator := 46963657970977516006932480 }, { target := 403, numerator := 45727772234899160322539520 }, { target := 404, numerator := 1417560939281873969998725120 }, { target := 405, numerator := 45727772234899160322539520 }, { target := 406, numerator := 59322515331761072850862080 }, { target := 407, numerator := 60558401067839428535255040 }, { target := 434, numerator := 72818891165849929195192320 }, { target := 435, numerator := 8606725421521657535995576320 }, { target := 437, numerator := 81676108614497303474491883520 }, { target := 445, numerator := 8606731324479761123052093440 }, { target := 452, numerator := 72818891165849929195192320 }, { target := 469, numerator := 72818891165849929195192320 }, { target := 470, numerator := 8606725421521657535995576320 }, { target := 472, numerator := 81676108614497303474491883520 }, { target := 480, numerator := 8606731324479761123052093440 }, { target := 487, numerator := 72818891165849929195192320 }]

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
    Slot4.Left6.expected,
    Slot4.Left14.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected,
    Slot5.Left9.expected,
    Slot6.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 72818891165849929195192320 }, { target := 3, numerator := 72818891165849929195192320 }, { target := 4, numerator := 72818891165849929195192320 }, { target := 5, numerator := 72818891165849929195192320 }, { target := 61, numerator := 11897998894825557295366144 }, { target := 62, numerator := 2086797223956170689994555392 }, { target := 67, numerator := 2086797474140137189680349184 }, { target := 75, numerator := 11897748710859057609572352 }, { target := 132, numerator := 288238618387548178349031424 }, { target := 133, numerator := 50554345651325296393093906432 }, { target := 138, numerator := 50554351712233646111288459264 }, { target := 146, numerator := 288232557479198460154478592 }, { target := 153, numerator := 2086797474140137189680349184 }, { target := 154, numerator := 50554351712233646111288459264 }, { target := 155, numerator := 38302831057604453578326409216 }, { target := 156, numerator := 42678374148543450911527141376 }, { target := 157, numerator := 2086797474140137189680349184 }, { target := 158, numerator := 42678374148543450911527141376 }, { target := 159, numerator := 42611058100990543260247130112 }, { target := 160, numerator := 2086797474140137189680349184 }, { target := 161, numerator := 50554351712233646111288459264 }, { target := 162, numerator := 2086797474140137189680349184 }, { target := 177, numerator := 218385850682443293582688256 }, { target := 178, numerator := 38302826465518100729254903808 }, { target := 183, numerator := 38302831057604453578326409216 }, { target := 191, numerator := 218381258596090444511182848 }, { target := 203, numerator := 243333267719980752427810816 }, { target := 204, numerator := 42678369031877813466340261888 }, { target := 209, numerator := 42678374148543450911527141376 }, { target := 217, numerator := 243328151054343307240931328 }, { target := 272, numerator := 11897998894825557295366144 }, { target := 273, numerator := 2086797223956170689994555392 }, { target := 278, numerator := 2086797474140137189680349184 }, { target := 286, numerator := 11897748710859057609572352 }, { target := 317, numerator := 243333267719980752427810816 }, { target := 318, numerator := 42678369031877813466340261888 }, { target := 323, numerator := 42678374148543450911527141376 }, { target := 331, numerator := 243328151054343307240931328 }, { target := 343, numerator := 242949461304018637676347392 }, { target := 344, numerator := 42611052992395356347308179456 }, { target := 349, numerator := 42611058100990543260247130112 }, { target := 357, numerator := 242944352708831724737396736 }, { target := 382, numerator := 11897748710859057609572352 }, { target := 383, numerator := 288232557479198460154478592 }, { target := 384, numerator := 218381258596090444511182848 }, { target := 385, numerator := 243328151054343307240931328 }, { target := 386, numerator := 11897748710859057609572352 }, { target := 387, numerator := 243328151054343307240931328 }, { target := 388, numerator := 242944352708831724737396736 }, { target := 389, numerator := 11897748710859057609572352 }, { target := 390, numerator := 288232557479198460154478592 }, { target := 391, numerator := 11897748710859057609572352 }, { target := 392, numerator := 11897998894825557295366144 }, { target := 393, numerator := 2086797223956170689994555392 }, { target := 398, numerator := 2086797474140137189680349184 }, { target := 406, numerator := 11897748710859057609572352 }, { target := 418, numerator := 288238618387548178349031424 }, { target := 419, numerator := 50554345651325296393093906432 }, { target := 424, numerator := 50554351712233646111288459264 }, { target := 432, numerator := 288232557479198460154478592 }, { target := 453, numerator := 11897998894825557295366144 }, { target := 454, numerator := 2086797223956170689994555392 }, { target := 459, numerator := 2086797474140137189680349184 }, { target := 467, numerator := 11897748710859057609572352 }]

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
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left2.expected,
    Slot7.Left3.expected,
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
  [{ target := 8, numerator := 8606725421521657535995576320 }, { target := 9, numerator := 8606725421521657535995576320 }, { target := 10, numerator := 8606725421521657535995576320 }, { target := 11, numerator := 8606725421521657535995576320 }, { target := 17, numerator := 59007574070190629676122112 }, { target := 19, numerator := 2667034998990153915996045312 }, { target := 24, numerator := 59322515331761072850862080 }, { target := 28, numerator := 81676108614497303474491883520 }, { target := 29, numerator := 81676108614497303474491883520 }, { target := 30, numerator := 81676108614497303474491883520 }, { target := 31, numerator := 81676108614497303474491883520 }, { target := 37, numerator := 44255680552642972257091584 }, { target := 39, numerator := 2000276249242615436997033984 }, { target := 44, numerator := 44491886498820804638146560 }, { target := 51, numerator := 46714329472234248493596672 }, { target := 53, numerator := 2111402707533871850163535872 }, { target := 58, numerator := 46963657970977516006932480 }, { target := 88, numerator := 60236898529986267794374656 }, { target := 90, numerator := 2722598228135782122579296256 }, { target := 95, numerator := 60558401067839428535255040 }, { target := 108, numerator := 806436845625938605573668864 }, { target := 110, numerator := 36449478319532103518612619264 }, { target := 115, numerator := 810741042867401328961781760 }, { target := 122, numerator := 1410035155385596921635667968 }, { target := 124, numerator := 63731023830035552950988832768 }, { target := 129, numerator := 1417560939281873969998725120 }, { target := 149, numerator := 8606731324479761123052093440 }, { target := 150, numerator := 8606731324479761123052093440 }, { target := 151, numerator := 8606731324479761123052093440 }, { target := 152, numerator := 8606731324479761123052093440 }, { target := 153, numerator := 43026356092847334138839040 }, { target := 155, numerator := 1944713020096987230413783040 }, { target := 160, numerator := 43256000762742448953753600 }, { target := 167, numerator := 806436845625938605573668864 }, { target := 169, numerator := 36449478319532103518612619264 }, { target := 174, numerator := 810741042867401328961781760 }, { target := 193, numerator := 45485005012438610375344128 }, { target := 195, numerator := 2055839478388243643580284928 }, { target := 200, numerator := 45727772234899160322539520 }, { target := 248, numerator := 46714329472234248493596672 }, { target := 250, numerator := 2111402707533871850163535872 }, { target := 255, numerator := 46963657970977516006932480 }, { target := 262, numerator := 46714329472234248493596672 }, { target := 264, numerator := 2111402707533871850163535872 }, { target := 269, numerator := 46963657970977516006932480 }, { target := 293, numerator := 45485005012438610375344128 }, { target := 295, numerator := 2055839478388243643580284928 }, { target := 300, numerator := 45727772234899160322539520 }, { target := 307, numerator := 1410035155385596921635667968 }, { target := 309, numerator := 63731023830035552950988832768 }, { target := 314, numerator := 1417560939281873969998725120 }, { target := 333, numerator := 45485005012438610375344128 }, { target := 335, numerator := 2055839478388243643580284928 }, { target := 340, numerator := 45727772234899160322539520 }, { target := 378, numerator := 72818891165849929195192320 }, { target := 379, numerator := 72818891165849929195192320 }, { target := 380, numerator := 72818891165849929195192320 }, { target := 381, numerator := 72818891165849929195192320 }, { target := 382, numerator := 59007574070190629676122112 }, { target := 384, numerator := 2667034998990153915996045312 }, { target := 389, numerator := 59322515331761072850862080 }, { target := 408, numerator := 60236898529986267794374656 }, { target := 410, numerator := 2722598228135782122579296256 }, { target := 415, numerator := 60558401067839428535255040 }]

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
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
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
    Slot9.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 2970656582080461887772819456 }, { target := 2, numerator := 29127556466339971678076928 }, { target := 3, numerator := 29042553869648318064230400 }, { target := 4, numerator := 28844214477367792965255168 }, { target := 5, numerator := 29042553869648318064230400 }, { target := 6, numerator := 115871601356415493111478747136 }, { target := 8, numerator := 436913346995099575171153920 }, { target := 9, numerator := 435638308044724770963456000 }, { target := 10, numerator := 432663217160516894478827520 }, { target := 11, numerator := 435638308044724770963456000 }, { target := 13, numerator := 767025653613619254189359104 }, { target := 14, numerator := 764787251900739042358067200 }, { target := 15, numerator := 759564314570685214751719424 }, { target := 16, numerator := 764787251900739042358067200 }, { target := 27, numerator := 115871558855117147284671823872 }, { target := 28, numerator := 29127556466339971678076928 }, { target := 29, numerator := 29042553869648318064230400 }, { target := 30, numerator := 28844214477367792965255168 }, { target := 31, numerator := 29042553869648318064230400 }, { target := 33, numerator := 485459274438999527967948800 }, { target := 34, numerator := 484042564494138634403840000 }, { target := 35, numerator := 480736907956129882754252800 }, { target := 36, numerator := 484042564494138634403840000 }, { target := 47, numerator := 29127556466339971678076928 }, { target := 48, numerator := 29042553869648318064230400 }, { target := 49, numerator := 28844214477367792965255168 }, { target := 50, numerator := 29042553869648318064230400 }, { target := 79, numerator := 767025653613619254189359104 }, { target := 80, numerator := 764787251900739042358067200 }, { target := 81, numerator := 759564314570685214751719424 }, { target := 82, numerator := 764787251900739042358067200 }, { target := 84, numerator := 762171060869229258909679616 }, { target := 85, numerator := 759946826255797656014028800 }, { target := 86, numerator := 754756945491123915924176896 }, { target := 87, numerator := 759946826255797656014028800 }, { target := 99, numerator := 485459274438999527967948800 }, { target := 100, numerator := 484042564494138634403840000 }, { target := 101, numerator := 480736907956129882754252800 }, { target := 102, numerator := 484042564494138634403840000 }, { target := 104, numerator := 11762678219656958562663399424 }, { target := 105, numerator := 11728351337692979111605043200 }, { target := 106, numerator := 11648255279777027059135545344 }, { target := 107, numerator := 11728351337692979111605043200 }, { target := 118, numerator := 752461875380449268350320640 }, { target := 119, numerator := 750265974965914883325952000 }, { target := 120, numerator := 745142207332001318269091840 }, { target := 121, numerator := 750265974965914883325952000 }, { target := 148, numerator := 2970670749179910496708460544 }, { target := 149, numerator := 436913346995099575171153920 }, { target := 150, numerator := 435638308044724770963456000 }, { target := 151, numerator := 432663217160516894478827520 }, { target := 152, numerator := 435638308044724770963456000 }, { target := 163, numerator := 767025653613619254189359104 }, { target := 164, numerator := 764787251900739042358067200 }, { target := 165, numerator := 759564314570685214751719424 }, { target := 166, numerator := 764787251900739042358067200 }, { target := 239, numerator := 29127556466339971678076928 }, { target := 240, numerator := 29042553869648318064230400 }, { target := 241, numerator := 28844214477367792965255168 }, { target := 242, numerator := 29042553869648318064230400 }, { target := 244, numerator := 752461875380449268350320640 }, { target := 245, numerator := 750265974965914883325952000 }, { target := 246, numerator := 745142207332001318269091840 }, { target := 247, numerator := 750265974965914883325952000 }]

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
    Slot9.Left15.expected,
    Slot9.Left16.expected,
    Slot9.Left17.expected,
    Slot9.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 258, numerator := 29127556466339971678076928 }, { target := 259, numerator := 29042553869648318064230400 }, { target := 260, numerator := 28844214477367792965255168 }, { target := 261, numerator := 29042553869648318064230400 }, { target := 289, numerator := 767025653613619254189359104 }, { target := 290, numerator := 764787251900739042358067200 }, { target := 291, numerator := 759564314570685214751719424 }, { target := 292, numerator := 764787251900739042358067200 }, { target := 303, numerator := 767025653613619254189359104 }, { target := 304, numerator := 764787251900739042358067200 }, { target := 305, numerator := 759564314570685214751719424 }, { target := 306, numerator := 764787251900739042358067200 }, { target := 378, numerator := 29127556466339971678076928 }, { target := 379, numerator := 29042553869648318064230400 }, { target := 380, numerator := 28844214477367792965255168 }, { target := 381, numerator := 29042553869648318064230400 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent3
