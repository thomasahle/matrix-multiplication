import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk2Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 10; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2.Parent1

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
    Slot0.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 29014219670751100192948224 }, { target := 3, numerator := 29014219670751100192948224 }, { target := 4, numerator := 29014219670751100192948224 }, { target := 5, numerator := 29014219670751100192948224 }, { target := 8, numerator := 420706185225890952797749248 }, { target := 9, numerator := 420706185225890952797749248 }, { target := 10, numerator := 420706185225890952797749248 }, { target := 11, numerator := 420706185225890952797749248 }, { target := 13, numerator := 744698304882611571619004416 }, { target := 14, numerator := 744698304882611571619004416 }, { target := 15, numerator := 744698304882611571619004416 }, { target := 16, numerator := 744698304882611571619004416 }, { target := 28, numerator := 24178516392292583494123520 }, { target := 29, numerator := 24178516392292583494123520 }, { target := 30, numerator := 24178516392292583494123520 }, { target := 31, numerator := 24178516392292583494123520 }, { target := 33, numerator := 464227514732017603087171584 }, { target := 34, numerator := 464227514732017603087171584 }, { target := 35, numerator := 464227514732017603087171584 }, { target := 36, numerator := 464227514732017603087171584 }, { target := 47, numerator := 24178516392292583494123520 }, { target := 48, numerator := 24178516392292583494123520 }, { target := 49, numerator := 24178516392292583494123520 }, { target := 50, numerator := 24178516392292583494123520 }, { target := 79, numerator := 739862601604153054920179712 }, { target := 80, numerator := 739862601604153054920179712 }, { target := 81, numerator := 739862601604153054920179712 }, { target := 82, numerator := 739862601604153054920179712 }, { target := 84, numerator := 773712524553362671811952640 }, { target := 85, numerator := 773712524553362671811952640 }, { target := 86, numerator := 773712524553362671811952640 }, { target := 87, numerator := 773712524553362671811952640 }, { target := 99, numerator := 464227514732017603087171584 }, { target := 100, numerator := 464227514732017603087171584 }, { target := 101, numerator := 464227514732017603087171584 }, { target := 102, numerator := 464227514732017603087171584 }, { target := 104, numerator := 11852308735501824428819349504 }, { target := 105, numerator := 11852308735501824428819349504 }, { target := 106, numerator := 11852308735501824428819349504 }, { target := 107, numerator := 11852308735501824428819349504 }, { target := 118, numerator := 759205414717987121715478528 }, { target := 119, numerator := 759205414717987121715478528 }, { target := 120, numerator := 759205414717987121715478528 }, { target := 121, numerator := 759205414717987121715478528 }, { target := 149, numerator := 420706185225890952797749248 }, { target := 150, numerator := 420706185225890952797749248 }, { target := 151, numerator := 420706185225890952797749248 }, { target := 152, numerator := 420706185225890952797749248 }, { target := 163, numerator := 739862601604153054920179712 }, { target := 164, numerator := 739862601604153054920179712 }, { target := 165, numerator := 739862601604153054920179712 }, { target := 166, numerator := 739862601604153054920179712 }, { target := 239, numerator := 24178516392292583494123520 }, { target := 240, numerator := 24178516392292583494123520 }, { target := 241, numerator := 24178516392292583494123520 }, { target := 242, numerator := 24178516392292583494123520 }, { target := 244, numerator := 759205414717987121715478528 }, { target := 245, numerator := 759205414717987121715478528 }, { target := 246, numerator := 759205414717987121715478528 }, { target := 247, numerator := 759205414717987121715478528 }, { target := 258, numerator := 24178516392292583494123520 }, { target := 259, numerator := 24178516392292583494123520 }, { target := 260, numerator := 24178516392292583494123520 }, { target := 261, numerator := 24178516392292583494123520 }]

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
    Slot2.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 17, numerator := 57778249610394991557869568 }, { target := 19, numerator := 2611471769844525709412794368 }, { target := 24, numerator := 58086629595682717166469120 }, { target := 37, numerator := 43026356092847334138839040 }, { target := 39, numerator := 1944713020096987230413783040 }, { target := 44, numerator := 43256000762742448953753600 }, { target := 51, numerator := 45485005012438610375344128 }, { target := 53, numerator := 2055839478388243643580284928 }, { target := 58, numerator := 45727772234899160322539520 }, { target := 61, numerator := 9024421596176809080127488 }, { target := 62, numerator := 1789857197990391402882662400 }, { target := 67, numerator := 1789857197990391402882662400 }, { target := 75, numerator := 9024421596176809080127488 }, { target := 88, numerator := 59007574070190629676122112 }, { target := 90, numerator := 2667034998990153915996045312 }, { target := 95, numerator := 59322515331761072850862080 }, { target := 108, numerator := 790455627648595310036385792 }, { target := 110, numerator := 35727156340638936833030356992 }, { target := 115, numerator := 794674528298382705064673280 }, { target := 122, numerator := 1429704346742327131527708672 }, { target := 124, numerator := 64620035496365604256320847872 }, { target := 129, numerator := 1437335111059127660949012480 }, { target := 153, numerator := 43026356092847334138839040 }, { target := 155, numerator := 1944713020096987230413783040 }, { target := 160, numerator := 43256000762742448953753600 }, { target := 167, numerator := 790455627648595310036385792 }, { target := 169, numerator := 35727156340638936833030356992 }, { target := 174, numerator := 794674528298382705064673280 }, { target := 193, numerator := 46714329472234248493596672 }, { target := 195, numerator := 2111402707533871850163535872 }, { target := 200, numerator := 46963657970977516006932480 }, { target := 248, numerator := 46714329472234248493596672 }, { target := 250, numerator := 2111402707533871850163535872 }, { target := 255, numerator := 46963657970977516006932480 }, { target := 262, numerator := 45485005012438610375344128 }, { target := 264, numerator := 2055839478388243643580284928 }, { target := 269, numerator := 45727772234899160322539520 }, { target := 289, numerator := 739862601604153054920179712 }, { target := 290, numerator := 739862601604153054920179712 }, { target := 291, numerator := 739862601604153054920179712 }, { target := 292, numerator := 739862601604153054920179712 }, { target := 293, numerator := 45485005012438610375344128 }, { target := 295, numerator := 2055839478388243643580284928 }, { target := 300, numerator := 45727772234899160322539520 }, { target := 303, numerator := 773712524553362671811952640 }, { target := 304, numerator := 773712524553362671811952640 }, { target := 305, numerator := 773712524553362671811952640 }, { target := 306, numerator := 773712524553362671811952640 }, { target := 307, numerator := 1429704346742327131527708672 }, { target := 309, numerator := 64620035496365604256320847872 }, { target := 314, numerator := 1437335111059127660949012480 }, { target := 333, numerator := 45485005012438610375344128 }, { target := 335, numerator := 2055839478388243643580284928 }, { target := 340, numerator := 45727772234899160322539520 }, { target := 378, numerator := 29014219670751100192948224 }, { target := 379, numerator := 29014219670751100192948224 }, { target := 380, numerator := 29014219670751100192948224 }, { target := 381, numerator := 29014219670751100192948224 }, { target := 382, numerator := 57778249610394991557869568 }, { target := 384, numerator := 2611471769844525709412794368 }, { target := 389, numerator := 58086629595682717166469120 }, { target := 408, numerator := 59007574070190629676122112 }, { target := 410, numerator := 2667034998990153915996045312 }, { target := 415, numerator := 59322515331761072850862080 }]

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
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
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
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 2900019424229697734666354688 }, { target := 6, numerator := 115942238514266257264585211904 }, { target := 27, numerator := 115942210180067360046713929728 }, { target := 132, numerator := 221243884293366932286996480 }, { target := 133, numerator := 43880370015248305360994304000 }, { target := 138, numerator := 43880370015248305360994304000 }, { target := 146, numerator := 221243884293366932286996480 }, { target := 148, numerator := 2900019424229697734666354688 }, { target := 177, numerator := 163604030227463442033278976 }, { target := 178, numerator := 32448378879696773174840524800 }, { target := 183, numerator := 32448378879696773174840524800 }, { target := 191, numerator := 163604030227463442033278976 }, { target := 203, numerator := 182526204542027719136772096 }, { target := 204, numerator := 36201305262579851922820300800 }, { target := 209, numerator := 36201305262579851922820300800 }, { target := 217, numerator := 182526204542027719136772096 }, { target := 219, numerator := 49292605527143531172331520 }, { target := 220, numerator := 8078108698050129352353382400 }, { target := 222, numerator := 83167256797952557560784486400 }, { target := 230, numerator := 8078108698050129352353382400 }, { target := 237, numerator := 49292605527143531172331520 }, { target := 272, numerator := 9024421596176809080127488 }, { target := 273, numerator := 1789857197990391402882662400 }, { target := 278, numerator := 1789857197990391402882662400 }, { target := 286, numerator := 9024421596176809080127488 }, { target := 317, numerator := 182235094167957499489026048 }, { target := 318, numerator := 36143567933612419942082150400 }, { target := 323, numerator := 36143567933612419942082150400 }, { target := 331, numerator := 182235094167957499489026048 }, { target := 343, numerator := 185437308282729915614232576 }, { target := 344, numerator := 36778678552254171730201804800 }, { target := 349, numerator := 36778678552254171730201804800 }, { target := 357, numerator := 185437308282729915614232576 }, { target := 359, numerator := 49148755511013734875136000 }, { target := 360, numerator := 8054534450876831309496320000 }, { target := 362, numerator := 82924550795623902237163520000 }, { target := 370, numerator := 8054534450876831309496320000 }, { target := 377, numerator := 49148755511013734875136000 }, { target := 392, numerator := 9024421596176809080127488 }, { target := 393, numerator := 1789857197990391402882662400 }, { target := 398, numerator := 1789857197990391402882662400 }, { target := 406, numerator := 9024421596176809080127488 }, { target := 418, numerator := 221243884293366932286996480 }, { target := 419, numerator := 43880370015248305360994304000 }, { target := 424, numerator := 43880370015248305360994304000 }, { target := 432, numerator := 221243884293366932286996480 }, { target := 434, numerator := 48813105473377543515013120 }, { target := 435, numerator := 7999527874139135876163174400 }, { target := 437, numerator := 82358236790190373148714598400 }, { target := 445, numerator := 7999527874139135876163174400 }, { target := 452, numerator := 48813105473377543515013120 }, { target := 453, numerator := 9024421596176809080127488 }, { target := 454, numerator := 1789857197990391402882662400 }, { target := 459, numerator := 1789857197990391402882662400 }, { target := 467, numerator := 9024421596176809080127488 }, { target := 469, numerator := 49148755511013734875136000 }, { target := 470, numerator := 8054534450876831309496320000 }, { target := 472, numerator := 82924550795623902237163520000 }, { target := 480, numerator := 8054534450876831309496320000 }, { target := 487, numerator := 49148755511013734875136000 }, { target := 488, numerator := 2900019424229697734666354688 }, { target := 490, numerator := 115942238514266257264585211904 }, { target := 493, numerator := 115942210180067360046713929728 }, { target := 500, numerator := 2900019424229697734666354688 }]

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
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 49292605527143531172331520 }, { target := 3, numerator := 49148755511013734875136000 }, { target := 4, numerator := 48813105473377543515013120 }, { target := 5, numerator := 49148755511013734875136000 }, { target := 8, numerator := 8078108698050129352353382400 }, { target := 9, numerator := 8054534450876831309496320000 }, { target := 10, numerator := 7999527874139135876163174400 }, { target := 11, numerator := 8054534450876831309496320000 }, { target := 17, numerator := 9024421596176809080127488 }, { target := 18, numerator := 221243884293366932286996480 }, { target := 19, numerator := 163604030227463442033278976 }, { target := 20, numerator := 182526204542027719136772096 }, { target := 21, numerator := 9024421596176809080127488 }, { target := 22, numerator := 182235094167957499489026048 }, { target := 23, numerator := 185437308282729915614232576 }, { target := 24, numerator := 9024421596176809080127488 }, { target := 25, numerator := 221243884293366932286996480 }, { target := 26, numerator := 9024421596176809080127488 }, { target := 28, numerator := 83167256797952557560784486400 }, { target := 29, numerator := 82924550795623902237163520000 }, { target := 30, numerator := 82358236790190373148714598400 }, { target := 31, numerator := 82924550795623902237163520000 }, { target := 37, numerator := 1789857197990391402882662400 }, { target := 38, numerator := 43880370015248305360994304000 }, { target := 39, numerator := 32448378879696773174840524800 }, { target := 40, numerator := 36201305262579851922820300800 }, { target := 41, numerator := 1789857197990391402882662400 }, { target := 42, numerator := 36143567933612419942082150400 }, { target := 43, numerator := 36778678552254171730201804800 }, { target := 44, numerator := 1789857197990391402882662400 }, { target := 45, numerator := 43880370015248305360994304000 }, { target := 46, numerator := 1789857197990391402882662400 }, { target := 149, numerator := 8078108698050129352353382400 }, { target := 150, numerator := 8054534450876831309496320000 }, { target := 151, numerator := 7999527874139135876163174400 }, { target := 152, numerator := 8054534450876831309496320000 }, { target := 153, numerator := 1789857197990391402882662400 }, { target := 154, numerator := 43880370015248305360994304000 }, { target := 155, numerator := 32448378879696773174840524800 }, { target := 156, numerator := 36201305262579851922820300800 }, { target := 157, numerator := 1789857197990391402882662400 }, { target := 158, numerator := 36143567933612419942082150400 }, { target := 159, numerator := 36778678552254171730201804800 }, { target := 160, numerator := 1789857197990391402882662400 }, { target := 161, numerator := 43880370015248305360994304000 }, { target := 162, numerator := 1789857197990391402882662400 }, { target := 378, numerator := 49292605527143531172331520 }, { target := 379, numerator := 49148755511013734875136000 }, { target := 380, numerator := 48813105473377543515013120 }, { target := 381, numerator := 49148755511013734875136000 }, { target := 382, numerator := 9024421596176809080127488 }, { target := 383, numerator := 221243884293366932286996480 }, { target := 384, numerator := 163604030227463442033278976 }, { target := 385, numerator := 182526204542027719136772096 }, { target := 386, numerator := 9024421596176809080127488 }, { target := 387, numerator := 182235094167957499489026048 }, { target := 388, numerator := 185437308282729915614232576 }, { target := 389, numerator := 9024421596176809080127488 }, { target := 390, numerator := 221243884293366932286996480 }, { target := 391, numerator := 9024421596176809080127488 }]

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
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 61, numerator := 57778249610394991557869568 }, { target := 62, numerator := 43026356092847334138839040 }, { target := 63, numerator := 45485005012438610375344128 }, { target := 64, numerator := 59007574070190629676122112 }, { target := 65, numerator := 790455627648595310036385792 }, { target := 66, numerator := 1429704346742327131527708672 }, { target := 67, numerator := 43026356092847334138839040 }, { target := 68, numerator := 790455627648595310036385792 }, { target := 69, numerator := 46714329472234248493596672 }, { target := 70, numerator := 46714329472234248493596672 }, { target := 71, numerator := 45485005012438610375344128 }, { target := 72, numerator := 45485005012438610375344128 }, { target := 73, numerator := 1429704346742327131527708672 }, { target := 74, numerator := 45485005012438610375344128 }, { target := 75, numerator := 57778249610394991557869568 }, { target := 76, numerator := 59007574070190629676122112 }, { target := 177, numerator := 2611471769844525709412794368 }, { target := 178, numerator := 1944713020096987230413783040 }, { target := 179, numerator := 2055839478388243643580284928 }, { target := 180, numerator := 2667034998990153915996045312 }, { target := 181, numerator := 35727156340638936833030356992 }, { target := 182, numerator := 64620035496365604256320847872 }, { target := 183, numerator := 1944713020096987230413783040 }, { target := 184, numerator := 35727156340638936833030356992 }, { target := 185, numerator := 2111402707533871850163535872 }, { target := 186, numerator := 2111402707533871850163535872 }, { target := 187, numerator := 2055839478388243643580284928 }, { target := 188, numerator := 2055839478388243643580284928 }, { target := 189, numerator := 64620035496365604256320847872 }, { target := 190, numerator := 2055839478388243643580284928 }, { target := 191, numerator := 2611471769844525709412794368 }, { target := 192, numerator := 2667034998990153915996045312 }, { target := 392, numerator := 58086629595682717166469120 }, { target := 393, numerator := 43256000762742448953753600 }, { target := 394, numerator := 45727772234899160322539520 }, { target := 395, numerator := 59322515331761072850862080 }, { target := 396, numerator := 794674528298382705064673280 }, { target := 397, numerator := 1437335111059127660949012480 }, { target := 398, numerator := 43256000762742448953753600 }, { target := 399, numerator := 794674528298382705064673280 }, { target := 400, numerator := 46963657970977516006932480 }, { target := 401, numerator := 46963657970977516006932480 }, { target := 402, numerator := 45727772234899160322539520 }, { target := 403, numerator := 45727772234899160322539520 }, { target := 404, numerator := 1437335111059127660949012480 }, { target := 405, numerator := 45727772234899160322539520 }, { target := 406, numerator := 58086629595682717166469120 }, { target := 407, numerator := 59322515331761072850862080 }]

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
    Slot9.Left1.expected,
    Slot9.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 219, numerator := 29014219670751100192948224 }, { target := 220, numerator := 420706185225890952797749248 }, { target := 221, numerator := 744698304882611571619004416 }, { target := 222, numerator := 24178516392292583494123520 }, { target := 223, numerator := 464227514732017603087171584 }, { target := 224, numerator := 24178516392292583494123520 }, { target := 225, numerator := 739862601604153054920179712 }, { target := 226, numerator := 773712524553362671811952640 }, { target := 227, numerator := 464227514732017603087171584 }, { target := 228, numerator := 11852308735501824428819349504 }, { target := 229, numerator := 759205414717987121715478528 }, { target := 230, numerator := 420706185225890952797749248 }, { target := 231, numerator := 739862601604153054920179712 }, { target := 232, numerator := 24178516392292583494123520 }, { target := 233, numerator := 759205414717987121715478528 }, { target := 234, numerator := 24178516392292583494123520 }, { target := 235, numerator := 739862601604153054920179712 }, { target := 236, numerator := 773712524553362671811952640 }, { target := 237, numerator := 29014219670751100192948224 }, { target := 359, numerator := 29014219670751100192948224 }, { target := 360, numerator := 420706185225890952797749248 }, { target := 361, numerator := 744698304882611571619004416 }, { target := 362, numerator := 24178516392292583494123520 }, { target := 363, numerator := 464227514732017603087171584 }, { target := 364, numerator := 24178516392292583494123520 }, { target := 365, numerator := 739862601604153054920179712 }, { target := 366, numerator := 773712524553362671811952640 }, { target := 367, numerator := 464227514732017603087171584 }, { target := 368, numerator := 11852308735501824428819349504 }, { target := 369, numerator := 759205414717987121715478528 }, { target := 370, numerator := 420706185225890952797749248 }, { target := 371, numerator := 739862601604153054920179712 }, { target := 372, numerator := 24178516392292583494123520 }, { target := 373, numerator := 759205414717987121715478528 }, { target := 374, numerator := 24178516392292583494123520 }, { target := 375, numerator := 739862601604153054920179712 }, { target := 376, numerator := 773712524553362671811952640 }, { target := 377, numerator := 29014219670751100192948224 }, { target := 434, numerator := 29014219670751100192948224 }, { target := 435, numerator := 420706185225890952797749248 }, { target := 436, numerator := 744698304882611571619004416 }, { target := 437, numerator := 24178516392292583494123520 }, { target := 438, numerator := 464227514732017603087171584 }, { target := 439, numerator := 24178516392292583494123520 }, { target := 440, numerator := 739862601604153054920179712 }, { target := 441, numerator := 773712524553362671811952640 }, { target := 442, numerator := 464227514732017603087171584 }, { target := 443, numerator := 11852308735501824428819349504 }, { target := 444, numerator := 759205414717987121715478528 }, { target := 445, numerator := 420706185225890952797749248 }, { target := 446, numerator := 739862601604153054920179712 }, { target := 447, numerator := 24178516392292583494123520 }, { target := 448, numerator := 759205414717987121715478528 }, { target := 449, numerator := 24178516392292583494123520 }, { target := 450, numerator := 739862601604153054920179712 }, { target := 451, numerator := 773712524553362671811952640 }, { target := 452, numerator := 29014219670751100192948224 }]

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
    Slot9.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 469, numerator := 29014219670751100192948224 }, { target := 470, numerator := 420706185225890952797749248 }, { target := 471, numerator := 744698304882611571619004416 }, { target := 472, numerator := 24178516392292583494123520 }, { target := 473, numerator := 464227514732017603087171584 }, { target := 474, numerator := 24178516392292583494123520 }, { target := 475, numerator := 739862601604153054920179712 }, { target := 476, numerator := 773712524553362671811952640 }, { target := 477, numerator := 464227514732017603087171584 }, { target := 478, numerator := 11852308735501824428819349504 }, { target := 479, numerator := 759205414717987121715478528 }, { target := 480, numerator := 420706185225890952797749248 }, { target := 481, numerator := 739862601604153054920179712 }, { target := 482, numerator := 24178516392292583494123520 }, { target := 483, numerator := 759205414717987121715478528 }, { target := 484, numerator := 24178516392292583494123520 }, { target := 485, numerator := 739862601604153054920179712 }, { target := 486, numerator := 773712524553362671811952640 }, { target := 487, numerator := 29014219670751100192948224 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2.Parent1
