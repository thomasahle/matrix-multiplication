import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk0Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 20; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk0.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
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
    Slot3.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 4860774709497697193164800 }, { target := 112, numerator := 169224460304660572271542272 }, { target := 115, numerator := 169224647077944318580752384 }, { target := 122, numerator := 4860753956910614269919232 }, { target := 206, numerator := 36995896400065806414643200 }, { target := 208, numerator := 1287986170096583244511182848 }, { target := 211, numerator := 1287987591648798424753504256 }, { target := 218, numerator := 36995738449819675276607488 }, { target := 241, numerator := 36995896400065806414643200 }, { target := 243, numerator := 1287986170096583244511182848 }, { target := 246, numerator := 1287987591648798424753504256 }, { target := 253, numerator := 36995738449819675276607488 }, { target := 302, numerator := 5130817748914235926118400 }, { target := 304, numerator := 178625819210475048508850176 }, { target := 307, numerator := 178626016360052336279683072 }, { target := 314, numerator := 5130795843405648396025856 }, { target := 337, numerator := 32945250808817725420339200 }, { target := 339, numerator := 1146965786509366100951564288 }, { target := 342, numerator := 1146967052417178159269543936 }, { target := 349, numerator := 32945110152394163385008128 }, { target := 363, numerator := 5130817748914235926118400 }, { target := 365, numerator := 178625819210475048508850176 }, { target := 368, numerator := 178626016360052336279683072 }, { target := 375, numerator := 5130795843405648396025856 }, { target := 473, numerator := 36725853360649267681689600 }, { target := 475, numerator := 1278584811190768768273874944 }, { target := 478, numerator := 1278586222366690407054573568 }, { target := 485, numerator := 36725696563324641150500864 }, { target := 508, numerator := 36725853360649267681689600 }, { target := 510, numerator := 1278584811190768768273874944 }, { target := 513, numerator := 1278586222366690407054573568 }, { target := 520, numerator := 36725696563324641150500864 }, { target := 569, numerator := 32945250808817725420339200 }, { target := 571, numerator := 1146965786509366100951564288 }, { target := 574, numerator := 1146967052417178159269543936 }, { target := 581, numerator := 32945110152394163385008128 }, { target := 604, numerator := 649453509796775652753408000 }, { target := 606, numerator := 22610268168483815350725509120 }, { target := 609, numerator := 22610293123469782565928304640 }, { target := 616, numerator := 649450737020557073286430720 }, { target := 630, numerator := 32945250808817725420339200 }, { target := 632, numerator := 1146965786509366100951564288 }, { target := 635, numerator := 1146967052417178159269543936 }, { target := 642, numerator := 32945110152394163385008128 }, { target := 679, numerator := 36995896400065806414643200 }, { target := 681, numerator := 1287986170096583244511182848 }, { target := 684, numerator := 1287987591648798424753504256 }, { target := 691, numerator := 36995738449819675276607488 }, { target := 705, numerator := 36725853360649267681689600 }, { target := 707, numerator := 1278584811190768768273874944 }, { target := 710, numerator := 1278586222366690407054573568 }, { target := 717, numerator := 36725696563324641150500864 }, { target := 785, numerator := 5130817748914235926118400 }, { target := 787, numerator := 178625819210475048508850176 }, { target := 790, numerator := 178626016360052336279683072 }, { target := 797, numerator := 5130795843405648396025856 }, { target := 820, numerator := 32945250808817725420339200 }, { target := 822, numerator := 1146965786509366100951564288 }, { target := 825, numerator := 1146967052417178159269543936 }, { target := 832, numerator := 32945110152394163385008128 }, { target := 846, numerator := 5130817748914235926118400 }, { target := 848, numerator := 178625819210475048508850176 }, { target := 851, numerator := 178626016360052336279683072 }, { target := 858, numerator := 5130795843405648396025856 }]

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
    Slot3.Left16.expected,
    Slot3.Left17.expected,
    Slot3.Left18.expected,
    Slot10.Left0.expected,
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
  [{ target := 56, numerator := 3711046255900755991986176 }, { target := 57, numerator := 115023602859538825749725184 }, { target := 59, numerator := 1350132320112968535990337536 }, { target := 67, numerator := 115024454516124059367899136 }, { target := 74, numerator := 3711519398448108002082816 }, { target := 110, numerator := 3711046255900755991986176 }, { target := 112, numerator := 181485845562339857088380928 }, { target := 115, numerator := 181485911793964827059159040 }, { target := 122, numerator := 3711289105192312551505920 }, { target := 152, numerator := 181485845562339857088380928 }, { target := 153, numerator := 5625140293360018405460017152 }, { target := 155, numerator := 66027176391869422114342699008 }, { target := 163, numerator := 5625181942966313151583223808 }, { target := 170, numerator := 181508984232503604934606848 }, { target := 206, numerator := 115023602859538825749725184 }, { target := 208, numerator := 5625140293360018405460017152 }, { target := 211, numerator := 5625142346204311352361615360 }, { target := 218, numerator := 115031129955279631055585280 }, { target := 283, numerator := 181485911793964827059159040 }, { target := 284, numerator := 5625142346204311352361615360 }, { target := 286, numerator := 66027200487892839600425533440 }, { target := 294, numerator := 5625183995825805747227197440 }, { target := 301, numerator := 181509050472572824206704640 }, { target := 302, numerator := 1350132320112968535990337536 }, { target := 304, numerator := 66027176391869422114342699008 }, { target := 307, numerator := 66027200487892839600425533440 }, { target := 314, numerator := 1350220672198832651627397120 }, { target := 660, numerator := 3711289105192312551505920 }, { target := 661, numerator := 115031129955279631055585280 }, { target := 663, numerator := 1350220672198832651627397120 }, { target := 671, numerator := 115031981667596910062469120 }, { target := 678, numerator := 3711762278701911999774720 }, { target := 679, numerator := 115024454516124059367899136 }, { target := 681, numerator := 5625181942966313151583223808 }, { target := 684, numerator := 5625183995825805747227197440 }, { target := 691, numerator := 115031981667596910062469120 }, { target := 895, numerator := 36995896400065806414643200 }, { target := 897, numerator := 1287986170096583244511182848 }, { target := 900, numerator := 1287987591648798424753504256 }, { target := 907, numerator := 36995738449819675276607488 }, { target := 921, numerator := 36725853360649267681689600 }, { target := 923, numerator := 1278584811190768768273874944 }, { target := 926, numerator := 1278586222366690407054573568 }, { target := 933, numerator := 36725696563324641150500864 }, { target := 966, numerator := 8302251068529266462294016 }, { target := 968, numerator := 341332085631349700968841216 }, { target := 971, numerator := 341332328268409125088526336 }, { target := 978, numerator := 8302474349117492143587328 }]

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
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 4860774709497697193164800 }, { target := 57, numerator := 36995896400065806414643200 }, { target := 58, numerator := 36995896400065806414643200 }, { target := 59, numerator := 5130817748914235926118400 }, { target := 60, numerator := 32945250808817725420339200 }, { target := 61, numerator := 5130817748914235926118400 }, { target := 62, numerator := 36725853360649267681689600 }, { target := 63, numerator := 36725853360649267681689600 }, { target := 64, numerator := 32945250808817725420339200 }, { target := 65, numerator := 649453509796775652753408000 }, { target := 66, numerator := 32945250808817725420339200 }, { target := 67, numerator := 36995896400065806414643200 }, { target := 68, numerator := 36725853360649267681689600 }, { target := 69, numerator := 5130817748914235926118400 }, { target := 70, numerator := 32945250808817725420339200 }, { target := 71, numerator := 5130817748914235926118400 }, { target := 72, numerator := 36995896400065806414643200 }, { target := 73, numerator := 36725853360649267681689600 }, { target := 74, numerator := 4590731670081158460211200 }, { target := 152, numerator := 169224460304660572271542272 }, { target := 153, numerator := 1287986170096583244511182848 }, { target := 154, numerator := 1287986170096583244511182848 }, { target := 155, numerator := 178625819210475048508850176 }, { target := 156, numerator := 1146965786509366100951564288 }, { target := 157, numerator := 178625819210475048508850176 }, { target := 158, numerator := 1278584811190768768273874944 }, { target := 159, numerator := 1278584811190768768273874944 }, { target := 160, numerator := 1146965786509366100951564288 }, { target := 161, numerator := 22610268168483815350725509120 }, { target := 162, numerator := 1146965786509366100951564288 }, { target := 163, numerator := 1287986170096583244511182848 }, { target := 164, numerator := 1278584811190768768273874944 }, { target := 165, numerator := 178625819210475048508850176 }, { target := 166, numerator := 1146965786509366100951564288 }, { target := 167, numerator := 178625819210475048508850176 }, { target := 168, numerator := 1287986170096583244511182848 }, { target := 169, numerator := 1278584811190768768273874944 }, { target := 170, numerator := 159823101398846096034234368 }, { target := 283, numerator := 169224647077944318580752384 }, { target := 284, numerator := 1287987591648798424753504256 }, { target := 285, numerator := 1287987591648798424753504256 }, { target := 286, numerator := 178626016360052336279683072 }, { target := 287, numerator := 1146967052417178159269543936 }, { target := 288, numerator := 178626016360052336279683072 }, { target := 289, numerator := 1278586222366690407054573568 }, { target := 290, numerator := 1278586222366690407054573568 }, { target := 291, numerator := 1146967052417178159269543936 }, { target := 292, numerator := 22610293123469782565928304640 }, { target := 293, numerator := 1146967052417178159269543936 }, { target := 294, numerator := 1287987591648798424753504256 }, { target := 295, numerator := 1278586222366690407054573568 }, { target := 296, numerator := 178626016360052336279683072 }, { target := 297, numerator := 1146967052417178159269543936 }, { target := 298, numerator := 178626016360052336279683072 }, { target := 299, numerator := 1287987591648798424753504256 }, { target := 300, numerator := 1278586222366690407054573568 }, { target := 301, numerator := 159823277795836300881821696 }]

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
    Slot18.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 660, numerator := 4860753956910614269919232 }, { target := 661, numerator := 36995738449819675276607488 }, { target := 662, numerator := 36995738449819675276607488 }, { target := 663, numerator := 5130795843405648396025856 }, { target := 664, numerator := 32945110152394163385008128 }, { target := 665, numerator := 5130795843405648396025856 }, { target := 666, numerator := 36725696563324641150500864 }, { target := 667, numerator := 36725696563324641150500864 }, { target := 668, numerator := 32945110152394163385008128 }, { target := 669, numerator := 649450737020557073286430720 }, { target := 670, numerator := 32945110152394163385008128 }, { target := 671, numerator := 36995738449819675276607488 }, { target := 672, numerator := 36725696563324641150500864 }, { target := 673, numerator := 5130795843405648396025856 }, { target := 674, numerator := 32945110152394163385008128 }, { target := 675, numerator := 5130795843405648396025856 }, { target := 676, numerator := 36995738449819675276607488 }, { target := 677, numerator := 36725696563324641150500864 }, { target := 678, numerator := 4590712070415580143812608 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk0.Parent2
