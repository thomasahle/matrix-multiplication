import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk2Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 41; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk2.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left6.expected,
    Slot6.Left14.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot13.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 3456157603768862632837120 }, { target := 35, numerator := 159807487443426325498429440 }, { target := 40, numerator := 159772771509593559743332352 }, { target := 48, numerator := 3477446801784261490769920 }, { target := 79, numerator := 59959617078379787971461120 }, { target := 80, numerator := 2708598891559975599602663424 }, { target := 85, numerator := 2708140176893571571283656704 }, { target := 93, numerator := 59959617078379787971461120 }, { target := 121, numerator := 3456157603768862632837120 }, { target := 122, numerator := 117923332965140306015027200 }, { target := 124, numerator := 1433682308011013315336601600 }, { target := 132, numerator := 117924750290164286016716800 }, { target := 139, numerator := 3618835375537718443376640 }, { target := 154, numerator := 734329728724671059659325440 }, { target := 155, numerator := 33172404798101621498066239488 }, { target := 160, numerator := 33166786886697981821843406848 }, { target := 168, numerator := 734329728724671059659325440 }, { target := 196, numerator := 159807487443426325498429440 }, { target := 197, numerator := 5455641985297007523311648768 }, { target := 199, numerator := 66316444023760314108661989376 }, { target := 207, numerator := 5455709042347628173065191424 }, { target := 214, numerator := 167156355645722594017017856 }, { target := 492, numerator := 59959668219568306530549760 }, { target := 493, numerator := 2708601201797653624680087552 }, { target := 498, numerator := 2708142486739999378733268992 }, { target := 506, numerator := 59959668219568306530549760 }, { target := 508, numerator := 159772771509593559743332352 }, { target := 509, numerator := 5454450636279985407969460224 }, { target := 511, numerator := 66301986621738448490634149888 }, { target := 519, numerator := 5454517675671428968849866752 }, { target := 526, numerator := 167120394919486097847222272 }, { target := 890, numerator := 1960190614727851308482560 }, { target := 891, numerator := 88549099961023192589402112 }, { target := 896, numerator := 88534103731431736189386752 }, { target := 904, numerator := 1960190614727851308482560 }, { target := 906, numerator := 3477446801784261490769920 }, { target := 907, numerator := 118667336356343064402329600 }, { target := 909, numerator := 1442658970094789089191526400 }, { target := 917, numerator := 118668771217258093477888000 }, { target := 924, numerator := 3640125199834940482519040 }]

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
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 79, numerator := 57963715886760518043566080 }, { target := 80, numerator := 2747043093737031923708985344 }, { target := 85, numerator := 2746310459386413836685803520 }, { target := 93, numerator := 58707719277963276430868480 }, { target := 154, numerator := 699352579286342255677276160 }, { target := 155, numerator := 33144039225658692610595749888 }, { target := 160, numerator := 33135199735040466668790743040 }, { target := 168, numerator := 708329241370118029532200960 }, { target := 492, numerator := 57965082070595979486167040 }, { target := 493, numerator := 2747107840549974548385103872 }, { target := 498, numerator := 2746375188931429590116597760 }, { target := 506, numerator := 58709102997689786947338240 }, { target := 890, numerator := 1658644760809867134894080 }, { target := 891, numerator := 78607255684699401427615744 }, { target := 896, numerator := 78586291188054361657835520 }, { target := 904, numerator := 1679934585107089174036480 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk2.Parent3
