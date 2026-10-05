import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk22Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 92; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left2.expected,
    Slot0.Left5.expected,
    Slot0.Left12.expected,
    Slot1.Left0.expected,
    Slot1.Left2.expected,
    Slot1.Left5.expected,
    Slot1.Left12.expected,
    Slot2.Left0.expected,
    Slot2.Left3.expected,
    Slot2.Left5.expected,
    Slot3.Left0.expected,
    Slot3.Left2.expected,
    Slot3.Left5.expected,
    Slot3.Left12.expected,
    Slot4.Left0.expected,
    Slot4.Left3.expected,
    Slot4.Left5.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
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
    Slot6.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 7833841178835634515188121600 }, { target := 17, numerator := 139442372983274294370348564480 }, { target := 18, numerator := 7833841178835634515188121600 }, { target := 19, numerator := 124035818664897546490478592000 }, { target := 20, numerator := 211774839867856653060585553920 }, { target := 21, numerator := 7833841178835634515188121600 }, { target := 22, numerator := 211774839867856653060585553920 }, { target := 23, numerator := 211774839867856653060585553920 }, { target := 24, numerator := 139442372983274294370348564480 }, { target := 25, numerator := 7833841178835634515188121600 }, { target := 26, numerator := 459318313002788305072979705856 }, { target := 27, numerator := 50080023152440176724064337920 }, { target := 28, numerator := 459318313002788305072979705856 }, { target := 29, numerator := 50080023152440176724064337920 }, { target := 44, numerator := 68439916284148633102855438336 }, { target := 49, numerator := 16905618661490974379091165184 }, { target := 50, numerator := 7833837443369959589003919360 }, { target := 51, numerator := 139442306491985280684269764608 }, { target := 52, numerator := 7833837443369959589003919360 }, { target := 53, numerator := 124035759520024360159228723200 }, { target := 54, numerator := 211774738885767907556072620032 }, { target := 55, numerator := 7833837443369959589003919360 }, { target := 56, numerator := 211774738885767907556072620032 }, { target := 57, numerator := 211774738885767907556072620032 }, { target := 58, numerator := 139442306491985280684269764608 }, { target := 59, numerator := 7833837443369959589003919360 }, { target := 60, numerator := 1661501215248749559678949654528 }, { target := 61, numerator := 171915962954309630094544470016 }, { target := 62, numerator := 1661501215248749559678949654528 }, { target := 63, numerator := 171915962954309630094544470016 }, { target := 64, numerator := 2018630275885433340043091509248 }, { target := 69, numerator := 133020525783836877351269957632 }, { target := 70, numerator := 16015849258254607306507419648 }, { target := 71, numerator := 459318313002788305072979705856 }, { target := 72, numerator := 50080023152440176724064337920 }, { target := 73, numerator := 459318313002788305072979705856 }, { target := 74, numerator := 50080023152440176724064337920 }, { target := 75, numerator := 2018586338987676720864023281664 }, { target := 76, numerator := 16015849258254607306507419648 }, { target := 91, numerator := 16015849258254607306507419648 }, { target := 96, numerator := 686012209895239012962067808256 }, { target := 97, numerator := 16015849258254607306507419648 }, { target := 102, numerator := 133020525783836877351269957632 }, { target := 103, numerator := 686012209895239012962067808256 }, { target := 104, numerator := 68483853181905252281923665920 }, { target := 109, numerator := 16015849258254607306507419648 }]

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
    Slot6.Left14.expected,
    Slot6.Left15.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot9.Left0.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected,
    Slot10.Left4.expected,
    Slot10.Left5.expected,
    Slot10.Left6.expected,
    Slot10.Left7.expected,
    Slot10.Left8.expected,
    Slot10.Left9.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot12.Left0.expected,
    Slot13.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 45569400960281283940021436416 }, { target := 1, numerator := 16905618661490974379091165184 }, { target := 2, numerator := 1169991003552392975676942057472 }, { target := 3, numerator := 133020525783836877351269957632 }, { target := 4, numerator := 16015849258254607306507419648 }, { target := 5, numerator := 1169990720210404003498229235712 }, { target := 6, numerator := 16015849258254607306507419648 }, { target := 7, numerator := 16015849258254607306507419648 }, { target := 8, numerator := 686012209895239012962067808256 }, { target := 9, numerator := 16015849258254607306507419648 }, { target := 10, numerator := 133020525783836877351269957632 }, { target := 11, numerator := 686012209895239012962067808256 }, { target := 12, numerator := 45569684302270256118734258176 }, { target := 13, numerator := 16015849258254607306507419648 }, { target := 14, numerator := 16015849258254607306507419648 }, { target := 15, numerator := 16905618661490974379091165184 }, { target := 16, numerator := 1293981596572346838408734179328 }, { target := 19, numerator := 4647951357602887191811342729216 }, { target := 21, numerator := 1293981317952724349099666571264 }, { target := 26, numerator := 839124010399604302092171214848 }, { target := 28, numerator := 839124006525788046613165375488 }, { target := 40, numerator := 144606905315988157124805918720 }, { target := 42, numerator := 144606836362058809598501978112 }, { target := 45, numerator := 8123983444718435793528422400 }, { target := 47, numerator := 8123979570902180314522583040 }, { target := 50, numerator := 1252709903953045933490110988288 }, { target := 53, numerator := 4506272853225924499357485236224 }, { target := 55, numerator := 1252709625333423444181043380224 }, { target := 60, numerator := 3101477467307839831230147198976 }, { target := 62, numerator := 3101477405972415786145888075776 }, { target := 65, numerator := 219618352455555047618385018880 }, { target := 67, numerator := 219618247733388941169260494848 }, { target := 71, numerator := 839123734141165054217926213632 }, { target := 73, numerator := 839123730267348798738920374272 }, { target := 87, numerator := 219618352455555047618385018880 }, { target := 89, numerator := 219618247733388941169260494848 }, { target := 92, numerator := 219618352455555047618385018880 }, { target := 94, numerator := 219618247733388941169260494848 }, { target := 98, numerator := 144606905315988157124805918720 }, { target := 100, numerator := 144606836362058809598501978112 }, { target := 105, numerator := 8123983444718435793528422400 }, { target := 107, numerator := 8123979570902180314522583040 }, { target := 110, numerator := 16015849258254607306507419648 }, { target := 111, numerator := 16905618661490974379091165184 }]

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
    Slot13.Left1.expected,
    Slot13.Left2.expected,
    Slot13.Left3.expected,
    Slot14.Left0.expected,
    Slot15.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 24978693058615947657713025024 }, { target := 2, numerator := 925759257112556103464814379008 }, { target := 5, numerator := 925715608279154939334104186880 }, { target := 12, numerator := 25022341892017111788423217152 }, { target := 30, numerator := 46227713679175547745290158080 }, { target := 33, numerator := 158691658111670427779579510784 }, { target := 35, numerator := 46227713679175547745290158080 }, { target := 50, numerator := 41271692619300904918623191040 }, { target := 53, numerator := 141678504376962692453857492992 }, { target := 55, numerator := 41271692619300904918623191040 }, { target := 77, numerator := 46227713679175547745290158080 }, { target := 80, numerator := 158691658111670427779579510784 }, { target := 82, numerator := 46227713679175547745290158080 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22.Parent2
