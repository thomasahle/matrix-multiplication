import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk12Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 51; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk12.Parent1

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
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot5.Left0.expected,
    Slot5.Left3.expected,
    Slot5.Left5.expected,
    Slot6.Left0.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 8310917542014491262872736235520 }, { target := 3, numerator := 30042265404772078743220274593792 }, { target := 5, numerator := 8312204774115124836504375918592 }, { target := 10, numerator := 23025229814573401750729891250176 }, { target := 12, numerator := 23025239818798899596100640964608 }, { target := 14, numerator := 8326843515193843895091536592896 }, { target := 15, numerator := 10348403782275215806158602240 }, { target := 17, numerator := 10348406249527235664811130880 }, { target := 19, numerator := 29072248110092602393334120448 }, { target := 20, numerator := 1508739422879057210033307648 }, { target := 21, numerator := 23025239873212182927525390843904 }, { target := 23, numerator := 23025249877441335443993751715840 }, { target := 25, numerator := 30123693136979634655552518225920 }, { target := 26, numerator := 46828950548592275711418433536 }, { target := 27, numerator := 8328199953575283923373782990848 }, { target := 28, numerator := 10348403782275215806158602240 }, { target := 30, numerator := 10348406249527235664811130880 }, { target := 32, numerator := 46828950548592275711418433536 }, { target := 33, numerator := 48801917486203350524538912768 }, { target := 34, numerator := 29072248110092602393334120448 }, { target := 35, numerator := 1450710983537555009647411200 }]

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
    Slot15.Left0.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1392682544196052809261514752 }, { target := 1, numerator := 29072248110092602393334120448 }, { target := 2, numerator := 1508739422879057210033307648 }, { target := 3, numerator := 31277328805069686007998185472 }, { target := 4, numerator := 46828950548592275711418433536 }, { target := 5, numerator := 1450710983537555009647411200 }, { target := 6, numerator := 46828950548592275711418433536 }, { target := 7, numerator := 48801917486203350524538912768 }, { target := 8, numerator := 29072248110092602393334120448 }, { target := 9, numerator := 1450710983537555009647411200 }, { target := 10, numerator := 9458634485107627157404778496 }, { target := 11, numerator := 10348403782275215806158602240 }, { target := 12, numerator := 9458634485107627157404778496 }, { target := 13, numerator := 10348403782275215806158602240 }, { target := 14, numerator := 14016437068339462480190242816 }, { target := 21, numerator := 9458636740222090168397463552 }, { target := 22, numerator := 10348406249527235664811130880 }, { target := 23, numerator := 9458636740222090168397463552 }, { target := 24, numerator := 10348406249527235664811130880 }, { target := 25, numerator := 51195293099951895502808678400 }, { target := 27, numerator := 14016432345972979610545029120 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk12.Parent1
