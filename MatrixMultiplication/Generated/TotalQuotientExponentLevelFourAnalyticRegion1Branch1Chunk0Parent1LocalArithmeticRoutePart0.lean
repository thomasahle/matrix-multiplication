import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk0Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 2; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0.Parent1

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
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 2900019424229697734666354688 }, { target := 2, numerator := 115942238514266257264585211904 }, { target := 5, numerator := 115942210180067360046713929728 }, { target := 12, numerator := 2900019424229697734666354688 }, { target := 16, numerator := 3584598489680632681045426176 }, { target := 17, numerator := 4845374685015433732222353408 }, { target := 18, numerator := 251456570479842868338884608 }, { target := 19, numerator := 17425187639764287557138907136 }, { target := 20, numerator := 7804825091432045951903072256 }, { target := 21, numerator := 3594272151352012725435760640 }, { target := 22, numerator := 7804825091432045951903072256 }, { target := 23, numerator := 8133652914367225087423152128 }, { target := 24, numerator := 4845374685015433732222353408 }, { target := 25, numerator := 241785163922925834941235200 }, { target := 26, numerator := 232113757366008801543585792 }, { target := 28, numerator := 232113757366008801543585792 }, { target := 30, numerator := 3667851394250150870211624960 }, { target := 33, numerator := 13361104776050129871893954560 }, { target := 35, numerator := 3667853861502170728864153600 }, { target := 40, numerator := 4845374685015433732222353408 }, { target := 42, numerator := 4845374685015433732222353408 }, { target := 44, numerator := 599627206528856070654263296 }, { target := 45, numerator := 251456570479842868338884608 }, { target := 47, numerator := 251456570479842868338884608 }, { target := 49, numerator := 676998458984192337835458560 }, { target := 50, numerator := 3352484732314623879501840384 }, { target := 53, numerator := 12212299505586006555805876224 }, { target := 55, numerator := 3352486987429086890494525440 }, { target := 60, numerator := 5212888134178281001333030912 }, { target := 62, numerator := 5212888134178281001333030912 }, { target := 64, numerator := 580284393415022003858964480 }, { target := 65, numerator := 7804825091432045951903072256 }, { target := 67, numerator := 7804825091432045951903072256 }, { target := 69, numerator := 7640411179964456384143032320 }, { target := 70, numerator := 676998458984192337835458560 }, { target := 71, numerator := 241785163922925834941235200 }, { target := 73, numerator := 241785163922925834941235200 }, { target := 75, numerator := 580284393415022003858964480 }, { target := 76, numerator := 676998458984192337835458560 }, { target := 77, numerator := 3667851394250150870211624960 }, { target := 80, numerator := 13361104776050129871893954560 }, { target := 82, numerator := 3667853861502170728864153600 }, { target := 87, numerator := 7804825091432045951903072256 }, { target := 89, numerator := 7804825091432045951903072256 }, { target := 91, numerator := 676998458984192337835458560 }, { target := 92, numerator := 8133652914367225087423152128 }, { target := 94, numerator := 8133652914367225087423152128 }, { target := 96, numerator := 28066421828173230919978582016 }, { target := 97, numerator := 696341272098026404630757376 }, { target := 98, numerator := 4845374685015433732222353408 }, { target := 100, numerator := 4845374685015433732222353408 }, { target := 102, numerator := 7640411179964456384143032320 }, { target := 103, numerator := 28066421828173230919978582016 }, { target := 104, numerator := 599627206528856070654263296 }, { target := 105, numerator := 241785163922925834941235200 }, { target := 107, numerator := 241785163922925834941235200 }, { target := 109, numerator := 676998458984192337835458560 }, { target := 110, numerator := 696341272098026404630757376 }, { target := 111, numerator := 676998458984192337835458560 }]

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
    Slot5.Left2.expected,
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 3352484732314623879501840384 }, { target := 27, numerator := 3667851394250150870211624960 }, { target := 28, numerator := 3352484732314623879501840384 }, { target := 29, numerator := 3667851394250150870211624960 }, { target := 44, numerator := 2900019424229697734666354688 }, { target := 50, numerator := 232113757366008801543585792 }, { target := 51, numerator := 4845374685015433732222353408 }, { target := 52, numerator := 251456570479842868338884608 }, { target := 53, numerator := 5212888134178281001333030912 }, { target := 54, numerator := 7804825091432045951903072256 }, { target := 55, numerator := 241785163922925834941235200 }, { target := 56, numerator := 7804825091432045951903072256 }, { target := 57, numerator := 8133652914367225087423152128 }, { target := 58, numerator := 4845374685015433732222353408 }, { target := 59, numerator := 241785163922925834941235200 }, { target := 60, numerator := 12212299505586006555805876224 }, { target := 61, numerator := 13361104776050129871893954560 }, { target := 62, numerator := 12212299505586006555805876224 }, { target := 63, numerator := 13361104776050129871893954560 }, { target := 64, numerator := 115942238514266257264585211904 }, { target := 71, numerator := 3352486987429086890494525440 }, { target := 72, numerator := 3667853861502170728864153600 }, { target := 73, numerator := 3352486987429086890494525440 }, { target := 74, numerator := 3667853861502170728864153600 }, { target := 75, numerator := 115942210180067360046713929728 }, { target := 104, numerator := 2900019424229697734666354688 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0.Parent1
