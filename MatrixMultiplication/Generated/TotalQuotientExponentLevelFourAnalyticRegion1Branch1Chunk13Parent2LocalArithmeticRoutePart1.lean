import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk13Parent2LocalData

/-! Line-budgeted sparse route chunks, part 1, for region 1, branch 1,
parent 56; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk19

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot27.Left12.expected,
    Slot27.Left13.expected,
    Slot27.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 660, numerator := 68342087740089505532608512 }, { target := 661, numerator := 990960272231297830222823424 }, { target := 662, numerator := 1754113585328963975336951808 }, { target := 663, numerator := 56951739783407921277173760 }, { target := 664, numerator := 1093473403841432088521736192 }, { target := 665, numerator := 56951739783407921277173760 }, { target := 666, numerator := 1742723237372282391081517056 }, { target := 667, numerator := 1822455673069053480869560320 }, { target := 668, numerator := 1093473403841432088521736192 }, { target := 669, numerator := 27917742841826563010070577152 }, { target := 670, numerator := 1788284629199008728103256064 }, { target := 671, numerator := 990960272231297830222823424 }, { target := 672, numerator := 1742723237372282391081517056 }, { target := 673, numerator := 56951739783407921277173760 }, { target := 674, numerator := 1788284629199008728103256064 }, { target := 675, numerator := 56951739783407921277173760 }, { target := 676, numerator := 1742723237372282391081517056 }, { target := 677, numerator := 1822455673069053480869560320 }, { target := 678, numerator := 68342087740089505532608512 }, { target := 766, numerator := 70240479066203102908514304 }, { target := 767, numerator := 1018486946459944992173457408 }, { target := 768, numerator := 1802838962699212974651867136 }, { target := 769, numerator := 58533732555169252423761920 }, { target := 770, numerator := 1123847665059249646536228864 }, { target := 771, numerator := 58533732555169252423761920 }, { target := 772, numerator := 1791132216188179124167114752 }, { target := 773, numerator := 1873079441765416077560381440 }, { target := 774, numerator := 1123847665059249646536228864 }, { target := 775, numerator := 28693235698543967538128093184 }, { target := 776, numerator := 1837959202232314526106124288 }, { target := 777, numerator := 1018486946459944992173457408 }, { target := 778, numerator := 1791132216188179124167114752 }, { target := 779, numerator := 58533732555169252423761920 }, { target := 780, numerator := 1837959202232314526106124288 }, { target := 781, numerator := 58533732555169252423761920 }, { target := 782, numerator := 1791132216188179124167114752 }, { target := 783, numerator := 1873079441765416077560381440 }, { target := 784, numerator := 70240479066203102908514304 }, { target := 801, numerator := 70240479066203102908514304 }, { target := 802, numerator := 1018486946459944992173457408 }, { target := 803, numerator := 1802838962699212974651867136 }, { target := 804, numerator := 58533732555169252423761920 }, { target := 805, numerator := 1123847665059249646536228864 }, { target := 806, numerator := 58533732555169252423761920 }, { target := 807, numerator := 1791132216188179124167114752 }, { target := 808, numerator := 1873079441765416077560381440 }, { target := 809, numerator := 1123847665059249646536228864 }, { target := 810, numerator := 28693235698543967538128093184 }, { target := 811, numerator := 1837959202232314526106124288 }, { target := 812, numerator := 1018486946459944992173457408 }, { target := 813, numerator := 1791132216188179124167114752 }, { target := 814, numerator := 58533732555169252423761920 }, { target := 815, numerator := 1837959202232314526106124288 }, { target := 816, numerator := 58533732555169252423761920 }, { target := 817, numerator := 1791132216188179124167114752 }, { target := 818, numerator := 1873079441765416077560381440 }, { target := 819, numerator := 70240479066203102908514304 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk19

namespace RouteChunk20

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot27.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 876, numerator := 77834044370657492412137472 }, { target := 877, numerator := 1128593643374533639975993344 }, { target := 878, numerator := 1997740472180208971911528448 }, { target := 879, numerator := 64861703642214577010114560 }, { target := 880, numerator := 1245344709930519878594199552 }, { target := 881, numerator := 64861703642214577010114560 }, { target := 882, numerator := 1984768131451766056509505536 }, { target := 883, numerator := 2075574516550866464323665920 }, { target := 884, numerator := 1245344709930519878594199552 }, { target := 885, numerator := 31795207125413585650358157312 }, { target := 886, numerator := 2036657494365537718117597184 }, { target := 887, numerator := 1128593643374533639975993344 }, { target := 888, numerator := 1984768131451766056509505536 }, { target := 889, numerator := 64861703642214577010114560 }, { target := 890, numerator := 2036657494365537718117597184 }, { target := 891, numerator := 64861703642214577010114560 }, { target := 892, numerator := 1984768131451766056509505536 }, { target := 893, numerator := 2075574516550866464323665920 }, { target := 894, numerator := 77834044370657492412137472 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk20

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent2
