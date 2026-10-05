import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk10Parent3LocalData

/-! Line-budgeted sparse route chunks, part 1, for region 1, branch 1,
parent 45; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk19

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot27.Left13.expected,
    Slot27.Left14.expected,
    Slot27.Left15.expected,
    Slot27.Left16.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 785, numerator := 57971770943707764643332096 }, { target := 786, numerator := 65451999452573282661826560 }, { target := 787, numerator := 56101713816491385138708480 }, { target := 788, numerator := 738672565250469904326328320 }, { target := 789, numerator := 65451999452573282661826560 }, { target := 790, numerator := 56101713816491385138708480 }, { target := 791, numerator := 65451999452573282661826560 }, { target := 792, numerator := 65451999452573282661826560 }, { target := 793, numerator := 2713452891590966661208866816 }, { target := 794, numerator := 67322056579789662166450176 }, { target := 795, numerator := 738672565250469904326328320 }, { target := 796, numerator := 2713452891590966661208866816 }, { target := 797, numerator := 57971770943707764643332096 }, { target := 798, numerator := 65451999452573282661826560 }, { target := 799, numerator := 67322056579789662166450176 }, { target := 800, numerator := 65451999452573282661826560 }, { target := 820, numerator := 1497604082712450586619412480 }, { target := 821, numerator := 1690843319191476468763852800 }, { target := 822, numerator := 1449294273592694116083302400 }, { target := 823, numerator := 19082374602303805861763481600 }, { target := 824, numerator := 1690843319191476468763852800 }, { target := 825, numerator := 1449294273592694116083302400 }, { target := 826, numerator := 1690843319191476468763852800 }, { target := 827, numerator := 1690843319191476468763852800 }, { target := 828, numerator := 70097533032766638747895726080 }, { target := 829, numerator := 1739153128311232939299962880 }, { target := 830, numerator := 19082374602303805861763481600 }, { target := 831, numerator := 70097533032766638747895726080 }, { target := 832, numerator := 1497604082712450586619412480 }, { target := 833, numerator := 1690843319191476468763852800 }, { target := 834, numerator := 1739153128311232939299962880 }, { target := 835, numerator := 1690843319191476468763852800 }, { target := 846, numerator := 57971770943707764643332096 }, { target := 847, numerator := 65451999452573282661826560 }, { target := 848, numerator := 56101713816491385138708480 }, { target := 849, numerator := 738672565250469904326328320 }, { target := 850, numerator := 65451999452573282661826560 }, { target := 851, numerator := 56101713816491385138708480 }, { target := 852, numerator := 65451999452573282661826560 }, { target := 853, numerator := 65451999452573282661826560 }, { target := 854, numerator := 2713452891590966661208866816 }, { target := 855, numerator := 67322056579789662166450176 }, { target := 856, numerator := 738672565250469904326328320 }, { target := 857, numerator := 2713452891590966661208866816 }, { target := 858, numerator := 57971770943707764643332096 }, { target := 859, numerator := 65451999452573282661826560 }, { target := 860, numerator := 67322056579789662166450176 }, { target := 861, numerator := 65451999452573282661826560 }, { target := 895, numerator := 1526589968184304468941078528 }, { target := 896, numerator := 1723569318917763110094766080 }, { target := 897, numerator := 1477345130500939808652656640 }, { target := 898, numerator := 19451710884929040813926645760 }, { target := 899, numerator := 1723569318917763110094766080 }, { target := 900, numerator := 1477345130500939808652656640 }, { target := 901, numerator := 1723569318917763110094766080 }, { target := 902, numerator := 1723569318917763110094766080 }, { target := 903, numerator := 71454259478562122078500159488 }, { target := 904, numerator := 1772814156601127770383187968 }, { target := 905, numerator := 19451710884929040813926645760 }, { target := 906, numerator := 71454259478562122078500159488 }, { target := 907, numerator := 1526589968184304468941078528 }, { target := 908, numerator := 1723569318917763110094766080 }, { target := 909, numerator := 1772814156601127770383187968 }, { target := 910, numerator := 1723569318917763110094766080 }]

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
    Slot27.Left17.expected,
    Slot27.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 921, numerator := 1526589968184304468941078528 }, { target := 922, numerator := 1723569318917763110094766080 }, { target := 923, numerator := 1477345130500939808652656640 }, { target := 924, numerator := 19451710884929040813926645760 }, { target := 925, numerator := 1723569318917763110094766080 }, { target := 926, numerator := 1477345130500939808652656640 }, { target := 927, numerator := 1723569318917763110094766080 }, { target := 928, numerator := 1723569318917763110094766080 }, { target := 929, numerator := 71454259478562122078500159488 }, { target := 930, numerator := 1772814156601127770383187968 }, { target := 931, numerator := 19451710884929040813926645760 }, { target := 932, numerator := 71454259478562122078500159488 }, { target := 933, numerator := 1526589968184304468941078528 }, { target := 934, numerator := 1723569318917763110094766080 }, { target := 935, numerator := 1772814156601127770383187968 }, { target := 936, numerator := 1723569318917763110094766080 }, { target := 966, numerator := 57971770943707764643332096 }, { target := 967, numerator := 65451999452573282661826560 }, { target := 968, numerator := 56101713816491385138708480 }, { target := 969, numerator := 738672565250469904326328320 }, { target := 970, numerator := 65451999452573282661826560 }, { target := 971, numerator := 56101713816491385138708480 }, { target := 972, numerator := 65451999452573282661826560 }, { target := 973, numerator := 65451999452573282661826560 }, { target := 974, numerator := 2713452891590966661208866816 }, { target := 975, numerator := 67322056579789662166450176 }, { target := 976, numerator := 738672565250469904326328320 }, { target := 977, numerator := 2713452891590966661208866816 }, { target := 978, numerator := 57971770943707764643332096 }, { target := 979, numerator := 65451999452573282661826560 }, { target := 980, numerator := 67322056579789662166450176 }, { target := 981, numerator := 65451999452573282661826560 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent3
