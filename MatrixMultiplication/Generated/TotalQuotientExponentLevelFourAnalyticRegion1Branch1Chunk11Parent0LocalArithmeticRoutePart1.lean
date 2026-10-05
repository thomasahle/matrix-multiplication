import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk11Parent0LocalData

/-! Line-budgeted sparse route chunks, part 1, for region 1, branch 1,
parent 46; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk20

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot24.Left13.expected,
    Slot24.Left14.expected,
    Slot24.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 776, numerator := 29410898455312150390898688 }, { target := 777, numerator := 426458027602026180668030976 }, { target := 778, numerator := 754879727019678526699732992 }, { target := 779, numerator := 24509082046093458659082240 }, { target := 780, numerator := 470574375284994406254379008 }, { target := 781, numerator := 24509082046093458659082240 }, { target := 782, numerator := 749977910610459834967916544 }, { target := 783, numerator := 784290625474990677090631680 }, { target := 784, numerator := 470574375284994406254379008 }, { target := 785, numerator := 12014352018995013434682114048 }, { target := 786, numerator := 769585176247334601895182336 }, { target := 787, numerator := 426458027602026180668030976 }, { target := 788, numerator := 749977910610459834967916544 }, { target := 789, numerator := 24509082046093458659082240 }, { target := 790, numerator := 769585176247334601895182336 }, { target := 791, numerator := 24509082046093458659082240 }, { target := 792, numerator := 749977910610459834967916544 }, { target := 793, numerator := 784290625474990677090631680 }, { target := 794, numerator := 29410898455312150390898688 }, { target := 811, numerator := 759781543428897218431549440 }, { target := 812, numerator := 11016832379719009667257466880 }, { target := 813, numerator := 19501059614675028606409768960 }, { target := 814, numerator := 633151286190747682026291200 }, { target := 815, numerator := 12156504694862355494904791040 }, { target := 816, numerator := 633151286190747682026291200 }, { target := 817, numerator := 19374429357436879070004510720 }, { target := 818, numerator := 20260841158103925824841318400 }, { target := 819, numerator := 12156504694862355494904791040 }, { target := 820, numerator := 310370760490704513729287946240 }, { target := 821, numerator := 19880950386389477215625543680 }, { target := 822, numerator := 11016832379719009667257466880 }, { target := 823, numerator := 19374429357436879070004510720 }, { target := 824, numerator := 633151286190747682026291200 }, { target := 825, numerator := 19880950386389477215625543680 }, { target := 826, numerator := 633151286190747682026291200 }, { target := 827, numerator := 19374429357436879070004510720 }, { target := 828, numerator := 20260841158103925824841318400 }, { target := 829, numerator := 759781543428897218431549440 }, { target := 846, numerator := 29410898455312150390898688 }, { target := 847, numerator := 426458027602026180668030976 }, { target := 848, numerator := 754879727019678526699732992 }, { target := 849, numerator := 24509082046093458659082240 }, { target := 850, numerator := 470574375284994406254379008 }, { target := 851, numerator := 24509082046093458659082240 }, { target := 852, numerator := 749977910610459834967916544 }, { target := 853, numerator := 784290625474990677090631680 }, { target := 854, numerator := 470574375284994406254379008 }, { target := 855, numerator := 12014352018995013434682114048 }, { target := 856, numerator := 769585176247334601895182336 }, { target := 857, numerator := 426458027602026180668030976 }, { target := 858, numerator := 749977910610459834967916544 }, { target := 859, numerator := 24509082046093458659082240 }, { target := 860, numerator := 769585176247334601895182336 }, { target := 861, numerator := 24509082046093458659082240 }, { target := 862, numerator := 749977910610459834967916544 }, { target := 863, numerator := 784290625474990677090631680 }, { target := 864, numerator := 29410898455312150390898688 }]

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

namespace RouteChunk21

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot24.Left16.expected,
    Slot24.Left17.expected,
    Slot24.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 907, numerator := 774486992656553293626998784 }, { target := 908, numerator := 11230061393520022757591482368 }, { target := 909, numerator := 19878499478184867869759635456 }, { target := 910, numerator := 645405827213794411355832320 }, { target := 911, numerator := 12391791882504852698031980544 }, { target := 912, numerator := 645405827213794411355832320 }, { target := 913, numerator := 19749418312742108987488468992 }, { target := 914, numerator := 20652986470841421163386634240 }, { target := 915, numerator := 12391791882504852698031980544 }, { target := 916, numerator := 316377936500202020446629003264 }, { target := 917, numerator := 20265742974513144516573134848 }, { target := 918, numerator := 11230061393520022757591482368 }, { target := 919, numerator := 19749418312742108987488468992 }, { target := 920, numerator := 645405827213794411355832320 }, { target := 921, numerator := 20265742974513144516573134848 }, { target := 922, numerator := 645405827213794411355832320 }, { target := 923, numerator := 19749418312742108987488468992 }, { target := 924, numerator := 20652986470841421163386634240 }, { target := 925, numerator := 774486992656553293626998784 }, { target := 942, numerator := 774486992656553293626998784 }, { target := 943, numerator := 11230061393520022757591482368 }, { target := 944, numerator := 19878499478184867869759635456 }, { target := 945, numerator := 645405827213794411355832320 }, { target := 946, numerator := 12391791882504852698031980544 }, { target := 947, numerator := 645405827213794411355832320 }, { target := 948, numerator := 19749418312742108987488468992 }, { target := 949, numerator := 20652986470841421163386634240 }, { target := 950, numerator := 12391791882504852698031980544 }, { target := 951, numerator := 316377936500202020446629003264 }, { target := 952, numerator := 20265742974513144516573134848 }, { target := 953, numerator := 11230061393520022757591482368 }, { target := 954, numerator := 19749418312742108987488468992 }, { target := 955, numerator := 645405827213794411355832320 }, { target := 956, numerator := 20265742974513144516573134848 }, { target := 957, numerator := 645405827213794411355832320 }, { target := 958, numerator := 19749418312742108987488468992 }, { target := 959, numerator := 20652986470841421163386634240 }, { target := 960, numerator := 774486992656553293626998784 }, { target := 1017, numerator := 29410898455312150390898688 }, { target := 1018, numerator := 426458027602026180668030976 }, { target := 1019, numerator := 754879727019678526699732992 }, { target := 1020, numerator := 24509082046093458659082240 }, { target := 1021, numerator := 470574375284994406254379008 }, { target := 1022, numerator := 24509082046093458659082240 }, { target := 1023, numerator := 749977910610459834967916544 }, { target := 1024, numerator := 784290625474990677090631680 }, { target := 1025, numerator := 470574375284994406254379008 }, { target := 1026, numerator := 12014352018995013434682114048 }, { target := 1027, numerator := 769585176247334601895182336 }, { target := 1028, numerator := 426458027602026180668030976 }, { target := 1029, numerator := 749977910610459834967916544 }, { target := 1030, numerator := 24509082046093458659082240 }, { target := 1031, numerator := 769585176247334601895182336 }, { target := 1032, numerator := 24509082046093458659082240 }, { target := 1033, numerator := 749977910610459834967916544 }, { target := 1034, numerator := 784290625474990677090631680 }, { target := 1035, numerator := 29410898455312150390898688 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk21

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent0
