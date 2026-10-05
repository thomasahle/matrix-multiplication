import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk14Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 58; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14.Parent0

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
    Slot0.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 250, numerator := 15810482984647572175454208 }, { target := 251, numerator := 18006383399181957199822848 }, { target := 252, numerator := 14053762653020064155959296 }, { target := 253, numerator := 188408255567050235090829312 }, { target := 254, numerator := 16688843150461326185201664 }, { target := 255, numerator := 14053762653020064155959296 }, { target := 256, numerator := 16688843150461326185201664 }, { target := 257, numerator := 16249663067554449180327936 }, { target := 258, numerator := 613973755903814052813471744 }, { target := 259, numerator := 16249663067554449180327936 }, { target := 260, numerator := 188408255567050235090829312 }, { target := 261, numerator := 613973755903814052813471744 }, { target := 262, numerator := 15810482984647572175454208 }, { target := 263, numerator := 16249663067554449180327936 }, { target := 264, numerator := 16249663067554449180327936 }, { target := 265, numerator := 18006383399181957199822848 }, { target := 466, numerator := 387611840913940479140167680 }, { target := 467, numerator := 441446818818654434576302080 }, { target := 468, numerator := 344543858590169314791260160 }, { target := 469, numerator := 4619041104224457376420331520 }, { target := 470, numerator := 409145832075826061314621440 }, { target := 471, numerator := 344543858590169314791260160 }, { target := 472, numerator := 409145832075826061314621440 }, { target := 473, numerator := 398378836494883270227394560 }, { target := 474, numerator := 15052259822158021939943178240 }, { target := 475, numerator := 398378836494883270227394560 }, { target := 476, numerator := 4619041104224457376420331520 }, { target := 477, numerator := 15052259822158021939943178240 }, { target := 478, numerator := 387611840913940479140167680 }, { target := 479, numerator := 398378836494883270227394560 }, { target := 480, numerator := 398378836494883270227394560 }, { target := 481, numerator := 441446818818654434576302080 }, { target := 562, numerator := 286628756044255985890492416 }, { target := 563, numerator := 326438305494847095041949696 }, { target := 564, numerator := 254781116483783098569326592 }, { target := 565, numerator := 3415659342860717165195034624 }, { target := 566, numerator := 302552575824492429551075328 }, { target := 567, numerator := 254781116483783098569326592 }, { target := 568, numerator := 302552575824492429551075328 }, { target := 569, numerator := 294590665934374207720783872 }, { target := 570, numerator := 11130750026385274118747455488 }, { target := 571, numerator := 294590665934374207720783872 }, { target := 572, numerator := 3415659342860717165195034624 }, { target := 573, numerator := 11130750026385274118747455488 }, { target := 574, numerator := 286628756044255985890492416 }, { target := 575, numerator := 294590665934374207720783872 }, { target := 576, numerator := 294590665934374207720783872 }, { target := 577, numerator := 326438305494847095041949696 }, { target := 597, numerator := 319779768754000895290638336 }, { target := 598, numerator := 364193625525389908525449216 }, { target := 599, numerator := 284248683336889684702789632 }, { target := 600, numerator := 3810708910985177335546773504 }, { target := 601, numerator := 337545311462556500584562688 }, { target := 602, numerator := 284248683336889684702789632 }, { target := 603, numerator := 337545311462556500584562688 }, { target := 604, numerator := 328662540108278697937600512 }, { target := 605, numerator := 12418114353280368100453122048 }, { target := 606, numerator := 328662540108278697937600512 }, { target := 607, numerator := 3810708910985177335546773504 }, { target := 608, numerator := 12418114353280368100453122048 }, { target := 609, numerator := 319779768754000895290638336 }, { target := 610, numerator := 328662540108278697937600512 }, { target := 611, numerator := 328662540108278697937600512 }, { target := 612, numerator := 364193625525389908525449216 }]

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
    Slot0.Left4.expected,
    Slot0.Left5.expected,
    Slot0.Left6.expected,
    Slot0.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 733, numerator := 15810482984647572175454208 }, { target := 734, numerator := 18006383399181957199822848 }, { target := 735, numerator := 14053762653020064155959296 }, { target := 736, numerator := 188408255567050235090829312 }, { target := 737, numerator := 16688843150461326185201664 }, { target := 738, numerator := 14053762653020064155959296 }, { target := 739, numerator := 16688843150461326185201664 }, { target := 740, numerator := 16249663067554449180327936 }, { target := 741, numerator := 613973755903814052813471744 }, { target := 742, numerator := 16249663067554449180327936 }, { target := 743, numerator := 188408255567050235090829312 }, { target := 744, numerator := 613973755903814052813471744 }, { target := 745, numerator := 15810482984647572175454208 }, { target := 746, numerator := 16249663067554449180327936 }, { target := 747, numerator := 16249663067554449180327936 }, { target := 748, numerator := 18006383399181957199822848 }, { target := 829, numerator := 319269753173850973607559168 }, { target := 830, numerator := 363612774447996942164164608 }, { target := 831, numerator := 283795336154534198762274816 }, { target := 832, numerator := 3804631225321724102156746752 }, { target := 833, numerator := 337006961683509361030201344 }, { target := 834, numerator := 283795336154534198762274816 }, { target := 835, numerator := 337006961683509361030201344 }, { target := 836, numerator := 328138357428680167318880256 }, { target := 837, numerator := 12398308748251212808426881024 }, { target := 838, numerator := 328138357428680167318880256 }, { target := 839, numerator := 3804631225321724102156746752 }, { target := 840, numerator := 12398308748251212808426881024 }, { target := 841, numerator := 319269753173850973607559168 }, { target := 842, numerator := 328138357428680167318880256 }, { target := 843, numerator := 328138357428680167318880256 }, { target := 844, numerator := 363612774447996942164164608 }, { target := 864, numerator := 324879924555500112121430016 }, { target := 865, numerator := 370002136299319572138295296 }, { target := 866, numerator := 288782155160444544107937792 }, { target := 867, numerator := 3871485767619709669447041024 }, { target := 868, numerator := 342928809253027896128176128 }, { target := 869, numerator := 288782155160444544107937792 }, { target := 870, numerator := 342928809253027896128176128 }, { target := 871, numerator := 333904366904264004124803072 }, { target := 872, numerator := 12616170403571921020715532288 }, { target := 873, numerator := 333904366904264004124803072 }, { target := 874, numerator := 3871485767619709669447041024 }, { target := 875, numerator := 12616170403571921020715532288 }, { target := 876, numerator := 324879924555500112121430016 }, { target := 877, numerator := 333904366904264004124803072 }, { target := 878, numerator := 333904366904264004124803072 }, { target := 879, numerator := 370002136299319572138295296 }, { target := 925, numerator := 15810482984647572175454208 }, { target := 926, numerator := 18006383399181957199822848 }, { target := 927, numerator := 14053762653020064155959296 }, { target := 928, numerator := 188408255567050235090829312 }, { target := 929, numerator := 16688843150461326185201664 }, { target := 930, numerator := 14053762653020064155959296 }, { target := 931, numerator := 16688843150461326185201664 }, { target := 932, numerator := 16249663067554449180327936 }, { target := 933, numerator := 613973755903814052813471744 }, { target := 934, numerator := 16249663067554449180327936 }, { target := 935, numerator := 188408255567050235090829312 }, { target := 936, numerator := 613973755903814052813471744 }, { target := 937, numerator := 15810482984647572175454208 }, { target := 938, numerator := 16249663067554449180327936 }, { target := 939, numerator := 16249663067554449180327936 }, { target := 940, numerator := 18006383399181957199822848 }]

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
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot2.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 613, numerator := 3517797193909415876375871488 }, { target := 616, numerator := 12848818678405895648654131200 }, { target := 618, numerator := 3517796008706109140537180160 }, { target := 880, numerator := 3507531248791003184129638400 }, { target := 883, numerator := 12811322125842454318940160000 }, { target := 885, numerator := 3507530067046460962111488000 }, { target := 960, numerator := 387611840913940479140167680 }, { target := 961, numerator := 441446818818654434576302080 }, { target := 962, numerator := 344543858590169314791260160 }, { target := 963, numerator := 4619041104224457376420331520 }, { target := 964, numerator := 409145832075826061314621440 }, { target := 965, numerator := 344543858590169314791260160 }, { target := 966, numerator := 409145832075826061314621440 }, { target := 967, numerator := 398378836494883270227394560 }, { target := 968, numerator := 15052259822158021939943178240 }, { target := 969, numerator := 398378836494883270227394560 }, { target := 970, numerator := 4619041104224457376420331520 }, { target := 971, numerator := 15052259822158021939943178240 }, { target := 972, numerator := 387611840913940479140167680 }, { target := 973, numerator := 398378836494883270227394560 }, { target := 974, numerator := 398378836494883270227394560 }, { target := 975, numerator := 441446818818654434576302080 }, { target := 976, numerator := 3483577376848040235555094528 }, { target := 979, numerator := 12723830169861091216274227200 }, { target := 981, numerator := 3483576203173948545784872960 }, { target := 986, numerator := 15810482984647572175454208 }, { target := 987, numerator := 18006383399181957199822848 }, { target := 988, numerator := 14053762653020064155959296 }, { target := 989, numerator := 188408255567050235090829312 }, { target := 990, numerator := 16688843150461326185201664 }, { target := 991, numerator := 14053762653020064155959296 }, { target := 992, numerator := 16688843150461326185201664 }, { target := 993, numerator := 16249663067554449180327936 }, { target := 994, numerator := 613973755903814052813471744 }, { target := 995, numerator := 16249663067554449180327936 }, { target := 996, numerator := 188408255567050235090829312 }, { target := 997, numerator := 613973755903814052813471744 }, { target := 998, numerator := 15810482984647572175454208 }, { target := 999, numerator := 16249663067554449180327936 }, { target := 1000, numerator := 16249663067554449180327936 }, { target := 1001, numerator := 18006383399181957199822848 }, { target := 1002, numerator := 3507531248791003184129638400 }, { target := 1005, numerator := 12811322125842454318940160000 }, { target := 1007, numerator := 3507530067046460962111488000 }, { target := 1012, numerator := 39614076534765685927126761472 }, { target := 1014, numerator := 39614085979498651666417188864 }]

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
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 39299900499479652445716480 }, { target := 122, numerator := 589498507492194786685747200 }, { target := 123, numerator := 1034897379819630847737200640 }, { target := 124, numerator := 39299900499479652445716480 }, { target := 125, numerator := 654998341657994207428608000 }, { target := 126, numerator := 39299900499479652445716480 }, { target := 127, numerator := 1034897379819630847737200640 }, { target := 128, numerator := 1028347396403050905662914560 }, { target := 129, numerator := 654998341657994207428608000 }, { target := 130, numerator := 15870609818373199645995171840 }, { target := 131, numerator := 1015247429569891021514342400 }, { target := 132, numerator := 589498507492194786685747200 }, { target := 133, numerator := 1034897379819630847737200640 }, { target := 134, numerator := 39299900499479652445716480 }, { target := 135, numerator := 1015247429569891021514342400 }, { target := 136, numerator := 39299900499479652445716480 }, { target := 137, numerator := 1034897379819630847737200640 }, { target := 138, numerator := 1034897379819630847737200640 }, { target := 139, numerator := 39299900499479652445716480 }, { target := 196, numerator := 7794539410603317399650304000 }, { target := 197, numerator := 116918091159049760994754560000 }, { target := 198, numerator := 205256204479220691524124672000 }, { target := 199, numerator := 7794539410603317399650304000 }, { target := 200, numerator := 129908990176721956660838400000 }, { target := 201, numerator := 7794539410603317399650304000 }, { target := 202, numerator := 205256204479220691524124672000 }, { target := 203, numerator := 203957114577453471957516288000 }, { target := 204, numerator := 129908990176721956660838400000 }, { target := 205, numerator := 3147694831981973009892114432000 }, { target := 206, numerator := 201358934773919032824299520000 }, { target := 207, numerator := 116918091159049760994754560000 }, { target := 208, numerator := 205256204479220691524124672000 }, { target := 209, numerator := 7794539410603317399650304000 }, { target := 210, numerator := 201358934773919032824299520000 }, { target := 211, numerator := 7794539410603317399650304000 }, { target := 212, numerator := 205256204479220691524124672000 }, { target := 213, numerator := 205256204479220691524124672000 }, { target := 214, numerator := 7794539410603317399650304000 }, { target := 508, numerator := 7794539410603317399650304000 }, { target := 509, numerator := 116918091159049760994754560000 }, { target := 510, numerator := 205256204479220691524124672000 }, { target := 511, numerator := 7794539410603317399650304000 }, { target := 512, numerator := 129908990176721956660838400000 }, { target := 513, numerator := 7794539410603317399650304000 }, { target := 514, numerator := 205256204479220691524124672000 }, { target := 515, numerator := 203957114577453471957516288000 }, { target := 516, numerator := 129908990176721956660838400000 }, { target := 517, numerator := 3147694831981973009892114432000 }, { target := 518, numerator := 201358934773919032824299520000 }, { target := 519, numerator := 116918091159049760994754560000 }, { target := 520, numerator := 205256204479220691524124672000 }, { target := 521, numerator := 7794539410603317399650304000 }, { target := 522, numerator := 201358934773919032824299520000 }, { target := 523, numerator := 7794539410603317399650304000 }, { target := 524, numerator := 205256204479220691524124672000 }, { target := 525, numerator := 205256204479220691524124672000 }, { target := 526, numerator := 7794539410603317399650304000 }]

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
    Slot3.Left14.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left7.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot6.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 81624628916875920754606080 }, { target := 35, numerator := 61218471687656940565954560 }, { target := 36, numerator := 64619497892526770597396480 }, { target := 37, numerator := 83325142019310835770327040 }, { target := 38, numerator := 1115536595197304250312949760 }, { target := 39, numerator := 1950488528492847523031941120 }, { target := 40, numerator := 59517958585222025550233600 }, { target := 41, numerator := 1115536595197304250312949760 }, { target := 42, numerator := 62918984790091855581675520 }, { target := 43, numerator := 64619497892526770597396480 }, { target := 44, numerator := 64619497892526770597396480 }, { target := 45, numerator := 62918984790091855581675520 }, { target := 46, numerator := 1950488528492847523031941120 }, { target := 47, numerator := 62918984790091855581675520 }, { target := 48, numerator := 81624628916875920754606080 }, { target := 49, numerator := 83325142019310835770327040 }, { target := 250, numerator := 734217735192128821091368960 }, { target := 252, numerator := 28638444859018807277791477760 }, { target := 255, numerator := 28638434354537339297485291520 }, { target := 262, numerator := 734221236685951481193431040 }, { target := 562, numerator := 33185305911871497508445224960 }, { target := 564, numerator := 1294405607402155842492705013760 }, { target := 567, numerator := 1294405132618703670376681963520 }, { target := 574, numerator := 33185464173022221547119575040 }, { target := 613, numerator := 31849973590107045643312693248 }, { target := 616, numerator := 114563407851556081842146770944 }, { target := 618, numerator := 31849984215431632100014424064 }, { target := 880, numerator := 31849973590107045643312693248 }, { target := 883, numerator := 114563407851556081842146770944 }, { target := 885, numerator := 31849984215431632100014424064 }, { target := 906, numerator := 39299900499479652445716480 }, { target := 907, numerator := 589498507492194786685747200 }, { target := 908, numerator := 1034897379819630847737200640 }, { target := 909, numerator := 39299900499479652445716480 }, { target := 910, numerator := 654998341657994207428608000 }, { target := 911, numerator := 39299900499479652445716480 }, { target := 912, numerator := 1034897379819630847737200640 }, { target := 913, numerator := 1028347396403050905662914560 }, { target := 914, numerator := 654998341657994207428608000 }, { target := 915, numerator := 15870609818373199645995171840 }, { target := 916, numerator := 1015247429569891021514342400 }, { target := 917, numerator := 589498507492194786685747200 }, { target := 918, numerator := 1034897379819630847737200640 }, { target := 919, numerator := 39299900499479652445716480 }, { target := 920, numerator := 1015247429569891021514342400 }, { target := 921, numerator := 39299900499479652445716480 }, { target := 922, numerator := 1034897379819630847737200640 }, { target := 923, numerator := 1034897379819630847737200640 }, { target := 924, numerator := 39299900499479652445716480 }, { target := 925, numerator := 738136477208429027812966400 }, { target := 927, numerator := 28791296897006103196755558400 }, { target := 930, numerator := 28791286336459041980337356800 }, { target := 937, numerator := 738139997390782766619033600 }, { target := 976, numerator := 31849973590107045643312693248 }, { target := 979, numerator := 114563407851556081842146770944 }, { target := 981, numerator := 31849984215431632100014424064 }, { target := 1002, numerator := 31849973590107045643312693248 }, { target := 1005, numerator := 114563407851556081842146770944 }, { target := 1007, numerator := 31849984215431632100014424064 }]

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
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 79, numerator := 26293036412801628512200949760 }, { target := 80, numerator := 19719777309601221384150712320 }, { target := 81, numerator := 20815320493467955905492418560 }, { target := 82, numerator := 26840808004734995772871802880 }, { target := 83, numerator := 359338164308288923000079646720 }, { target := 84, numerator := 628294015947572247989468528640 }, { target := 85, numerator := 19172005717667854123479859200 }, { target := 86, numerator := 359338164308288923000079646720 }, { target := 87, numerator := 20267548901534588644821565440 }, { target := 88, numerator := 20815320493467955905492418560 }, { target := 89, numerator := 20815320493467955905492418560 }, { target := 90, numerator := 20267548901534588644821565440 }, { target := 91, numerator := 628294015947572247989468528640 }, { target := 92, numerator := 20267548901534588644821565440 }, { target := 93, numerator := 26293036412801628512200949760 }, { target := 94, numerator := 26840808004734995772871802880 }, { target := 154, numerator := 279637499217475054288270000128 }, { target := 155, numerator := 209728124413106290716202500096 }, { target := 156, numerator := 221379686880501084644880416768 }, { target := 157, numerator := 285463280451172451252608958464 }, { target := 158, numerator := 3821712489305492408606356668416 }, { target := 159, numerator := 6682171075050914318096785211392 }, { target := 160, numerator := 203902343179408893751863541760 }, { target := 161, numerator := 3821712489305492408606356668416 }, { target := 162, numerator := 215553905646803687680541458432 }, { target := 163, numerator := 221379686880501084644880416768 }, { target := 164, numerator := 221379686880501084644880416768 }, { target := 165, numerator := 215553905646803687680541458432 }, { target := 166, numerator := 6682171075050914318096785211392 }, { target := 167, numerator := 215553905646803687680541458432 }, { target := 168, numerator := 279637499217475054288270000128 }, { target := 169, numerator := 285463280451172451252608958464 }, { target := 492, numerator := 26293115660014169168434692096 }, { target := 493, numerator := 19719836745010626876326019072 }, { target := 494, numerator := 20815383230844550591677464576 }, { target := 495, numerator := 26840888902931131026110414848 }, { target := 496, numerator := 359339247353526978635274125312 }, { target := 497, numerator := 628295909625755250754053996544 }, { target := 498, numerator := 19172063502093665018650296320 }, { target := 499, numerator := 359339247353526978635274125312 }, { target := 500, numerator := 20267609987927588734001741824 }, { target := 501, numerator := 20815383230844550591677464576 }, { target := 502, numerator := 20815383230844550591677464576 }, { target := 503, numerator := 20267609987927588734001741824 }, { target := 504, numerator := 628295909625755250754053996544 }, { target := 505, numerator := 20267609987927588734001741824 }, { target := 506, numerator := 26293115660014169168434692096 }, { target := 507, numerator := 26840888902931131026110414848 }, { target := 890, numerator := 81624628916875920754606080 }, { target := 891, numerator := 61218471687656940565954560 }, { target := 892, numerator := 64619497892526770597396480 }, { target := 893, numerator := 83325142019310835770327040 }, { target := 894, numerator := 1115536595197304250312949760 }, { target := 895, numerator := 1950488528492847523031941120 }, { target := 896, numerator := 59517958585222025550233600 }, { target := 897, numerator := 1115536595197304250312949760 }, { target := 898, numerator := 62918984790091855581675520 }, { target := 899, numerator := 64619497892526770597396480 }, { target := 900, numerator := 64619497892526770597396480 }, { target := 901, numerator := 62918984790091855581675520 }, { target := 902, numerator := 1950488528492847523031941120 }, { target := 903, numerator := 62918984790091855581675520 }, { target := 904, numerator := 81624628916875920754606080 }, { target := 905, numerator := 83325142019310835770327040 }]

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
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot8.Left4.expected,
    Slot8.Left5.expected,
    Slot8.Left6.expected,
    Slot8.Left7.expected,
    Slot8.Left8.expected,
    Slot8.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 83556284505377220719542272 }, { target := 122, numerator := 9875816377681759191718428672 }, { target := 124, numerator := 93719528812127209674655137792 }, { target := 132, numerator := 9875823151051125710624129024 }, { target := 139, numerator := 83556284505377220719542272 }, { target := 196, numerator := 14654987287462648448387383296 }, { target := 197, numerator := 1732125408938301726093786218496 }, { target := 199, numerator := 16437524854762127013562502086656 }, { target := 207, numerator := 1732126596923652525595119583232 }, { target := 214, numerator := 14654987287462648448387383296 }, { target := 250, numerator := 545319915883035846644858880 }, { target := 252, numerator := 21341073122420210732235751424 }, { target := 255, numerator := 21341073122420210732235751424 }, { target := 262, numerator := 545319915883035846644858880 }, { target := 466, numerator := 13210814736392255510654484480 }, { target := 468, numerator := 517004706933470266448679010304 }, { target := 471, numerator := 517004706933470266448679010304 }, { target := 478, numerator := 13210814736392255510654484480 }, { target := 508, numerator := 14654989044433956675929505792 }, { target := 509, numerator := 1732125616601030192602590216192 }, { target := 511, numerator := 16437526825440025369792072384512 }, { target := 519, numerator := 1732126804586523418442139172864 }, { target := 526, numerator := 14654989044433956675929505792 }, { target := 562, numerator := 10009259101207980540029829120 }, { target := 564, numerator := 391711955053454835698133630976 }, { target := 567, numerator := 391711955053454835698133630976 }, { target := 574, numerator := 10009259101207980540029829120 }, { target := 597, numerator := 11152671828059507315252920320 }, { target := 599, numerator := 436459366439174632394756980736 }, { target := 602, numerator := 436459366439174632394756980736 }, { target := 609, numerator := 11152671828059507315252920320 }, { target := 733, numerator := 545319915883035846644858880 }, { target := 735, numerator := 21341073122420210732235751424 }, { target := 738, numerator := 21341073122420210732235751424 }, { target := 745, numerator := 545319915883035846644858880 }, { target := 829, numerator := 11152671828059507315252920320 }, { target := 831, numerator := 436459366439174632394756980736 }, { target := 834, numerator := 436459366439174632394756980736 }, { target := 841, numerator := 11152671828059507315252920320 }, { target := 864, numerator := 11135080863031022287941795840 }, { target := 866, numerator := 435770944725548173984039698432 }, { target := 869, numerator := 435770944725548173984039698432 }, { target := 876, numerator := 11135080863031022287941795840 }, { target := 906, numerator := 83554527534068993177419776 }, { target := 907, numerator := 9875608714953292682914430976 }, { target := 909, numerator := 93717558134228853445084839936 }, { target := 917, numerator := 9875615488180232863604539392 }, { target := 924, numerator := 83554527534068993177419776 }, { target := 925, numerator := 545319915883035846644858880 }, { target := 927, numerator := 21341073122420210732235751424 }, { target := 930, numerator := 21341073122420210732235751424 }, { target := 937, numerator := 545319915883035846644858880 }, { target := 960, numerator := 13210814736392255510654484480 }, { target := 962, numerator := 517004706933470266448679010304 }, { target := 965, numerator := 517004706933470266448679010304 }, { target := 972, numerator := 13210814736392255510654484480 }, { target := 986, numerator := 545319915883035846644858880 }, { target := 988, numerator := 21341073122420210732235751424 }, { target := 991, numerator := 21341073122420210732235751424 }, { target := 998, numerator := 545319915883035846644858880 }]

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

namespace RouteChunk7

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 537849780049021656964792320 }, { target := 11, numerator := 13029844671510169818727710720 }, { target := 12, numerator := 9872145962835268477837639680 }, { target := 13, numerator := 10999895501647733242441236480 }, { target := 14, numerator := 537849780049021656964792320 }, { target := 15, numerator := 10999895501647733242441236480 }, { target := 16, numerator := 10982545508742926092216565760 }, { target := 17, numerator := 537849780049021656964792320 }, { target := 18, numerator := 13029844671510169818727710720 }, { target := 19, numerator := 537849780049021656964792320 }, { target := 34, numerator := 83060891514238620596699136 }, { target := 35, numerator := 14568100011054767133475995648 }, { target := 40, numerator := 14568101757609249422910160896 }, { target := 48, numerator := 83059144959756331162533888 }, { target := 55, numerator := 21048729654989796886588686336 }, { target := 56, numerator := 509922450674107660058971078656 }, { target := 57, numerator := 386346037860941755757063307264 }, { target := 58, numerator := 430480471008501007293458939904 }, { target := 59, numerator := 21048729654989796886588686336 }, { target := 60, numerator := 430480471008501007293458939904 }, { target := 61, numerator := 429801479729307788039052853248 }, { target := 62, numerator := 21048729654989796886588686336 }, { target := 63, numerator := 509922450674107660058971078656 }, { target := 64, numerator := 21048729654989796886588686336 }, { target := 79, numerator := 9817264106667835718249742336 }, { target := 80, numerator := 1721855890703489660524060213248 }, { target := 85, numerator := 1721856097135016179602970116096 }, { target := 93, numerator := 9817057675141316639339839488 }, { target := 144, numerator := 21048729654989796886588686336 }, { target := 145, numerator := 509922450674107660058971078656 }, { target := 146, numerator := 386346037860941755757063307264 }, { target := 147, numerator := 430480471008501007293458939904 }, { target := 148, numerator := 21048729654989796886588686336 }, { target := 149, numerator := 430480471008501007293458939904 }, { target := 150, numerator := 429801479729307788039052853248 }, { target := 151, numerator := 21048729654989796886588686336 }, { target := 152, numerator := 509922450674107660058971078656 }, { target := 153, numerator := 21048729654989796886588686336 }, { target := 154, numerator := 93163879431818155071840976896 }, { target := 155, numerator := 16340069173805039303995925987328 }, { target := 160, numerator := 16340071132799076602777494880256 }, { target := 168, numerator := 93161920437780856290272083968 }, { target := 482, numerator := 537849780049021656964792320 }, { target := 483, numerator := 13029844671510169818727710720 }, { target := 484, numerator := 9872145962835268477837639680 }, { target := 485, numerator := 10999895501647733242441236480 }, { target := 486, numerator := 537849780049021656964792320 }, { target := 487, numerator := 10999895501647733242441236480 }, { target := 488, numerator := 10982545508742926092216565760 }, { target := 489, numerator := 537849780049021656964792320 }, { target := 490, numerator := 13029844671510169818727710720 }, { target := 491, numerator := 537849780049021656964792320 }, { target := 492, numerator := 9817270839878885834869440512 }, { target := 493, numerator := 1721857071645449052123211759616 }, { target := 498, numerator := 1721857278077117153115407122432 }, { target := 506, numerator := 9817064408210784842674077696 }, { target := 890, numerator := 83060891514238620596699136 }, { target := 891, numerator := 14568100011054767133475995648 }, { target := 896, numerator := 14568101757609249422910160896 }, { target := 904, numerator := 83059144959756331162533888 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk7

namespace RouteChunk8

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left2.expected,
    Slot11.Left3.expected,
    Slot11.Left4.expected,
    Slot11.Left5.expected,
    Slot11.Left6.expected,
    Slot11.Left7.expected,
    Slot11.Left8.expected,
    Slot11.Left9.expected,
    Slot11.Left10.expected,
    Slot11.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 82080632430378020870553600 }, { target := 122, numerator := 26439924884381525878190899200 }, { target := 124, numerator := 281199719883494467999377653760 }, { target := 132, numerator := 26440004574315924303453880320 }, { target := 139, numerator := 82080632430378020870553600 }, { target := 196, numerator := 61560474322783515652915200 }, { target := 197, numerator := 19829943663286144408643174400 }, { target := 199, numerator := 210899789912620850999533240320 }, { target := 207, numerator := 19830003430736943227590410240 }, { target := 214, numerator := 61560474322783515652915200 }, { target := 231, numerator := 64980500674049266522521600 }, { target := 232, numerator := 20931607200135374653567795200 }, { target := 234, numerator := 222616444907766453832840642560 }, { target := 242, numerator := 20931670288000106740234321920 }, { target := 249, numerator := 64980500674049266522521600 }, { target := 337, numerator := 83790645606010896305356800 }, { target := 338, numerator := 26990756652806141000653209600 }, { target := 340, numerator := 287058047381067269416031354880 }, { target := 348, numerator := 26990838002947506059775836160 }, { target := 355, numerator := 83790645606010896305356800 }, { target := 412, numerator := 1121768643215166285230899200 }, { target := 413, numerator := 361345640086547520335275622400 }, { target := 415, numerator := 3843062838407757729324827934720 }, { target := 423, numerator := 361346729182317632147203031040 }, { target := 430, numerator := 1121768643215166285230899200 }, { target := 447, numerator := 1961385112450908123719270400 }, { target := 448, numerator := 631804038383033545464270028800 }, { target := 450, numerator := 6719501639716003224901795184640 }, { target := 458, numerator := 631805942640424274501283348480 }, { target := 465, numerator := 1961385112450908123719270400 }, { target := 508, numerator := 59850461147150640218112000 }, { target := 509, numerator := 19279111894861529286180864000 }, { target := 511, numerator := 205041462415048049582879539200 }, { target := 519, numerator := 19279170002105361471268454400 }, { target := 526, numerator := 59850461147150640218112000 }, { target := 543, numerator := 1121768643215166285230899200 }, { target := 544, numerator := 361345640086547520335275622400 }, { target := 546, numerator := 3843062838407757729324827934720 }, { target := 554, numerator := 361346729182317632147203031040 }, { target := 561, numerator := 1121768643215166285230899200 }, { target := 578, numerator := 63270487498416391087718400 }, { target := 579, numerator := 20380775431710759531105484800 }, { target := 581, numerator := 216758117410193652416186941440 }, { target := 589, numerator := 20380836859368524983912366080 }, { target := 596, numerator := 63270487498416391087718400 }, { target := 679, numerator := 64980500674049266522521600 }, { target := 680, numerator := 20931607200135374653567795200 }, { target := 682, numerator := 222616444907766453832840642560 }, { target := 690, numerator := 20931670288000106740234321920 }, { target := 697, numerator := 64980500674049266522521600 }, { target := 714, numerator := 64980500674049266522521600 }, { target := 715, numerator := 20931607200135374653567795200 }, { target := 717, numerator := 222616444907766453832840642560 }, { target := 725, numerator := 20931670288000106740234321920 }, { target := 732, numerator := 64980500674049266522521600 }, { target := 775, numerator := 63270487498416391087718400 }, { target := 776, numerator := 20380775431710759531105484800 }, { target := 778, numerator := 216758117410193652416186941440 }, { target := 786, numerator := 20380836859368524983912366080 }, { target := 793, numerator := 63270487498416391087718400 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk8

namespace RouteChunk9

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot11.Left12.expected,
    Slot11.Left13.expected,
    Slot11.Left14.expected,
    Slot11.Left15.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left2.expected,
    Slot14.Left3.expected,
    Slot14.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 31849973590107045643312693248 }, { target := 2, numerator := 31849973590107045643312693248 }, { target := 3, numerator := 31849973590107045643312693248 }, { target := 4, numerator := 31849973590107045643312693248 }, { target := 10, numerator := 776173034345964753725161472 }, { target := 12, numerator := 35081609106835583080356380672 }, { target := 17, numerator := 780315704477482115116564480 }, { target := 34, numerator := 38426569377268993502478336 }, { target := 35, numerator := 7621327423701021457435852800 }, { target := 40, numerator := 7621327423701021457435852800 }, { target := 48, numerator := 38426569377268993502478336 }, { target := 51, numerator := 114563407851556081842146770944 }, { target := 52, numerator := 114563407851556081842146770944 }, { target := 53, numerator := 114563407851556081842146770944 }, { target := 54, numerator := 114563407851556081842146770944 }, { target := 55, numerator := 30274927422391310550808133632 }, { target := 57, numerator := 1368371642110850462063716728832 }, { target := 62, numerator := 30436513862549309093713018880 }, { target := 79, numerator := 576398540659034902537175040 }, { target := 80, numerator := 114319911355515321861537792000 }, { target := 85, numerator := 114319911355515321861537792000 }, { target := 93, numerator := 576398540659034902537175040 }, { target := 105, numerator := 1011899660268083495565262848 }, { target := 106, numerator := 200694955490793565045810790400 }, { target := 111, numerator := 200694955490793565045810790400 }, { target := 119, numerator := 1011899660268083495565262848 }, { target := 140, numerator := 31849984215431632100014424064 }, { target := 141, numerator := 31849984215431632100014424064 }, { target := 142, numerator := 31849984215431632100014424064 }, { target := 143, numerator := 31849984215431632100014424064 }, { target := 144, numerator := 30274916317653758685913022464 }, { target := 146, numerator := 1368371140196915308683920932864 }, { target := 151, numerator := 30436502698542415807785205760 }, { target := 154, numerator := 38426569377268993502478336 }, { target := 155, numerator := 7621327423701021457435852800 }, { target := 160, numerator := 7621327423701021457435852800 }, { target := 168, numerator := 38426569377268993502478336 }, { target := 180, numerator := 640442822954483225041305600 }, { target := 181, numerator := 127022123728350357623930880000 }, { target := 186, numerator := 127022123728350357623930880000 }, { target := 194, numerator := 640442822954483225041305600 }, { target := 482, numerator := 776176735925148708690198528 }, { target := 484, numerator := 35081776411480634206954979328 }, { target := 489, numerator := 780319425813113210425835520 }, { target := 810, numerator := 1961385112450908123719270400 }, { target := 811, numerator := 631804038383033545464270028800 }, { target := 813, numerator := 6719501639716003224901795184640 }, { target := 821, numerator := 631805942640424274501283348480 }, { target := 828, numerator := 1961385112450908123719270400 }, { target := 845, numerator := 63270487498416391087718400 }, { target := 846, numerator := 20380775431710759531105484800 }, { target := 848, numerator := 216758117410193652416186941440 }, { target := 856, numerator := 20380836859368524983912366080 }, { target := 863, numerator := 63270487498416391087718400 }, { target := 906, numerator := 82080632430378020870553600 }, { target := 907, numerator := 26439924884381525878190899200 }, { target := 909, numerator := 281199719883494467999377653760 }, { target := 917, numerator := 26440004574315924303453880320 }, { target := 924, numerator := 82080632430378020870553600 }, { target := 941, numerator := 83790645606010896305356800 }, { target := 942, numerator := 26990756652806141000653209600 }, { target := 944, numerator := 287058047381067269416031354880 }, { target := 952, numerator := 26990838002947506059775836160 }, { target := 959, numerator := 83790645606010896305356800 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk9

namespace RouteChunk10

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot14.Left5.expected,
    Slot14.Left6.expected,
    Slot14.Left7.expected,
    Slot14.Left8.expected,
    Slot14.Left9.expected,
    Slot14.Left10.expected,
    Slot14.Left11.expected,
    Slot14.Left12.expected,
    Slot14.Left13.expected,
    Slot14.Left14.expected,
    Slot14.Left15.expected,
    Slot14.Left16.expected,
    Slot14.Left17.expected,
    Slot14.Left18.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 39614076534765685927126761472 }, { target := 1, numerator := 3517797193909415876375871488 }, { target := 2, numerator := 3507531248791003184129638400 }, { target := 3, numerator := 3483577376848040235555094528 }, { target := 4, numerator := 3507531248791003184129638400 }, { target := 50, numerator := 39614085979498651666417188864 }, { target := 215, numerator := 38426569377268993502478336 }, { target := 216, numerator := 7621327423701021457435852800 }, { target := 221, numerator := 7621327423701021457435852800 }, { target := 229, numerator := 38426569377268993502478336 }, { target := 295, numerator := 1011899660268083495565262848 }, { target := 296, numerator := 200694955490793565045810790400 }, { target := 301, numerator := 200694955490793565045810790400 }, { target := 309, numerator := 1011899660268083495565262848 }, { target := 321, numerator := 1005495232038538663314849792 }, { target := 322, numerator := 199424734253510061469571481600 }, { target := 327, numerator := 199424734253510061469571481600 }, { target := 335, numerator := 1005495232038538663314849792 }, { target := 370, numerator := 640442822954483225041305600 }, { target := 371, numerator := 127022123728350357623930880000 }, { target := 376, numerator := 127022123728350357623930880000 }, { target := 384, numerator := 640442822954483225041305600 }, { target := 396, numerator := 15517929600187128542750834688 }, { target := 397, numerator := 3077746057937929165227845222400 }, { target := 402, numerator := 3077746057937929165227845222400 }, { target := 410, numerator := 15517929600187128542750834688 }, { target := 431, numerator := 992686375579448998814023680 }, { target := 432, numerator := 196884291778943054317092864000 }, { target := 437, numerator := 196884291778943054317092864000 }, { target := 445, numerator := 992686375579448998814023680 }, { target := 492, numerator := 576398540659034902537175040 }, { target := 493, numerator := 114319911355515321861537792000 }, { target := 498, numerator := 114319911355515321861537792000 }, { target := 506, numerator := 576398540659034902537175040 }, { target := 527, numerator := 1011899660268083495565262848 }, { target := 528, numerator := 200694955490793565045810790400 }, { target := 533, numerator := 200694955490793565045810790400 }, { target := 541, numerator := 1011899660268083495565262848 }, { target := 637, numerator := 38426569377268993502478336 }, { target := 638, numerator := 7621327423701021457435852800 }, { target := 643, numerator := 7621327423701021457435852800 }, { target := 651, numerator := 38426569377268993502478336 }, { target := 663, numerator := 992686375579448998814023680 }, { target := 664, numerator := 196884291778943054317092864000 }, { target := 669, numerator := 196884291778943054317092864000 }, { target := 677, numerator := 992686375579448998814023680 }, { target := 698, numerator := 38426569377268993502478336 }, { target := 699, numerator := 7621327423701021457435852800 }, { target := 704, numerator := 7621327423701021457435852800 }, { target := 712, numerator := 38426569377268993502478336 }, { target := 759, numerator := 1011899660268083495565262848 }, { target := 760, numerator := 200694955490793565045810790400 }, { target := 765, numerator := 200694955490793565045810790400 }, { target := 773, numerator := 1011899660268083495565262848 }, { target := 794, numerator := 1011899660268083495565262848 }, { target := 795, numerator := 200694955490793565045810790400 }, { target := 800, numerator := 200694955490793565045810790400 }, { target := 808, numerator := 1011899660268083495565262848 }, { target := 890, numerator := 38426569377268993502478336 }, { target := 891, numerator := 7621327423701021457435852800 }, { target := 896, numerator := 7621327423701021457435852800 }, { target := 904, numerator := 38426569377268993502478336 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk10

namespace RouteChunk11

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left2.expected,
    Slot17.Left3.expected,
    Slot17.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 15810482984647572175454208 }, { target := 11, numerator := 387611840913940479140167680 }, { target := 12, numerator := 286628756044255985890492416 }, { target := 13, numerator := 319779768754000895290638336 }, { target := 14, numerator := 15810482984647572175454208 }, { target := 15, numerator := 319269753173850973607559168 }, { target := 16, numerator := 324879924555500112121430016 }, { target := 17, numerator := 15810482984647572175454208 }, { target := 18, numerator := 387611840913940479140167680 }, { target := 19, numerator := 15810482984647572175454208 }, { target := 24, numerator := 18006383399181957199822848 }, { target := 25, numerator := 441446818818654434576302080 }, { target := 26, numerator := 326438305494847095041949696 }, { target := 27, numerator := 364193625525389908525449216 }, { target := 28, numerator := 18006383399181957199822848 }, { target := 29, numerator := 363612774447996942164164608 }, { target := 30, numerator := 370002136299319572138295296 }, { target := 31, numerator := 18006383399181957199822848 }, { target := 32, numerator := 441446818818654434576302080 }, { target := 33, numerator := 18006383399181957199822848 }, { target := 51, numerator := 12848818678405895648654131200 }, { target := 52, numerator := 12811322125842454318940160000 }, { target := 53, numerator := 12723830169861091216274227200 }, { target := 54, numerator := 12811322125842454318940160000 }, { target := 55, numerator := 14053762653020064155959296 }, { target := 56, numerator := 344543858590169314791260160 }, { target := 57, numerator := 254781116483783098569326592 }, { target := 58, numerator := 284248683336889684702789632 }, { target := 59, numerator := 14053762653020064155959296 }, { target := 60, numerator := 283795336154534198762274816 }, { target := 61, numerator := 288782155160444544107937792 }, { target := 62, numerator := 14053762653020064155959296 }, { target := 63, numerator := 344543858590169314791260160 }, { target := 64, numerator := 14053762653020064155959296 }, { target := 69, numerator := 188408255567050235090829312 }, { target := 70, numerator := 4619041104224457376420331520 }, { target := 71, numerator := 3415659342860717165195034624 }, { target := 72, numerator := 3810708910985177335546773504 }, { target := 73, numerator := 188408255567050235090829312 }, { target := 74, numerator := 3804631225321724102156746752 }, { target := 75, numerator := 3871485767619709669447041024 }, { target := 76, numerator := 188408255567050235090829312 }, { target := 77, numerator := 4619041104224457376420331520 }, { target := 78, numerator := 188408255567050235090829312 }, { target := 95, numerator := 16688843150461326185201664 }, { target := 96, numerator := 409145832075826061314621440 }, { target := 97, numerator := 302552575824492429551075328 }, { target := 98, numerator := 337545311462556500584562688 }, { target := 99, numerator := 16688843150461326185201664 }, { target := 100, numerator := 337006961683509361030201344 }, { target := 101, numerator := 342928809253027896128176128 }, { target := 102, numerator := 16688843150461326185201664 }, { target := 103, numerator := 409145832075826061314621440 }, { target := 104, numerator := 16688843150461326185201664 }, { target := 140, numerator := 3517796008706109140537180160 }, { target := 141, numerator := 3507530067046460962111488000 }, { target := 142, numerator := 3483576203173948545784872960 }, { target := 143, numerator := 3507530067046460962111488000 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk11

namespace RouteChunk12

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot17.Left5.expected,
    Slot17.Left6.expected,
    Slot17.Left7.expected,
    Slot17.Left8.expected,
    Slot17.Left9.expected,
    Slot17.Left10.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 144, numerator := 14053762653020064155959296 }, { target := 145, numerator := 344543858590169314791260160 }, { target := 146, numerator := 254781116483783098569326592 }, { target := 147, numerator := 284248683336889684702789632 }, { target := 148, numerator := 14053762653020064155959296 }, { target := 149, numerator := 283795336154534198762274816 }, { target := 150, numerator := 288782155160444544107937792 }, { target := 151, numerator := 14053762653020064155959296 }, { target := 152, numerator := 344543858590169314791260160 }, { target := 153, numerator := 14053762653020064155959296 }, { target := 170, numerator := 16688843150461326185201664 }, { target := 171, numerator := 409145832075826061314621440 }, { target := 172, numerator := 302552575824492429551075328 }, { target := 173, numerator := 337545311462556500584562688 }, { target := 174, numerator := 16688843150461326185201664 }, { target := 175, numerator := 337006961683509361030201344 }, { target := 176, numerator := 342928809253027896128176128 }, { target := 177, numerator := 16688843150461326185201664 }, { target := 178, numerator := 409145832075826061314621440 }, { target := 179, numerator := 16688843150461326185201664 }, { target := 271, numerator := 16249663067554449180327936 }, { target := 272, numerator := 398378836494883270227394560 }, { target := 273, numerator := 294590665934374207720783872 }, { target := 274, numerator := 328662540108278697937600512 }, { target := 275, numerator := 16249663067554449180327936 }, { target := 276, numerator := 328138357428680167318880256 }, { target := 277, numerator := 333904366904264004124803072 }, { target := 278, numerator := 16249663067554449180327936 }, { target := 279, numerator := 398378836494883270227394560 }, { target := 280, numerator := 16249663067554449180327936 }, { target := 285, numerator := 613973755903814052813471744 }, { target := 286, numerator := 15052259822158021939943178240 }, { target := 287, numerator := 11130750026385274118747455488 }, { target := 288, numerator := 12418114353280368100453122048 }, { target := 289, numerator := 613973755903814052813471744 }, { target := 290, numerator := 12398308748251212808426881024 }, { target := 291, numerator := 12616170403571921020715532288 }, { target := 292, numerator := 613973755903814052813471744 }, { target := 293, numerator := 15052259822158021939943178240 }, { target := 294, numerator := 613973755903814052813471744 }, { target := 311, numerator := 16249663067554449180327936 }, { target := 312, numerator := 398378836494883270227394560 }, { target := 313, numerator := 294590665934374207720783872 }, { target := 314, numerator := 328662540108278697937600512 }, { target := 315, numerator := 16249663067554449180327936 }, { target := 316, numerator := 328138357428680167318880256 }, { target := 317, numerator := 333904366904264004124803072 }, { target := 318, numerator := 16249663067554449180327936 }, { target := 319, numerator := 398378836494883270227394560 }, { target := 320, numerator := 16249663067554449180327936 }, { target := 360, numerator := 188408255567050235090829312 }, { target := 361, numerator := 4619041104224457376420331520 }, { target := 362, numerator := 3415659342860717165195034624 }, { target := 363, numerator := 3810708910985177335546773504 }, { target := 364, numerator := 188408255567050235090829312 }, { target := 365, numerator := 3804631225321724102156746752 }, { target := 366, numerator := 3871485767619709669447041024 }, { target := 367, numerator := 188408255567050235090829312 }, { target := 368, numerator := 4619041104224457376420331520 }, { target := 369, numerator := 188408255567050235090829312 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk12

namespace RouteChunk13

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot17.Left11.expected,
    Slot17.Left12.expected,
    Slot17.Left13.expected,
    Slot17.Left14.expected,
    Slot17.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 386, numerator := 613973755903814052813471744 }, { target := 387, numerator := 15052259822158021939943178240 }, { target := 388, numerator := 11130750026385274118747455488 }, { target := 389, numerator := 12418114353280368100453122048 }, { target := 390, numerator := 613973755903814052813471744 }, { target := 391, numerator := 12398308748251212808426881024 }, { target := 392, numerator := 12616170403571921020715532288 }, { target := 393, numerator := 613973755903814052813471744 }, { target := 394, numerator := 15052259822158021939943178240 }, { target := 395, numerator := 613973755903814052813471744 }, { target := 482, numerator := 15810482984647572175454208 }, { target := 483, numerator := 387611840913940479140167680 }, { target := 484, numerator := 286628756044255985890492416 }, { target := 485, numerator := 319779768754000895290638336 }, { target := 486, numerator := 15810482984647572175454208 }, { target := 487, numerator := 319269753173850973607559168 }, { target := 488, numerator := 324879924555500112121430016 }, { target := 489, numerator := 15810482984647572175454208 }, { target := 490, numerator := 387611840913940479140167680 }, { target := 491, numerator := 15810482984647572175454208 }, { target := 627, numerator := 16249663067554449180327936 }, { target := 628, numerator := 398378836494883270227394560 }, { target := 629, numerator := 294590665934374207720783872 }, { target := 630, numerator := 328662540108278697937600512 }, { target := 631, numerator := 16249663067554449180327936 }, { target := 632, numerator := 328138357428680167318880256 }, { target := 633, numerator := 333904366904264004124803072 }, { target := 634, numerator := 16249663067554449180327936 }, { target := 635, numerator := 398378836494883270227394560 }, { target := 636, numerator := 16249663067554449180327936 }, { target := 653, numerator := 16249663067554449180327936 }, { target := 654, numerator := 398378836494883270227394560 }, { target := 655, numerator := 294590665934374207720783872 }, { target := 656, numerator := 328662540108278697937600512 }, { target := 657, numerator := 16249663067554449180327936 }, { target := 658, numerator := 328138357428680167318880256 }, { target := 659, numerator := 333904366904264004124803072 }, { target := 660, numerator := 16249663067554449180327936 }, { target := 661, numerator := 398378836494883270227394560 }, { target := 662, numerator := 16249663067554449180327936 }, { target := 749, numerator := 18006383399181957199822848 }, { target := 750, numerator := 441446818818654434576302080 }, { target := 751, numerator := 326438305494847095041949696 }, { target := 752, numerator := 364193625525389908525449216 }, { target := 753, numerator := 18006383399181957199822848 }, { target := 754, numerator := 363612774447996942164164608 }, { target := 755, numerator := 370002136299319572138295296 }, { target := 756, numerator := 18006383399181957199822848 }, { target := 757, numerator := 441446818818654434576302080 }, { target := 758, numerator := 18006383399181957199822848 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk13

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14.Parent0
