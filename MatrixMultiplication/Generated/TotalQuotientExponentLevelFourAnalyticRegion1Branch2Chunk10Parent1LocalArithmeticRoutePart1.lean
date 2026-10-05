import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk10Parent1LocalData

/-! Line-budgeted sparse route chunks, part 1, for region 1, branch 2,
parent 43; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk19

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot25.Left0.expected,
    Slot25.Left3.expected,
    Slot25.Left5.expected,
    Slot26.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 7737127090208034089074688000 }, { target := 5, numerator := 155052026887769003145056747520 }, { target := 6, numerator := 260276955314598266756472504320 }, { target := 7, numerator := 249754462471915340395330928640 }, { target := 8, numerator := 7737127090208034089074688000 }, { target := 9, numerator := 249754462471915340395330928640 }, { target := 10, numerator := 166812460064885214960450273280 }, { target := 11, numerator := 8046612173816355452637675520 }, { target := 12, numerator := 155052026887769003145056747520 }, { target := 13, numerator := 7427642006599712725511700480 }, { target := 14, numerator := 78181505057243634296401428480 }, { target := 15, numerator := 80415262344593452419155755008 }, { target := 16, numerator := 78181505057243634296401428480 }, { target := 17, numerator := 69246475907844361805384122368 }, { target := 18, numerator := 3241181823944586096116527792128 }, { target := 19, numerator := 882334128503178158487958978560 }, { target := 20, numerator := 80415262344593452419155755008 }, { target := 21, numerator := 3241181823944586096116527792128 }, { target := 22, numerator := 78181505057243634296401428480 }, { target := 23, numerator := 78181505057243634296401428480 }, { target := 24, numerator := 67012718620494543682629795840 }, { target := 25, numerator := 78181505057243634296401428480 }, { target := 26, numerator := 882334128503178158487958978560 }, { target := 27, numerator := 67012718620494543682629795840 }, { target := 28, numerator := 78181505057243634296401428480 }, { target := 29, numerator := 69246475907844361805384122368 }, { target := 136, numerator := 284362986684221943338080665600 }, { target := 137, numerator := 292487643446628284576311541760 }, { target := 138, numerator := 284362986684221943338080665600 }, { target := 139, numerator := 251864359634596578385157160960 }, { target := 140, numerator := 11788876962251601136673001308160 }, { target := 141, numerator := 3209239421150504789101196083200 }, { target := 142, numerator := 292487643446628284576311541760 }, { target := 143, numerator := 11788876962251601136673001308160 }, { target := 144, numerator := 284362986684221943338080665600 }, { target := 145, numerator := 284362986684221943338080665600 }, { target := 146, numerator := 243739702872190237146926284800 }, { target := 147, numerator := 284362986684221943338080665600 }, { target := 148, numerator := 3209239421150504789101196083200 }, { target := 149, numerator := 243739702872190237146926284800 }, { target := 150, numerator := 284362986684221943338080665600 }, { target := 151, numerator := 251864359634596578385157160960 }, { target := 267, numerator := 78181505057243634296401428480 }, { target := 268, numerator := 80415262344593452419155755008 }, { target := 269, numerator := 78181505057243634296401428480 }, { target := 270, numerator := 69246475907844361805384122368 }, { target := 271, numerator := 3241181823944586096116527792128 }, { target := 272, numerator := 882334128503178158487958978560 }, { target := 273, numerator := 80415262344593452419155755008 }, { target := 274, numerator := 3241181823944586096116527792128 }, { target := 275, numerator := 78181505057243634296401428480 }, { target := 276, numerator := 78181505057243634296401428480 }, { target := 277, numerator := 67012718620494543682629795840 }, { target := 278, numerator := 78181505057243634296401428480 }, { target := 279, numerator := 882334128503178158487958978560 }, { target := 280, numerator := 67012718620494543682629795840 }, { target := 281, numerator := 78181505057243634296401428480 }, { target := 282, numerator := 69246475907844361805384122368 }]

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
    Slot26.Left2.expected,
    Slot27.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 20696810031802451470969733120 }, { target := 1, numerator := 18917271225329717325802242048 }, { target := 2, numerator := 20696810031802451470969733120 }, { target := 3, numerator := 18917271225329717325802242048 }, { target := 126, numerator := 7737123400859219347164364800 }, { target := 127, numerator := 155051952953218755717173870592 }, { target := 128, numerator := 260276831204904138838609231872 }, { target := 129, numerator := 249754343379735600526465695744 }, { target := 130, numerator := 7737123400859219347164364800 }, { target := 131, numerator := 249754343379735600526465695744 }, { target := 132, numerator := 166812380522524769124863705088 }, { target := 133, numerator := 8046608336893588121050939392 }, { target := 134, numerator := 155051952953218755717173870592 }, { target := 135, numerator := 7427638464824850573277790208 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent1
