import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk1Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 33; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk1.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 40022899209825270919856128 }, { target := 27, numerator := 1149393285124709564918267904 }, { target := 29, numerator := 11916072065242622469928386560 }, { target := 37, numerator := 1149339606572132148273217536 }, { target := 44, numerator := 40039940020167307950030848 }, { target := 80, numerator := 45495466860862193155440640 }, { target := 82, numerator := 1880432843268579259083390976 }, { target := 85, numerator := 1880427358966222932295024640 }, { target := 92, numerator := 45499221054756169759850496 }, { target := 131, numerator := 40022899209825270919856128 }, { target := 134, numerator := 141723845528693891538092032 }, { target := 136, numerator := 40076976061316682164994048 }, { target := 157, numerator := 141723845528693891538092032 }, { target := 158, numerator := 4070080868922726759033470976 }, { target := 160, numerator := 42195632750878934400908656640 }, { target := 168, numerator := 4069890789467118053709840384 }, { target := 175, numerator := 141784188213014115450355712 }, { target := 176, numerator := 1880432843268579259083390976 }, { target := 178, numerator := 75421829694862552116861337600 }, { target := 181, numerator := 75421674619298966026525343744 }, { target := 188, numerator := 1880561315147054448195403776 }, { target := 227, numerator := 1149393285124709564918267904 }, { target := 230, numerator := 4070080868922726759033470976 }, { target := 232, numerator := 1150946285312403503226814464 }, { target := 267, numerator := 40076976061316682164994048 }, { target := 268, numerator := 1150946285312403503226814464 }, { target := 270, numerator := 11932172439582192773848104960 }, { target := 278, numerator := 1150892534232168837547032576 }, { target := 285, numerator := 40094039896311814126829568 }, { target := 286, numerator := 1880427358966222932295024640 }, { target := 288, numerator := 75421674619298966026525343744 }, { target := 291, numerator := 75421519542168127265864417280 }, { target := 298, numerator := 1880555831223000490106159104 }, { target := 302, numerator := 11916072065242622469928386560 }, { target := 305, numerator := 42195632750878934400908656640 }, { target := 307, numerator := 11932172439582192773848104960 }, { target := 573, numerator := 45499221054756169759850496 }, { target := 575, numerator := 1880561315147054448195403776 }, { target := 578, numerator := 1880555831223000490106159104 }, { target := 585, numerator := 45502975248650146364260352 }, { target := 589, numerator := 1149339606572132148273217536 }, { target := 592, numerator := 4069890789467118053709840384 }, { target := 594, numerator := 1150892534232168837547032576 }, { target := 763, numerator := 40039940020167307950030848 }, { target := 766, numerator := 141784188213014115450355712 }, { target := 768, numerator := 40094039896311814126829568 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk1.Parent1
