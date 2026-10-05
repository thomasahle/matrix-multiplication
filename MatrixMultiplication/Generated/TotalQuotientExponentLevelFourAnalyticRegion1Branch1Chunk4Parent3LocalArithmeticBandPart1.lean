import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk4Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 1, for region 1, branch 1,
parent 21; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band4

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 256, upper := 320, values := [2718394143929281475136576290816, 86573061908575843157215805440, 2649135694402420800610803646464, 2770337981074426981030905774080, 180933427001085400593358389248, 95951603990528687865856000, 16829009870614279758020608000, 0, 0, 0, 0, 16829011888226912820002816000, 0, 0, 0, 0, 0, 0, 0, 95949586377895625883648000, 0, 486555748906740823716003840, 156729999175750489511276052480, 0, 1666889450642714429751866425344, 0, 0, 0, 0, 0, 0, 0, 156730471559972729065473835008, 0, 0, 0, 0, 0, 0, 486555748906740823716003840, 252437594582674239061567209472, 17502170265438850948341432320, 9483312605230440257883104870400, 197524492995667032131281879040, 17502170265438850948341432320, 9483310414192241359696554885120, 17502170265438850948341432320, 17502170265438850948341432320, 725589973004336363601240522752, 18002232273022818118294044672, 197524492995667032131281879040, 725589973004336363601240522752, 252437668306239851146397089792, 17502170265438850948341432320, 18002232273022818118294044672, 17502170265438850948341432320, 25341445255559417901875200, 8163020790403671328712294400, 0, 86817158887641376549576376320, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band4

namespace Band5

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 320, upper := 384, values := [0, 0, 0, 8163045393748579638826762240, 0, 0, 0, 0, 0, 0, 25341445255559417901875200, 5429668990152024552565112832, 0, 212496057020518699078420267008, 0, 0, 212496134956859488996668997632, 0, 0, 0, 0, 0, 0, 5429746926492814470813843456, 0, 0, 0, 6781764152758496372430209024, 0, 0, 24447407598909192900272193536, 0, 6783045015543232910422179840, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 95951603990528687865856000, 16829009870614279758020608000, 0, 0, 0, 0, 16829011888226912820002816000, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band5

namespace Band6

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 384, upper := 448, values := [0, 95949586377895625883648000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3977879354007346459810201600, 697682666350323426539654348800, 0, 0, 0, 0, 697682749994778585766402457600, 0, 0, 0, 0, 0, 0, 0, 3977795709552187233062092800, 0, 775448224820118187797381120, 249788436186352342658596208640, 0, 2656605061961826122417037115392, 0, 0, 0, 0, 0, 0, 0, 249789189048706536948098924544, 0, 0, 0, 0, 0, 0, 775448224820118187797381120, 98693078390258078947737600, 17309838724060402036821196800, 0, 0, 0, 0, 17309840799319110329145753600, 0, 0, 0, 0, 0, 0, 0, 98691003131549786623180800, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band6

namespace Band7

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 448, upper := 512, values := [810926248177901372860006400, 261216665292917482518793420800, 0, 2778149084404524049586444042240, 0, 0, 0, 0, 0, 0, 0, 261217452599954548442456391680, 0, 0, 0, 0, 0, 0, 810926248177901372860006400, 7043894906143166987111497728, 0, 275670560459051285290923589632, 0, 0, 275670661565655553292975996928, 0, 0, 0, 0, 0, 0, 7043996012747434989163905024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1082882387893109477343232000, 189927397111218300126232576000, 0, 0, 0, 0, 189927419881418016111460352000, 0, 0, 0, 0, 0, 0, 0, 1082859617693393492115456000, 0, 486555748906740823716003840, 156729999175750489511276052480, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent3
