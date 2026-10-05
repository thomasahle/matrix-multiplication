import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 1, for region 1, branch 2,
parent 6; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band4

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 256, upper := 320, values := [888327273678172607257509888000, 46267045504071489961328640000, 1425025001525401890808922112000, 805046591770843925327118336000, 55560456167648363810075443200, 216875487770841681231872000, 18158796970371521774302003200, 0, 0, 0, 0, 18158803542024098033329766400, 0, 0, 0, 0, 0, 0, 0, 216868916118265422204108800, 0, 1256049070744881893505761280, 131694479698765763191945297920, 0, 1419534862675094816119848960000, 0, 0, 0, 0, 0, 0, 0, 131694580158581067109556551680, 0, 0, 0, 0, 0, 0, 1256049070744881893505761280, 24408933229059565735586562048, 21561182086925343748855431168, 100582830801750680924414017536, 533524569512642016594018435072, 16973696536515696142715977728, 100582871808862756780747259904, 17432445091556660903329923072, 17432445091556660903329923072, 294975320891340341074766856192, 16056199426433766621488087040, 533524569512642016594018435072, 294975320891340341074766856192, 24408912725503527807419940864, 16973696536515696142715977728, 16056199426433766621488087040, 21561182086925343748855431168, 40001562762575856481075200, 4194091710151775897832652800, 0, 45208116645703656564326400000, 0, 0, 0, 0] }

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
  { lower := 320, upper := 384, values := [0, 0, 0, 4194094909508951181833011200, 0, 0, 0, 0, 0, 0, 40001562762575856481075200, 2322641404118444525391708160, 0, 81286658313422901871095316480, 0, 0, 81286698181448531175863746560, 0, 0, 0, 0, 0, 0, 2322621470105629873007493120, 0, 0, 0, 446174857675326745477120000, 0, 0, 1525502067993792934313984000, 0, 446174713560138669621248000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 216875487770841681231872000, 18158796970371521774302003200, 0, 0, 0, 0, 18158803542024098033329766400, 0, 0, 0, 0, 0, 0] }

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
  { lower := 384, upper := 448, values := [0, 216868916118265422204108800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3669761543069768448212992000, 307265959261812855286215475200, 0, 0, 0, 0, 307266070461091974616606310400, 0, 0, 0, 0, 0, 0, 0, 3669650343790649117822156800, 0, 1224047820534821208320901120, 128339206330644342473679175680, 0, 1383368369358531890868387840000, 0, 0, 0, 0, 0, 0, 0, 128339304230973906164090142720, 0, 0, 0, 0, 0, 0, 1224047820534821208320901120, 199753738736301548503040000, 16725207735868506897383424000, 0, 0, 0, 0, 16725213788706406083330048000, 0, 0, 0, 0, 0, 0, 0, 199747685898402362556416000, 0] }

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
  { lower := 448, upper := 512, values := [696027192068819902770708480, 72977195756640900622288158720, 0, 786621229635243624219279360000, 0, 0, 0, 0, 0, 0, 0, 72977251425455750563894394880, 0, 0, 0, 0, 0, 0, 696027192068819902770708480, 2057196672219193722489798656, 0, 71996754506174570228684423168, 0, 0, 71996789817854413327193604096, 0, 0, 0, 0, 0, 0, 2057179016379272173235208192, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6637531375723391454543872000, 555754759909002100618769203200, 0, 0, 0, 0, 555754961036158579283224166400, 0, 0, 0, 0, 0, 0, 0, 6637330248566912790088908800, 0, 1256049070744881893505761280, 131694479698765763191945297920, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent1
