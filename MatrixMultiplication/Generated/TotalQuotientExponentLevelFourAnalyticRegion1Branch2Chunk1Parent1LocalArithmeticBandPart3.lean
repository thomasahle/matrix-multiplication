import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 2,
parent 6; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 0, 0, 0, 0, 0, 211161839378311068988211200, 0, 40001562762575856481075200, 4194091710151775897832652800, 0, 45208116645703656564326400000, 0, 0, 0, 0, 0, 0, 0, 4194094909508951181833011200, 0, 0, 0, 0, 0, 0, 40001562762575856481075200, 199753738736301548503040000, 16725207735868506897383424000, 0, 0, 0, 0, 16725213788706406083330048000, 0, 0, 0, 0, 0, 0, 0, 199747685898402362556416000, 0, 768030005041456444436643840, 80526560834914097238386933760, 0, 867995839597510206035066880000, 0, 0, 0, 0, 0, 0, 0, 80526622262571862691193815040, 0, 0, 0, 0, 0, 0, 768030005041456444436643840, 2322641404118444525391708160, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band12

namespace Band13

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 832, upper := 896, values := [81286658313422901871095316480, 0, 0, 81286698181448531175863746560, 0, 0, 0, 0, 0, 0, 2322621470105629873007493120, 0, 0, 0, 40001562762575856481075200, 4194091710151775897832652800, 0, 45208116645703656564326400000, 0, 0, 0, 0, 0, 0, 0, 4194094909508951181833011200, 0, 0, 0, 0, 0, 0, 40001562762575856481075200, 1990835489244381021764321280, 0, 69674278554362487318081699840, 0, 0, 69674312726955883865026068480, 0, 0, 0, 0, 0, 0, 1990818402947682748292136960, 0, 0, 0, 446174857675326745477120000, 0, 0, 1525502067993792934313984000, 0, 446174713560138669621248000, 0, 0, 0, 0, 268240734874462079418368000, 22459564673880566405057740800, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band13

namespace Band14

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 896, upper := 960, values := [0, 22459572801977173883328921600, 0, 0, 0, 0, 0, 0, 0, 268232606777854601147187200, 0, 1232048133087336379617116160, 129178024672674697653245706240, 0, 1392409992687672622181253120000, 0, 0, 0, 0, 0, 0, 0, 129178123212875696400456744960, 0, 0, 0, 0, 0, 0, 1232048133087336379617116160, 2322641404118444525391708160, 0, 81286658313422901871095316480, 0, 0, 81286698181448531175863746560, 0, 0, 0, 0, 0, 0, 2322621470105629873007493120, 0, 0, 0, 696027192068819902770708480, 72977195756640900622288158720, 0, 786621229635243624219279360000, 0, 0, 0, 0, 0, 0, 0, 72977251425455750563894394880, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band14

namespace Band15

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 960, upper := 1024, values := [696027192068819902770708480, 26212667275051016786563563520, 0, 917378000965772749688075714560, 0, 0, 917378450904919137556176568320, 0, 0, 0, 0, 0, 0, 26212442305477822852513136640, 0, 0, 0, 14402524405759547344001433600, 0, 0, 49243206754839635919655403520, 0, 14402519753721276255373885440, 0, 0, 0, 0, 1990835489244381021764321280, 0, 69674278554362487318081699840, 0, 0, 69674312726955883865026068480, 0, 0, 0, 0, 0, 0, 1990818402947682748292136960, 0, 0, 0, 9619529931480044632486707200, 0, 0, 32889824585946175663809495040, 0, 9619526824356589717034106880, 0, 0, 0, 0, 0, 0, 0, 0, 97128118880805809358372864, 6342943213934525252894720000, 1252719210925726930317606912, 54290678511149150195175915520, 1285470039969536784704995328, 40938536304762317984235520, 1252719210925726930317606912] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent1
