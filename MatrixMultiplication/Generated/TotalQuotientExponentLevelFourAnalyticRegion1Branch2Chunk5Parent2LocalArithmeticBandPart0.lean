import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk5Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 2,
parent 24; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [17861373691592479004245884928, 2727336649050603418137133056, 541668157640453156835136897024, 67487074954167059048797569024, 2147052255635581414278168576, 541668379591677851708461940736, 2205080694977083614664065024, 2205080694977083614664065024, 37312286496585914848131416064, 2030995376952577013506375680, 67487074954167059048797569024, 37312286496585914848131416064, 17861198964032612827372978176, 2147052255635581414278168576, 2030995376952577013506375680, 2727336649050603418137133056, 86042977610190211466435493888, 44101613899541672293281300480, 1798881619586568211962789888, 324244943555628020228220256256, 36325803027780377441571176448, 86042958716452615741293723648, 36383831467121879641957072896, 32611982909924236616873803776, 44101613899541672293281300480, 1798881619586568211962789888, 86042977610190211466435493888, 25573987576907119160576704512, 86016527806908646002805178368, 25825205529528996559010660352, 25573987576907119160576704512, 0, 0, 86688911095367321662145953792, 0, 25573987576907119160576704512, 0, 0, 0, 0, 44101613899541672293281300480, 0, 44101613899541672293281300480, 0, 17861373691592479004245884928, 1798881619586568211962789888, 0, 1798881619586568211962789888, 0, 2727336649050603418137133056, 86016527806908646002805178368, 44101613899541672293281300480, 1798881619586568211962789888, 324154509886159763190832955392, 36325803027780377441571176448, 86016508921714378770785239040, 36383831467121879641957072896, 32611982909924236616873803776, 44101613899541672293281300480, 1798881619586568211962789888, 324244943555628020228220256256, 86688911095367321662145953792, 324154509886159763190832955392, 87540472108091951540948959232] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band0

namespace Band1

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 64, upper := 128, values := [541668157640453156835136897024, 36325803027780377441571176448, 0, 36325803027780377441571176448, 0, 67487074954167059048797569024, 2147052255635581414278168576, 86042958716452615741293723648, 25573987576907119160576704512, 86016508921714378770785239040, 25825205529528996559010660352, 541668379591677851708461940736, 2205080694977083614664065024, 25825205529528996559010660352, 0, 0, 87540472108091951540948959232, 0, 25825205529528996559010660352, 0, 0, 0, 0, 36383831467121879641957072896, 0, 36383831467121879641957072896, 0, 2205080694977083614664065024, 32611982909924236616873803776, 0, 32611982909924236616873803776, 0, 37312286496585914848131416064, 2030995376952577013506375680, 44101613899541672293281300480, 0, 44101613899541672293281300480, 0, 67487074954167059048797569024, 37312286496585914848131416064, 17861198964032612827372978176, 1798881619586568211962789888, 0, 1798881619586568211962789888, 0, 2147052255635581414278168576, 2030995376952577013506375680, 2727336649050603418137133056, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band1

namespace Band2

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 128, upper := 192, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band2

namespace Band3

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 192, upper := 256, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5.Parent2
