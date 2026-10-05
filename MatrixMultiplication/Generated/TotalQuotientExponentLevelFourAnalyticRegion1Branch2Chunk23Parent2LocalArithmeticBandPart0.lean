import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk23Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 2,
parent 96; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk23.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [16322104169401669537906032640, 2205080694977083614664065024, 541814768230280327840441303040, 17350503363109157915383037952, 2089023816294079213892272128, 541788455204237778177310588928, 2089023816294079213892272128, 2089023816294079213892272128, 89479853464596392995052322816, 2089023816294079213892272128, 17350503363109157915383037952, 89479853464596392995052322816, 16348417195444219201036746752, 2089023816294079213892272128, 2089023816294079213892272128, 2205080694977083614664065024, 85368370741977518820888150016, 36151717709755870840413487104, 2030995376952577013506375680, 331876604761932202479246639104, 54904575023617998598455689216, 85368351852511587342307295232, 54904575023617998598455689216, 54904575023617998598455689216, 36151717709755870840413487104, 2030995376952577013506375680, 85368370741977518820888150016, 29701079998924770615301767168, 85368370741977518820888150016, 29701079998924770615301767168, 29701079998924770615301767168, 0, 0, 108029230315498140949503016960, 0, 29701079998924770615301767168, 0, 0, 0, 0, 36151717709755870840413487104, 0, 36151717709755870840413487104, 0, 15295102796173110575412281344, 2030995376952577013506375680, 0, 2030995376952577013506375680, 0, 2205080694977083614664065024, 85368370741977518820888150016, 36151717709755870840413487104, 2030995376952577013506375680, 331876604761932202479246639104, 54904575023617998598455689216, 85368351852511587342307295232, 54904575023617998598455689216, 54904575023617998598455689216, 36151717709755870840413487104, 2030995376952577013506375680, 331876604761932202479246639104, 108029230315498140949503016960, 331876604761932202479246639104, 108029230315498140949503016960] }

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
  { lower := 64, upper := 128, values := [503227688346376718006163079168, 54904575023617998598455689216, 0, 54904575023617998598455689216, 0, 17350503363109157915383037952, 2089023816294079213892272128, 85368351852511587342307295232, 29701079998924770615301767168, 85368351852511587342307295232, 29701079998924770615301767168, 503204293742820581783774429184, 2089023816294079213892272128, 29701079998924770615301767168, 0, 0, 108029230315498140949503016960, 0, 29701079998924770615301767168, 0, 0, 0, 0, 54904575023617998598455689216, 0, 54904575023617998598455689216, 0, 2089023816294079213892272128, 54904575023617998598455689216, 0, 54904575023617998598455689216, 0, 89479853464596392995052322816, 2089023816294079213892272128, 36151717709755870840413487104, 0, 36151717709755870840413487104, 0, 17350503363109157915383037952, 89479853464596392995052322816, 15318497399729246797800931328, 2030995376952577013506375680, 0, 2030995376952577013506375680, 0, 2089023816294079213892272128, 2089023816294079213892272128, 2205080694977083614664065024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk23.Parent2
