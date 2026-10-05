import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk24Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 1,
parent 101; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk24.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [3666997854178488292403576832, 793055337667196738607251456, 116490571376058183248928309248, 8298066825834814655183192064, 735026898325694538221355008, 116490528874759837422121385984, 735026898325694538221355008, 715684085211860471426056192, 27041252733140025379827744768, 715684085211860471426056192, 8298066825834814655183192064, 27041252733140025379827744768, 3667012021277936901339217920, 715684085211860471426056192, 715684085211860471426056192, 793055337667196738607251456, 3610653528783939479242014720, 5415987671873538702683668480, 280470790150593968531832832, 17237681250126687000453971968, 7543697114395286050166538240, 3610652403532550982959366144, 7553368520952203083564187648, 7553368520952203083564187648, 5406316265316621669286019072, 280470790150593968531832832, 3610653528783939479242014720, 3668364388979468695987290112, 3610653528783939479242014720, 3668364388979468695987290112, 3668364388979468695987290112, 0, 0, 13398768116003035151125708800, 0, 3668363153047615757447331840, 0, 0, 0, 0, 5415987671873538702683668480, 0, 5415987671873538702683668480, 0, 2970656582080461887772819456, 280470790150593968531832832, 0, 280470790150593968531832832, 0, 0, 3610653528783939479242014720, 5415987671873538702683668480, 280470790150593968531832832, 17237681250126687000453971968, 7543697114395286050166538240, 3610652403532550982959366144, 7553368520952203083564187648, 7553368520952203083564187648, 5406316265316621669286019072, 280470790150593968531832832, 17237681250126687000453971968, 13398768116003035151125708800, 17237681250126687000453971968, 13398768116003035151125708800] }

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
  { lower := 64, upper := 128, values := [115871601356415493111478747136, 7543697114395286050166538240, 0, 7543697114395286050166538240, 0, 0, 0, 3610652403532550982959366144, 3668363153047615757447331840, 3610652403532550982959366144, 3668363153047615757447331840, 115871558855117147284671823872, 0, 3668364388979468695987290112, 0, 0, 13398768116003035151125708800, 0, 3668363153047615757447331840, 0, 0, 0, 0, 7553368520952203083564187648, 0, 7553368520952203083564187648, 0, 0, 7553368520952203083564187648, 0, 7553368520952203083564187648, 0, 0, 0, 5406316265316621669286019072, 0, 5406316265316621669286019072, 0, 0, 0, 2970670749179910496708460544, 280470790150593968531832832, 0, 280470790150593968531832832, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk24.Parent3
