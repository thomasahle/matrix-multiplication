import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk3Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 1,
parent 16; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk3.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [14548515544697351145707798528, 2030995376952577013506375680, 503974166983423371434027646976, 22921233539893369152429096960, 2030995376952577013506375680, 503974256708386545957286707200, 2030995376952577013506375680, 2030995376952577013506375680, 84199265484519692759935746048, 2089023816294079213892272128, 22921233539893369152429096960, 84199265484519692759935746048, 14548643048592388626128568320, 2030995376952577013506375680, 2089023816294079213892272128, 2030995376952577013506375680, 91906602254416934603707121664, 33917610665220886156919439360, 1760195363863758563033743360, 363783574577298911299027075072, 54633756101463583091085803520, 91982219437107182454010019840, 54633756101463583091085803520, 56935550038823882750437621760, 33917610665220886156919439360, 1692495542176690925993984000, 91906602254416934603707121664, 29647951014809245671825080320, 91906603416561811247408873472, 29647951014809245671825080320, 29647951014809245671825080320, 0, 0, 106269962580747774009477693440, 0, 29656566658862592086455091200, 0, 0, 0, 0, 33917610665220886156919439360, 0, 33917634924995186094193508352, 0, 14548515544697351145707798528, 1760195363863758563033743360, 0, 1760196622854041593710641152, 0, 2030995376952577013506375680, 91906603416561811247408873472, 33917634924995186094193508352, 1760196622854041593710641152, 363783600677135932588828917760, 54633795178585060235557208064, 91982220647674762291199344640, 54633795178585060235557208064, 56935590762317268473486508032, 33917634924995186094193508352, 1692496752744270763183308800, 363783574577298911299027075072, 106269962580747774009477693440, 363783600677135932588828917760, 106269962580747774009477693440] }

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
  { lower := 64, upper := 128, values := [503974166983423371434027646976, 54633756101463583091085803520, 0, 54633795178585060235557208064, 0, 22921233539893369152429096960, 2030995376952577013506375680, 91982219437107182454010019840, 29656566658862592086455091200, 91982220647674762291199344640, 29656566658862592086455091200, 503974256708386545957286707200, 2030995376952577013506375680, 29647951014809245671825080320, 0, 0, 106269962580747774009477693440, 0, 29656566658862592086455091200, 0, 0, 0, 0, 54633756101463583091085803520, 0, 54633795178585060235557208064, 0, 2030995376952577013506375680, 56935550038823882750437621760, 0, 56935590762317268473486508032, 0, 84199265484519692759935746048, 2089023816294079213892272128, 33917610665220886156919439360, 0, 33917634924995186094193508352, 0, 22921233539893369152429096960, 84199265484519692759935746048, 14548643048592388626128568320, 1692495542176690925993984000, 0, 1692496752744270763183308800, 0, 2030995376952577013506375680, 2089023816294079213892272128, 2030995376952577013506375680, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk3.Parent2
