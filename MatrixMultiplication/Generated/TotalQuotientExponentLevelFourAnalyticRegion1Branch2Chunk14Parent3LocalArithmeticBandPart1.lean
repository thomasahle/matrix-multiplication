import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk14Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 1, for region 1, branch 2,
parent 61; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band4

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 256, upper := 320, values := [2938418161620676917040093593600, 114271817396359657884892528640, 2971067252305351105007205744640, 2971067252305351105007205744640, 177628265296668922428763668480, 246553186097377911295180800, 20643684976843414227627540480, 0, 0, 0, 0, 20643692447774764079995944960, 0, 0, 0, 0, 0, 0, 0, 246545715166028058926776320, 0, 1013988228302225001563553792, 149760754922459691811835215872, 0, 1560931302803330789958934855680, 0, 0, 0, 0, 0, 0, 0, 149760754922459691811835215872, 0, 0, 0, 0, 0, 0, 1013988228302225001563553792, 339228659088130192724157530112, 21790556364445826129162403840, 11869497218688113049074202050560, 171457272446560579279462072320, 20643684976843414227627540480, 11869480048329912780081879580672, 20643684976843414227627540480, 20643684976843414227627540480, 884237839841459576083379650560, 20643684976843414227627540480, 171457272446560579279462072320, 884237839841459576083379650560, 339245829446330461716480000000, 20643684976843414227627540480, 20643684976843414227627540480, 21790556364445826129162403840, 73936641647037239697342464, 10920055046429352527946317824, 0, 113817907496076203434505666560, 0, 0, 0, 0] }

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
  { lower := 320, upper := 384, values := [0, 0, 0, 10920055046429352527946317824, 0, 0, 0, 0, 0, 0, 73936641647037239697342464, 5756824103839773871791144960, 0, 216298670442975312938239262720, 0, 0, 216282311316928425096579645440, 0, 0, 0, 0, 0, 0, 5773183229886661713450762240, 0, 0, 0, 15407558938326927777479000064, 0, 0, 55386599916348219518160470016, 0, 15407555301408175472485859328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 246553186097377911295180800, 20643684976843414227627540480, 0, 0, 0, 0, 20643692447774764079995944960, 0, 0, 0, 0, 0, 0] }

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
  { lower := 384, upper := 448, values := [0, 246545715166028058926776320, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10560694804504353867143577600, 884237839841459576083379650560, 0, 0, 0, 0, 884238159846352394759826309120, 0, 0, 0, 0, 0, 0, 0, 10560374799611535190696919040, 0, 1922352682822968232130904064, 283921431207163165726604263424, 0, 2959265594897981289297147330560, 0, 0, 0, 0, 0, 0, 0, 283921431207163165726604263424, 0, 0, 0, 0, 0, 0, 1922352682822968232130904064, 246553186097377911295180800, 20643684976843414227627540480, 0, 0, 0, 0, 20643692447774764079995944960, 0, 0, 0, 0, 0, 0, 0, 246545715166028058926776320, 0] }

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
  { lower := 448, upper := 512, values := [1922352682822968232130904064, 283921431207163165726604263424, 0, 2959265594897981289297147330560, 0, 0, 0, 0, 0, 0, 0, 283921431207163165726604263424, 0, 0, 0, 0, 0, 0, 1922352682822968232130904064, 6764268322011734299354595328, 0, 254150937770495992702431133696, 0, 0, 254131715797390899488481083392, 0, 0, 0, 0, 0, 0, 6783490295116827513304645632, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2047761184530999874368307200, 171457272446560579279462072320, 0, 0, 0, 0, 171457334496795957219966320640, 0, 0, 0, 0, 0, 0, 0, 2047699134295621933864058880, 0, 1013988228302225001563553792, 149760754922459691811835215872, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent3
