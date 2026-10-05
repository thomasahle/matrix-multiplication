import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk14Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 4, for region 1, branch 2,
parent 61; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band16

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 1024, upper := 1088, values := [1930019094319769700653858816, 1018032049751087314630606848, 23817708163968146965211906048, 1908810093283288714932387840, 18229744833875428426395942912, 1930019094319769700653858816, 74231503627683450025148416, 1908810093283288714932387840, 74231503627683450025148416, 1930019094319769700653858816, 1930019094319769700653858816, 176974016881731986006212608, 10451682452683545100280659968, 260242699341918506644930560, 382242518974672776408732794880, 2047699134295621933864058880, 246545715166028058926776320, 382224080991802702751877562368, 246545715166028058926776320, 246545715166028058926776320, 10560374799611535190696919040, 246545715166028058926776320, 2047699134295621933864058880, 10560374799611535190696919040, 10470120435553618757135892480, 246545715166028058926776320, 246545715166028058926776320, 260242699341918506644930560, 15407558938326927777479000064, 0, 0, 55386599916348219518160470016, 0, 15407555301408175472485859328, 0, 0, 0, 0, 6764268322011734299354595328, 0, 254150937770495992702431133696, 0, 0, 254131715797390899488481083392, 0, 0, 0, 0, 0, 0, 6783490295116827513304645632, 0, 0, 0, 106932123046036454650561953792, 0, 0, 388935181787451948307568394240, 0, 106932123046036454650561953792, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band16

namespace Band17

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 1088, upper := 1107, values := [9903520314283042199192993792, 0, 9903520314283042199192993792, 0, 4467514574699636245508653056, 0, 0, 16249313524812682476461752320, 0, 4467514574699636245508653056, 0, 0, 0, 0, 9903520314283042199192993792, 0, 9903520314283042199192993792, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent3
