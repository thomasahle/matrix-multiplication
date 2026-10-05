import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk14Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 2,
parent 61; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 0, 0, 0, 0, 0, 246545715166028058926776320, 0, 73936641647037239697342464, 10920055046429352527946317824, 0, 113817907496076203434505666560, 0, 0, 0, 0, 0, 0, 0, 10920055046429352527946317824, 0, 0, 0, 0, 0, 0, 73936641647037239697342464, 246553186097377911295180800, 20643684976843414227627540480, 0, 0, 0, 0, 20643692447774764079995944960, 0, 0, 0, 0, 0, 0, 0, 246545715166028058926776320, 0, 1901227928066671877931663360, 280801415479611922147191029760, 0, 2926746192756245231173002854400, 0, 0, 0, 0, 0, 0, 0, 280801415479611922147191029760, 0, 0, 0, 0, 0, 0, 1901227928066671877931663360, 5612903501243779524996366336, 0] }

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
  { lower := 832, upper := 896, values := [210891203681900930114783281152, 0, 0, 210875253534005214469165154304, 0, 0, 0, 0, 0, 0, 5628853649139495170614493184, 0, 0, 0, 73936641647037239697342464, 10920055046429352527946317824, 0, 113817907496076203434505666560, 0, 0, 0, 0, 0, 0, 0, 10920055046429352527946317824, 0, 0, 0, 0, 0, 0, 73936641647037239697342464, 5612903501243779524996366336, 0, 210891203681900930114783281152, 0, 0, 210875253534005214469165154304, 0, 0, 0, 0, 0, 0, 5628853649139495170614493184, 0, 0, 0, 4467514574699636245508653056, 0, 0, 16249313524812682476461752320, 0, 4467514574699636245508653056, 0, 0, 0, 0, 260250585325010017478246400, 21790556364445826129162403840, 0, 0, 0] }

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
  { lower := 896, upper := 960, values := [0, 21790564250428917639995719680, 0, 0, 0, 0, 0, 0, 0, 260242699341918506644930560, 0, 1922352682822968232130904064, 283921431207163165726604263424, 0, 2959265594897981289297147330560, 0, 0, 0, 0, 0, 0, 0, 283921431207163165726604263424, 0, 0, 0, 0, 0, 0, 1922352682822968232130904064, 5612903501243779524996366336, 0, 210891203681900930114783281152, 0, 0, 210875253534005214469165154304, 0, 0, 0, 0, 0, 0, 5628853649139495170614493184, 0, 0, 0, 1922352682822968232130904064, 283921431207163165726604263424, 0, 2959265594897981289297147330560, 0, 0, 0, 0, 0, 0, 0, 283921431207163165726604263424, 0, 0, 0, 0, 0, 0] }

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
  { lower := 960, upper := 1024, values := [1922352682822968232130904064, 179612912039800944799883722752, 0, 6748518517820829763673064996864, 0, 0, 6748008113088166863013284937728, 0, 0, 0, 0, 0, 0, 180123316772463845459663781888, 0, 0, 0, 92664899081673100189098835968, 0, 0, 337042212788856607495642152960, 0, 92664899081673100189098835968, 0, 0, 0, 0, 5612903501243779524996366336, 0, 210891203681900930114783281152, 0, 0, 210875253534005214469165154304, 0, 0, 0, 0, 0, 0, 5628853649139495170614493184, 0, 0, 0, 93097239201805323051567415296, 0, 0, 338614727000935254186912645120, 0, 93097239201805323051567415296, 0, 0, 0, 0, 9903520314283042199192993792, 0, 9903520314283042199192993792, 0, 166375219062282249731833856, 18229744833875428426395942912, 1930019094319769700653858816, 177239452406695086794427334656, 1018032049751087314630606848, 74231503627683450025148416, 1930019094319769700653858816] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent3
