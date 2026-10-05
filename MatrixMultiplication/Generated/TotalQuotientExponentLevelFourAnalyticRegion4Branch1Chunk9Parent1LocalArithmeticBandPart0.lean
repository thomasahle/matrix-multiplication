import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk9Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 4, branch 1,
parent 74; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk9.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 184837681792221608899772416, 4915191938188716677527502848, 486344063295122969756434432, 49082000192224557092915118080, 429127114672167326255677440, 71521185778694554375946240, 475615885428318786600042496, 486344063295122969756434432, 429127114672167326255677440, 8664791657088845262645886976, 429127114672167326255677440, 4911669461025224794870644736, 475615885428318786600042496, 71521185778694554375946240, 429127114672167326255677440, 71521185778694554375946240, 486344063295122969756434432, 486344063295122969756434432, 184821232232734526554505216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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
  { lower := 64, upper := 128, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 140457321710900842101473280, 0, 5156312082702085790137057280, 0, 0, 5156860386024873594789560320, 0, 0, 0, 0, 0, 0, 139913269589128791499735040, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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
  { lower := 128, upper := 192, values := [0, 0, 0, 184837681792221608899772416, 0, 0, 635736296332094258894864384, 0, 184860347376977425008164864, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 635736296332094258894864384, 16948109890281460019759153152, 1657933672904564011991826432, 169437693930888727402943348736, 1462882652562850598816317440, 243813775427141766469386240, 1621361606590492747021418496, 1657933672904564011991826432, 1462882652562850598816317440, 29538038892998225007766142976, 1462882652562850598816317440, 16936104812011150299717697536, 1621361606590492747021418496, 243813775427141766469386240, 1462882652562850598816317440, 243813775427141766469386240, 1657933672904564011991826432, 1657933672904564011991826432, 635679473473498978296266752, 5156312082702085790137057280, 0, 187617183127531582223758131200, 0, 0, 187635418039133541872676372480, 0, 0, 0, 0, 0, 0, 5138214590933002973263953920, 0, 0, 0] }

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
  { lower := 192, upper := 256, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4915191938188716677527502848, 0, 0, 16948109890281460019759153152, 0, 4915958734566723635730448384, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 486344063295122969756434432, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk9.Parent1
