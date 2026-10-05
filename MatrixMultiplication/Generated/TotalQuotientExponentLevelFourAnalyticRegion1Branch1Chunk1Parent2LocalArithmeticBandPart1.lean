import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 1, for region 1, branch 1,
parent 7; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band4

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 256, upper := 320, values := [1458145301190250696938283335680, 46437748445549385252811571200, 1420995102433811188736034078720, 1486007950257580328089970278400, 55752965287761559791201157120, 88303480134633293149634560, 17513656453454367490572288000, 0, 0, 0, 0, 17513656453454367490572288000, 0, 0, 0, 0, 0, 0, 0, 88303480134633293149634560, 0, 531209339564111766283616256, 87054979961555012662560030720, 0, 896264725399258379067504721920, 0, 0, 0, 0, 0, 0, 0, 87054979961555012662560030720, 0, 0, 0, 0, 0, 0, 531209339564111766283616256, 17337588086230585515872092160, 17513656453454367490572288000, 87994551796819546432476282880, 197654122831842147393601536000, 17513656453454367490572288000, 87994533961123870164553564160, 17513656453454367490572288000, 17513656453454367490572288000, 726066157541779635109153996800, 18014046637838777990302924800, 197654122831842147393601536000, 726066157541779635109153996800, 17337588086230585515872092160, 17513656453454367490572288000, 18014046637838777990302924800, 17513656453454367490572288000, 27667153102297487827271680, 4534113539664323576175001600, 0, 46680454447878040576432537600, 0, 0, 0, 0] }

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
  { lower := 320, upper := 384, values := [0, 0, 0, 4534113539664323576175001600, 0, 0, 0, 0, 0, 0, 27667153102297487827271680, 1929806220046080597035057152, 0, 77153294623303644665731874816, 0, 0, 77153275768425358325356429312, 0, 0, 0, 0, 0, 0, 1929806220046080597035057152, 0, 0, 0, 637589120869652394261086208, 0, 0, 2322584568547031921656332288, 0, 637589549756452108008161280, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 88303480134633293149634560, 17513656453454367490572288000, 0, 0, 0, 0, 17513656453454367490572288000, 0, 0, 0, 0, 0, 0] }

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
  { lower := 384, upper := 448, values := [0, 88303480134633293149634560, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3660809990724368810289135616, 726066157541779635109153996800, 0, 0, 0, 0, 726066157541779635109153996800, 0, 0, 0, 0, 0, 0, 0, 3660809990724368810289135616, 0, 846614884930303127514513408, 138743874313728301430955048960, 0, 1428421906105068041638835650560, 0, 0, 0, 0, 0, 0, 0, 138743874313728301430955048960, 0, 0, 0, 0, 0, 0, 846614884930303127514513408, 90826436709908530096766976, 18014046637838777990302924800, 0, 0, 0, 0, 18014046637838777990302924800, 0, 0, 0, 0, 0, 0, 0, 90826436709908530096766976, 0] }

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
  { lower := 448, upper := 512, values := [885348899273519610472693760, 145091633269258354437600051200, 0, 1493774542332097298445841203200, 0, 0, 0, 0, 0, 0, 0, 145091633269258354437600051200, 0, 0, 0, 0, 0, 0, 885348899273519610472693760, 2503532393573293747504939008, 0, 100090760592393917404192702464, 0, 0, 100090736132011275665327259648, 0, 0, 0, 0, 0, 0, 2503532393573293747504939008, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 996567847233718594117304320, 197654122831842147393601536000, 0, 0, 0, 0, 197654122831842147393601536000, 0, 0, 0, 0, 0, 0, 0, 996567847233718594117304320, 0, 531209339564111766283616256, 87054979961555012662560030720, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent2
