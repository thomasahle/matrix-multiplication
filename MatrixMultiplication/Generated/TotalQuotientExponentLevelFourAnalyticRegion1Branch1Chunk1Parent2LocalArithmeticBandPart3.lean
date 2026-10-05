import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 1,
parent 7; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 0, 0, 0, 0, 0, 88303480134633293149634560, 0, 27667153102297487827271680, 4534113539664323576175001600, 0, 46680454447878040576432537600, 0, 0, 0, 0, 0, 0, 0, 4534113539664323576175001600, 0, 0, 0, 0, 0, 0, 27667153102297487827271680, 90826436709908530096766976, 18014046637838777990302924800, 0, 0, 0, 0, 18014046637838777990302924800, 0, 0, 0, 0, 0, 0, 0, 90826436709908530096766976, 0, 868748607412141117776330752, 142371165145459760291895050240, 0, 1465766269663370474099981680640, 0, 0, 0, 0, 0, 0, 0, 142371165145459760291895050240, 0, 0, 0, 0, 0, 0, 868748607412141117776330752, 1981963144912190883441410048, 0] }

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
  { lower := 832, upper := 896, values := [79238518802311851278319222784, 0, 0, 79238499437842259901717413888, 0, 0, 0, 0, 0, 0, 1981963144912190883441410048, 0, 0, 0, 27667153102297487827271680, 4534113539664323576175001600, 0, 46680454447878040576432537600, 0, 0, 0, 0, 0, 0, 0, 4534113539664323576175001600, 0, 0, 0, 0, 0, 0, 27667153102297487827271680, 1929806220046080597035057152, 0, 77153294623303644665731874816, 0, 0, 77153275768425358325356429312, 0, 0, 0, 0, 0, 0, 1929806220046080597035057152, 0, 0, 0, 637589120869652394261086208, 0, 0, 2322584568547031921656332288, 0, 637589549756452108008161280, 0, 0, 0, 0, 88303480134633293149634560, 17513656453454367490572288000, 0, 0, 0] }

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
  { lower := 896, upper := 960, values := [0, 17513656453454367490572288000, 0, 0, 0, 0, 0, 0, 0, 88303480134633293149634560, 0, 846614884930303127514513408, 138743874313728301430955048960, 0, 1428421906105068041638835650560, 0, 0, 0, 0, 0, 0, 0, 138743874313728301430955048960, 0, 0, 0, 0, 0, 0, 846614884930303127514513408, 1929806220046080597035057152, 0, 77153294623303644665731874816, 0, 0, 77153275768425358325356429312, 0, 0, 0, 0, 0, 0, 1929806220046080597035057152, 0, 0, 0, 885348899273519610472693760, 145091633269258354437600051200, 0, 1493774542332097298445841203200, 0, 0, 0, 0, 0, 0, 0, 145091633269258354437600051200, 0, 0, 0, 0, 0, 0] }

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
  { lower := 960, upper := 1024, values := [885348899273519610472693760, 60658503619286263090588418048, 0, 2425115720186544290439085686784, 0, 0, 2425115127531856533307825061888, 0, 0, 0, 0, 0, 0, 60658503619286263090588418048, 0, 0, 0, 12875186763367819316369031168, 0, 0, 46901223868078773643769806848, 0, 12875195424114161923003514880, 0, 0, 0, 0, 1929806220046080597035057152, 0, 77153294623303644665731874816, 0, 0, 77153275768425358325356429312, 0, 0, 0, 0, 0, 0, 1929806220046080597035057152, 0, 0, 0, 13101428064321566940139094016, 0, 0, 47725366779498688196615602176, 0, 13101436877253548154877378560, 0, 0, 0, 0, 0, 0, 0, 0, 66228547426158215228817408, 5919841721296506124033327104, 847717735053964899126345728, 56044068640539816383249121280, 528447419254419677377462272, 27523303086167691530076160, 842213074436731360820330496] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent2
