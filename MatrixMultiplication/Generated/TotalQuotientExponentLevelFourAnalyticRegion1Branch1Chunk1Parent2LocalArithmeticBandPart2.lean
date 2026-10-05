import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 1, branch 1,
parent 7; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [896264725399258379067504721920, 0, 0, 0, 0, 0, 0, 0, 87054979961555012662560030720, 0, 0, 0, 0, 0, 0, 531209339564111766283616256, 3660809990724368810289135616, 726066157541779635109153996800, 0, 0, 0, 0, 726066157541779635109153996800, 0, 0, 0, 0, 0, 0, 0, 3660809990724368810289135616, 0, 13562438450746228532928577536, 2222622457143451417040985784320, 0, 22882758770349815490567229931520, 0, 0, 0, 0, 0, 0, 0, 2222622457143451417040985784320, 0, 0, 0, 0, 0, 0, 13562438450746228532928577536, 33536902688908914159284912128, 0, 1340799147102276851893664743424, 0, 0, 1340798819435067713600113082368, 0, 0, 0, 0, 0, 0, 33536902688908914159284912128] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band8

namespace Band9

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 576, upper := 640, values := [0, 0, 0, 868748607412141117776330752, 142371165145459760291895050240, 0, 1465766269663370474099981680640, 0, 0, 0, 0, 0, 0, 0, 142371165145459760291895050240, 0, 0, 0, 0, 0, 0, 868748607412141117776330752, 60658503619286263090588418048, 0, 2425115720186544290439085686784, 0, 0, 2425115127531856533307825061888, 0, 0, 0, 0, 0, 0, 60658503619286263090588418048, 0, 0, 0, 15631217156804381278658887680, 0, 0, 56940782970830460014800404480, 0, 15631227671448503293103308800, 0, 0, 0, 0, 2540679319231698537052897280, 17345848232702593932271288320, 1938538374887918065799921664, 2514860594449191004280979456, 33688653379808954494847287296, 60932976486341857041224564736, 17345848232702593932271288320, 33688653379808954494847287296, 1990931303938942878389108736, 1990931303938942878389108736, 1938538374887918065799921664, 1938538374887918065799921664, 60932976486341857041224564736, 1938538374887918065799921664, 2540679319231698537052897280, 2514860594449191004280979456] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band9

namespace Band10

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 640, upper := 704, values := [5894055614969206928176054272, 157376959279503074505177169920, 138924610208723586426192527360, 816750446685568931563244093440, 86602354415827690239704432640, 4510539292491025533317939200, 138022502350225381319528939520, 144337257359712817066174054400, 86602354415827690239704432640, 2211066361179100716432453795840, 141630933784218201746183290880, 157376959279503074505177169920, 138022502350225381319528939520, 4510539292491025533317939200, 141630933784218201746183290880, 4510539292491025533317939200, 138022502350225381319528939520, 144337257359712817066174054400, 5894055614969206928176054272, 17337588086230585515872092160, 17513656453454367490572288000, 87994551796819546432476282880, 197654122831842147393601536000, 17513656453454367490572288000, 87994533961123870164553564160, 17513656453454367490572288000, 17513656453454367490572288000, 726066157541779635109153996800, 18014046637838777990302924800, 197654122831842147393601536000, 726066157541779635109153996800, 17337588086230585515872092160, 17513656453454367490572288000, 18014046637838777990302924800, 17513656453454367490572288000, 846614884930303127514513408, 138743874313728301430955048960, 0, 1428421906105068041638835650560, 0, 0, 0, 0, 0, 0, 0, 138743874313728301430955048960, 0, 0, 0, 0, 0, 0, 846614884930303127514513408, 33536902688908914159284912128, 0, 1340799147102276851893664743424, 0, 0, 1340798819435067713600113082368, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band10

namespace Band11

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 704, upper := 768, values := [0, 0, 33536902688908914159284912128, 0, 0, 0, 11558873739636924050797756416, 0, 0, 42106210565271998063576088576, 0, 11558881514939551119373762560, 0, 0, 0, 0, 1981963144912190883441410048, 0, 79238518802311851278319222784, 0, 0, 79238499437842259901717413888, 0, 0, 0, 0, 0, 0, 1981963144912190883441410048, 0, 0, 0, 12895754154363614554893582336, 0, 0, 46976145950935129512210333696, 0, 12895762828945015216810229760, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 88303480134633293149634560, 17513656453454367490572288000, 0, 0, 0, 0, 17513656453454367490572288000, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent2
