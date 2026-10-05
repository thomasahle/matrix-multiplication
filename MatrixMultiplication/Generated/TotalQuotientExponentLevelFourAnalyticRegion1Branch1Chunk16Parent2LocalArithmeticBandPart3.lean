import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk16Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 1,
parent 68; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 0, 0, 0, 0, 1117511125459582083863150592, 0, 112613277392812449095221248, 13310166384298532103518158848, 0, 126310825783122978302934908928, 0, 0, 0, 0, 0, 0, 0, 13310175513131005580532514816, 0, 0, 0, 0, 0, 0, 112613277392812449095221248, 1117534624305688980618215424, 196005073818777285730272018432, 0, 0, 0, 0, 196005097317623392627027083264, 0, 0, 0, 0, 0, 0, 0, 1117511125459582083863150592, 0, 3491011599177185921951858688, 412615157913254495209062924288, 0, 3915635599276812327390982176768, 0, 0, 0, 0, 0, 0, 0, 412615440907061172996507959296, 0, 0, 0, 0, 0, 0, 3491011599177185921951858688, 4444864251150014019253829632, 0, 173373637901941345731416686592] }

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
  { lower := 832, upper := 896, values := [0, 0, 173373574309096994626951184384, 0, 0, 0, 0, 0, 0, 4444885448764797720742330368, 0, 0, 0, 112613277392812449095221248, 13310166384298532103518158848, 0, 126310825783122978302934908928, 0, 0, 0, 0, 0, 0, 0, 13310175513131005580532514816, 0, 0, 0, 0, 0, 0, 112613277392812449095221248, 4437853424255455637519990784, 0, 173100177905250586511020130304, 0, 0, 173100114412710406307350315008, 0, 0, 0, 0, 0, 0, 4437874588435515705409929216, 0, 0, 0, 3504109267084865620047560704, 0, 0, 12798823274987973875702169600, 0, 3504108086493244902636257280, 0, 0, 0, 0, 191261632528016766740201472, 7554848357961127220427620352, 117818690315996252627533824, 151924100670626746809188352, 2033922653876145834833215488, 3556264152432834256941613056] }

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
  { lower := 896, upper := 960, values := [7551748758471950832110665728, 2033922653876145834833215488, 114718198465575298611019776, 117818690315996252627533824, 117818690315996252627533824, 114718198465575298611019776, 3556264152432834256941613056, 114718198465575298611019776, 191260740166772201040642048, 151924100670626746809188352, 188530031748052828695822336, 17903799847126321555310641152, 1117511125459582083863150592, 163905130039181781503947309056, 707285522442773470799462400, 42437131346566408247967744, 1117511125459582083863150592, 1110438270235154349155155968, 707285522442773470799462400, 17137528208788401197470973952, 1096292559786298879739166720, 17903811689936016876842778624, 1117511125459582083863150592, 42437131346566408247967744, 1096292559786298879739166720, 42437131346566408247967744, 1117511125459582083863150592, 1117511125459582083863150592, 188530031748052828695822336, 261827520230130638387150848, 50671315179212583060111360, 8516808240968043214193819648, 530194980777614588604579840, 46963657970977516006932480, 8516805131538745289527525376, 46963657970977516006932480, 45727772234899160322539520, 1727768259037541246781358080, 45727772234899160322539520, 530194980777614588604579840, 1727768259037541246781358080, 261828556706563279942582272, 45727772234899160322539520, 45727772234899160322539520, 50671315179212583060111360, 149136502493184054207184896, 17626977103530488461415940096, 0, 167276499010081782076859744256, 0, 0, 0, 0, 0, 0, 0, 17626989193065385768813330432, 0, 0, 0, 0, 0, 0, 149136502493184054207184896] }

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
  { lower := 960, upper := 1024, values := [5265130997813344682112974848, 0, 205368457514760174517813772288, 0, 0, 205368382186327828020252901376, 0, 0, 0, 0, 0, 0, 5265156107290793514633265152, 0, 0, 0, 3504109267084865620047560704, 0, 0, 12798823274987973875702169600, 0, 3504108086493244902636257280, 0, 0, 0, 0, 217335633731309833749004288, 0, 8477259897413535832293244928, 0, 0, 8477256787984237907626950656, 0, 0, 0, 0, 0, 0, 217336670207742475304435712, 0, 0, 0, 3504109267084865620047560704, 0, 0, 12798823274987973875702169600, 0, 3504108086493244902636257280, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent2
