import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk16Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 1, branch 1,
parent 68; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [124053859061786957358877900800, 7443231543707217441532674048, 196005097317623392627027083264, 194764558727005523053438304256, 124053859061786957358877900800, 3005825005067097976805611536384, 192283481545769783906260746240, 124239179722083537172142489600, 196005097317623392627027083264, 7443231543707217441532674048, 192283481545769783906260746240, 7443231543707217441532674048, 196005097317623392627027083264, 196005097317623392627027083264, 7549757616916634623109234688, 1117534624305688980618215424, 196005073818777285730272018432, 0, 0, 0, 0, 196005097317623392627027083264, 0, 0, 0, 0, 0, 0, 0, 1117511125459582083863150592, 0, 1996602972153647746120679424, 235985652651346947565078708224, 0, 2239456803073747939641224331264, 0, 0, 0, 0, 0, 0, 0, 235985814503079450292684587008, 0, 0, 0, 0, 0, 0, 1996602972153647746120679424, 5989436752246334643551338496, 2278092394970756469913288704, 157376761449702099016304558080, 23836625303474500624214654976, 2111402707533871850163535872, 157376704376628856463558705152, 2111402707533871850163535872, 2055839478388243643580284928, 77677394345588232803384819712, 2055839478388243643580284928, 23836625303474500624214654976, 77677394345588232803384819712, 5989455776604082161133289472, 2055839478388243643580284928] }

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
  { lower := 576, upper := 640, values := [2055839478388243643580284928, 2278092394970756469913288704, 112613277392812449095221248, 13310166384298532103518158848, 0, 126310825783122978302934908928, 0, 0, 0, 0, 0, 0, 0, 13310175513131005580532514816, 0, 0, 0, 0, 0, 0, 112613277392812449095221248, 4444864251150014019253829632, 0, 173373637901941345731416686592, 0, 0, 173373574309096994626951184384, 0, 0, 0, 0, 0, 0, 4444885448764797720742330368, 0, 0, 0, 3504109267084865620047560704, 0, 0, 12798823274987973875702169600, 0, 3504108086493244902636257280, 0, 0, 0, 0, 0, 0, 0, 0, 45485005012438610375344128, 0, 2055839478388243643580284928, 0, 0, 0, 0, 45727772234899160322539520, 0, 0, 42438023707810973947527168, 7443230651345972875833114624, 0] }

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
  { lower := 640, upper := 704, values := [0, 0, 0, 7443231543707217441532674048, 0, 0, 0, 0, 0, 0, 0, 42437131346566408247967744, 0, 45485005012438610375344128, 0, 2055839478388243643580284928, 0, 0, 0, 0, 45727772234899160322539520, 0, 0, 1096315612451783493644451840, 192283458493104299292355461120, 0, 0, 0, 0, 192283481545769783906260746240, 0, 0, 0, 0, 0, 0, 0, 1096292559786298879739166720, 0, 115656879484510082854551552, 13669900610901195133342973952, 0, 129724631885369545284095311872, 0, 0, 0, 0, 0, 0, 0, 13669909986458870596222582784, 0, 0, 0, 0, 0, 0, 115656879484510082854551552, 42438023707810973947527168, 7443230651345972875833114624, 0, 0, 0, 0] }

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
  { lower := 704, upper := 768, values := [7443231543707217441532674048, 0, 0, 0, 0, 0, 0, 0, 42437131346566408247967744, 0, 115656879484510082854551552, 13669900610901195133342973952, 0, 129724631885369545284095311872, 0, 0, 0, 0, 0, 0, 0, 13669909986458870596222582784, 0, 0, 0, 0, 0, 0, 115656879484510082854551552, 217335633731309833749004288, 0, 8477259897413535832293244928, 0, 0, 8477256787984237907626950656, 0, 0, 0, 0, 0, 0, 217336670207742475304435712, 0, 0, 0, 50402302851621162848354304, 0, 2278092394970756469913288704, 0, 0, 0, 0, 50671315179212583060111360, 0, 0, 1117534624305688980618215424, 196005073818777285730272018432, 0, 0, 0, 0, 196005097317623392627027083264, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent2
