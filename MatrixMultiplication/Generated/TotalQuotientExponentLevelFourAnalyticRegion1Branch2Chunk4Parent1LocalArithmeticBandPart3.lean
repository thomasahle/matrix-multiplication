import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk4Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 2,
parent 19; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 0, 0, 0, 0, 0, 197662087790056723795935232, 0, 47388532603855231254528000, 6999038272173776723509248000, 0, 72949805402698036669317120000, 0, 0, 0, 0, 0, 0, 0, 6999038272173776723509248000, 0, 0, 0, 0, 0, 0, 47388532603855231254528000, 186973857500465663280414720, 15722489928628054275852861440, 0, 0, 0, 0, 15722486135516304119326310400, 0, 0, 0, 0, 0, 0, 0, 186977650612215819806965760, 0, 909859825994020440086937600, 134381534825736513091377561600, 0, 1400636263731802304050888704000, 0, 0, 0, 0, 0, 0, 0, 134381534825736513091377561600, 0, 0, 0, 0, 0, 0, 909859825994020440086937600, 7217132098215396644214538240, 0] }

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
  { lower := 832, upper := 896, values := [261551256118508961476462510080, 0, 0, 261551352237574800549294899200, 0, 0, 0, 0, 0, 0, 7217035979149557571382149120, 0, 0, 0, 47388532603855231254528000, 6999038272173776723509248000, 0, 72949805402698036669317120000, 0, 0, 0, 0, 0, 0, 0, 6999038272173776723509248000, 0, 0, 0, 0, 0, 0, 47388532603855231254528000, 6186113227041768552183889920, 0, 224186790958721966979825008640, 0, 0, 224186873346492686185109913600, 0, 0, 0, 0, 0, 0, 6186030839271049346898984960, 0, 0, 0, 3947710684058073403962163200, 0, 0, 13381673057101326666904371200, 0, 3947710684058073403962163200, 0, 0, 0, 0, 251079180072053890690842624, 21113057904157672884716699648, 0, 0, 0] }

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
  { lower := 896, upper := 960, values := [0, 21113052810550465531666759680, 0, 0, 0, 0, 0, 0, 0, 251084273679261243740782592, 0, 1459566804198741122639462400, 215570378782952323084084838400, 0, 2246854006403099529414967296000, 0, 0, 0, 0, 0, 0, 0, 215570378782952323084084838400, 0, 0, 0, 0, 0, 0, 1459566804198741122639462400, 7217132098215396644214538240, 0, 261551256118508961476462510080, 0, 0, 261551352237574800549294899200, 0, 0, 0, 0, 0, 0, 7217035979149557571382149120, 0, 0, 0, 824560467307081023828787200, 121783265935823714989060915200, 0, 1269326614006945838046117888000, 0, 0, 0, 0, 0, 0, 0, 121783265935823714989060915200, 0, 0, 0, 0, 0, 0] }

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
  { lower := 960, upper := 1024, values := [824560467307081023828787200, 81450490822716619270421217280, 0, 2951792747623172565234362613760, 0, 0, 2951793832395487034770613862400, 0, 0, 0, 0, 0, 0, 81449406050402149734169968640, 0, 0, 0, 127432100881394609479898628096, 0, 0, 431960406283230824807673102336, 0, 127432100881394609479898628096, 0, 0, 0, 0, 6186113227041768552183889920, 0, 224186790958721966979825008640, 0, 0, 224186873346492686185109913600, 0, 0, 0, 0, 0, 0, 6186030839271049346898984960, 0, 0, 0, 85112642348292062589424238592, 0, 0, 288508871111104602938458243072, 0, 85112642348292062589424238592, 0, 0, 0, 0, 9458635612664858662901121024, 0, 9458635612664858662901121024, 0, 226514158663555325630611456, 21750114506631235798634070016, 1446866677460907920663248896, 215191071517260994220035932160, 1484693257263807474144641024, 47283224753624441851740160, 1446866677460907920663248896] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent1
