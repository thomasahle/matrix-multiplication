import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk4Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 1, for region 1, branch 2,
parent 19; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band4

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 256, upper := 320, values := [1397523738701287187819664506880, 72787694724025374365607526400, 2241860997499981530460711813120, 1266505888198041513961570959360, 214996644010704030244987207680, 203000188143362720133021696, 17070131922510458928068820992, 0, 0, 0, 0, 17070127804274844472411422720, 0, 0, 0, 0, 0, 0, 0, 203004306378977175790419968, 0, 1487999923761054261392179200, 219769801746256589118190387200, 0, 2290623889644718351416557568000, 0, 0, 0, 0, 0, 0, 0, 219769801746256589118190387200, 0, 0, 0, 0, 0, 0, 1487999923761054261392179200, 297423026326983559133156868096, 22011485900079275986194006016, 9648880984539522974931482574848, 544667193655153148339226148864, 17328191027721983223174004736, 9648885675370364605447352090624, 17796520514957712499476004864, 17796520514957712499476004864, 301135860292573924662186082304, 16391532053250524670570004480, 544667193655153148339226148864, 301135860292573924662186082304, 297420631478900312352051167232, 17328191027721983223174004736, 16391532053250524670570004480, 22011485900079275986194006016, 47388532603855231254528000, 6999038272173776723509248000, 0, 72949805402698036669317120000, 0, 0, 0, 0] }

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
  { lower := 320, upper := 384, values := [0, 0, 0, 6999038272173776723509248000, 0, 0, 0, 0, 0, 0, 47388532603855231254528000, 7217132098215396644214538240, 0, 261551256118508961476462510080, 0, 0, 261551352237574800549294899200, 0, 0, 0, 0, 0, 0, 7217035979149557571382149120, 0, 0, 0, 13956381777734665905289297920, 0, 0, 47601997642006026202596245504, 0, 13956378544917997189739839488, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 203000188143362720133021696, 17070131922510458928068820992, 0, 0, 0, 0, 17070127804274844472411422720, 0, 0, 0, 0, 0, 0] }

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
  { lower := 384, upper := 448, values := [0, 203004306378977175790419968, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3434976867794269185408761856, 288844600688795397124953997312, 0, 0, 0, 0, 288844531003913815677909073920, 0, 0, 0, 0, 0, 0, 0, 3435046552675850632453685248, 0, 1450089097677970076388556800, 214170571128517567739382988800, 0, 2232264045322559922081103872000, 0, 0, 0, 0, 0, 0, 0, 214170571128517567739382988800, 0, 0, 0, 0, 0, 0, 1450089097677970076388556800, 186973857500465663280414720, 15722489928628054275852861440, 0, 0, 0, 0, 15722486135516304119326310400, 0, 0, 0, 0, 0, 0, 0, 186977650612215819806965760, 0] }

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
  { lower := 448, upper := 512, values := [824560467307081023828787200, 121783265935823714989060915200, 0, 1269326614006945838046117888000, 0, 0, 0, 0, 0, 0, 0, 121783265935823714989060915200, 0, 0, 0, 0, 0, 0, 824560467307081023828787200, 6392317001276494170590019584, 0, 231659683990679365879152508928, 0, 0, 231659769124709109057946910720, 0, 0, 0, 0, 0, 0, 6392231867246750991795617792, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6212874179229759039860637696, 522435879628412203509053652992, 0, 0, 0, 0, 522435753588727476879328542720, 0, 0, 0, 0, 0, 0, 0, 6213000218914485669585747968, 0, 1487999923761054261392179200, 219769801746256589118190387200, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent1
