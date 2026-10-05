import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk14Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 1, branch 2,
parent 60; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [128456056936984271953644748800, 9366587484988436496619929600, 243531274609699348912118169600, 243531274609699348912118169600, 128456056936984271953644748800, 3005336498754861195915480268800, 240855106756845509913083904000, 125045815107710098104406507520, 243531274609699348912118169600, 9366587484988436496619929600, 240855106756845509913083904000, 9366587484988436496619929600, 243531274609699348912118169600, 243531274609699348912118169600, 8107711479537296229500190720, 2834046299645356138743988224, 238312804790523954598246350848, 0, 0, 0, 0, 238312747296634362864001351680, 0, 0, 0, 0, 0, 0, 0, 2834103793534947872988987392, 0, 1256154649531666265517588480, 200541563850174782298768015360, 0, 2001103232643639739586193653760, 0, 0, 0, 0, 0, 0, 0, 200541563850174782298768015360, 0, 0, 0, 0, 0, 0, 1256011318330213542301532160, 6014682727530862082275672064, 2436926144450540310779396096, 148190882925156756889763053568, 19174760978702935603237879808, 2308666873689985557580480512, 148190847092356393708959039488, 2308666873689985557580480512, 2308666873689985557580480512, 98887897756387714716363915264, 2308666873689985557580480512, 19174760978702935603237879808, 98887897756387714716363915264, 6014718560331225263079686144, 2308666873689985557580480512] }

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
  { lower := 576, upper := 640, values := [2308666873689985557580480512, 2436926144450540310779396096, 90533668434714685803069440, 14453446043255840165676974080, 0, 144223656406748810060266209280, 0, 0, 0, 0, 0, 0, 0, 14453446043255840165676974080, 0, 0, 0, 0, 0, 0, 90523338258033408454164480, 4597967838942556764007038976, 0, 169796835195385389462407086080, 0, 0, 169796793616424247321077743616, 0, 0, 0, 0, 0, 0, 4598009417903698905336381440, 0, 0, 0, 3551282166473871223498473472, 0, 0, 12704477476209962668800344064, 0, 3551280985882250506087170048, 0, 0, 0, 0, 0, 0, 0, 0, 238349107351060030471274496, 0, 2308666873689985557580480512, 0, 0, 0, 0, 238349107351060030471274496, 0, 0, 109001780755590620720922624, 9165877107327844407624859648, 0] }

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
  { lower := 640, upper := 704, values := [0, 0, 0, 9165874896024398571692359680, 0, 0, 0, 0, 0, 0, 0, 109003992059036456653422592, 0, 238349107351060030471274496, 0, 2308666873689985557580480512, 0, 0, 0, 0, 238349107351060030471274496, 0, 0, 2802902933715187389966581760, 235693982759858856196067819520, 0, 0, 0, 0, 235693925897770248986374963200, 0, 0, 0, 0, 0, 0, 0, 2802959795803794599659438080, 0, 88270326723846818657992704, 14092109892174444161535049728, 0, 140618064996580089808759554048, 0, 0, 0, 0, 0, 0, 0, 14092109892174444161535049728, 0, 0, 0, 0, 0, 0, 88260254801582573242810368, 109001780755590620720922624, 9165877107327844407624859648, 0, 0, 0, 0] }

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
  { lower := 704, upper := 768, values := [9165874896024398571692359680, 0, 0, 0, 0, 0, 0, 0, 109003992059036456653422592, 0, 88270326723846818657992704, 14092109892174444161535049728, 0, 140618064996580089808759554048, 0, 0, 0, 0, 0, 0, 0, 14092109892174444161535049728, 0, 0, 0, 0, 0, 0, 88260254801582573242810368, 221330750011210030565556224, 0, 8173450141392774958594129920, 0, 0, 8173448139921042961107779584, 0, 0, 0, 0, 0, 0, 221332751482942028051906560, 0, 0, 0, 251590724426118921053011968, 0, 2436926144450540310779396096, 0, 0, 0, 0, 251590724426118921053011968, 0, 0, 2834046299645356138743988224, 238312804790523954598246350848, 0, 0, 0, 0, 238312747296634362864001351680, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent2
