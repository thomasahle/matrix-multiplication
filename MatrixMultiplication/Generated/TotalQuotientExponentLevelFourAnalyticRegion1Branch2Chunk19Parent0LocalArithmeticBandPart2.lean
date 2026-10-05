import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk19Parent0LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 1, branch 2,
parent 78; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [0, 0, 60296071087123767663853043712, 0, 0, 0, 259239371081188108771635757056, 0, 0, 942909474214015196975144632320, 0, 259239371081188108771635757056, 0, 0, 0, 0, 310077189025826956048003497984, 0, 11650396557408557574290656985088, 0, 0, 11649515413269351588072234418176, 0, 0, 0, 0, 0, 0, 310958333165032942266426064896, 0, 0, 0, 6065121119253630128136394899456, 0, 0, 22060152907132063879230987960320, 0, 6065121119253630128136394899456, 0, 0, 0, 0, 284484423871714537391857336320, 0, 284484423871714537391857336320, 0, 486073820777227703946817044480, 0, 0, 1767955264151278494328396185600, 0, 486073820777227703946817044480, 0, 0, 0, 0, 639705515300720257054122442752, 0, 639705515300720257054122442752, 0, 0, 47840530446999790821958483968, 7672600743761393533285564416, 1538084704604573474591264997376] }

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
  { lower := 576, upper := 640, values := [60371253220648859643483783168, 7268779651984478084165271552, 1538066102863288679366398050304, 7268779651984478084165271552, 7268779651984478084165271552, 311346061760001811271745798144, 7268779651984478084165271552, 60371253220648859643483783168, 311346061760001811271745798144, 47859132188284586046825431040, 7268779651984478084165271552, 7268779651984478084165271552, 7672600743761393533285564416, 919629979339221984686957920256, 38205416915039255874729148416, 2146371736799958195209502720, 3329781771218859984243260391424, 58023582618158869877163556864, 919629749739159117981340925952, 58023582618158869877163556864, 58023582618158869877163556864, 38205416915039255874729148416, 2146371736799958195209502720, 203341083830882606075636350976, 10340960753931617932664635392, 203341083830882606075636350976, 10340960753931617932664635392, 491474641008085789546226122752, 0, 0, 1787599211530737144265378365440, 0, 491474641008085789546226122752, 0, 0, 0, 0, 284484423871714537391857336320, 0, 284484423871714537391857336320, 0, 0, 20503381900664110803016744960, 0, 20503381900664110803016744960, 0, 0, 14848406882541305793085440, 2193031991947783373366231040, 0, 22857605692845384823052697600, 0, 0, 0, 0, 0, 0, 0, 2193031991947783373366231040, 0, 0, 0, 0, 0] }

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
  { lower := 640, upper := 704, values := [0, 14848406882541305793085440, 7239156164027088468046774272, 0, 271993693947281499788886933504, 0, 0, 271973122488778636297406251008, 0, 0, 0, 0, 0, 0, 7259727622529951959527456768, 0, 0, 0, 18902870808003299597931773952, 0, 0, 68753815828105274779437629440, 0, 18902870808003299597931773952, 0, 0, 0, 0, 7239156164027088468046774272, 0, 271993693947281499788886933504, 0, 0, 271973122488778636297406251008, 0, 0, 0, 0, 0, 0, 7259727622529951959527456768, 0, 0, 0, 486073820777227703946817044480, 0, 0, 1767955264151278494328396185600, 0, 486073820777227703946817044480, 0, 0, 0, 0, 19990797353147508032941326336, 0, 19990797353147508032941326336, 0, 18902870808003299597931773952, 0, 0, 68753815828105274779437629440, 0, 18902870808003299597931773952] }

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
  { lower := 704, upper := 768, values := [0, 0, 0, 0, 19990797353147508032941326336, 0, 19990797353147508032941326336, 0, 0, 7641331506473037827382706176, 0, 287104454722130471999380652032, 0, 0, 287082740404821893869484376064, 0, 0, 0, 0, 0, 0, 7663045823781615957278982144, 0, 0, 0, 491474641008085789546226122752, 0, 0, 1787599211530737144265378365440, 0, 491474641008085789546226122752, 0, 0, 0, 0, 19990797353147508032941326336, 0, 19990797353147508032941326336, 0, 491474641008085789546226122752, 0, 0, 1787599211530737144265378365440, 0, 491474641008085789546226122752, 0, 0, 0, 0, 639705515300720257054122442752, 0, 639705515300720257054122442752, 0, 0, 19990797353147508032941326336, 0, 19990797353147508032941326336, 0, 0, 20542596021876388540509585408, 258678203306911089008050176, 14532483331848937584721920, 74636498373509629527808016384, 392861466070982946040315904] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19.Parent0
