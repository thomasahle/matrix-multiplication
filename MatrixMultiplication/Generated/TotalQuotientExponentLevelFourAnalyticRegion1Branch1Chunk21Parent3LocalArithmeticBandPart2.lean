import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk21Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 1, branch 1,
parent 89; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [0, 0, 25409533617558145569380106240, 0, 0, 0, 41405978644264525393140121600, 0, 0, 151236095339213363179683840000, 0, 41405964693914319650291712000, 0, 0, 0, 0, 82802700677765218195073925120, 0, 3229751154019032433724982558720, 0, 0, 3229749969357598805051509309440, 0, 0, 0, 0, 0, 0, 82803095564909761086231674880, 0, 0, 0, 1003266862550529450275785146368, 0, 0, 3664450590069139789843739443200, 0, 1003266524533543965126568181760, 0, 0, 0, 0, 19033328104012721726574034944, 0, 19033328104012721726574034944, 0, 64179266898610014359367188480, 0, 0, 234415947775780712928509952000, 0, 64179245275567195457952153600, 0, 0, 0, 0, 33279309962351511921311612928, 0, 33279309962351511921311612928, 0, 0, 4281933215792434732005851136, 2448240777746171354180222976, 85080379684660047347756040192] }

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
  { lower := 576, upper := 640, values := [25616958381783110023007698944, 2269101208642792962410938368, 85080349178357035450585055232, 2269101208642792962410938368, 2209388018941666831821176832, 83479039202174330564486627328, 2209388018941666831821176832, 25616958381783110023007698944, 83479039202174330564486627328, 4281943384560105364396179456, 2209388018941666831821176832, 2209388018941666831821176832, 2448240777746171354180222976, 38677422637760533663076843520, 28240837158449216185014681600, 1462471924276834409581117440, 162386550375920672633845186560, 39335451756411408257699020800, 38677410082445348494513274880, 39385881822765781858029404160, 39385881822765781858029404160, 28190407092094842584684298240, 1462471924276834409581117440, 10401278032995983885223329792, 10308971853816714596024582144, 10401278032995983885223329792, 10308971853816714596024582144, 65421446257937950121161392128, 0, 0, 238953030635957113823900467200, 0, 65421424216384625047460904960, 0, 0, 0, 0, 19033328104012721726574034944, 0, 19033328104012721726574034944, 0, 0, 1073526127817790707139084288, 0, 1073526127817790707139084288, 0, 0, 12373522522322155937464320, 1462470921235125401624248320, 0, 13878557518479033988829675520, 0, 0, 0, 0, 0, 0, 0, 1462471924276834409581117440, 0, 0, 0, 0, 0] }

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
  { lower := 640, upper := 704, values := [0, 12373522522322155937464320, 2191487786178335531629281280, 0, 85479823103508011479130439680, 0, 0, 85479791749807693695926927360, 0, 0, 0, 0, 0, 0, 2191498237411774792697118720, 0, 0, 0, 2484358718655871523588407296, 0, 0, 9074165720352801790781030400, 0, 2484357881634859179017502720, 0, 0, 0, 0, 2191487786178335531629281280, 0, 85479823103508011479130439680, 0, 0, 85479791749807693695926927360, 0, 0, 0, 0, 0, 0, 2191498237411774792697118720, 0, 0, 0, 64179266898610014359367188480, 0, 0, 234415947775780712928509952000, 0, 64179245275567195457952153600, 0, 0, 0, 0, 1102540347488541807332032512, 0, 1102540347488541807332032512, 0, 2484358718655871523588407296, 0, 0, 9074165720352801790781030400, 0, 2484357881634859179017502720] }

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
  { lower := 704, upper := 768, values := [0, 0, 0, 0, 1102540347488541807332032512, 0, 1102540347488541807332032512, 0, 0, 2428405384684101535048663040, 0, 94720885060644012720117514240, 0, 0, 94720850317354471392783892480, 0, 0, 0, 0, 0, 0, 2428416965780615310826536960, 0, 0, 0, 65421446257937950121161392128, 0, 0, 238953030635957113823900467200, 0, 65421424216384625047460904960, 0, 0, 0, 0, 1073526127817790707139084288, 0, 1073526127817790707139084288, 0, 65421446257937950121161392128, 0, 0, 238953030635957113823900467200, 0, 65421424216384625047460904960, 0, 0, 0, 0, 33279309962351511921311612928, 0, 33279309962351511921311612928, 0, 0, 1073526127817790707139084288, 0, 1073526127817790707139084288, 0, 0, 2496305567987768777596993536, 238936986637945080171724800, 12373522522322155937464320, 9296462452564175695726510080, 332805088531423504524902400] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21.Parent3
