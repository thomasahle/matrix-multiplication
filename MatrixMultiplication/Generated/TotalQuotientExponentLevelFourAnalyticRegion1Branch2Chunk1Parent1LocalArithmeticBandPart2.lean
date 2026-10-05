import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 1, branch 2,
parent 6; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [1419534862675094816119848960000, 0, 0, 0, 0, 0, 0, 0, 131694580158581067109556551680, 0, 0, 0, 0, 0, 0, 1256049070744881893505761280, 3669761543069768448212992000, 307265959261812855286215475200, 0, 0, 0, 0, 307266070461091974616606310400, 0, 0, 0, 0, 0, 0, 0, 3669650343790649117822156800, 0, 19608766066214684847023063040, 2055943756316400545117566402560, 0, 22161018779723932447832801280000, 0, 0, 0, 0, 0, 0, 0, 2055945324641287869334542090240, 0, 0, 0, 0, 0, 0, 19608766066214684847023063040, 96290076496453228752667672576, 0, 3369912606079332303284551548928, 0, 0, 3369914258893766249605094178816, 0, 0, 0, 0, 0, 0, 96289250089236255592396357632] }

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
  { lower := 576, upper := 640, values := [0, 0, 0, 768030005041456444436643840, 80526560834914097238386933760, 0, 867995839597510206035066880000, 0, 0, 0, 0, 0, 0, 0, 80526622262571862691193815040, 0, 0, 0, 0, 0, 0, 768030005041456444436643840, 26212667275051016786563563520, 0, 917378000965772749688075714560, 0, 0, 917378450904919137556176568320, 0, 0, 0, 0, 0, 0, 26212442305477822852513136640, 0, 0, 0, 8941344147813547979361484800, 0, 0, 30571061442595610403652239360, 0, 8941341259745178939209809920, 0, 0, 0, 0, 2568359477288567990114058240, 25297393858862333207620091904, 2294411492735925866452746240, 2032193036423248624572432384, 95119745027423669492083851264, 25894072560876877635680993280, 25297402159897166376918319104, 95119745027423669492083851264, 2294411492735925866452746240, 2294411492735925866452746240, 1966638422345079314102353920, 2294411492735925866452746240, 25894072560876877635680993280, 1966638422345079314102353920, 2568351176253734820815831040, 2032193036423248624572432384] }

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
  { lower := 640, upper := 704, values := [6430851972945312318272569344, 271565653779333759687395901440, 131345450095843565227393155072, 1450952067632969414150843269120, 134779318072205488501311930368, 4292334970452404092398469120, 131345450095843565227393155072, 74686628485871831207733362688, 134779318072205488501311930368, 2104102602515768486093729562624, 82412831432686158574050607104, 271565756158763368775407370240, 131345450095843565227393155072, 4292334970452404092398469120, 82412831432686158574050607104, 4292334970452404092398469120, 132203917089934046045872848896, 74686628485871831207733362688, 6430851972945312318272569344, 24408941198053005578112860160, 21561189889898086927995764736, 100582836944516457469694705664, 533524762594712236111895199744, 16973702679281472687996665856, 100582877951628533326027948032, 17432451400343134111996575744, 17432451400343134111996575744, 294975427642648295631942057984, 16056205237158149839996846080, 533524762594712236111895199744, 294975427642648295631942057984, 24408920694496967649946238976, 16973702679281472687996665856, 16056205237158149839996846080, 21561189889898086927995764736, 1224047820534821208320901120, 128339206330644342473679175680, 0, 1383368369358531890868387840000, 0, 0, 0, 0, 0, 0, 0, 128339304230973906164090142720, 0, 0, 0, 0, 0, 0, 1224047820534821208320901120, 96290076496453228752667672576, 0, 3369912606079332303284551548928, 0, 0, 3369914258893766249605094178816, 0, 0, 0, 0] }

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
  { lower := 704, upper := 768, values := [0, 0, 96289250089236255592396357632, 0, 0, 0, 15009322212197991717850316800, 0, 0, 51317889567311194310322421760, 0, 15009317364163064846058782720, 0, 0, 0, 0, 2322641404118444525391708160, 0, 81286658313422901871095316480, 0, 0, 81286698181448531175863746560, 0, 0, 0, 0, 0, 0, 2322621470105629873007493120, 0, 0, 0, 14402524405759547344001433600, 0, 0, 49243206754839635919655403520, 0, 14402519753721276255373885440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 211168238092661636988928000, 17680933892203850148662476800, 0, 0, 0, 0, 17680940290918200716663193600, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent1
