import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk2Parent0LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 1, for region 1, branch 2,
parent 9; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk2.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band4

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 256, upper := 320, values := [13668787826052928164530749440, 0, 13662607103794608217226477568, 0, 39842884635593685977020760064, 435311714205507266386329600, 0, 435114875917025739402117120, 0, 676998458984192337835458560, 74092984720590955788369920, 7768515816281127248598138880, 0, 83736835877087133239869440000, 0, 0, 0, 0, 0, 0, 0, 7768521742297660927791595520, 0, 0, 0, 0, 0, 0, 74092984720590955788369920, 4716748697594379651564699648, 0, 165074444574951123799762796544, 0, 0, 165074525537710863310984839168, 0, 0, 0, 0, 0, 0, 4716708216214509895953678336, 0, 0, 0, 6917494993398265861877268480, 0, 0, 23651384062175765653604007936, 0, 6917492759036389933807828992, 0, 0, 0, 0, 4227771559885233435692761088, 0, 147961463877388407616374308864, 0, 0, 147961536446879593589750366208, 0, 0, 0] }

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
  { lower := 320, upper := 384, values := [0, 0, 0, 4227735275139640449004732416, 0, 0, 0, 117051296861975919715449569280, 0, 0, 400206314525763613559667818496, 0, 117051259054221019143116685312, 0, 0, 0, 0, 13320538454688522351421685760, 0, 13314515203060987625704783872, 0, 6371376967603665925413273600, 0, 0, 21784169530951363102003691520, 0, 6371374909638780202191421440, 0, 0, 0, 0, 7574423827175826435122135040, 0, 7570998840956247865596837888, 0, 599627206528856070654263296, 5717271148599248062502666240, 0, 200090235848425604605773086720, 0, 0, 200090333985104076740587683840, 0, 0, 0, 0, 0, 0, 5717222080260011995095367680, 0, 0, 0, 211711754666373242035875348480, 0, 0, 723856833271326722503722663936, 0, 211711686283140039289960660992, 0, 0, 0, 0, 13668787826052928164530749440, 0] }

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
  { lower := 384, upper := 448, values := [13662607103794608217226477568, 0, 117051296861975919715449569280, 0, 0, 400206314525763613559667818496, 0, 117051259054221019143116685312, 0, 0, 0, 0, 213389802303539661982578769920, 0, 213293312174526017454917812224, 0, 28066421828173230919978582016, 8357984912745739514617528320, 0, 8354205617606894196520648704, 0, 7640411179964456384143032320, 8971090892303152104276492288, 5717222080260011995095367680, 233202479589553120852574208, 34667367322124161405704732672, 4709185555582588827539079168, 8971088069951308826715095040, 4716708216214509895953678336, 4227735275139640449004732416, 5717222080260011995095367680, 233202479589553120852574208, 21675825813579250472792883200, 7692952464648850996587397120, 21669526988347841609298083840, 7768521742297660927791595520, 39842898802693134585956401152, 13320538454688522351421685760, 0, 13314515203060987625704783872, 0, 28066421828173230919978582016, 676998458984192337835458560, 233204481061285118338924544, 0, 8161575409606833872077586432, 0, 0, 8161579412550297867050287104, 0, 0, 0, 0, 0, 0, 233202479589553120852574208, 0, 0, 0, 6735455651466732549722603520, 0, 0, 23028979218434298136403902464, 0] }

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
  { lower := 448, upper := 512, values := [6735453475903853356602359808, 0, 0, 0, 0, 435311714205507266386329600, 0, 435114875917025739402117120, 0, 6371376967603665925413273600, 0, 0, 21784169530951363102003691520, 0, 6371374909638780202191421440, 0, 0, 0, 0, 8357984912745739514617528320, 0, 8354205617606894196520648704, 0, 676998458984192337835458560, 435311714205507266386329600, 0, 435114875917025739402117120, 0, 580284393415022003858964480, 8555849070782065671269253120, 0, 0, 29253027655848973308404957184, 0, 8555846307229219128657051648, 0, 0, 0, 0, 13407600797529623804698951680, 0, 13401538178244392773585207296, 0, 676998458984192337835458560, 7574423827175826435122135040, 0, 7570998840956247865596837888, 0, 7640411179964456384143032320, 580284393415022003858964480, 596250817103618184335851520, 73372235841985985401323520, 596014611157440351954796544, 74092984720590955788369920, 1144522185521252953281789952, 599627206528856070654263296, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk2.Parent0
