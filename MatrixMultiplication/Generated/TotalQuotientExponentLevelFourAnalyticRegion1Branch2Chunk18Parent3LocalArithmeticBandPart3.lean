import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk18Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 2,
parent 77; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 151821152592461470590226661376, 0, 0, 0, 0, 0, 0, 0, 15214832933034496031547457536, 0, 0, 0, 0, 0, 0, 95291978398411954078089216, 962074792387437148990603264, 0, 35528142146860529860340613120, 0, 0, 35528133446914856097073332224, 0, 0, 0, 0, 0, 0, 962083492333110912257884160, 0, 0, 0, 95302852754043405858766848, 15214832933034496031547457536, 0, 151821152592461470590226661376, 0, 0, 0, 0, 0, 0, 0, 15214832933034496031547457536, 0, 0, 0, 0, 0, 0, 95291978398411954078089216, 24739066089962669545472655360, 0, 913580798062127910694472908800, 0, 0, 913580574349239156781885685760, 0, 0, 0, 0, 0, 0] }

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
  { lower := 832, upper := 896, values := [24739289802851423458059878400, 0, 0, 0, 7303711174408176559265415168, 0, 0, 26128544496970880254388207616, 0, 7303708746355487857245683712, 0, 0, 0, 0, 962074792387437148990603264, 0, 35528142146860529860340613120, 0, 0, 35528133446914856097073332224, 0, 0, 0, 0, 0, 0, 962083492333110912257884160, 0, 0, 0, 7303711174408176559265415168, 0, 0, 26128544496970880254388207616, 0, 7303708746355487857245683712, 0, 0, 0, 0, 299813603264428035327131648, 0, 299813603264428035327131648, 0, 100597455684823595073142784, 16060101429314190255522316288, 0, 160255661069820441178572587008, 0, 0, 0, 0, 0, 0, 0, 16060101429314190255522316288, 0, 0, 0, 0, 0, 0, 100585977198323729304649728, 25013944602073365873755684864] }

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
  { lower := 896, upper := 960, values := [0, 923731695818373776368855941120, 0, 0, 923731469619786258523906637824, 0, 0, 0, 0, 0, 0, 25014170800660883718704988160, 0, 0, 0, 7303711174408176559265415168, 0, 0, 26128544496970880254388207616, 0, 7303708746355487857245683712, 0, 0, 0, 0, 25013944602073365873755684864, 0, 923731695818373776368855941120, 0, 0, 923731469619786258523906637824, 0, 0, 0, 0, 0, 0, 25014170800660883718704988160, 0, 0, 0, 233718757581061649896493285376, 0, 0, 836113423903068168140422643712, 0, 233718679883375611431861878784, 0, 0, 0, 0, 6218714416097652474688569344, 0, 6218714416097652474688569344, 0, 7303711174408176559265415168, 0, 0, 26128544496970880254388207616, 0, 7303708746355487857245683712, 0, 0, 0] }

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
  { lower := 960, upper := 1024, values := [0, 6247728635768403574881517568, 0, 6247728635768403574881517568, 0, 0, 905783243127683218856214528, 96362901819768152883462144, 30526233378021104297718054912, 758223885371333624004083712, 91291170145043513258016768, 30526225920924812500631814144, 91291170145043513258016768, 91291170145043513258016768, 3910305121212697151218384896, 91291170145043513258016768, 758223885371333624004083712, 3910305121212697151218384896, 905790700223975015942455296, 91291170145043513258016768, 91291170145043513258016768, 96362901819768152883462144, 8447818607947362245416058880, 364180177848960174262321152, 20459560553312369340579840, 30472263615522051269622497280, 553090120291211051173675008, 8447815806348106050777907200, 553090120291211051173675008, 553090120291211051173675008, 364180177848960174262321152, 20459560553312369340579840, 299813603264428035327131648, 0, 299813603264428035327131648, 0, 8801908338389340981678833664, 0, 0, 31488245932246958255288352768, 0, 8801905412274562289501208576, 0, 0, 0, 0, 7176183665232438781055860736, 0, 7176183665232438781055860736, 0, 0, 299813603264428035327131648, 0, 299813603264428035327131648, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18.Parent3
