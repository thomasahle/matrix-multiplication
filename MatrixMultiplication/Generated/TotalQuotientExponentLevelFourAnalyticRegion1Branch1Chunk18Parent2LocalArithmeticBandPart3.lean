import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk18Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 1,
parent 76; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 0, 0, 0, 0, 0, 105489716680612105257222144, 0, 47872731965673996420120576, 5658249564226933450422091776, 0, 53695660468046469432644468736, 0, 0, 0, 0, 0, 0, 0, 5658253444960717957069012992, 0, 0, 0, 0, 0, 0, 47872731965673996420120576, 105491934901586968830803968, 18502294280606785288246657024, 0, 0, 0, 0, 18502296498827760151820238848, 0, 0, 0, 0, 0, 0, 0, 105489716680612105257222144, 0, 1236712242446578240853114880, 146171447075862447469237370880, 0, 1387137895424533793676648775680, 0, 0, 0, 0, 0, 0, 0, 146171547328151880557616168960, 0, 0, 0, 0, 0, 0, 1236712242446578240853114880, 2011865566086719061689892864, 0] }

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
  { lower := 832, upper := 896, values := [78473589395189594211729014784, 0, 0, 78473560611351310197187411968, 0, 0, 0, 0, 0, 0, 2011875160699480399870427136, 0, 0, 0, 47872731965673996420120576, 5658249564226933450422091776, 0, 53695660468046469432644468736, 0, 0, 0, 0, 0, 0, 0, 5658253444960717957069012992, 0, 0, 0, 0, 0, 0, 47872731965673996420120576, 2011865566086719061689892864, 0, 78473589395189594211729014784, 0, 0, 78473560611351310197187411968, 0, 0, 0, 0, 0, 0, 2011875160699480399870427136, 0, 0, 0, 742570030231851405810860032, 0, 0, 2712250635422256182643916800, 0, 742569780047884906125066240, 0, 0, 0, 0, 116896468404461235731431424, 20502542310942653968057106432, 0, 0, 0] }

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
  { lower := 896, upper := 960, values := [0, 20502544768971301789854859264, 0, 0, 0, 0, 0, 0, 0, 116894010375813413933678592, 0, 1260648608429415239063175168, 149000571857975914194448416768, 0, 1413985725658557028392971010048, 0, 0, 0, 0, 0, 0, 0, 149000674050632239536150675456, 0, 0, 0, 0, 0, 0, 1260648608429415239063175168, 1958921735400226454803316736, 0, 76408494937421446995630882816, 0, 0, 76408466911052591507787743232, 0, 0, 0, 0, 0, 0, 1958931077523178284084363264, 0, 0, 0, 1260648608429415239063175168, 149000571857975914194448416768, 0, 1413985725658557028392971010048, 0, 0, 0, 0, 0, 0, 0, 149000674050632239536150675456, 0, 0, 0, 0, 0, 0] }

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
  { lower := 960, upper := 1024, values := [1260648608429415239063175168, 60726573797407020098902818816, 0, 2368663343060064856864557367296, 0, 0, 2368662474242630336741420040192, 0, 0, 0, 0, 0, 0, 60726863403218526806615261184, 0, 0, 0, 15186754811838509396260814848, 0, 0, 55469900092184207090201395200, 0, 15186749695172871951073935360, 0, 0, 0, 0, 1958921735400226454803316736, 0, 76408494937421446995630882816, 0, 0, 76408466911052591507787743232, 0, 0, 0, 0, 0, 0, 1958931077523178284084363264, 0, 0, 0, 15162800939895546447686270976, 0, 0, 55382408136202843987535462400, 0, 15162795831300359534747320320, 0, 0, 0, 0, 0, 0, 0, 0, 95830798569432973226016768, 6377620563283318102510534656, 1262895753898986389221933056, 53743618534650228409450364928, 799301110062649613431603200, 47958066603758976805896192, 1262895753898986389221933056] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent2
