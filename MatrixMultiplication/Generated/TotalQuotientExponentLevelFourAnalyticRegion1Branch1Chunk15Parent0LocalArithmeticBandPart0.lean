import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk15Parent0LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 1,
parent 62; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [2491046388265846356539747598336, 2824050714619773752113627136, 97697799529816183706651904180224, 31219300365728183807612289024, 2766022275278271551727730688, 97697818112328293798705820073984, 2766022275278271551727730688, 2746679462164437484932431872, 111240518217659718139763490816, 2804707901505939685318328320, 31219300365728183807612289024, 111240518217659718139763490816, 2491069060347330613706418552832, 2746679462164437484932431872, 2804707901505939685318328320, 2824050714619773752113627136, 76030216859277399315667287539712, 4845374685015433732222353408, 251456570479842868338884608, 277876939526239673137754433126400, 7804825091432045951903072256, 76030132590642200410432231964672, 7804825091432045951903072256, 8133652914367225087423152128, 4845374685015433732222353408, 241785163922925834941235200, 76113802954674999001704529133568, 0, 76113810469302552949082795540480, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4845374685015433732222353408, 0, 4845374685015433732222353408, 0, 2480293918684204872481198047232, 251456570479842868338884608, 0, 251456570479842868338884608, 0, 2030995376952577013506375680, 76030224394527782633505000783872, 4845374685015433732222353408, 251456570479842868338884608, 277876967848831526915546795737088, 7804825091432045951903072256, 76030140121903207921102379548672, 7804825091432045951903072256, 8133652914367225087423152128, 4845374685015433732222353408, 241785163922925834941235200, 278185136541922553620790427779072, 0, 278185164792430198212757001601024, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band0

namespace Band1

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 64, upper := 128, values := [97311096125820186378291849986048, 7804825091432045951903072256, 0, 7804825091432045951903072256, 0, 22921233539893369152429096960, 2030995376952577013506375680, 76113718511315704061356001984512, 0, 76113726021946954539439900065792, 0, 97311114424990307498167053058048, 2030995376952577013506375680, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7804825091432045951903072256, 0, 7804825091432045951903072256, 0, 2030995376952577013506375680, 8133652914367225087423152128, 0, 8133652914367225087423152128, 0, 84199265484519692759935746048, 2089023816294079213892272128, 4845374685015433732222353408, 0, 4845374685015433732222353408, 0, 22921233539893369152429096960, 84199265484519692759935746048, 2480316373536830917644189171712, 241785163922925834941235200, 0, 241785163922925834941235200, 0, 2030995376952577013506375680, 2089023816294079213892272128, 2030995376952577013506375680, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band1

namespace Band2

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 128, upper := 192, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band2

namespace Band3

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 192, upper := 256, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15.Parent0
