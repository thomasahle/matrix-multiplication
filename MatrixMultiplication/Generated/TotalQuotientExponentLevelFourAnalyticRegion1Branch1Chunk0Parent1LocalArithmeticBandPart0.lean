import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk0Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 1,
parent 2; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [2900019424229697734666354688, 0, 115942238514266257264585211904, 0, 0, 115942210180067360046713929728, 0, 0, 0, 0, 0, 0, 2900019424229697734666354688, 0, 0, 0, 3584598489680632681045426176, 4845374685015433732222353408, 251456570479842868338884608, 17425187639764287557138907136, 7804825091432045951903072256, 3594272151352012725435760640, 7804825091432045951903072256, 8133652914367225087423152128, 4845374685015433732222353408, 241785163922925834941235200, 3584598489680632681045426176, 3667851394250150870211624960, 3584598489680632681045426176, 3667851394250150870211624960, 3667851394250150870211624960, 0, 0, 13361104776050129871893954560, 0, 3667853861502170728864153600, 0, 0, 0, 0, 4845374685015433732222353408, 0, 4845374685015433732222353408, 0, 3499646630758553805320617984, 251456570479842868338884608, 0, 251456570479842868338884608, 0, 676998458984192337835458560, 3584598489680632681045426176, 4845374685015433732222353408, 251456570479842868338884608, 17425187639764287557138907136, 7804825091432045951903072256, 3594272151352012725435760640, 7804825091432045951903072256, 8133652914367225087423152128, 4845374685015433732222353408, 241785163922925834941235200, 17425187639764287557138907136, 13361104776050129871893954560, 17425187639764287557138907136, 13361104776050129871893954560] }

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
  { lower := 64, upper := 128, values := [116522522907681279268444176384, 7804825091432045951903072256, 0, 7804825091432045951903072256, 0, 7640411179964456384143032320, 676998458984192337835458560, 3594272151352012725435760640, 3667853861502170728864153600, 3594272151352012725435760640, 3667853861502170728864153600, 116522494573482382050572894208, 676998458984192337835458560, 3667851394250150870211624960, 0, 0, 13361104776050129871893954560, 0, 3667853861502170728864153600, 0, 0, 0, 0, 7804825091432045951903072256, 0, 7804825091432045951903072256, 0, 676998458984192337835458560, 8133652914367225087423152128, 0, 8133652914367225087423152128, 0, 28066421828173230919978582016, 696341272098026404630757376, 4845374685015433732222353408, 0, 4845374685015433732222353408, 0, 7640411179964456384143032320, 28066421828173230919978582016, 3499646630758553805320617984, 241785163922925834941235200, 0, 241785163922925834941235200, 0, 676998458984192337835458560, 696341272098026404630757376, 676998458984192337835458560, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0.Parent1
