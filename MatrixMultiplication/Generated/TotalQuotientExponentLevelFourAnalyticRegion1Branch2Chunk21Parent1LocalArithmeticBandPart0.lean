import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk21Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 2,
parent 87; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk21.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [376427666755534500725117681664, 38956425611261810525731815424, 12758754448728007291549899554816, 306525559414928456505100337152, 36906087421195399445430140928, 12758501599059415002136222629888, 36906087421195399445430140928, 36906087421195399445430140928, 1580810744541202942912591036416, 36906087421195399445430140928, 306525559414928456505100337152, 1580810744541202942912591036416, 376680544758325687356665888768, 36906087421195399445430140928, 36906087421195399445430140928, 38956425611261810525731815424, 10323354534687768638392050384896, 144606870839023483361653948416, 8123981507810308054025502720, 37267458976879517746007747067904, 219618300094471994393822756864, 10323353325761660793386723966976, 219618300094471994393822756864, 219618300094471994393822756864, 144606870839023483361653948416, 8123981507810308054025502720, 10418012212499553289882623279104, 31064894255642439440633167872, 10418010475088291348835014279168, 31064894255642439440633167872, 27181782473687134510554021888, 0, 0, 92138901576804952886485188608, 0, 27181782473687134510554021888, 0, 0, 0, 0, 149771401940417179195998732288, 0, 149771401940417179195998732288, 0, 382903353466163987813754732544, 8414123704517819055954984960, 0, 8414123704517819055954984960, 0, 40426479407913199602174525440, 10323352800663273289822117036032, 144606870839023483361653948416, 8123981507810308054025502720, 37267452773521375065361912692736, 219618300094471994393822756864, 10323351591737741905569094041600, 219618300094471994393822756864, 219618300094471994393822756864, 144606870839023483361653948416, 8123981507810308054025502720, 37616986049380497728900704501760, 105301601802062803298840215552, 37616979833906421175831733731328, 105301601802062803298840215552] }

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
  { lower := 64, upper := 128, values := [12952708991502926404594148835328, 227461810812131708479316426752, 0, 227461810812131708479316426752, 0, 318092561657001228448689029120, 38298769965391452254691655680, 10418011001212261640492520833024, 31064894255642439440633167872, 10418009263801577286097122099200, 31064894255642439440633167872, 12952461888954343767538696978432, 38298769965391452254691655680, 27181782473687134510554021888, 0, 0, 92138901576804952886485188608, 0, 27181782473687134510554021888, 0, 0, 0, 0, 227461810812131708479316426752, 0, 227461810812131708479316426752, 0, 38298769965391452254691655680, 227461810812131708479316426752, 0, 227461810812131708479316426752, 0, 1640463980184267204909292584960, 38298769965391452254691655680, 149771401940417179195998732288, 0, 149771401940417179195998732288, 0, 318092561657001228448689029120, 1640463980184267204909292584960, 383150484348945522087077871616, 8414123704517819055954984960, 0, 8414123704517819055954984960, 0, 38298769965391452254691655680, 38298769965391452254691655680, 40426479407913199602174525440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk21.Parent1
