import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk0Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 1, for region 1, branch 1,
parent 4; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band4

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 256, upper := 320, values := [8356095265176316855569088512, 0, 8356095265176316855569088512, 0, 40092348367417757855079464960, 435213295061266502894223360, 0, 435213295061266502894223360, 0, 715684085211860471426056192, 51306505752960679333068800, 8408148158476301952352256000, 0, 86565140830553732091478016000, 0, 0, 0, 0, 0, 0, 0, 8408148158476301952352256000, 0, 0, 0, 0, 0, 0, 51306505752960679333068800, 5332750562328633627321040896, 0, 213202378049182971122279251968, 0, 0, 213202325946354334929650712576, 0, 0, 0, 0, 0, 0, 5332750562328633627321040896, 0, 0, 0, 6238775268724555685780520960, 0, 0, 22726365133094613426959810560, 0, 6238779465358832454703513600, 0, 0, 0, 0, 5557426546367262553379176448, 0, 222184882204910630376501673984, 0, 0, 222184827906919449412436492288, 0, 0, 0] }

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
  { lower := 320, upper := 384, values := [0, 0, 0, 5557426546367262553379176448, 0, 0, 0, 258641797569123722859072454656, 0, 0, 942170165946293830929105289216, 0, 258641971549590454050708520960, 0, 0, 0, 0, 13317526828874754988563234816, 0, 13317526828874754988563234816, 0, 6417025990688114419659964416, 0, 0, 23375689851183030953444376576, 0, 6417030307226227667695042560, 0, 0, 0, 0, 13926825441960528092615147520, 0, 13926825441960528092615147520, 0, 928455029464035206174343168, 3310666705980973292797820928, 0, 132359840647634037834277453824, 0, 0, 132359808301268304584578695168, 0, 0, 0, 0, 0, 0, 3310666705980973292797820928, 0, 0, 0, 70409035175605699882380165120, 0, 0, 256483263644924922961403576320, 0, 70409082537621109131653939200, 0, 0, 0, 0, 8356095265176316855569088512, 0] }

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
  { lower := 384, upper := 448, values := [8356095265176316855569088512, 0, 258641797569123722859072454656, 0, 0, 942170165946293830929105289216, 0, 258641971549590454050708520960, 0, 0, 0, 0, 213341557239032839718748291072, 0, 213341557239032839718748291072, 0, 12437428832195304949377138688, 13665697464923768190878613504, 0, 13665697464923768190878613504, 0, 22495691651389019682932523008, 5690031293570830973515333632, 3428904802623150910397743104, 177947155425552741856968704, 23818047675139902084902551552, 5523205939554656256868220928, 5696879131952283085292175360, 5523205939554656256868220928, 5755906065880379073142718464, 3428904802623150910397743104, 171103034063031482554777600, 15257915912561199121761828864, 8408148158476301952352256000, 15257915912561199121761828864, 8408148158476301952352256000, 40092348367417757855079464960, 13317526828874754988563234816, 0, 13317526828874754988563234816, 0, 12437428832195304949377138688, 735026898325694538221355008, 165202929440168327983923200, 0, 6604782467446808275163545600, 0, 0, 6604780853356701825577779200, 0, 0, 0, 0, 0, 0, 165202929440168327983923200, 0, 0, 0, 6238775268724555685780520960, 0, 0, 22726365133094613426959810560, 0] }

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
  { lower := 448, upper := 512, values := [6238779465358832454703513600, 0, 0, 0, 0, 435213295061266502894223360, 0, 435213295061266502894223360, 0, 6417025990688114419659964416, 0, 0, 23375689851183030953444376576, 0, 6417030307226227667695042560, 0, 0, 0, 0, 13665697464923768190878613504, 0, 13665697464923768190878613504, 0, 735026898325694538221355008, 435213295061266502894223360, 0, 435213295061266502894223360, 0, 715684085211860471426056192, 6238775268724555685780520960, 0, 0, 22726365133094613426959810560, 0, 6238779465358832454703513600, 0, 0, 0, 0, 13317526828874754988563234816, 0, 13317526828874754988563234816, 0, 715684085211860471426056192, 13926825441960528092615147520, 0, 13926825441960528092615147520, 0, 22495691651389019682932523008, 715684085211860471426056192, 569151059331833396358807552, 51306505752960679333068800, 569151059331833396358807552, 51306505752960679333068800, 1107843565048804418907013120, 928455029464035206174343168, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0.Parent3
