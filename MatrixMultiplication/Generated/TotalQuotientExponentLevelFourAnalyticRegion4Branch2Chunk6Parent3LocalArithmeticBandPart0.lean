import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk6Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 4, branch 2,
parent 62; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk6.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 155281166946236887696670720, 7014627797254137159660601344, 0, 0, 0, 0, 7013439835219598829131137024, 0, 0, 0, 0, 0, 0, 0, 155281166946236887696670720, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20552619062635198754586624, 595304452357969679491268608, 36725853360649267681689600, 6779352352867576665180471296, 31324992572318493022617600, 4590731670081158460211200, 36455810321232728948736000, 36455810321232728948736000] }

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
  { lower := 64, upper := 128, values := [31324992572318493022617600, 661875489609936434469273600, 31324992572318493022617600, 595313616858389255326531584, 36455810321232728948736000, 4590731670081158460211200, 31324992572318493022617600, 4590731670081158460211200, 36455810321232728948736000, 36455810321232728948736000, 21031407999427399494139904, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20552619062635198754586624, 0, 784488551843275275948261376, 0, 0, 784488332014977639623163904, 0, 0, 0, 0, 0, 0, 20551904680551681993211904, 0, 0, 0, 0, 0] }

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
  { lower := 128, upper := 192, values := [0, 0, 0, 0, 0, 0, 0, 0, 547480435776829129081487360, 24731727348382232696504451072, 0, 0, 0, 0, 24727538907599967340736806912, 0, 0, 0, 0, 0, 0, 0, 547480435776829129081487360, 0, 784488551843275275948261376, 23040402929194379069928505344, 1278584811190768768273874944, 264314362366342123020842172416, 1090557633074479243527716864, 159823101398846096034234368, 1269183452284954292036567040, 1269183452284954292036567040, 1090557633074479243527716864, 23042730678151281257641672704, 1090557633074479243527716864, 23040731413988964041156984832, 1269183452284954292036567040, 159823101398846096034234368, 1090557633074479243527716864, 159823101398846096034234368, 1269183452284954292036567040, 1269183452284954292036567040, 806547297227862374053052416, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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
  { lower := 192, upper := 256, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 595304452357969679491268608, 0, 23040402929194379069928505344, 0, 0, 23040391459582503744870285312, 0, 0, 0, 0, 0, 0, 595280778504514537909125120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36725853360649267681689600, 0, 1278584811190768768273874944, 0, 0, 1278586222366690407054573568, 0, 0, 0, 0, 0, 0, 36725696563324641150500864, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk6.Parent3
