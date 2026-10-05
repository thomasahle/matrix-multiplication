import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk13Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 4, for region 1, branch 1,
parent 57; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band16

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 1024, upper := 1088, values := [1195470354047209787719942144, 761446085380388399821619200, 18449838648766810927677833216, 1180241432339602019723509760, 31607069601562896172614418432, 1203084814901013671718158336, 45686765122823303989297152, 1180241432339602019723509760, 45686765122823303989297152, 1203084814901013671718158336, 1203084814901013671718158336, 197909899008071131679686656, 11356497667910043456818380800, 218400005099755351843012608, 436933607375777452457283551232, 2285209809458415754650058752, 202419516921724472439865344, 436933683103016493807430533120, 202419516921724472439865344, 197092687529047512638816256, 7446907490962389801866625024, 197092687529047512638816256, 2285209809458415754650058752, 7446907490962389801866625024, 11356599265309280500312965120, 197092687529047512638816256, 197092687529047512638816256, 218400005099755351843012608, 23856457562024474394039943168, 0, 0, 86692609804735996876763955200, 0, 23854960680829760299432148992, 0, 0, 0, 0, 6961426075818815804009349120, 223046813718899082733289472, 264952490011811552889925533696, 2333831294766041621770272768, 206726315154101588874756096, 264952587123542807429253169152, 206726315154101588874756096, 201286148965835757588578304, 7605352331195632138076553216, 201286148965835757588578304, 2333831294766041621770272768, 7605352331195632138076553216, 6961523187550070343336984576, 201286148965835757588578304, 201286148965835757588578304, 223046813718899082733289472, 191062028030357550529612087296, 0, 0, 708614882166058170103638261760, 0, 191025635666459637820059287552, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band16

namespace Band17

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 1088, upper := 1107, values := [59363098175640762892058361856, 0, 59363088717072739097485770752, 0, 7877815897029290817264549888, 0, 0, 29217910907362187706483343360, 0, 7876313685272726775321853952, 0, 0, 0, 0, 59430798013468731593593978880, 0, 59430788571041608863517245440, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent3
