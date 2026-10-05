import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk22Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 2,
parent 92; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [70548094018897231597734461440, 16905618661490974379091165184, 2095750260664949079141756436480, 133020525783836877351269957632, 16015849258254607306507419648, 2095706328489558942832333422592, 16015849258254607306507419648, 16015849258254607306507419648, 686012209895239012962067808256, 16015849258254607306507419648, 133020525783836877351269957632, 686012209895239012962067808256, 70592026194287367907157475328, 16015849258254607306507419648, 16015849258254607306507419648, 16905618661490974379091165184, 1301815437751182472923922300928, 139442372983274294370348564480, 7833841178835634515188121600, 4771987176267784738301821321216, 211774839867856653060585553920, 1301815159131559983614854692864, 211774839867856653060585553920, 211774839867856653060585553920, 139442372983274294370348564480, 7833841178835634515188121600, 1298442323402392607165150920704, 50080023152440176724064337920, 1298442319528576351686145081344, 50080023152440176724064337920, 46227713679175547745290158080, 0, 0, 158691658111670427779579510784, 0, 46227713679175547745290158080, 0, 0, 0, 0, 144606905315988157124805918720, 0, 144606836362058809598501978112, 0, 68439916284148633102855438336, 8123983444718435793528422400, 0, 8123979570902180314522583040, 0, 16905618661490974379091165184, 1301815434015716797997738098688, 139442306491985280684269764608, 7833837443369959589003919360, 4771987117122911551970571452416, 211774738885767907556072620032, 1301815155396094308688670490624, 211774738885767907556072620032, 211774738885767907556072620032, 139442306491985280684269764608, 7833837443369959589003919360, 4762978682556589390909096853504, 171915962954309630094544470016, 4762978621221165345824837730304, 171915962954309630094544470016] }

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
  { lower := 64, upper := 128, values := [2018630275885433340043091509248, 219618352455555047618385018880, 0, 219618247733388941169260494848, 0, 133020525783836877351269957632, 16015849258254607306507419648, 1298442047143953359290905919488, 50080023152440176724064337920, 1298442043270137103811900080128, 50080023152440176724064337920, 2018586338987676720864023281664, 16015849258254607306507419648, 46227713679175547745290158080, 0, 0, 158691658111670427779579510784, 0, 46227713679175547745290158080, 0, 0, 0, 0, 219618352455555047618385018880, 0, 219618247733388941169260494848, 0, 16015849258254607306507419648, 219618352455555047618385018880, 0, 219618247733388941169260494848, 0, 686012209895239012962067808256, 16015849258254607306507419648, 144606905315988157124805918720, 0, 144606836362058809598501978112, 0, 133020525783836877351269957632, 686012209895239012962067808256, 68483853181905252281923665920, 8123983444718435793528422400, 0, 8123979570902180314522583040, 0, 16015849258254607306507419648, 16015849258254607306507419648, 16905618661490974379091165184, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22.Parent2
