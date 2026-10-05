import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk11Parent0LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 4, for region 1, branch 1,
parent 46; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band16

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 1024, upper := 1088, values := [1522736517134282838446702592, 940922076978811069538500608, 23410876831036191186056380416, 1498624113872750429985570816, 30580855939579039839493816320, 1493127279286690162956828672, 52729944147722458456129536, 1498624113872750429985570816, 52729944147722458456129536, 1493127279286690162956828672, 1527439994151221005079543808, 234990744150784247611785216, 11659731333173980093466279936, 0, 458032107362849202952663465984, 0, 0, 458032077845347518041703841792, 0, 0, 0, 0, 0, 0, 11659788164881304216917770240, 0, 0, 0, 33919924934951391420825468928, 0, 0, 124873635118410614297665208320, 0, 33916015800945217018781499392, 0, 0, 0, 0, 5885954079367351789535887360, 0, 232108046844339391425111130112, 0, 0, 232107974385528669893992382464, 0, 0, 0, 0, 0, 0, 5885969795993302590073864192, 0, 0, 0, 222187385347376927440176676864, 0, 0, 797827588386486988392500297728, 0, 222219170062787521895003586560, 0, 0, 0, 0] }

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
  { lower := 1088, upper := 1107, values := [98745060911535265851795046400, 0, 98745060980710556128205864960, 0, 9116308913208847178785619968, 0, 0, 32734382728074180652926238720, 0, 9117620913669738173900521472, 0, 0, 0, 0, 99083560181379614681952419840, 0, 99083560169850399635883950080, 0, 79228162514264337593543950336] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent0
