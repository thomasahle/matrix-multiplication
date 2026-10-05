import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 4, for region 1, branch 2,
parent 6; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band16

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 1024, upper := 1088, values := [712330531702864332925698048, 1285470039969536784704995328, 20068070496594488275872251904, 786019897051436505297321984, 6342947053163135593695150080, 1252719210925726930317606912, 40938536304762317984235520, 786019897051436505297321984, 40938536304762317984235520, 1260906918186679393914454016, 712330531702864332925698048, 97128118880805809358372864, 2585623500295541121580269568, 257503302506740417101299712, 81489373679226080497323999232, 6371837038624236278485352448, 202715365803178626228682752, 81489413547251709802092429312, 208194159473534805315944448, 208194159473534805315944448, 3522864330039023153109270528, 191757778462466268054159360, 6371837038624236278485352448, 3522864330039023153109270528, 2585603566282726469196054528, 202715365803178626228682752, 191757778462466268054159360, 257503302506740417101299712, 464021851982339815296204800, 0, 0, 1586522150713544651686543360, 0, 464021702102544216406097920, 0, 0, 0, 0, 2057196672219193722489798656, 0, 71996754506174570228684423168, 0, 0, 71996789817854413327193604096, 0, 0, 0, 0, 0, 0, 2057179016379272173235208192, 0, 0, 0, 8941344147813547979361484800, 0, 0, 30571061442595610403652239360, 0, 8941341259745178939209809920, 0, 0, 0, 0] }

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
  { lower := 1088, upper := 1107, values := [0, 0, 0, 0, 428327863368313675658035200, 0, 0, 1464481985274041216941424640, 0, 428327725017733122836398080, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent1
