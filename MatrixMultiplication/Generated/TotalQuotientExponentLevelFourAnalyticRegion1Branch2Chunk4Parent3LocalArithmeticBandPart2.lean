import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk4Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 1, branch 2,
parent 21; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [0, 0, 183936251235851734163732299776, 0, 0, 0, 601196860075203998689397833728, 0, 0, 2037894989865961038102866690048, 0, 601196860075203998689397833728, 0, 0, 0, 0, 101696117558253779262973673472, 0, 3685500961845216577822365057024, 0, 0, 3685502316252436251266525429760, 0, 0, 0, 0, 0, 0, 101694763151034105818813300736, 0, 0, 0, 9385563720027547775717924143104, 0, 0, 31814526243066691110765135396864, 0, 9385563720027547775717924143104, 0, 0, 0, 0, 701660545704330772999464550400, 0, 701660545704330772999464550400, 0, 367610818899487795376956637184, 0, 0, 1246101395077275539222135046144, 0, 367610818899487795376956637184, 0, 0, 0, 0, 191010279499111409603575808000, 0, 191010279499111409603575808000, 0, 0, 50924377767103298852043620352, 7347924289098869446732152832, 1534815346897530335800749719552] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band8

namespace Band9

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 576, upper := 640, values := [181822041451531599288287100928, 5784536142482088713384886272, 1534816062998432916546397405184, 5940874957143766786719612928, 5940874957143766786719612928, 100525857827459001154229239808, 5471858513158732566715432960, 181822041451531599288287100928, 100525857827459001154229239808, 50923969163349874478193573888, 5784536142482088713384886272, 5471858513158732566715432960, 7347924289098869446732152832, 1164146404141472084477601644544, 48464451680207751712121815040, 1976839476429526714573389824, 3996182508958445310352444882944, 39919403620802700752352968704, 1164146226656986981559745642496, 39983172636171395162500497408, 35838186637206258502911131648, 48464451680207751712121815040, 1976839476429526714573389824, 183826858228310744592380067840, 9729781693590028932203151360, 183756037401174190904120967168, 9825359116906237467882946560, 585879742621058673882024640512, 0, 0, 1985974098404407890635277729792, 0, 585879742621058673882024640512, 0, 0, 0, 0, 701660545704330772999464550400, 0, 701660545704330772999464550400, 0, 0, 16924961474604808445886464000, 0, 16924961474604808445886464000, 0, 0, 13384627764333333094334464, 1976839476429526714573389824, 0, 20604267259295378801489346560, 0, 0, 0, 0, 0, 0, 0, 1976839476429526714573389824, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band9

namespace Band10

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 640, upper := 704, values := [0, 13384627764333333094334464, 5851876126991275012021813248, 0, 212073927820020238537212297216, 0, 0, 212074005756361028455461027840, 0, 0, 0, 0, 0, 0, 5851798190650485093773082624, 0, 0, 0, 19146396817681656009216491520, 0, 0, 64901114326941434334486200320, 0, 19146396817681656009216491520, 0, 0, 0, 0, 5535558498505260146507120640, 0, 200610472262181306724390010880, 0, 0, 200610545985746918809219891200, 0, 0, 0, 0, 0, 0, 5535484774939648061677240320, 0, 0, 0, 367610818899487795376956637184, 0, 0, 1246101395077275539222135046144, 0, 367610818899487795376956637184, 0, 0, 0, 0, 16924961474604808445886464000, 0, 16924961474604808445886464000, 0, 19146396817681656009216491520, 0, 0, 64901114326941434334486200320, 0, 19146396817681656009216491520] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band10

namespace Band11

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 704, upper := 768, values := [0, 0, 0, 0, 14507109835375550096474112000, 0, 14507109835375550096474112000, 0, 0, 7433464269421349339595276288, 0, 269391205609214897601323728896, 0, 0, 269391304609431576686666711040, 0, 0, 0, 0, 0, 0, 7433365269204670254252294144, 0, 0, 0, 589709021984595005083867938816, 0, 0, 1998954321269796177502174969856, 0, 589709021984595005083867938816, 0, 0, 0, 0, 16924961474604808445886464000, 0, 16924961474604808445886464000, 0, 333147304627660814560366952448, 0, 0, 1129279389288780957420059885568, 0, 333147304627660814560366952448, 0, 0, 0, 0, 191010279499111409603575808000, 0, 191010279499111409603575808000, 0, 0, 14507109835375550096474112000, 0, 14507109835375550096474112000, 0, 0, 28229822844319288422425427968, 328139261319139779086909440, 13384627764333333094334464, 96074890179966526737705074688, 270283128402344081195270144] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent3
