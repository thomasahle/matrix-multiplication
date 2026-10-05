import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk8Parent0LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 4, for region 1, branch 1,
parent 34; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band16

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 1024, upper := 1088, values := [1763582520422927972696064000, 1058149512253756783617638400, 27015879734728727881737830400, 1730515348164998073208012800, 26289989077775278942839635968, 1686425785154424873890611200, 55111953763216499146752000, 1730515348164998073208012800, 55111953763216499146752000, 1686425785154424873890611200, 1763582520422927972696064000, 203924290487886149306023936, 12455529170519701341207527424, 174538665206862087098204160, 482605213842250160021876768768, 1969793507334586411536875520, 174538665206862087098204160, 482605242891598441543022673920, 174538665206862087098204160, 174538665206862087098204160, 7235874377575911096556978176, 179525484212772432443867136, 1969793507334586411536875520, 7235874377575911096556978176, 12455570427739463978537975808, 174538665206862087098204160, 179525484212772432443867136, 174538665206862087098204160, 23090045527987633428415643648, 0, 0, 83758531760914738562820210688, 0, 23092889990239770766380892160, 0, 0, 0, 0, 8508941961305046111892799488, 178174887398671713912750080, 326973857050392205447007305728, 2010830872070723628443893760, 178174887398671713912750080, 326973857050392205447007305728, 178174887398671713912750080, 178174887398671713912750080, 7386621760442075911068581888, 183265598467205191453114368, 2010830872070723628443893760, 7386621760442075911068581888, 8508941961305046111892799488, 178174887398671713912750080, 183265598467205191453114368, 178174887398671713912750080, 195519678054172288975076589568, 0, 0, 725194912340495343094593486848, 0, 195481783152241026419843399680, 0, 0, 0, 0] }

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
  { lower := 1088, upper := 1107, values := [59130970278845421592143462400, 0, 59130989099136062794313498624, 0, 7982695160219957670757531648, 0, 0, 29607823083779314372667506688, 0, 7981149452193789326298972160, 0, 0, 0, 0, 59469469467985265099821547520, 0, 59469488368980411624470872064, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent0
