import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk4Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 4, for region 1, branch 1,
parent 21; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band16

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 1024, upper := 1088, values := [808646230610390872280268800, 485187738366234523368161280, 12387449445162925174743367680, 793484113786446043425013760, 17716416053144711788566151168, 773267958021186271618007040, 25270194706574714758758400, 793484113786446043425013760, 25270194706574714758758400, 773267958021186271618007040, 808646230610390872280268800, 106383384518508896799686656, 8154258473013514970385612800, 99787569833011450918993920, 316738488630061379657553412096, 1126174002401129231800074240, 99787569833011450918993920, 316738576211397825845283258368, 99787569833011450918993920, 99787569833011450918993920, 4136907537934274722384576512, 102638643256811778088108032, 1126174002401129231800074240, 4136907537934274722384576512, 8154357473230194055728594944, 99787569833011450918993920, 102638643256811778088108032, 99787569833011450918993920, 6794464784502970189969620992, 0, 0, 24493672960620946507834589184, 0, 6795745655831035221083422720, 0, 0, 0, 0, 7043894906143166987111497728, 0, 275670560459051285290923589632, 0, 0, 275670661565655553292975996928, 0, 0, 0, 0, 0, 0, 7043996012747434989163905024, 0, 0, 0, 107924083366992534478279147520, 0, 0, 386842527338329513800855715840, 0, 107955445921747473062376243200, 0, 0, 0, 0] }

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
  { lower := 1088, upper := 1107, values := [9845488353919264929496432640, 0, 9845495395963815068117762048, 0, 4402166558390484958982438912, 0, 0, 15779103088800282799771746304, 0, 4403445820492331138070609920, 0, 0, 0, 0, 9913188175606332566536192000, 0, 9913195266073585898645094400, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent3
