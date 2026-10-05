import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk6Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 1,
parent 29; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk6.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [61218345954649334161650745344, 16247963015620616108051005440, 1868575390285049496044914606080, 183369868319146953219432775680, 16247963015620616108051005440, 1868575305282452804391300759552, 16247963015620616108051005440, 16247963015620616108051005440, 673594123876157542079485968384, 16712190530352633711138177024, 183369868319146953219432775680, 673594123876157542079485968384, 61218515959842717468878438400, 16247963015620616108051005440, 16712190530352633711138177024, 16247963015620616108051005440, 1271669617884185512191000051712, 135670475007249277877376516096, 7040783134108744959704170496, 4733583822851207473698609037312, 218535076508682968556971753472, 1272052817425133503106282160128, 218535076508682968556971753472, 227742254453286711965815668736, 135670475007249277877376516096, 6769983782796870153561702400, 1282705031801038211882082631680, 47083145164683293270076293120, 1282705610859509564569332744192, 47083145164683293270076293120, 50704925561966623521620623360, 0, 0, 188356162653538982081173913600, 0, 50694252229728714990781726720, 0, 0, 0, 0, 140515849114651037801568534528, 0, 140515882616244118667327963136, 0, 61218345954649334161650745344, 7292239674612628708265033728, 0, 7292241413218257655390273536, 0, 16247963015620616108051005440, 1271670191865980940324299603968, 135670507353615011127075274752, 7040784812762455667273367552, 4733585942884741541937469718528, 218535128611511604749600292864, 1272053391471877593265705320448, 218535128611511604749600292864, 227742308751277892929880850432, 135670507353615011127075274752, 6769985396886976603147468800, 4777498224245778984358790561792, 174902151035429054789661491200, 4777500363813686569416339226624, 174902151035429054789661491200] }

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
  { lower := 64, upper := 128, values := [1868575390285049496044914606080, 226339900669707360291149316096, 0, 226339954633351304919228874752, 0, 183369868319146953219432775680, 16247963015620616108051005440, 1283100665613093835342815952896, 47073234213319521062868746240, 1283101244738823070765123895296, 47073234213319521062868746240, 1868575305282452804391300759552, 16247963015620616108051005440, 50704925561966623521620623360, 0, 0, 188356162653538982081173913600, 0, 50694252229728714990781726720, 0, 0, 0, 0, 226339900669707360291149316096, 0, 226339954633351304919228874752, 0, 16247963015620616108051005440, 235875906398046951678880514048, 0, 235875962635252103391662309376, 0, 673594123876157542079485968384, 16712190530352633711138177024, 140515849114651037801568534528, 0, 140515882616244118667327963136, 0, 183369868319146953219432775680, 673594123876157542079485968384, 61218515959842717468878438400, 7011768917896758373331763200, 0, 7011770589632940053259878400, 0, 16247963015620616108051005440, 16712190530352633711138177024, 16247963015620616108051005440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk6.Parent3
