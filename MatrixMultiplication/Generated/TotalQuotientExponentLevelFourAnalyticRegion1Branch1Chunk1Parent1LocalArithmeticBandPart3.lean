import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 1,
parent 6; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 139879559342081684846883635200, 0, 0, 0, 0, 0, 0, 0, 13586624454210772033286963200, 0, 0, 0, 0, 0, 0, 82905559296139265950351360, 654911613137810157364838400, 0, 26183244781664132805112627200, 0, 0, 26183238382949782237111910400, 0, 0, 0, 0, 0, 0, 654911613137810157364838400, 0, 0, 0, 85274289561743244977504256, 13974813724331079805666590720, 0, 143876118180426875842508881920, 0, 0, 0, 0, 0, 0, 0, 13974813724331079805666590720, 0, 0, 0, 0, 0, 0, 85274289561743244977504256, 20564224652527238941255925760, 0, 822153886144253770080536494080, 0, 0, 822153685224623162245313986560, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band12

namespace Band13

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 832, upper := 896, values := [20564224652527238941255925760, 0, 0, 0, 6513007148668492199441203200, 0, 0, 23725326237846025006166835200, 0, 6513011529770209705459712000, 0, 0, 0, 0, 654911613137810157364838400, 0, 26183244781664132805112627200, 0, 0, 26183238382949782237111910400, 0, 0, 0, 0, 0, 0, 654911613137810157364838400, 0, 0, 0, 6341612223703531878403276800, 0, 0, 23100975547376392769162444800, 0, 6341616489513098923737088000, 0, 0, 0, 0, 0, 0, 0, 0, 82905559296139265950351360, 13586624454210772033286963200, 0, 139879559342081684846883635200, 0, 0, 0, 0, 0, 0, 0, 13586624454210772033286963200, 0, 0, 0, 0, 0, 0, 82905559296139265950351360, 20040295362016990815364055040] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band13

namespace Band14

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 896, upper := 960, values := [0, 801207290318922463836446392320, 0, 0, 801207094518263336455624458240, 0, 0, 0, 0, 0, 0, 20040295362016990815364055040, 0, 0, 0, 6341612223703531878403276800, 0, 0, 23100975547376392769162444800, 0, 6341616489513098923737088000, 0, 0, 0, 0, 20957171620409925035674828800, 0, 837863833013252249763604070400, 0, 0, 837863628254393031587581132800, 0, 0, 0, 0, 0, 0, 20957171620409925035674828800, 0, 0, 0, 199332297734248853367108403200, 0, 0, 726119853016182291636106035200, 0, 199332431819019839143411712000, 0, 0, 0, 0, 0, 0, 0, 0, 6341612223703531878403276800, 0, 0, 23100975547376392769162444800, 0, 6341616489513098923737088000, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band14

namespace Band15

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 960, upper := 1024, values := [0, 0, 0, 0, 0, 0, 858432703899090801636933632, 81898609183230691869982720, 31490092545868299959166566400, 924284303639317808246947840, 81898609183230691869982720, 31490084867411079277565706240, 81898609183230691869982720, 81898609183230691869982720, 3395282340710506682952712192, 84238569445608711637696512, 924284303639317808246947840, 3395282340710506682952712192, 858432703899090801636933632, 81898609183230691869982720, 84238569445608711637696512, 81898609183230691869982720, 8063712563827101238919430144, 170154013644043384107565056, 8830348013463329314963456, 29527542358967204927697321984, 274080417187111798352904192, 8064057611327921480689254400, 274080417187111798352904192, 285627795358563844380164096, 170154013644043384107565056, 8490719243714739725926400, 0, 0, 0, 0, 8226956398318095409820467200, 0, 0, 29968833142542347376210739200, 0, 8226961932341317522685952000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent1
