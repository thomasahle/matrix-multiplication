import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk16Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 1,
parent 67; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 0, 0, 0, 0, 0, 96939754565383142699433984, 0, 30238732989108013938769920, 9740541771641944082208522240, 0, 103594757915412371717826281472, 0, 0, 0, 0, 0, 0, 0, 9740571129635137390959919104, 0, 0, 0, 0, 0, 0, 30238732989108013938769920, 96939754565383142699433984, 19226530546154849585804083200, 0, 0, 0, 0, 19226530546154849585804083200, 0, 0, 0, 0, 0, 0, 0, 96939754565383142699433984, 0, 781167268885290360084889600, 251630662434083555457053491200, 0, 2676197912814819602710512271360, 0, 0, 0, 0, 0, 0, 0, 251631420848907715933131243520, 0, 0, 0, 0, 0, 0, 781167268885290360084889600, 4981375740669075131172126720, 0] }

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
  { lower := 832, upper := 896, values := [194945940603919839265036435456, 0, 0, 194945940603919839265036435456, 0, 0, 0, 0, 0, 0, 4981375740669075131172126720, 0, 0, 0, 30238732989108013938769920, 9740541771641944082208522240, 0, 103594757915412371717826281472, 0, 0, 0, 0, 0, 0, 0, 9740571129635137390959919104, 0, 0, 0, 0, 0, 0, 30238732989108013938769920, 4981375740669075131172126720, 0, 194945940603919839265036435456, 0, 0, 194945940603919839265036435456, 0, 0, 0, 0, 0, 0, 4981375740669075131172126720, 0, 0, 0, 4606772438760057708608487424, 0, 0, 16570423466376329979989327872, 0, 4606773975604423349535506432, 0, 0, 0, 0, 107419728031911050018291712, 21305074388982400892377497600, 0, 0, 0] }

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
  { lower := 896, upper := 960, values := [0, 21305074388982400892377497600, 0, 0, 0, 0, 0, 0, 0, 107419728031911050018291712, 0, 796286635379844367054274560, 256500933319904527498157752320, 0, 2727995291772525788569425412096, 0, 0, 0, 0, 0, 0, 0, 256501706413725284628611203072, 0, 0, 0, 0, 0, 0, 796286635379844367054274560, 4850286905388309996141281280, 0, 189815784272237738231746002944, 0, 0, 189815784272237738231746002944, 0, 0, 0, 0, 0, 0, 4850286905388309996141281280, 0, 0, 0, 796286635379844367054274560, 256500933319904527498157752320, 0, 2727995291772525788569425412096, 0, 0, 0, 0, 0, 0, 0, 256501706413725284628611203072, 0, 0, 0, 0, 0, 0] }

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
  { lower := 960, upper := 1024, values := [796286635379844367054274560, 150358894067037609880379719680, 0, 5884289312439369885184126091264, 0, 0, 5884289312439369885184126091264, 0, 0, 0, 0, 0, 0, 150358894067037609880379719680, 0, 0, 0, 94215926650770212492186484736, 0, 0, 338891886376857845397201092608, 0, 94215958081716271084048744448, 0, 0, 0, 0, 4850286905388309996141281280, 0, 189815784272237738231746002944, 0, 0, 189815784272237738231746002944, 0, 0, 0, 0, 0, 0, 4850286905388309996141281280, 0, 0, 0, 94067321088229565469328146432, 0, 0, 338357356587619899268814340096, 0, 94067352469599999363095986176, 0, 0, 0, 0, 9903519133691421481781690368, 0, 9903521494874662916604297216, 0, 158167292107176371130728448, 21728668864694865618762989568, 799288658510399859484262400, 213069426179499097344945684480, 505878897791392316129280000, 30352733867483538967756800, 799288658510399859484262400] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent1
