import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1Parent0LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 1, for region 1, branch 2,
parent 5; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band4

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 256, upper := 320, values := [251590724426118921053011968, 251590724426118921053011968, 4257179889631433322028597248, 231728298813530585180405760, 7700000329146744873280339968, 4257179889631433322028597248, 512581986877941038268284928, 244969915888589475762143232, 231728298813530585180405760, 311178001263883928670830592, 0, 0, 0, 0, 0, 188693043319589190789758976, 0, 1827694608337905233084547072, 0, 0, 0, 0, 188693043319589190789758976, 0, 0, 0, 0, 0, 0, 3192884917223574991521447936, 0, 30926516662138764865088520192, 0, 0, 0, 0, 3192884917223574991521447936, 0, 0, 2148094633873405052159262720, 179858105360748246458204946432, 0, 0, 0, 0, 179858170451237632046964670464, 0, 0, 0, 0, 0, 0, 0, 2148029543384019463399538688, 0, 173796224110147938885304320, 0, 1683402928732281135735767040, 0, 0, 0, 0, 173796224110147938885304320, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band4

namespace Band5

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 320, upper := 384, values := [0, 1221465576124093068874874880, 102272255989445081319371440128, 0, 0, 0, 0, 102272293001684143712979910656, 0, 0, 0, 0, 0, 0, 0, 1221428563885030675266404352, 0, 105459975917479267032629248, 11057288270800141430105833472, 0, 119186515812601063576436736000, 0, 0, 0, 0, 0, 0, 0, 11057296705573869133798309888, 0, 0, 0, 0, 0, 0, 105459975917479267032629248, 0, 0, 0, 0, 5775000246860058654960254976, 0, 55937074460446941738877059072, 0, 0, 0, 0, 5775000246860058654960254976, 0, 0, 2204253970706696687509831680, 184560278049918135254497886208, 0, 0, 0, 0, 184560344842119661642963746816, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band5

namespace Band6

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 384, upper := 448, values := [2204187178505170299043971072, 0, 3192884917223574991521447936, 0, 30926516662138764865088520192, 0, 0, 0, 0, 3192884917223574991521447936, 0, 0, 34411633644599449561061130240, 2881256315288849359928498847744, 0, 0, 0, 0, 2881257358012963634948434034688, 0, 0, 0, 0, 0, 0, 0, 34410590920485174541125943296, 0, 4936207259879432789172420608, 517552428417129200486566592512, 0, 5578697885293036879013216256000, 0, 0, 0, 0, 0, 0, 0, 517552823218957552036817666048, 0, 0, 0, 0, 0, 0, 4936207259879432789172420608, 1347824083998999248413655040, 112852144540077331111030554624, 0, 0, 0, 0, 112852185381168710303977832448, 0, 0, 0, 0, 0, 0, 0, 1347783242907620055466377216, 0, 1343764209271106789609308160] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band6

namespace Band7

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 448, upper := 512, values := [140891253773098576286832394240, 0, 1518666895031529681054597120000, 0, 0, 0, 0, 0, 0, 0, 140891361248441235737107496960, 0, 0, 0, 0, 0, 0, 1343764209271106789609308160, 3903488370206695258463404032, 0, 136612360744444342543105130496, 0, 0, 136612427747630504274623987712, 0, 0, 0, 0, 0, 0, 3903454868613614392703975424, 0, 0, 0, 433132284427587694777860096, 3903454868613614392703975424, 8861172950544376184854020096, 6287600956030313003816583168, 194783177076527664306585600, 6287600956030313003816583168, 4199525297769936442449985536, 440923611510648801350123520, 3903454868613614392703975424, 186991849993466557734322176, 14942012118331733856328089600, 201145278744509907963803074560, 12695638645000068442305331200, 11244708514142917763184721920, 526324904968431408851001016320, 143279350422143629563160166400, 201145346812995539952048537600, 526324904968431408851001016320, 12695638645000068442305331200, 12695638645000068442305331200, 10881975981428630093404569600, 12695638645000068442305331200, 143279350422143629563160166400, 10881975981428630093404569600, 14941944049846101868082626560, 11244708514142917763184721920, 7347762006173723996165505024, 205515184708762478450407636992, 184244955096389769413963808768, 144431224359212960665860833280] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent0
