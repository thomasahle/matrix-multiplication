import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 2,
parent 7; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 133213250382673441342881792000, 0, 0, 0, 0, 0, 0, 0, 12358599666686376149134606336, 0, 0, 0, 0, 0, 0, 117871271607056857097568256, 775109363896091666368430080, 0, 27126895226631008895096586240, 0, 0, 27126908531345172058110689280, 0, 0, 0, 0, 0, 0, 775102711539010084861378560, 0, 0, 0, 111499851520188918876078080, 11690558334423058223328133120, 0, 126012534145772174243266560000, 0, 0, 0, 0, 0, 0, 0, 11690567252270896357289492480, 0, 0, 0, 0, 0, 0, 111499851520188918876078080, 14882099786804959994273857536, 0, 520836388351315370785854455808, 0, 0, 520836643801827303515725234176, 0, 0, 0, 0, 0, 0] }

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
  { lower := 832, upper := 896, values := [14881972061548993629338468352, 0, 0, 0, 6496305927752757414146867200, 0, 0, 22211310109989625123611607040, 0, 6496303829435619029685370880, 0, 0, 0, 0, 775109363896091666368430080, 0, 27126895226631008895096586240, 0, 0, 27126908531345172058110689280, 0, 0, 0, 0, 0, 0, 775102711539010084861378560, 0, 0, 0, 5568262223788077783554457600, 0, 0, 19038265808562535820238520320, 0, 5568260425230530596873175040, 0, 0, 0, 0, 0, 0, 0, 0, 149728372041396548205019136, 15698749763368106757040635904, 0, 169216831567179776840957952000, 0, 0, 0, 0, 0, 0, 0, 15698761738763775108360175616, 0, 0, 0, 0, 0, 0, 149728372041396548205019136, 23873368407999623324147646464] }

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
  { lower := 896, upper := 960, values := [0, 835508372980235073968974856192, 0, 0, 835508782765431299389809229824, 0, 0, 0, 0, 0, 0, 23873163515401510613730459648, 0, 0, 0, 6496305927752757414146867200, 0, 0, 22211310109989625123611607040, 0, 6496303829435619029685370880, 0, 0, 0, 0, 13486902931791994994810683392, 0, 472007976943379554774680600576, 0, 0, 472008208445405993811125993472, 0, 0, 0, 0, 0, 0, 13486787180778775476587986944, 0, 0, 0, 73315452613209690816800358400, 0, 0, 250670499812740054966473850880, 0, 73315428932201986192163471360, 0, 0, 0, 0, 0, 0, 0, 0, 5568262223788077783554457600, 0, 0, 19038265808562535820238520320, 0, 5568260425230530596873175040, 0, 0, 0] }

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
  { lower := 960, upper := 1024, values := [0, 0, 0, 0, 0, 0, 1083737237683601288529444864, 150405875987285220368842752, 32670678897734435209299886080, 3721745399430057686999236608, 118404625777224535183982592, 32670694863391431004916809728, 121604750798230603702468608, 121604750798230603702468608, 2057680388506902057386508288, 112004375735212398147010560, 3721745399430057686999236608, 2057680388506902057386508288, 1083729254855103390720983040, 118404625777224535183982592, 112004375735212398147010560, 150405875987285220368842752, 6517536253225387608110006272, 520485398683837013289861120, 21230325472630193963139072, 22647559055991735883434819584, 428715604705371013578227712, 6517534154908249223648509952, 429400453914165535964135424, 384885255342521580880134144, 520485398683837013289861120, 21230325472630193963139072, 0, 0, 0, 0, 5753870964581013709672939520, 0, 0, 19672874668847953680913137664, 0, 5753869106071548283435614208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent2
