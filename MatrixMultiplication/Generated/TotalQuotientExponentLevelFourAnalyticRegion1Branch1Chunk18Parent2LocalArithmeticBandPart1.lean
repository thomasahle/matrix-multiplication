import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk18Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 1, for region 1, branch 1,
parent 76; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band4

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 256, upper := 320, values := [1389610511993917989387302338560, 53791374657829083460153638912, 1416506199322832531117379158016, 1416506199322832531117379158016, 53839247389794757456573759488, 108343068277305535555960832, 19002356288190752458199269376, 0, 0, 0, 0, 19002358566363645561328893952, 0, 0, 0, 0, 0, 0, 0, 108340790104412432426336256, 0, 797878866094566607002009600, 94304159403782224173701529600, 0, 894927674467441157210741145600, 0, 0, 0, 0, 0, 0, 0, 94304224082678632617816883200, 0, 0, 0, 0, 0, 0, 797878866094566607002009600, 21292997275661384129156481024, 22079660950245935042523037696, 91576306587162322251745853440, 231028647503792832518106906624, 20464076002666964185753059328, 91576279318262895290601177088, 20464076002666964185753059328, 19925547686807307233496399872, 752862585571800419254809919488, 19925547686807307233496399872, 231028647503792832518106906624, 752862585571800419254809919488, 21293006365294526449538039808, 19925547686807307233496399872, 19925547686807307233496399872, 22079660950245935042523037696, 47872731965673996420120576, 5658249564226933450422091776, 0, 53695660468046469432644468736, 0, 0, 0, 0] }

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
  { lower := 320, upper := 384, values := [0, 0, 0, 5658253444960717957069012992, 0, 0, 0, 0, 0, 0, 47872731965673996420120576, 2011865566086719061689892864, 0, 78473589395189594211729014784, 0, 0, 78473560611351310197187411968, 0, 0, 0, 0, 0, 0, 2011875160699480399870427136, 0, 0, 0, 742570030231851405810860032, 0, 0, 2712250635422256182643916800, 0, 742569780047884906125066240, 0, 0, 0, 0, 0, 0, 0, 0, 320034134366797790118412288, 0, 14464960654245209780506329088, 0, 0, 0, 0, 321742253292398596503633920, 0, 0, 105491934901586968830803968, 18502294280606785288246657024, 0, 0, 0, 0, 18502296498827760151820238848, 0, 0, 0, 0, 0, 0] }

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
  { lower := 384, upper := 448, values := [0, 105489716680612105257222144, 0, 320034134366797790118412288, 0, 14464960654245209780506329088, 0, 0, 0, 0, 321742253292398596503633920, 0, 0, 3985884459254556281769295872, 699086686602386103593752068096, 0, 0, 0, 0, 699086770415167802493099835392, 0, 0, 0, 0, 0, 0, 0, 3985800646472857382421528576, 0, 1260648608429415239063175168, 149000571857975914194448416768, 0, 1413985725658557028392971010048, 0, 0, 0, 0, 0, 0, 0, 149000674050632239536150675456, 0, 0, 0, 0, 0, 0, 1260648608429415239063175168, 105491934901586968830803968, 18502294280606785288246657024, 0, 0, 0, 0, 18502296498827760151820238848, 0, 0, 0, 0, 0, 0, 0, 105489716680612105257222144, 0] }

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
  { lower := 448, upper := 512, values := [1252669819768469572993155072, 148057530263938091952711401472, 0, 1405036448913882616820863598592, 0, 0, 0, 0, 0, 0, 0, 148057631809805453209972506624, 0, 0, 0, 0, 0, 0, 1252669819768469572993155072, 2594247703638137737442230272, 0, 101189628430639213588808466432, 0, 0, 101189591314637215780583768064, 0, 0, 0, 0, 0, 0, 2594260075638803673517129728, 0, 0, 0, 229064124341920569367724032, 0, 10353281697468722493345759232, 0, 0, 0, 0, 230286708822600275858554880, 0, 0, 1223136218183265125092294656, 214526601253521915909670699008, 0, 0, 0, 0, 214526626972894840679213039616, 0, 0, 0, 0, 0, 0, 0, 1223110498810340355549954048, 0, 797878866094566607002009600, 94304159403782224173701529600, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent2
