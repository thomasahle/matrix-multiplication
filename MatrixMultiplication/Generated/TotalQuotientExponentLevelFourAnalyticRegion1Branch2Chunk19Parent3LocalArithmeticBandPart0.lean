import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk19Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 2,
parent 81; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [1458952972261405747265681752064, 16170591763165279840869810176, 53868262494282034796319060525056, 127237024662800491379475611648, 15319507986156580901876662272, 53865796398946816541674145054720, 15319507986156580901876662272, 15319507986156580901876662272, 656185592073706881963717033984, 15319507986156580901876662272, 127237024662800491379475611648, 656185592073706881963717033984, 1461419114820288830607049359360, 15319507986156580901876662272, 15319507986156580901876662272, 16170591763165279840869810176, 39489440908813224056487313145856, 30987186608362175006068703232, 1740853180245066011576893440, 140968647008558194049783663951872, 47061064305958284512962019328, 39489439748358530338539199004672, 47061064305958284512962019328, 47061064305958284512962019328, 30987186608362175006068703232, 1740853180245066011576893440, 39508490327165390775312158031872, 3862089568037628308849950720, 39508478930923229861916547481600, 3862089568037628308849950720, 3862089568037628308849950720, 0, 0, 13204745900554271639421845504, 0, 3862088320576560324241522688, 0, 0, 0, 0, 36151717709755870840413487104, 0, 36151717709755870840413487104, 0, 1450984791068598274546546507776, 2030995376952577013506375680, 0, 2030995376952577013506375680, 0, 16170591763165279840869810176, 39489429472360858517698951249920, 30987186608362175006068703232, 1740853180245066011576893440, 140968605411715700990963930365952, 47061064305958284512962019328, 39489428311906164799750837108736, 47061064305958284512962019328, 47061064305958284512962019328, 30987186608362175006068703232, 1740853180245066011576893440, 141014950411733363766549662400512, 13204745900554271639421845504, 141014908961144052634687396380672, 13204745900554271639421845504] }

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
  { lower := 64, upper := 128, values := [53559318025417784918664019968000, 54904575023617998598455689216, 0, 54904575023617998598455689216, 0, 127237024662800491379475611648, 15319507986156580901876662272, 39508489178516613264538156924928, 3862088320576560324241522688, 39508477782274452351142546374656, 3862088320576560324241522688, 53556910232419164172658912788480, 15319507986156580901876662272, 3862089568037628308849950720, 0, 0, 13204745900554271639421845504, 0, 3862088320576560324241522688, 0, 0, 0, 0, 54904575023617998598455689216, 0, 54904575023617998598455689216, 0, 15319507986156580901876662272, 54904575023617998598455689216, 0, 54904575023617998598455689216, 0, 656185592073706881963717033984, 15319507986156580901876662272, 36151717709755870840413487104, 0, 36151717709755870840413487104, 0, 127237024662800491379475611648, 656185592073706881963717033984, 1453392631290883849248105824256, 2030995376952577013506375680, 0, 2030995376952577013506375680, 0, 15319507986156580901876662272, 15319507986156580901876662272, 16170591763165279840869810176, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19.Parent3
