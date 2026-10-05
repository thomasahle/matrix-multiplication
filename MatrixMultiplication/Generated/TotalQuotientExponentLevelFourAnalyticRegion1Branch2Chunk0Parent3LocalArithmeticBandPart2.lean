import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk0Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 1, branch 2,
parent 4; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [0, 0, 0, 0, 10090484300469585418649600, 227278054087550284844761088, 227278054087550284844761088, 227278054087550284844761088, 227278054087550284844761088, 2294110158253952793286017024, 0, 22220918659266110991712124928, 0, 0, 0, 0, 2294110158253952793286017024, 0, 0, 207743888285753610443161600, 17394216045303247173278760960, 0, 0, 0, 0, 17394222340254662326663249920, 0, 0, 0, 0, 0, 0, 0, 207737593334338457058672640, 0, 1296023271221388915687555072, 0, 12553376125689296469343862784, 0, 0, 0, 0, 1296023271221388915687555072, 0, 0, 2344538167796362175001395200, 196306152511279503812717445120, 0, 0, 0, 0, 196306223554302617686628106240, 0, 0, 0, 0, 0, 0, 0, 2344467124773248301090734080, 0, 325720833219158217314009088, 34151241903635866013487071232, 0] }

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
  { lower := 576, upper := 640, values := [368116253595070206748655616000, 0, 0, 0, 0, 0, 0, 0, 34151267955050184109801340928, 0, 0, 0, 0, 0, 0, 325720833219158217314009088, 178066189959217380379852800, 14909328038831354719953223680, 0, 0, 0, 0, 14909333434503996279997071360, 0, 0, 0, 0, 0, 0, 0, 178060794286575820336005120, 0, 217550841518124261626085376, 22809813365625442108140683264, 0, 245866989699805255808581632000, 0, 0, 0, 0, 0, 0, 0, 22809830765516789634675245056, 0, 0, 0, 0, 0, 0, 217550841518124261626085376, 1313790221647101645941637120, 0, 45979382203891034141082255360, 0, 0, 45979404755035664251009105920, 0, 0, 0, 0, 0, 0, 1313778946074786590978211840] }

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
  { lower := 640, upper := 704, values := [0, 0, 0, 99831773996419582038900736, 209435209145032295067942912, 1217316965639677039486173184, 337353720119842439360937984, 10450858739772070612172800, 337353720119842439360937984, 225320514429485842398445568, 100249808346010464863387648, 209435209145032295067942912, 10032824390181187787685888, 415481481620092067501834240, 17607888998447138157681967104, 207737593334338457058672640, 183996154096128347680538624, 8612207083660717176918114304, 2344467124773248301090734080, 17607895293398553311066456064, 8612207083660717176918114304, 207737593334338457058672640, 207737593334338457058672640, 178060794286575820336005120, 207737593334338457058672640, 2344467124773248301090734080, 178060794286575820336005120, 415475186668676914117345280, 183996154096128347680538624, 109806231735430048198426624, 3748611258251595360896024576, 2532459265605012823757291520, 11942763320438852112560947200, 2598667350980307276665978880, 82760106719118066135859200, 2532459265605012823757291520, 1440025856912654350763950080, 2598667350980307276665978880, 40569004313711676019798179840, 1588994049007066869808496640, 3748612097578450714680623104, 2532459265605012823757291520, 82760106719118066135859200, 1588994049007066869808496640, 82760106719118066135859200, 2549011286948836436984463360, 1440025856912654350763950080, 109806231735430048198426624, 184001729624524626392514560, 15406305640125733210618331136, 0, 0, 0, 0, 15406311215654129489330307072, 0, 0, 0, 0, 0, 0, 0, 183996154096128347680538624, 0] }

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
  { lower := 704, upper := 768, values := [202213305381410491789737984, 21201700363967247673800523776, 0, 228533138848984106048421888000, 0, 0, 0, 0, 0, 0, 0, 21201716537150114298649903104, 0, 0, 0, 0, 0, 0, 202213305381410491789737984, 1437377849859303436766412800, 0, 50304641061516775594026598400, 0, 0, 50304665734036974180551884800, 0, 0, 0, 0, 0, 0, 1437365513599204143503769600, 0, 0, 0, 9686864928450802001903616, 1015650316836754379583258624, 0, 10947695274202831427469312000, 0, 0, 0, 0, 0, 0, 0, 1015651091600005475384426496, 0, 0, 0, 0, 0, 0, 9686864928450802001903616, 1313790221647101645941637120, 0, 45979382203891034141082255360, 0, 0, 45979404755035664251009105920, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0.Parent3
