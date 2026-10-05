import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk20Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 1, branch 2,
parent 84; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk20.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [0, 0, 17307048204379866670468956160, 0, 0, 0, 42948318700793380109184663552, 0, 0, 153644774477914236025804161024, 0, 42948304423013467057991712768, 0, 0, 0, 0, 89254939803483746358276390912, 0, 3296066182940413121954536488960, 0, 0, 3296065375816961234848387694592, 0, 0, 0, 0, 0, 0, 89255746926935633464425185280, 0, 0, 0, 1004811706270645122137799524352, 0, 0, 3594647536222868480353709850624, 0, 1004811372230085906377597779968, 0, 0, 0, 0, 21470522556355814142781685760, 0, 21470522556355814142781685760, 0, 80528097563987587704721244160, 0, 0, 288083952146089192548382801920, 0, 80528070793150250733734461440, 0, 0, 0, 0, 48279661532129830721065844736, 0, 48279661532129830721065844736, 0, 0, 3745300593422570597103173632, 2248006379117070183531806720, 70116438455131741087512657920] }

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
  { lower := 576, upper := 640, values := [17688260719894841707263426560, 2129690253900382279135395840, 70116421705488122159239790592, 2129690253900382279135395840, 2129690253900382279135395840, 91221732542066374289632788480, 2129690253900382279135395840, 17688260719894841707263426560, 91221732542066374289632788480, 3745317343066189525376040960, 2129690253900382279135395840, 2129690253900382279135395840, 2248006379117070183531806720, 38934789429749442611068796928, 24119188084683183276473450496, 1355010566555235015532216320, 155893511638632844268505399296, 36630452315876519919887581184, 38934776936692018691274964992, 36630452315876519919887581184, 36630452315876519919887581184, 24119188084683183276473450496, 1355010566555235015532216320, 10586776010314129222339133440, 10341477202813763560553840640, 10586776010314129222339133440, 10341477202813763560553840640, 81422854203587449790329257984, 0, 0, 291284884947712405798920388608, 0, 81422827135296364630775955456, 0, 0, 0, 0, 21470522556355814142781685760, 0, 21470522556355814142781685760, 0, 0, 1547425049106725343623905280, 0, 1547425049106725343623905280, 0, 0, 8487531415754501794037760, 1355010566555235015532216320, 0, 13520967788132700943149957120, 0, 0, 0, 0, 0, 0, 0, 1355010566555235015532216320, 0, 0, 0, 0, 0] }

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
  { lower := 640, upper := 704, values := [0, 8486562961690632042577920, 2083772913700009642605674496, 0, 76950961469425987282985287680, 0, 0, 76950942626076915988678311936, 0, 0, 0, 0, 0, 0, 2083791757049080936912650240, 0, 0, 0, 3131648238599517299628048384, 0, 0, 11203264805681246376881553408, 0, 3131647197511398639645229056, 0, 0, 0, 0, 2083772913700009642605674496, 0, 76950961469425987282985287680, 0, 0, 76950942626076915988678311936, 0, 0, 0, 0, 0, 0, 2083791757049080936912650240, 0, 0, 0, 80528097563987587704721244160, 0, 0, 288083952146089192548382801920, 0, 80528070793150250733734461440, 0, 0, 0, 0, 1508739422879057210033307648, 0, 1508739422879057210033307648, 0, 3131648238599517299628048384, 0, 0, 11203264805681246376881553408, 0, 3131647197511398639645229056] }

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
  { lower := 704, upper := 768, values := [0, 0, 0, 0, 1508739422879057210033307648, 0, 1508739422879057210033307648, 0, 0, 2199538075572232400528211968, 0, 81226014884394097687595581440, 0, 0, 81225994994192300210271551488, 0, 0, 0, 0, 0, 0, 2199557965774029877852241920, 0, 0, 0, 81422854203587449790329257984, 0, 0, 291284884947712405798920388608, 0, 81422827135296364630775955456, 0, 0, 0, 0, 1508739422879057210033307648, 0, 1508739422879057210033307648, 0, 81422854203587449790329257984, 0, 0, 291284884947712405798920388608, 0, 81422827135296364630775955456, 0, 0, 0, 0, 48279661532129830721065844736, 0, 48279661532129830721065844736, 0, 0, 1508739422879057210033307648, 0, 1508739422879057210033307648, 0, 0, 2692756481761276888866619392, 151060820718093250357886976, 8486562961690632042577920, 9737168985096408092286910464, 229420085397703419551023104] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk20.Parent2
