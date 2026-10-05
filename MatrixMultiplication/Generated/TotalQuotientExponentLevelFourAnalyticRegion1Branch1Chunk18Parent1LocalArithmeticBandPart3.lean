import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk18Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 1,
parent 75; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 326341387878680443359925895168, 0, 0, 0, 0, 0, 0, 0, 30684482160493723725779173376, 0, 0, 0, 0, 0, 0, 95257233955949122137620480, 2230919921009786066388910080, 0, 87306961982928109129049309184, 0, 0, 87306961982928109129049309184, 0, 0, 0, 0, 0, 0, 2230919921009786066388910080, 0, 0, 0, 95257233955949122137620480, 30684389677742310182942146560, 0, 326341387878680443359925895168, 0, 0, 0, 0, 0, 0, 0, 30684482160493723725779173376, 0, 0, 0, 0, 0, 0, 95257233955949122137620480, 57632097959419473381713510400, 0, 2255429851225642819167107153920, 0, 0, 2255429851225642819167107153920, 0, 0, 0, 0, 0, 0] }

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
  { lower := 832, upper := 896, values := [57632097959419473381713510400, 0, 0, 0, 41761619017236712191166513152, 0, 0, 150215301701193977102919008256, 0, 41761632949140173860305371136, 0, 0, 0, 0, 2230919921009786066388910080, 0, 87306961982928109129049309184, 0, 0, 87306961982928109129049309184, 0, 0, 0, 0, 0, 0, 2230919921009786066388910080, 0, 0, 0, 41761619017236712191166513152, 0, 0, 150215301701193977102919008256, 0, 41761632949140173860305371136, 0, 0, 0, 0, 1798881405143168355089252352, 0, 1798881834029968068836327424, 0, 105555313302538216422768640, 34001620994254992364881838080, 0, 361621537919618869669107073024, 0, 0, 0, 0, 0, 0, 0, 34001723475141693858295840768, 0, 0, 0, 0, 0, 0, 105555313302538216422768640, 58747557919924366414907965440] }

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
  { lower := 896, upper := 960, values := [0, 2299083332217106873731631808512, 0, 0, 2299083332217106873731631808512, 0, 0, 0, 0, 0, 0, 58747557919924366414907965440, 0, 0, 0, 40662629043098903975609499648, 0, 0, 146262267445899398758105350144, 0, 40662642608373327179771019264, 0, 0, 0, 0, 58747557919924366414907965440, 0, 2299083332217106873731631808512, 0, 0, 2299083332217106873731631808512, 0, 0, 0, 0, 0, 0, 58747557919924366414907965440, 0, 0, 0, 1260541500336066023243894489088, 0, 0, 4534130290822881361501265854464, 0, 1260541920859573142572901597184, 0, 0, 0, 0, 36790026156798991520212451328, 0, 36790034928225798569104244736, 0, 40662629043098903975609499648, 0, 0, 146262267445899398758105350144, 0, 40662642608373327179771019264, 0, 0, 0] }

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
  { lower := 960, upper := 1024, values := [0, 36731997724375018347467636736, 0, 36732006481966767341077266432, 0, 0, 4044131080055663667242336256, 101465531790816256007864320, 154636097055151895805385768960, 1061675930201467654326190080, 94041224586610188495093760, 154636072388108074365743005696, 94041224586610188495093760, 91566455518541499324170240, 3459727157160027460951080960, 91566455518541499324170240, 1061675930201467654326190080, 3459727157160027460951080960, 4044139302403604147123257344, 91566455518541499324170240, 91566455518541499324170240, 101465531790816256007864320, 57647868873957938861805928448, 190192111059210169860751360, 9849234322709098082074624, 207771865306554667062632906752, 264910440403899879448903680, 57647884825695434109127491584, 265250069173648469037940736, 265250069173648469037940736, 189852482289461580271714304, 9849234322709098082074624, 2642579400972659168968179712, 0, 2642579829859458882715254784, 0, 53850508732752602562293661696, 0, 0, 193698678509434338895869247488, 0, 53850526697575487346183241728, 0, 0, 0, 0, 43579352750403852731355758592, 0, 43579363140532452248260706304, 0, 0, 1798881405143168355089252352, 0, 1798881834029968068836327424, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent1
