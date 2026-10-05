import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk8Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 2,
parent 36; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [78467148433183411397711626240, 20909580976054626205718020096, 2058894220883739132196301045760, 517400907981947452707448029184, 16460733959872790842799292416, 2058868715382365153242501873664, 16905618661490974379091165184, 16905618661490974379091165184, 286060863140492013835674189824, 15570964556636423770215546880, 517400907981947452707448029184, 286060863140492013835674189824, 78492927831813396790933192704, 16460733959872790842799292416, 15570964556636423770215546880, 20909580976054626205718020096, 1282557369655330731000441339904, 205807531531194470701979402240, 8394780891403984989159686144, 4517787940505423008364872335360, 169520414129641761393998823424, 1282557105202807690300309372928, 169791213513235438329133006848, 152189253579646437545411084288, 205807531531194470701979402240, 8394780891403984989159686144, 1246306538917832392046282801152, 50742250104406185032800010240, 1246123706711590737621299494912, 51240700498359094512493527040, 50742250104406185032800010240, 0, 0, 174189272289550749900998705152, 0, 50742250104406185032800010240, 0, 0, 0, 0, 213157800514451416084192952320, 0, 213157800514451416084192952320, 0, 75374484790651529356197756928, 8694594494668413024486817792, 0, 8694594494668413024486817792, 0, 20000468759704425066338975744, 1282374537449089076575458033664, 205807531531194470701979402240, 8394780891403984989159686144, 4517168188703925908348097003520, 169520414129641761393998823424, 1282374272996566035875326066688, 169791213513235438329133006848, 152189253579646437545411084288, 205807531531194470701979402240, 8394780891403984989159686144, 4398979497072127641460173438976, 174189272289550749900998705152, 4398359745270630541443398107136, 175900365337581700292953505792] }

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
  { lower := 64, upper := 128, values := [1981114587619697263836315779072, 175574714634271824300927352832, 0, 175574714634271824300927352832, 0, 494905216330558433024515506176, 15745049874660930371373236224, 1246306286271225558520263868416, 50742250104406185032800010240, 1246123454064983904095280562176, 51240700498359094512493527040, 1981089049061757904795000111104, 16170591763165279840869810176, 51240700498359094512493527040, 0, 0, 175900365337581700292953505792, 0, 51240700498359094512493527040, 0, 0, 0, 0, 175855185424422418269459185664, 0, 175855185424422418269459185664, 0, 16170591763165279840869810176, 157624584064633810314890051584, 0, 157624584064633810314890051584, 0, 273623434308296708886297051136, 14893966097652231432380088320, 213157800514451416084192952320, 0, 213157800514451416084192952320, 0, 494905216330558433024515506176, 273623434308296708886297051136, 75400287801113929097645391872, 8694594494668413024486817792, 0, 8694594494668413024486817792, 0, 15745049874660930371373236224, 14893966097652231432380088320, 20000468759704425066338975744, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8.Parent2
