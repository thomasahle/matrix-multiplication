import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk22Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 1,
parent 92; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk22.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [64469180540158452099952148480, 18240272766345524987966783488, 1906872965491720782279367196672, 190855536994200737069213417472, 16905618661490974379091165184, 1906872696316831258709590016000, 16905618661490974379091165184, 16460733959872790842799292416, 621948812862220583736038129664, 16460733959872790842799292416, 190855536994200737069213417472, 621948812862220583736038129664, 64469440270315009930438901760, 16460733959872790842799292416, 16460733959872790842799292416, 18240272766345524987966783488, 1294957275891477989567682838528, 157063661207777857193021276160, 8133653883974210461781458944, 4827184214179652658848012959744, 218767242396547729661708206080, 1294946707862511558380094488576, 219047713220133047263838601216, 219047713220133047263838601216, 156783190384192539590890881024, 8133653883974210461781458944, 1302236293006078447396912627712, 54428251204033598546572738560, 1302236488234131903755340218368, 54428251204033598546572738560, 54428251204033598546572738560, 0, 0, 202187389550661337240672665600, 0, 54416794115756858281159557120, 0, 0, 0, 0, 162479649525287438475539251200, 0, 162479610787124883685480857600, 0, 63478990013663862021899157504, 8414124707559528063911854080, 0, 8414122701476110047998115840, 0, 18240272766345524987966783488, 1294957469513205545234111397888, 157063623760887387562631495680, 8133651944760239713064845312, 4827184893386349330983945240576, 218767190238378861247951011840, 1294946901484173248901972754432, 219047660995094731582884282368, 219047660995094731582884282368, 156783153004171517227698225152, 8133651944760239713064845312, 4857820661094977225505120452608, 202187389550661337240672665600, 4857821345203284208629997109248, 202187389550661337240672665600] }

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
  { lower := 64, upper := 128, values := [1868249084205816169299938639872, 226310940410221789305215385600, 0, 226310886453495373704776908800, 0, 190855536994200737069213417472, 16905618661490974379091165184, 1302225722615929056249478381568, 54416794115756858281159557120, 1302225917843916084513402257408, 54416794115756858281159557120, 1868248815030926645730161459200, 16905618661490974379091165184, 54428251204033598546572738560, 0, 0, 202187389550661337240672665600, 0, 54416794115756858281159557120, 0, 0, 0, 0, 226601082641516945445350277120, 0, 226601028615615239568500981760, 0, 16460733959872790842799292416, 226601082641516945445350277120, 0, 226601028615615239568500981760, 0, 621948812862220583736038129664, 16460733959872790842799292416, 162189507293992282335404359680, 0, 162189468625005017821756784640, 0, 190855536994200737069213417472, 621948812862220583736038129664, 63479230854354488373805056000, 8414124707559528063911854080, 0, 8414122701476110047998115840, 0, 16460733959872790842799292416, 16460733959872790842799292416, 18240272766345524987966783488, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk22.Parent2
