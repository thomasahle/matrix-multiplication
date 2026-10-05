import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 1, for region 1, branch 1,
parent 8; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band4

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 256, upper := 320, values := [43026356092847334138839040, 43026356092847334138839040, 1783749791163470909584441344, 44255680552642972257091584, 485583161619277056709754880, 1783749791163470909584441344, 250276820491823820033753088, 43026356092847334138839040, 44255680552642972257091584, 43026356092847334138839040, 0, 0, 0, 0, 0, 43026356092847334138839040, 0, 1944713020096987230413783040, 0, 0, 0, 0, 43256000762742448953753600, 0, 0, 0, 0, 0, 0, 1783749791163470909584441344, 0, 80622245490306527752297119744, 0, 0, 0, 0, 1793270203049694098054184960, 0, 0, 935337631887615728208052224, 185510037972358954111677235200, 0, 0, 0, 0, 185510037972358954111677235200, 0, 0, 0, 0, 0, 0, 0, 935337631887615728208052224, 0, 44255680552642972257091584, 0, 2000276249242615436997033984, 0, 0, 0, 0, 44491886498820804638146560, 0] }

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
  { lower := 320, upper := 384, values := [0, 978130856875938016426721280, 193997425330571455280185344000, 0, 0, 0, 0, 193997425330571455280185344000, 0, 0, 0, 0, 0, 0, 0, 978130856875938016426721280, 0, 102651371510222637678723072, 16822582782865483382799728640, 0, 173195003261728438935921623040, 0, 0, 0, 0, 0, 0, 0, 16822582782865483382799728640, 0, 0, 0, 0, 0, 0, 102651371510222637678723072, 0, 0, 0, 0, 485583161619277056709754880, 0, 21947475512523141600384122880, 0, 0, 0, 0, 488174865750950495335219200, 0, 0, 586878514125562809856032768, 116398455198342873168111206400, 0, 0, 0, 0, 116398455198342873168111206400, 0, 0, 0, 0, 0, 0, 0] }

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
  { lower := 384, upper := 448, values := [586878514125562809856032768, 0, 1783749791163470909584441344, 0, 80622245490306527752297119744, 0, 0, 0, 0, 1793270203049694098054184960, 0, 0, 14983742063768275489136836608, 2971798059282691480573339238400, 0, 0, 0, 0, 2971798059282691480573339238400, 0, 0, 0, 0, 0, 0, 0, 14983742063768275489136836608, 0, 1375100664189024083904561152, 225352515195468871148754698240, 0, 2320091397860237213245783408640, 0, 0, 0, 0, 0, 0, 0, 225352515195468871148754698240, 0, 0, 0, 0, 0, 0, 1375100664189024083904561152, 959790903309514178618720256, 190359973605623240493681868800, 0, 0, 0, 0, 190359973605623240493681868800, 0, 0, 0, 0, 0, 0, 0, 959790903309514178618720256, 0, 2487157188883102658757394432] }

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
  { lower := 448, upper := 512, values := [407597162009844941129085091840, 0, 4196370599862295301718267658240, 0, 0, 0, 0, 0, 0, 0, 407597162009844941129085091840, 0, 0, 0, 0, 0, 0, 2487157188883102658757394432, 5201532235516157069665239040, 0, 207956293689325220549435064320, 0, 0, 207956242868545297479620362240, 0, 0, 0, 0, 0, 0, 5201532235516157069665239040, 0, 0, 0, 235644561027123196698034176, 4842805874446077271757291520, 5303587605407494702406565888, 3995314846418013749199765504, 197535502773458415032205312, 3988942733425321542263242752, 4059035976344935818564993024, 235847960591887441248387072, 4842805874446077271757291520, 197535502773458415032205312, 17447166808506746981136203776, 118082606096430483041891123200, 13316306419956954475192647680, 17275208328592805805655326720, 231415811568441127771591147520, 418563901794863190666190520320, 118082606096430483041891123200, 231415811568441127771591147520, 13676206593469304596143800320, 13676206593469304596143800320, 13316306419956954475192647680, 13316306419956954475192647680, 418563901794863190666190520320, 13316306419956954475192647680, 17447166808506746981136203776, 17275208328592805805655326720, 7349753408289300246314352640, 117752566636004310441892249600, 186722521880675025707178393600, 132350442753257344701615308800] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent3
