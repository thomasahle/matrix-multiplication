import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 1, branch 1,
parent 8; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [116398455198342873168111206400, 6062419541580357977505792000, 185510037972358954111677235200, 193997425330571455280185344000, 116398455198342873168111206400, 2971798059282691480573339238400, 190359973605623240493681868800, 117752566636004310441892249600, 185510037972358954111677235200, 6062419541580357977505792000, 190359973605623240493681868800, 6062419541580357977505792000, 185510037972358954111677235200, 193997425330571455280185344000, 7349753408289300246314352640, 935337631887615728208052224, 185510037972358954111677235200, 0, 0, 0, 0, 185510037972358954111677235200, 0, 0, 0, 0, 0, 0, 0, 935337631887615728208052224, 0, 1375100664189024083904561152, 225352515195468871148754698240, 0, 2320091397860237213245783408640, 0, 0, 0, 0, 0, 0, 0, 225352515195468871148754698240, 0, 0, 0, 0, 0, 0, 1375100664189024083904561152, 5568856309251422131912179712, 1944713020096987230413783040, 155445103523580390866948194304, 21947475512523141600384122880, 1944713020096987230413783040, 155445065942951026702164164608, 1944713020096987230413783040, 1944713020096987230413783040, 80622245490306527752297119744, 2000276249242615436997033984, 21947475512523141600384122880, 80622245490306527752297119744, 5568856309251422131912179712, 1944713020096987230413783040] }

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
  { lower := 576, upper := 640, values := [2000276249242615436997033984, 1944713020096987230413783040, 81265669112259588162322432, 13317878036435174344716451840, 0, 137112710915535014157604618240, 0, 0, 0, 0, 0, 0, 0, 13317878036435174344716451840, 0, 0, 0, 0, 0, 0, 81265669112259588162322432, 4291264094300829582473822208, 0, 171563942293693306953283928064, 0, 0, 171563900366549870420686798848, 0, 0, 0, 0, 0, 0, 4291264094300829582473822208, 0, 0, 0, 3523879657279584200539766784, 0, 0, 12836650196055638792810266624, 0, 3523882027686197672217149440, 0, 0, 0, 0, 0, 0, 0, 0, 43026356092847334138839040, 0, 1944713020096987230413783040, 0, 0, 0, 0, 43256000762742448953753600, 0, 0, 30566589277373063013335040, 6062419541580357977505792000, 0] }

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
  { lower := 640, upper := 704, values := [0, 0, 0, 6062419541580357977505792000, 0, 0, 0, 0, 0, 0, 0, 30566589277373063013335040, 0, 44255680552642972257091584, 0, 2000276249242615436997033984, 0, 0, 0, 0, 44491886498820804638146560, 0, 0, 959790903309514178618720256, 190359973605623240493681868800, 0, 0, 0, 0, 190359973605623240493681868800, 0, 0, 0, 0, 0, 0, 0, 959790903309514178618720256, 0, 81265669112259588162322432, 13317878036435174344716451840, 0, 137112710915535014157604618240, 0, 0, 0, 0, 0, 0, 0, 13317878036435174344716451840, 0, 0, 0, 0, 0, 0, 81265669112259588162322432, 30566589277373063013335040, 6062419541580357977505792000, 0, 0, 0, 0] }

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
  { lower := 704, upper := 768, values := [6062419541580357977505792000, 0, 0, 0, 0, 0, 0, 0, 30566589277373063013335040, 0, 79127098872463283210682368, 12967407561792143440908124160, 0, 133504481680915671679772917760, 0, 0, 0, 0, 0, 0, 0, 12967407561792143440908124160, 0, 0, 0, 0, 0, 0, 79127098872463283210682368, 212167762238159038367924224, 0, 8482427768906686627674324992, 0, 0, 8482425695953821344563462144, 0, 0, 0, 0, 0, 0, 212167762238159038367924224, 0, 0, 0, 43026356092847334138839040, 0, 1944713020096987230413783040, 0, 0, 0, 0, 43256000762742448953753600, 0, 0, 935337631887615728208052224, 185510037972358954111677235200, 0, 0, 0, 0, 185510037972358954111677235200, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent3
