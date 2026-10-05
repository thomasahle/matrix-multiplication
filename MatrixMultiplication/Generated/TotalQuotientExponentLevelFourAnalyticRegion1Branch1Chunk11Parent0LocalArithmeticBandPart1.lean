import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk11Parent0LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 1, for region 1, branch 1,
parent 46; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band4

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 256, upper := 320, values := [1377117624268514458637172736, 48026467130784291823288320, 1369269051173985108292009984, 1403581766038515950414725120, 301779613145788986155448926208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 941715434547933169934401536, 13880640697758062962425200640, 24471718682480994026151477248, 860018494394288307737460736, 15368469481850973383452262400, 860018494394288307737460736, 24390021742327349163954536448, 24886644691131852533207662592, 15368469481850973383452262400, 382583597309242401266690162688, 24491042606128896614365921280, 13880640697758062962425200640, 24390021742327349163954536448, 860018494394288307737460736, 24491042606128896614365921280, 860018494394288307737460736, 24390021742327349163954536448, 24961900323402863199333122048, 941715434547933169934401536, 1107315191180372729257275686912, 0, 43336608465763088338591399542784, 0, 0, 43336615681568583999967631245312, 0, 0, 0, 0, 0, 0, 1107322471420345440100971184128, 0, 0, 0, 52928283540002983555104768, 779218803872388678131122176, 1374170867583203800023826432, 48026467130784291823288320, 862530793363174958991147008, 48026467130784291823288320, 1369269051173985108292009984, 1399662201857734144887357440] }

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
  { lower := 320, upper := 384, values := [862530793363174958991147008, 21511456029029328227494002688, 1377117624268514458637172736, 779218803872388678131122176, 1369269051173985108292009984, 48026467130784291823288320, 1377117624268514458637172736, 48026467130784291823288320, 1369269051173985108292009984, 1403581766038515950414725120, 52928283540002983555104768, 4549204484337946015152734208, 0, 179400970156791046830368489472, 0, 0, 179400914184757841177161498624, 0, 0, 0, 0, 0, 0, 4549216599237116423900758016, 0, 0, 0, 33788243362150413008122150912, 0, 0, 124384470890870962963779420160, 0, 33784361946973534539858575360, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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
  { lower := 384, upper := 448, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1494118976248092788451704832, 22024541147393115179962073088, 38828808379428741233476894720, 1365037810805333906180538368, 24385658275697177611777081344, 1365037810805333906180538368, 38699727213985982351205728256, 39483356708153371277966442496, 24385658275697177611777081344, 606989319207252053106672795648, 38856235883961248132878041088, 22024541147393115179962073088, 38699727213985982351205728256, 1365037810805333906180538368, 38856235883961248132878041088, 1365037810805333906180538368, 38699727213985982351205728256, 39603295372085294527103893504, 1494118976248092788451704832, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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
  { lower := 448, upper := 512, values := [1522141498957441263149776896, 22447329896237951646299062272, 39570002688381063528347336704, 1393877302916218829500579840, 24855968198459131317899493376, 1393877302916218829500579840, 39441738492339841094698139648, 40214161810843380353366753280, 24855968198459131317899493376, 618282872818134258244162420736, 39578517115149677498667630592, 22447329896237951646299062272, 39441738492339841094698139648, 1393877302916218829500579840, 39578517115149677498667630592, 1393877302916218829500579840, 39441738492339841094698139648, 40339587864628398130242519040, 1522141498957441263149776896, 5885954079367351789535887360, 0, 232108046844339391425111130112, 0, 0, 232107974385528669893992382464, 0, 0, 0, 0, 0, 0, 5885969795993302590073864192, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 941715434547933169934401536, 13880640697758062962425200640, 24471718682480994026151477248] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent0
