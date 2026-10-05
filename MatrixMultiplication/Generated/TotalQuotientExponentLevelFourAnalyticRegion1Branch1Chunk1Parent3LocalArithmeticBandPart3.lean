import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 1,
parent 8; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 0, 0, 0, 0, 935337631887615728208052224, 0, 79127098872463283210682368, 12967407561792143440908124160, 0, 133504481680915671679772917760, 0, 0, 0, 0, 0, 0, 0, 12967407561792143440908124160, 0, 0, 0, 0, 0, 0, 79127098872463283210682368, 978130856875938016426721280, 193997425330571455280185344000, 0, 0, 0, 0, 193997425330571455280185344000, 0, 0, 0, 0, 0, 0, 0, 978130856875938016426721280, 0, 2487157188883102658757394432, 407597162009844941129085091840, 0, 4196370599862295301718267658240, 0, 0, 0, 0, 0, 0, 0, 407597162009844941129085091840, 0, 0, 0, 0, 0, 0, 2487157188883102658757394432, 4284419972938308323171631104, 0, 171290315591470510610455724032] }

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
  { lower := 832, upper := 896, values := [0, 0, 171290273731196521345055719424, 0, 0, 0, 0, 0, 0, 4284419972938308323171631104, 0, 0, 0, 79127098872463283210682368, 12967407561792143440908124160, 0, 133504481680915671679772917760, 0, 0, 0, 0, 0, 0, 0, 12967407561792143440908124160, 0, 0, 0, 0, 0, 0, 79127098872463283210682368, 4359705307926042175495733248, 0, 174300209315921270381565968384, 0, 0, 174300166720083361176997593088, 0, 0, 0, 0, 0, 0, 4359705307926042175495733248, 0, 0, 0, 3513595961781686581277491200, 0, 0, 12799189154627460858590003200, 0, 3513598325270771025313792000, 0, 0, 0, 0, 139897088706514178730360832, 7351767308515117394475089920, 81256079111184268409176064, 105413291819914726584877056, 1412098888337607691543248896, 2554076216386683896212750336] }

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
  { lower := 896, upper := 960, values := [7351767308515117394475089920, 1412098888337607691543248896, 83452189357432491879694336, 83452189357432491879694336, 81256079111184268409176064, 81256079111184268409176064, 2554076216386683896212750336, 81256079111184268409176064, 139897088706514178730360832, 105413291819914726584877056, 137192708403274008343085056, 17003970961648743775423430656, 941450949743090340810719232, 169617340616386469521103257600, 586878514125562809856032768, 30566589277373063013335040, 935337631887615728208052224, 978130856875938016426721280, 586878514125562809856032768, 14983742063768275489136836608, 959790903309514178618720256, 17003970961648743775423430656, 935337631887615728208052224, 30566589277373063013335040, 959790903309514178618720256, 30566589277373063013335040, 935337631887615728208052224, 978130856875938016426721280, 137192708403274008343085056, 250480220056588064584105984, 43256000762742448953753600, 8519504340989037298206113792, 488174865750950495335219200, 43256000762742448953753600, 8519502268036172015095250944, 43256000762742448953753600, 43256000762742448953753600, 1793270203049694098054184960, 44491886498820804638146560, 488174865750950495335219200, 1793270203049694098054184960, 250480220056588064584105984, 43256000762742448953753600, 44491886498820804638146560, 43256000762742448953753600, 102651371510222637678723072, 16822582782865483382799728640, 0, 173195003261728438935921623040, 0, 0, 0, 0, 0, 0, 0, 16822582782865483382799728640, 0, 0, 0, 0, 0, 0, 102651371510222637678723072] }

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
  { lower := 960, upper := 1024, values := [5201532235516157069665239040, 0, 207956293689325220549435064320, 0, 0, 207956242868545297479620362240, 0, 0, 0, 0, 0, 0, 5201532235516157069665239040, 0, 0, 0, 3489600672286592136332181504, 0, 0, 12711780057961712345409388544, 0, 3489603019634775515872624640, 0, 0, 0, 0, 212167762238159038367924224, 0, 8482427768906686627674324992, 0, 0, 8482425695953821344563462144, 0, 0, 0, 0, 0, 0, 212167762238159038367924224, 0, 0, 0, 3513595961781686581277491200, 0, 0, 12799189154627460858590003200, 0, 3513598325270771025313792000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent3
