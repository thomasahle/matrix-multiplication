import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk16Parent0LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 2,
parent 66; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [2899788708292810655279794356224, 3462363547376297956358488064, 105133921452130253591116676857856, 73270576075203445020591915008, 2843393527733607818908925952, 105132556518211510880342691020800, 2901421967075110019294822400, 2901421967075110019294822400, 67138904318118045846482190336, 2727336649050603418137133056, 73270576075203445020591915008, 67138904318118045846482190336, 2901157155652216621069819183104, 2843393527733607818908925952, 2727336649050603418137133056, 3462363547376297956358488064, 77198357498137803796867975217152, 7350268983256945382213550080, 299813603264428035327131648, 264727135218514539192743771504640, 6054300504630062906928529408, 77198357186457344263224830197760, 6063971911186979940326178816, 5435330484987372769478967296, 7350268983256945382213550080, 299813603264428035327131648, 76967218589121399776785238851584, 0, 76967175536464403888047575269376, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7350268983256945382213550080, 0, 7350268983256945382213550080, 0, 2912534342373510447624043364352, 299813603264428035327131648, 0, 299813603264428035327131648, 0, 3462363547376297956358488064, 77198317615772343983382441492480, 7350268983256945382213550080, 299813603264428035327131648, 264726995204300802737933471711232, 6054300504630062906928529408, 77198317304100427778232418304000, 6063971911186979940326178816, 5435330484987372769478967296, 7350268983256945382213550080, 299813603264428035327131648, 263921771271867341238549555970048, 0, 263921619908250764188490905157632, 0] }

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
  { lower := 64, upper := 128, values := [105596544807302239272942627192832, 6054300504630062906928529408, 0, 6054300504630062906928529408, 0, 73270576075203445020591915008, 2843393527733607818908925952, 76967218286885139250850564145152, 0, 76967175234237754606667662622720, 0, 105595188803378515668667740454912, 2901421967075110019294822400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6063971911186979940326178816, 0, 6063971911186979940326178816, 0, 2901421967075110019294822400, 5435330484987372769478967296, 0, 5435330484987372769478967296, 0, 67138904318118045846482190336, 2727336649050603418137133056, 7350268983256945382213550080, 0, 7350268983256945382213550080, 0, 73270576075203445020591915008, 67138904318118045846482190336, 2913893831403698409697097809920, 299813603264428035327131648, 0, 299813603264428035327131648, 0, 2843393527733607818908925952, 2727336649050603418137133056, 3462363547376297956358488064, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16.Parent0
