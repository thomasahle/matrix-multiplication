import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk17Parent0LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 2,
parent 70; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 315143159339655518411449958400, 0, 0, 0, 0, 0, 0, 0, 30235845335790715445559951360, 0, 0, 0, 0, 0, 0, 204718460848654599019560960, 2502814381730340713772613632, 0, 94037165869415486661563777024, 0, 0, 94030053639615833593817858048, 0, 0, 0, 0, 0, 0, 2509926611529993781518532608, 0, 0, 0, 204718460848654599019560960, 30235845335790715445559951360, 0, 315143159339655518411449958400, 0, 0, 0, 0, 0, 0, 0, 30235845335790715445559951360, 0, 0, 0, 0, 0, 0, 204718460848654599019560960, 64358084101637332639867207680, 0, 2418098550927826799868782837760, 0, 0, 2417915665018692863841030635520, 0, 0, 0, 0, 0, 0] }

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
  { lower := 832, upper := 896, values := [64540970010771268667619409920, 0, 0, 0, 46569207225670862614472687616, 0, 0, 169382245129614229316850155520, 0, 46569207225670862614472687616, 0, 0, 0, 0, 2502814381730340713772613632, 0, 94037165869415486661563777024, 0, 0, 94030053639615833593817858048, 0, 0, 0, 0, 0, 0, 2509926611529993781518532608, 0, 0, 0, 46569207225670862614472687616, 0, 0, 169382245129614229316850155520, 0, 46569207225670862614472687616, 0, 0, 0, 0, 2098695222850996247289921536, 0, 2098695222850996247289921536, 0, 216091708673579854520647680, 31915614521112421859202170880, 0, 332651112636303047212086067200, 0, 0, 0, 0, 0, 0, 0, 31915614521112421859202170880, 0, 0, 0, 0, 0, 0, 216091708673579854520647680, 65073173924988858558087954432] }

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
  { lower := 896, upper := 960, values := [0, 2444966312604802653200658202624, 0, 0, 2444781394630011673439264309248, 0, 0, 0, 0, 0, 0, 65258091899779838319481847808, 0, 0, 0, 46569207225670862614472687616, 0, 0, 169382245129614229316850155520, 0, 46569207225670862614472687616, 0, 0, 0, 0, 65073173924988858558087954432, 0, 2444966312604802653200658202624, 0, 0, 2444781394630011673439264309248, 0, 0, 0, 0, 0, 0, 65258091899779838319481847808, 0, 0, 0, 1490214631221467603663126003712, 0, 0, 5420231844147655338139204976640, 0, 1490214631221467603663126003712, 0, 0, 0, 0, 43531000912683567322819985408, 0, 43531000912683567322819985408, 0, 46569207225670862614472687616, 0, 0, 169382245129614229316850155520, 0, 46569207225670862614472687616, 0, 0, 0] }

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
  { lower := 960, upper := 1024, values := [0, 43734100450378825024170622976, 0, 43734100450378825024170622976, 0, 0, 3692691253092306534046629888, 216091708673579854520647680, 131192442314517507820058836992, 1700300549826325697412464640, 204718460848654599019560960, 131186333769920880716248252416, 204718460848654599019560960, 204718460848654599019560960, 8768774073017371991337861120, 204718460848654599019560960, 1700300549826325697412464640, 8768774073017371991337861120, 3698799797688933637857214464, 204718460848654599019560960, 204718460848654599019560960, 216091708673579854520647680, 64191874892912308733240934400, 426661057078987446420504576, 23969722307808283506769920, 233148250445040397888520192000, 647981493054417264133013504, 64191871424155433239471718400, 647981493054417264133013504, 647981493054417264133013504, 426661057078987446420504576, 23969722307808283506769920, 5488549194066072236214714368, 0, 5488549194066072236214714368, 0, 56121865118116167766159392768, 0, 0, 204127321053637660971588648960, 0, 56121865118116167766159392768, 0, 0, 0, 0, 50233285656627071467391025152, 0, 50233285656627071467391025152, 0, 0, 2098695222850996247289921536, 0, 2098695222850996247289921536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17.Parent0
