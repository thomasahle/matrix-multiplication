import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk9Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 1,
parent 41; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk9.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [365262287615730343498018193408, 42650902916004117283633889280, 13059017758230232520321086259200, 481345904337760752201011036160, 42650902916004117283633889280, 13059016303741355796470360440832, 42650902916004117283633889280, 42650902916004117283633889280, 1768184575174913547958650667008, 43869500142175663491737714688, 481345904337760752201011036160, 1768184575174913547958650667008, 365263279312691746123513069568, 42650902916004117283633889280, 43869500142175663491737714688, 42650902916004117283633889280, 10108128572800079073365570093056, 150206633141502333747833339904, 7795154614129861631624085504, 36678480867648668415460995235840, 241949606677030705258486038528, 10109913451631831977387911806976, 241949606677030705258486038528, 252143270403200524315225227264, 150206633141502333747833339904, 7495340975124866953484697600, 10157509254343598809416812462080, 29582874775533453852729671680, 10157514198475093788342649618432, 29582874775533453852729671680, 29582874775533453852729671680, 0, 0, 106408720834344624627688407040, 0, 29582884644541533287339786240, 0, 0, 0, 0, 140515882616244118667327963136, 0, 140515849114651037801568534528, 0, 372436686226432257553183277056, 7292241413218257655390273536, 0, 7292239674612628708265033728, 0, 41973904457019924945798430720, 10108133479684459884431452143616, 150206597329454557649952571392, 7795152755620396205386760192, 36678498476038591107246095073280, 241949548991756143759504441344, 10109918359610086472446279417856, 241949548991756143759504441344, 252143210287567431105010204672, 150206597329454557649952571392, 7495339188096534812871884800, 36845646972421552220529777180672, 106408720834344624627688407040, 36845664716799580816508543041536, 106408720834344624627688407040] }

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
  { lower := 64, upper := 128, values := [13367576098076644078565583749120, 226339954633351304919228874752, 0, 226339900669707360291149316096, 0, 473705493157796295816868003840, 41973904457019924945798430720, 10159291554756520874019808870400, 29582884644541533287339786240, 10159296499995351922124248842240, 29582884644541533287339786240, 13367574615253568457496986648576, 41973904457019924945798430720, 29582874775533453852729671680, 0, 0, 106408720834344624627688407040, 0, 29582884644541533287339786240, 0, 0, 0, 0, 226339954633351304919228874752, 0, 226339900669707360291149316096, 0, 41973904457019924945798430720, 235875962635252103391662309376, 0, 235875906398046951678880514048, 0, 1740118153346740317038672084992, 43173158870077637087106957312, 140515882616244118667327963136, 0, 140515849114651037801568534528, 0, 473705493157796295816868003840, 1740118153346740317038672084992, 372437706257592557396549435392, 7011770589632940053259878400, 0, 7011768917896758373331763200, 0, 41973904457019924945798430720, 43173158870077637087106957312, 41973904457019924945798430720, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk9.Parent3
