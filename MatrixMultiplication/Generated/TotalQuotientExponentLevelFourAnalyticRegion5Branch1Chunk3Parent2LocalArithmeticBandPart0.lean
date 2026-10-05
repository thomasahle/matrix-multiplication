import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk3Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 5, branch 1,
parent 54; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk3.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 170998865339216691409715200, 6033600511747205647734669312, 0, 66828521806658157096302804992, 0, 0, 0, 0, 0, 0, 0, 6023917322352214780730671104, 0, 0, 0, 0, 0, 0, 170944558241194330847969280, 1998994677495314583830659072, 0, 70988124535017184218048364544, 0, 0, 70987887272075892366835187712, 0, 0, 0, 0, 0, 0, 1999121677487374832370712576, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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
  { lower := 64, upper := 128, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1998994677495314583830659072, 0, 0, 6844906646210920988368961536, 0, 1999431311432143329906655232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 170998865339216691409715200, 0, 170999637716685884611362816, 0, 170999637716685884611362816, 6033627844756499204405198848] }

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
  { lower := 128, upper := 192, values := [0, 66828824542126657651324485632, 0, 0, 0, 0, 0, 0, 0, 6023944609205241656387829760, 0, 0, 0, 0, 0, 0, 170945330385602243333193728, 6844906646210920988368961536, 0, 243309755393078517228753649664, 0, 0, 243308931109861022277977505792, 0, 0, 0, 0, 0, 0, 6845346867525498763479089152, 0, 0, 0, 70988124535017184218048364544, 0, 0, 243309755393078517228753649664, 0, 70999902239542511276105138176, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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
  { lower := 192, upper := 256, values := [0, 0, 0, 0, 0, 6033600511747205647734669312, 0, 6033627844756499204405198848, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1999431311432143329906655232, 0, 70999902239542511276105138176, 0, 0, 70999665134918508925660692480, 0, 0, 0, 0, 0, 0, 1999558277998487144102887424, 0, 0, 0, 70987887272075892366835187712, 0, 0, 243308931109861022277977505792, 0, 70999665134918508925660692480, 0, 0, 0, 0, 66828521806658157096302804992, 0, 66828824542126657651324485632, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk3.Parent2
