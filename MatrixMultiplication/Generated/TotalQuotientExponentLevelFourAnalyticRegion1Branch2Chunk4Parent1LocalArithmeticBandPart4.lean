import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk4Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 4, for region 1, branch 2,
parent 19; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band16

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 1024, upper := 1088, values := [822728110713065288220278784, 1484693257263807474144641024, 23178236774226701395723026432, 907837915269589283553411072, 21750123537107908163643899904, 1446866677460907920663248896, 47283224753624441851740160, 907837915269589283553411072, 47283224753624441851740160, 1456323322411632809033596928, 822728110713065288220278784, 226514158663555325630611456, 10679436709917466360123752448, 261768710857102147729752064, 373573186022922255151210168320, 6477383206953399953397907456, 206073240461974031191506944, 373573336983428642222905491456, 211642787501486842845331456, 211642787501486842845331456, 3581218746406737893409161216, 194934146382948407883857920, 6477383206953399953397907456, 3581218746406737893409161216, 10679313170131353287859896320, 206073240461974031191506944, 194934146382948407883857920, 261768710857102147729752064, 14114290205096988841447784448, 0, 0, 48137264564290079269272420352, 0, 14114286972280320125898326016, 0, 0, 0, 0, 6392317001276494170590019584, 0, 231659683990679365879152508928, 0, 0, 231659769124709109057946910720, 0, 0, 0, 0, 0, 0, 6392231867246750991795617792, 0, 0, 0, 79112122108523791015401750528, 0, 0, 268168728064310586404763598848, 0, 79112122108523791015401750528, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band16

namespace Band17

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 1088, upper := 1107, values := [10348405015901225735484866560, 0, 10348405015901225735484866560, 0, 3789802256695750467803676672, 0, 0, 12846406134817273600228196352, 0, 3789802256695750467803676672, 0, 0, 0, 0, 9458635612664858662901121024, 0, 9458635612664858662901121024, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent1
