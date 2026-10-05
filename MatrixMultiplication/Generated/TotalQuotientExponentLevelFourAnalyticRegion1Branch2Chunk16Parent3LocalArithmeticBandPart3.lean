import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk16Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 2,
parent 69; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 0, 0, 0, 0, 0, 237330902418423484350726144, 0, 40598691938692366914813952, 6481467210022540824295768064, 0, 64675295919901419511400628224, 0, 0, 0, 0, 0, 0, 0, 6481467210022540824295768064, 0, 0, 0, 0, 0, 0, 40594059500086856603664384, 237326087818220246157754368, 19956570803024545488134209536, 0, 0, 0, 0, 19956565988424342249941237760, 0, 0, 0, 0, 0, 0, 0, 237330902418423484350726144, 0, 1043966364137803720666644480, 166666299686293906910462607360, 0, 1663079037940322216007444725760, 0, 0, 0, 0, 0, 0, 0, 166666299686293906910462607360, 0, 0, 0, 0, 0, 0, 1043847244287947741237084160, 2346921916017485162817257472, 0] }

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
  { lower := 832, upper := 896, values := [86668704033846890229147893760, 0, 0, 86668682810867833426308759552, 0, 0, 0, 0, 0, 0, 2346943138996541965656391680, 0, 0, 0, 40598691938692366914813952, 6481467210022540824295768064, 0, 64675295919901419511400628224, 0, 0, 0, 0, 0, 0, 0, 6481467210022540824295768064, 0, 0, 0, 0, 0, 0, 40594059500086856603664384, 2346921916017485162817257472, 0, 86668704033846890229147893760, 0, 0, 86668682810867833426308759552, 0, 0, 0, 0, 0, 0, 2346943138996541965656391680, 0, 0, 0, 752566630981279351073406976, 0, 0, 2692257433923400292118822912, 0, 752566380797312851387613184, 0, 0, 0, 0, 250510870474788037610962944, 21065269180970353570808332288, 0, 0, 0] }

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
  { lower := 896, upper := 960, values := [0, 21065264098892361263826862080, 0, 0, 0, 0, 0, 0, 0, 250515952552780344592433152, 0, 1055565990406001539785162752, 168518147460586061431689969664, 0, 1681557693917436907296416333824, 0, 0, 0, 0, 0, 0, 0, 168518147460586061431689969664, 0, 0, 0, 0, 0, 0, 1055445547002258271695273984, 2346921916017485162817257472, 0, 86668704033846890229147893760, 0, 0, 86668682810867833426308759552, 0, 0, 0, 0, 0, 0, 2346943138996541965656391680, 0, 0, 0, 1055565990406001539785162752, 168518147460586061431689969664, 0, 1681557693917436907296416333824, 0, 0, 0, 0, 0, 0, 0, 168518147460586061431689969664, 0, 0, 0, 0, 0, 0] }

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
  { lower := 960, upper := 1024, values := [1055445547002258271695273984, 75101501312559525210152239104, 0, 2773398529083100487332732600320, 0, 0, 2773397849947770669641880305664, 0, 0, 0, 0, 0, 0, 75102180447889342901004533760, 0, 0, 0, 15609688507127826540006473728, 0, 0, 55842630000411173801045262336, 0, 15609683317828134304588234752, 0, 0, 0, 0, 2346921916017485162817257472, 0, 86668704033846890229147893760, 0, 0, 86668682810867833426308759552, 0, 0, 0, 0, 0, 0, 2346943138996541965656391680, 0, 0, 0, 15682517535932466477207126016, 0, 0, 56103171042403760926089019392, 0, 15682512322421422645045100544, 0, 0, 0, 0, 0, 0, 0, 0, 63592574567472387500015616, 6039277411692829590109028352, 1048090525768793057258373120, 55470520366259528583088177152, 552838958647275458773647360, 40311174068030502202245120, 1048090525768793057258373120] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16.Parent3
