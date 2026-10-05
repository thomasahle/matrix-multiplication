import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent0LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 1, branch 1,
parent 5; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [0, 0, 22000310117732130763801886720, 0, 0, 0, 40476625479725029416316698624, 0, 0, 147446659061308349090956836864, 0, 40476652707119282211614883840, 0, 0, 0, 0, 80816329065390687945003892736, 0, 3231021841460878912162719858688, 0, 0, 3231021051857222209062217711616, 0, 0, 0, 0, 0, 0, 80816329065390687945003892736, 0, 0, 0, 1033418844279229657285335711744, 0, 0, 3764497514159028787728491741184, 0, 1033419539428639173965292503040, 0, 0, 0, 0, 18656143248292957424065708032, 0, 18656143248292957424065708032, 0, 66196147919966975191267934208, 0, 0, 241136723673181362575835660288, 0, 66196192448101326116911841280, 0, 0, 0, 0, 33743537477083529524398784512, 0, 33743537477083529524398784512, 0, 0, 3482477752598748353901101056, 1982435153282019935807078400, 70728642319728659003686780928] }

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
  { lower := 576, upper := 640, values := [22373196729897082132679884800, 1982435153282019935807078400, 70728625450181203596301828096, 1982435153282019935807078400, 1982435153282019935807078400, 82186097354634597910173450240, 2039076157661506219687280640, 22373196729897082132679884800, 82186097354634597910173450240, 3482477752598748353901101056, 1982435153282019935807078400, 2039076157661506219687280640, 1982435153282019935807078400, 37775786909841837097104703488, 22834015812056484311350640640, 1184998824577781620948336640, 158189471945365471890262458368, 36780540439779606465588756480, 37821388462536254909034004480, 36780540439779606465588756480, 38330154287304397816059658240, 22834015812056484311350640640, 1139421946709405404758016000, 10426682310167701367071703040, 10296490332525369898303488000, 10426682310167701367071703040, 10296490332525369898303488000, 64509621858311765632254738432, 0, 0, 234993112878960181363712458752, 0, 64509665251971356024761221120, 0, 0, 0, 0, 18656143248292957424065708032, 0, 18656143248292957424065708032, 0, 0, 1102540347488541807332032512, 0, 1102540347488541807332032512, 0, 0, 6952750779606821031116800, 1139421946709405404758016000, 0, 11730790112551673975013376000, 0, 0, 0, 0, 0, 0, 0, 1139421946709405404758016000, 0, 0, 0, 0, 0] }

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
  { lower := 640, upper := 704, values := [0, 6952750779606821031116800, 1949394567393986270210293760, 0, 77936433115872337646929838080, 0, 0, 77936414069609081541817794560, 0, 0, 0, 0, 0, 0, 1949394567393986270210293760, 0, 0, 0, 2108157577069011948766494720, 0, 0, 7679513492776476515154001920, 0, 2108158995162462615188275200, 0, 0, 0, 0, 2005091555033814449359159296, 0, 80163188347754404436842119168, 0, 0, 80163168757312198157298302976, 0, 0, 0, 0, 0, 0, 2005091555033814449359159296, 0, 0, 0, 66196147919966975191267934208, 0, 0, 241136723673181362575835660288, 0, 66196192448101326116911841280, 0, 0, 0, 0, 1102540347488541807332032512, 0, 1102540347488541807332032512, 0, 2108157577069011948766494720, 0, 0, 7679513492776476515154001920, 0, 2108158995162462615188275200] }

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
  { lower := 704, upper := 768, values := [0, 0, 0, 0, 1073526127817790707139084288, 0, 1073526127817790707139084288, 0, 0, 1949394567393986270210293760, 0, 77936433115872337646929838080, 0, 0, 77936414069609081541817794560, 0, 0, 0, 0, 0, 0, 1949394567393986270210293760, 0, 0, 0, 64509621858311765632254738432, 0, 0, 234993112878960181363712458752, 0, 64509665251971356024761221120, 0, 0, 0, 0, 1073526127817790707139084288, 0, 1073526127817790707139084288, 0, 67461042466208382360527831040, 0, 0, 245744431768847248484928061440, 0, 67461087845198803686024806400, 0, 0, 0, 0, 33743537477083529524398784512, 0, 33743537477083529524398784512, 0, 0, 1073526127817790707139084288, 0, 1073526127817790707139084288, 0, 0, 2536463733231236886709665792, 139333125623320693463580672, 7230860810791093872361472, 9365317498140094879615680512, 224434795165708182884450304] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent0
