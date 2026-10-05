import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk12Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 1,
parent 52; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk12.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [1382206465279920719798032400384, 16924961474604808445886464000, 54106999894822947873805473677312, 191010279499111409603575808000, 16924961474604808445886464000, 54107001656265645984183138385920, 16924961474604808445886464000, 16924961474604808445886464000, 701660545704330772999464550400, 17408531802450660115768934400, 191010279499111409603575808000, 701660545704330772999464550400, 1382215083598751956900547395584, 16924961474604808445886464000, 17408531802450660115768934400, 16924961474604808445886464000, 39433011599070856947243352588288, 33917618751812319469344129024, 1760195783527186239926042624, 142867670710567309843683380035584, 54633769127170742139242938368, 39438407926236852741596390621184, 54633769127170742139242938368, 56935563613321677991453917184, 33917618751812319469344129024, 1692495945699217538390425600, 39335022571371971359689288974336, 3661520425567193567823134720, 39335034340970516131139184230400, 3661520425567193567823134720, 3661520425567193567823134720, 0, 0, 13373770414294074264649728000, 0, 3661519191941183638496870400, 0, 0, 0, 0, 33917618751812319469344129024, 0, 33917626838403752781768818688, 0, 1376476444959302832558283161600, 1760195783527186239926042624, 0, 1760196203190613916818341888, 0, 18278958392573193121557381120, 39433023361750260402385567350784, 33917626838403752781768818688, 1760196203190613916818341888, 142867713704175592842383455158272, 54633782152877901187400073216, 39438419689249560849760854736896, 54633782152877901187400073216, 56935577187819473232470212608, 33917626838403752781768818688, 1692496349221744150786867200, 142509043165886556564811765776384, 13373770414294074264649728000, 142509086183431362370695063404544, 13373770414294074264649728000] }

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
  { lower := 64, upper := 128, values := [53837791287602690407357975887872, 54633769127170742139242938368, 0, 54633782152877901187400073216, 0, 206291101859040322371861872640, 18278958392573193121557381120, 39340427342127175313388679987200, 3661519191941183638496870400, 39340439112063151161019402813440, 3661519191941183638496870400, 53837792926263859963124865040384, 18278958392573193121557381120, 3661520425567193567823134720, 0, 0, 13373770414294074264649728000, 0, 3661519191941183638496870400, 0, 0, 0, 0, 54633769127170742139242938368, 0, 54633782152877901187400073216, 0, 18278958392573193121557381120, 56935563613321677991453917184, 0, 56935577187819473232470212608, 0, 757793389360677234839421714432, 18801214346646712925030449152, 33917618751812319469344129024, 0, 33917626838403752781768818688, 0, 206291101859040322371861872640, 757793389360677234839421714432, 1376484949941338480789313028096, 1692495945699217538390425600, 0, 1692496349221744150786867200, 0, 18278958392573193121557381120, 18801214346646712925030449152, 18278958392573193121557381120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk12.Parent2
