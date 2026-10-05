import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk4Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 1,
parent 21; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 0, 0, 0, 0, 0, 95949586377895625883648000, 0, 25341445255559417901875200, 8163020790403671328712294400, 0, 86817158887641376549576376320, 0, 0, 0, 0, 0, 0, 0, 8163045393748579638826762240, 0, 0, 0, 0, 0, 0, 25341445255559417901875200, 98693078390258078947737600, 17309838724060402036821196800, 0, 0, 0, 0, 17309840799319110329145753600, 0, 0, 0, 0, 0, 0, 0, 98691003131549786623180800, 0, 795721381024565722118881280, 256318852818675279721566044160, 0, 2726058789071939223656698216448, 0, 0, 0, 0, 0, 0, 0, 256319625363705400659160334336, 0, 0, 0, 0, 0, 0, 795721381024565722118881280, 5576416800696673864796602368, 0] }

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
  { lower := 832, upper := 896, values := [218239193696748934188647841792, 0, 0, 218239273739477313023605997568, 0, 0, 0, 0, 0, 0, 5576496843425052699754758144, 0, 0, 0, 25341445255559417901875200, 8163020790403671328712294400, 0, 86817158887641376549576376320, 0, 0, 0, 0, 0, 0, 0, 8163045393748579638826762240, 0, 0, 0, 0, 0, 0, 25341445255559417901875200, 5429668990152024552565112832, 0, 212496057020518699078420267008, 0, 0, 212496134956859488996668997632, 0, 0, 0, 0, 0, 0, 5429746926492814470813843456, 0, 0, 0, 4402166558390484958982438912, 0, 0, 15779103088800282799771746304, 0, 4403445820492331138070609920, 0, 0, 0, 0, 95951603990528687865856000, 16829009870614279758020608000, 0, 0, 0] }

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
  { lower := 896, upper := 960, values := [0, 16829011888226912820002816000, 0, 0, 0, 0, 0, 0, 0, 95949586377895625883648000, 0, 775448224820118187797381120, 249788436186352342658596208640, 0, 2656605061961826122417037115392, 0, 0, 0, 0, 0, 0, 0, 249789189048706536948098924544, 0, 0, 0, 0, 0, 0, 775448224820118187797381120, 5429668990152024552565112832, 0, 212496057020518699078420267008, 0, 0, 212496134956859488996668997632, 0, 0, 0, 0, 0, 0, 5429746926492814470813843456, 0, 0, 0, 810926248177901372860006400, 261216665292917482518793420800, 0, 2778149084404524049586444042240, 0, 0, 0, 0, 0, 0, 0, 261217452599954548442456391680, 0, 0, 0, 0, 0, 0] }

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
  { lower := 960, upper := 1024, values := [810926248177901372860006400, 170667703663427150125222330368, 0, 6679267954455763433194669473792, 0, 0, 6679270404184529343327730925568, 0, 0, 0, 0, 0, 0, 170670153392193060258283782144, 0, 0, 0, 88895363404917534978161508352, 0, 0, 318636081728676678472810102784, 0, 88921196246070944917167800320, 0, 0, 0, 0, 5429668990152024552565112832, 0, 212496057020518699078420267008, 0, 0, 212496134956859488996668997632, 0, 0, 0, 0, 0, 0, 5429746926492814470813843456, 0, 0, 0, 90457422506281900608768180224, 0, 0, 324235118308573553014664593408, 0, 90483709279148868869386403840, 0, 0, 0, 0, 9913188175606332566536192000, 0, 9913195266073585898645094400, 0, 106383384518508896799686656, 17716386529130821816428789760, 778321996962501214569758720, 181226272125415055961047957504, 485187738366234523368161280, 25270194706574714758758400, 773267958021186271618007040] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent3
