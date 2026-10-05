import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 1, branch 1,
parent 6; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [0, 837863628254393031587581132800, 0, 0, 0, 0, 0, 0, 20957171620409925035674828800, 0, 0, 0, 8226956398318095409820467200, 0, 0, 29968833142542347376210739200, 0, 8226961932341317522685952000, 0, 0, 0, 0, 121538581174316702933975040, 24105334843902851958177792000, 0, 0, 0, 0, 24105334843902851958177792000, 0, 0, 0, 0, 0, 0, 0, 121538581174316702933975040, 0, 935648454913571715725393920, 153334761697521570089952870400, 0, 1578640741146350443271972454400, 0, 0, 0, 0, 0, 0, 0, 153334761697521570089952870400, 0, 0, 0, 0, 0, 0, 935648454913571715725393920, 12574302972245955021404897280, 0, 502718299807951349858162442240, 0, 0, 502718176952635818952548679680, 0] }

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
  { lower := 576, upper := 640, values := [0, 0, 0, 0, 0, 12574302972245955021404897280, 0, 0, 0, 3437027615391373568398852096, 563262630944566577722839531520, 0, 5799006874438872134652232990720, 0, 0, 0, 0, 0, 0, 0, 563262630944566577722839531520, 0, 0, 0, 0, 0, 0, 3437027615391373568398852096, 321037672760154539140243783680, 0, 12835026591971757901066209853440, 0, 0, 12835023455321983252632258478080, 0, 0, 0, 0, 0, 0, 321037672760154539140243783680, 0, 0, 0, 110206936752469486427386675200, 0, 0, 401457493971973528393823027200, 0, 110207010885322232647647232000, 0, 0, 0, 0, 20564224652527238941255925760, 0, 822153886144253770080536494080, 0, 0, 822153685224623162245313986560, 0, 0, 0, 0] }

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
  { lower := 640, upper := 704, values := [0, 0, 20564224652527238941255925760, 0, 0, 0, 199332297734248853367108403200, 0, 0, 726119853016182291636106035200, 0, 199332431819019839143411712000, 0, 0, 0, 0, 0, 0, 0, 0, 877732900422428580940611584, 23696250175465766794702094336, 20643758062843434264871043072, 124563575873858175223631708160, 12868836195019283697581948928, 670251885157254359249059840, 20509707685811983393021231104, 21448060325032139495969914880, 12868836195019283697581948928, 328557474104086086903889133568, 21045909193937786880420478976, 23696250175465766794702094336, 20509707685811983393021231104, 670251885157254359249059840, 21045909193937786880420478976, 670251885157254359249059840, 20509707685811983393021231104, 21448060325032139495969914880, 877732900422428580940611584, 23283169109852989816202854400, 13421604723997685733287526400, 467092691821525355723206164480, 151472396170831024704244940800, 13421604723997685733287526400, 467092580483895655839993692160, 13421604723997685733287526400, 13421604723997685733287526400, 556421384414875485685720023040, 13805079144683333897095741440, 151472396170831024704244940800, 556421384414875485685720023040, 23283169109852989816202854400, 13421604723997685733287526400, 13805079144683333897095741440, 13421604723997685733287526400, 7615467584861706696995635200, 33747468781463992741448908800, 1751365645345436749057228800, 58159431198790605515993907200, 54359695222837209864968601600, 7682831837215643465154560000, 54359695222837209864968601600, 56649942605212011767581900800, 33747468781463992741448908800] }

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
  { lower := 704, upper := 768, values := [1684005428216766104862720000, 20040295362016990815364055040, 0, 801207290318922463836446392320, 0, 0, 801207094518263336455624458240, 0, 0, 0, 0, 0, 0, 20040295362016990815364055040, 0, 0, 0, 110206936752469486427386675200, 0, 0, 401457493971973528393823027200, 0, 110207010885322232647647232000, 0, 0, 0, 0, 0, 0, 0, 0, 6513007148668492199441203200, 0, 0, 23725326237846025006166835200, 0, 6513011529770209705459712000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6064799459796242661376000, 1202861020154832932044800000, 0, 0, 0, 0, 1202861020154832932044800000, 0, 0, 0, 0, 0, 0, 0, 6064799459796242661376000, 0, 82905559296139265950351360, 13586624454210772033286963200] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent1
