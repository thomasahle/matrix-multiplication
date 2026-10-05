import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk22Parent0LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 1, for region 1, branch 2,
parent 90; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band4

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 256, upper := 320, values := [9284550294640352061743431680, 0, 9284550294640352061743431680, 0, 39825520494036174291569999872, 676998458984192337835458560, 0, 676998458984192337835458560, 0, 773712524553362671811952640, 43730995199268433053089792, 6981530633394115651456466944, 0, 69665176889331344859467874304, 0, 0, 0, 0, 0, 0, 0, 6981530633394115651456466944, 0, 0, 0, 0, 0, 0, 43726005354996494619377664, 5583501650916435529140535296, 0, 206191287725895844779188551680, 0, 0, 206191237234851472026932084736, 0, 0, 0, 0, 0, 0, 5583552141960808281397002240, 0, 0, 0, 6117638419589754724854792192, 0, 0, 21885447527377318503675592704, 0, 6117636385836220598376726528, 0, 0, 0, 0, 5583501650916435529140535296, 0, 206191287725895844779188551680, 0, 0, 206191237234851472026932084736, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band4

namespace Band5

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 320, upper := 384, values := [0, 0, 0, 5583552141960808281397002240, 0, 0, 0, 262038845639094494047946932224, 0, 0, 937426669089328475907437887488, 0, 262038758526651448963803119616, 0, 0, 0, 0, 17601959933589000783721922560, 0, 17601959933589000783721922560, 0, 6117638419589754724854792192, 0, 0, 21885447527377318503675592704, 0, 6117636385836220598376726528, 0, 0, 0, 0, 17601959933589000783721922560, 0, 17601959933589000783721922560, 0, 909112216350201139379044352, 3676436352144730669002522624, 0, 135765903385485056858306641920, 0, 0, 135765870139840550015267241984, 0, 0, 0, 0, 0, 0, 3676469597789237512041922560, 0, 0, 0, 50810385762703796186988412928, 0, 0, 181770800296828284238861172736, 0, 50810368871250832192073367552, 0, 0, 0, 0, 9284550294640352061743431680, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band5

namespace Band6

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 384, upper := 448, values := [9284550294640352061743431680, 0, 262038845639094494047946932224, 0, 0, 937426669089328475907437887488, 0, 262038758526651448963803119616, 0, 0, 0, 0, 217219791268356570111205703680, 0, 217219791268356570111205703680, 0, 10735261278177907071390842880, 17408531802450660115768934400, 0, 17408531802450660115768934400, 0, 24139830766064915360532922368, 5652093802719188241354850304, 3812635138448098160636067840, 214192985306072930372812800, 22845120069459326734170062848, 5790350369440838217745039360, 5652091994938269017818791936, 5790350369440838217745039360, 5790350369440838217745039360, 3812635138448098160636067840, 214192985306072930372812800, 14357030113964389125473697792, 6981530633394115651456466944, 14357030113964389125473697792, 6981530633394115651456466944, 39825511049303208552279572480, 17601959933589000783721922560, 0, 17601959933589000783721922560, 0, 10735261278177907071390842880, 773712524553362671811952640, 206541368098018576910254080, 0, 7627297943004778475185766400, 0, 0, 7627296075271941012093665280, 0, 0, 0, 0, 0, 0, 206543235830856040002355200, 0, 0, 0, 6117638419589754724854792192, 0, 0, 21885447527377318503675592704, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band6

namespace Band7

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 448, upper := 512, values := [6117636385836220598376726528, 0, 0, 0, 0, 676998458984192337835458560, 0, 676998458984192337835458560, 0, 6117638419589754724854792192, 0, 0, 21885447527377318503675592704, 0, 6117636385836220598376726528, 0, 0, 0, 0, 17408531802450660115768934400, 0, 17408531802450660115768934400, 0, 754369711439528605016653824, 676998458984192337835458560, 0, 676998458984192337835458560, 0, 754369711439528605016653824, 6457507220678074431791169536, 0, 0, 23101305723342725087213125632, 0, 6457505073938232853842100224, 0, 0, 0, 0, 17601959933589000783721922560, 0, 17601959933589000783721922560, 0, 754369711439528605016653824, 17601959933589000783721922560, 0, 17601959933589000783721922560, 0, 24139830766064915360532922368, 754369711439528605016653824, 619322583038798911254822912, 43726005354996494619377664, 619322583038798911254822912, 43726005354996494619377664, 1335995256935685588116307968, 909112216350201139379044352, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22.Parent0
