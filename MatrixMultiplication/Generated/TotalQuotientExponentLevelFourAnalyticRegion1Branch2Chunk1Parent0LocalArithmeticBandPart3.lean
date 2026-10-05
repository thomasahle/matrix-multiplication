import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1Parent0LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 2,
parent 5; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 0, 0, 0, 0, 2162068952164307172310646784, 0, 119067714745541107940065280, 12484035144451772582377553920, 0, 134565421078743136295976960000, 0, 0, 0, 0, 0, 0, 0, 12484044667583400634933575680, 0, 0, 0, 0, 0, 0, 119067714745541107940065280, 1221465576124093068874874880, 102272255989445081319371440128, 0, 0, 0, 0, 102272293001684143712979910656, 0, 0, 0, 0, 0, 0, 0, 1221428563885030675266404352, 0, 1343764209271106789609308160, 140891253773098576286832394240, 0, 1518666895031529681054597120000, 0, 0, 0, 0, 0, 0, 0, 140891361248441235737107496960, 0, 0, 0, 0, 0, 0, 1343764209271106789609308160, 6287654919674257631896141824, 0, 220052245750033102659253174272] }

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
  { lower := 832, upper := 896, values := [0, 0, 220052353677320991915412291584, 0, 0, 0, 0, 0, 0, 6287600956030313003816583168, 0, 0, 0, 102058041210463806805770240, 10700601552387233642037903360, 0, 115341789496065545396551680000, 0, 0, 0, 0, 0, 0, 0, 10700609715071486258514493440, 0, 0, 0, 0, 0, 0, 102058041210463806805770240, 4199561340402013461700149248, 0, 146974176529452097067332665344, 0, 0, 146974248614716251105832992768, 0, 0, 0, 0, 0, 0, 4199525297769936442449985536, 0, 0, 0, 3490872086451756456612986880, 0, 0, 11935528179983435918072610816, 0, 3490870958894524951116644352, 0, 0, 0, 0, 205324816855572478049648640, 7177804439977772077321027584, 121085811605635025023795200, 107247433136419593592504320, 5019871789707897751700766720, 1366539873835023853839974400] }

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
  { lower := 896, upper := 960, values := [7177806992545983276880232448, 5019871789707897751700766720, 121085811605635025023795200, 121085811605635025023795200, 103787838519115735734681600, 121085811605635025023795200, 1366539873835023853839974400, 103787838519115735734681600, 205322264287361278490443776, 107247433136419593592504320, 205358715053650928564436992, 14785128486001367799027466240, 2200420507856800425921478656, 134637330245666561146497269760, 2257947841395540306337726464, 71909166923424850520309760, 2200420507856800425921478656, 1251219504467592399053389824, 2257947841395540306337726464, 35249873625862861725055844352, 1380656004929757129989947392, 14785138009132995851583488000, 2200420507856800425921478656, 71909166923424850520309760, 1380656004929757129989947392, 71909166923424850520309760, 2214802341241485396025540608, 1251219504467592399053389824, 205358715053650928564436992, 520375052566631091965788160, 311178001263883928670830592, 7334633347736000466023088128, 7700000329146744873280339968, 244969915888589475762143232, 7334636824947258360273567744, 251590724426118921053011968, 251590724426118921053011968, 4257179889631433322028597248, 231728298813530585180405760, 7700000329146744873280339968, 4257179889631433322028597248, 520373313961002144840548352, 244969915888589475762143232, 231728298813530585180405760, 311178001263883928670830592, 105459975917479267032629248, 11057288270800141430105833472, 0, 119186515812601063576436736000, 0, 0, 0, 0, 0, 0, 0, 11057296705573869133798309888, 0, 0, 0, 0, 0, 0, 105459975917479267032629248] }

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
  { lower := 960, upper := 1024, values := [3903488370206695258463404032, 0, 136612360744444342543105130496, 0, 0, 136612427747630504274623987712, 0, 0, 0, 0, 0, 0, 3903454868613614392703975424, 0, 0, 0, 3819256781700796941284147200, 0, 0, 13058297702026867517727703040, 0, 3819255548074787011957882880, 0, 0, 0, 0, 186993454860200970465312768, 0, 6544304706320687067933179904, 0, 0, 6544307916054155893395161088, 0, 0, 0, 0, 0, 0, 186991849993466557734322176, 0, 0, 0, 3490872086451756456612986880, 0, 0, 11935528179983435918072610816, 0, 3490870958894524951116644352, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent0
