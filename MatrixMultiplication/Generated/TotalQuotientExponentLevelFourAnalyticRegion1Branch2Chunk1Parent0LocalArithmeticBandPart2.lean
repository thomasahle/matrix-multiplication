import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1Parent0LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 1, branch 2,
parent 5; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [189061816667537214365962862592, 6021076963934306189998817280, 184244955096389769413963808768, 104766739172456927705979420672, 189061816667537214365962862592, 2951531927720596894337420230656, 115604677707538678847977291776, 205515194503983581590179545088, 184244955096389769413963808768, 6021076963934306189998817280, 115604677707538678847977291776, 6021076963934306189998817280, 185449170489176630651963572224, 104766739172456927705979420672, 7347762006173723996165505024, 2148094633873405052159262720, 179858105360748246458204946432, 0, 0, 0, 0, 179858170451237632046964670464, 0, 0, 0, 0, 0, 0, 0, 2148029543384019463399538688, 0, 4936207259879432789172420608, 517552428417129200486566592512, 0, 5578697885293036879013216256000, 0, 0, 0, 0, 0, 0, 0, 517552823218957552036817666048, 0, 0, 0, 0, 0, 0, 4936207259879432789172420608, 9630784812312856416829308928, 3014092862873036700174516224, 231696140593057672273005117440, 74582765947262588985169412096, 2372796509070262934179938304, 231696253067467975698568708096, 2436926144450540310779396096, 2436926144450540310779396096, 41235355549518353153451360256, 2244537238309708180981022720, 74582765947262588985169412096, 41235355549518353153451360256, 9630728575107704704047513600, 2372796509070262934179938304] }

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
  { lower := 576, upper := 640, values := [2244537238309708180981022720, 3014092862873036700174516224, 119067714745541107940065280, 12484035144451772582377553920, 0, 134565421078743136295976960000, 0, 0, 0, 0, 0, 0, 0, 12484044667583400634933575680, 0, 0, 0, 0, 0, 0, 119067714745541107940065280, 6287654919674257631896141824, 0, 220052245750033102659253174272, 0, 0, 220052353677320991915412291584, 0, 0, 0, 0, 0, 0, 6287600956030313003816583168, 0, 0, 0, 3819256781700796941284147200, 0, 0, 13058297702026867517727703040, 0, 3819255548074787011957882880, 0, 0, 0, 0, 0, 0, 0, 0, 183727436916442106821607424, 0, 1779597381802697200634953728, 0, 0, 0, 0, 183727436916442106821607424, 0, 0, 70199171041614544188211200, 5877715861462360995366174720, 0] }

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
  { lower := 640, upper := 704, values := [0, 0, 0, 5877717988602536994998845440, 0, 0, 0, 0, 0, 0, 0, 70197043901438544555540480, 0, 173796224110147938885304320, 0, 1683402928732281135735767040, 0, 0, 0, 0, 173796224110147938885304320, 0, 0, 1347824083998999248413655040, 112852144540077331111030554624, 0, 0, 0, 0, 112852185381168710303977832448, 0, 0, 0, 0, 0, 0, 0, 1347783242907620055466377216, 0, 119067714745541107940065280, 12484035144451772582377553920, 0, 134565421078743136295976960000, 0, 0, 0, 0, 0, 0, 0, 12484044667583400634933575680, 0, 0, 0, 0, 0, 0, 119067714745541107940065280, 70199171041614544188211200, 5877715861462360995366174720, 0, 0, 0, 0] }

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
  { lower := 704, upper := 768, values := [5877717988602536994998845440, 0, 0, 0, 0, 0, 0, 0, 70197043901438544555540480, 0, 102058041210463806805770240, 10700601552387233642037903360, 0, 115341789496065545396551680000, 0, 0, 0, 0, 0, 0, 0, 10700609715071486258514493440, 0, 0, 0, 0, 0, 0, 102058041210463806805770240, 194784848812709344234700800, 0, 6816984069084049029097062400, 0, 0, 6816987412556412388953292800, 0, 0, 0, 0, 0, 0, 194783177076527664306585600, 0, 0, 0, 233383500947912946503122944, 0, 2260569647154777525130887168, 0, 0, 0, 0, 233383500947912946503122944, 0, 0, 2162134468081727960996904960, 181033648533040718657278181376, 0, 0, 0, 0, 181033714048958139445964439552, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent0
