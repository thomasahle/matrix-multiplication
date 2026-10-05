import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk10Parent0LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 1, for region 1, branch 2,
parent 42; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band4

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 256, upper := 320, values := [1061852437872136944170827776, 46893099174895576972001280, 1325303819218468711352500224, 1029154772344747520711196672, 390017797285306421140724383744, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 980391616042635564234571776, 20657331048005661236983234560, 31061025530688324778630053888, 1020881186266759902296801280, 21779705334722255554212790272, 1132092916938340047079342080, 31061025530688324778630053888, 26393362941156241535089508352, 21779705334722255554212790272, 423121562345083187453069623296, 26807438923840183506007228416, 20657331048005661236983234560, 31061025530688324778630053888, 1132092916938340047079342080, 26807438923840183506007228416, 1132092916938340047079342080, 31131747691135780585350365184, 26393362941156241535089508352, 1091603346714215709017112576, 1357399532184360963574260039680, 0, 50203742569321304427428707303424, 0, 0, 50201591821323778823219526500352, 0, 0, 0, 0, 0, 0, 1359550298986036307921115021312, 0, 0, 0, 48649819506523084991496192, 1122600960307772060199813120, 1433597127403635415392976896, 47034770169381666328412160, 1149631786055717909403009024, 50576545031533900238684160, 1433597127403635415392976896, 1093246730250254345551478784] }

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
  { lower := 320, upper := 384, values := [1149631786055717909403009024, 20594202452862659819766546432, 1132574598319592750891139072, 1122600960307772060199813120, 1433597127403635415392976896, 50576545031533900238684160, 1132574598319592750891139072, 50576545031533900238684160, 1438753951602929067966332928, 1093246730250254345551478784, 52191594368675318901768192, 5101059276907086940355952640, 0, 183539714870531226544981934080, 0, 0, 183539734366433869446764298240, 0, 0, 0, 0, 0, 0, 5101061271461289910201221120, 0, 0, 0, 130949194497484367246099742720, 0, 0, 450193023688787133987471491072, 0, 130949194497484367246099742720, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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
  { lower := 384, upper := 448, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1346356128999101589715156992, 30556166774737696748124241920, 40238699227088371029897117696, 1320657010599324980462223360, 31454474216575092139254349824, 1429035321381183338116546560, 40238699227088371029897117696, 31389588901100463214018166784, 31454474216575092139254349824, 572041464940241175181296402432, 32379529142171461200874831872, 30556166774737696748124241920, 40238699227088371029897117696, 1429035321381183338116546560, 32379529142171461200874831872, 1429035321381183338116546560, 40372776656270005996804374528, 31389588901100463214018166784, 1454734439780959947369480192, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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
  { lower := 448, upper := 512, values := [1112598988097054151637204992, 26629046807583299788414648320, 31729939298253844283859664896, 1040148441516868054768680960, 26966337111255781328157671424, 1101775324118316924807413760, 31729939298253844283859664896, 22880828972265936467980713984, 26966337111255781328157671424, 467037757247041465996680364032, 23964272069697753430068559872, 26629046807583299788414648320, 31729939298253844283859664896, 1101775324118316924807413760, 23964272069697753430068559872, 1101775324118316924807413760, 31864016727435479250766921728, 22880828972265936467980713984, 1174225870698503021675937792, 5242450423909284581407195136, 0, 187914868705194309486865547264, 0, 0, 187914898406758111168457342976, 0, 0, 0, 0, 0, 0, 5242445973632276798977867776, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 980391616042635564234571776, 20657331048005661236983234560, 31061025530688324778630053888] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent0
