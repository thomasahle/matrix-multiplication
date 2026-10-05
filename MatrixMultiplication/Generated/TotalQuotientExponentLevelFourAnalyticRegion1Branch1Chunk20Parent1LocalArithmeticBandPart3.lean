import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk20Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 1,
parent 83; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 158183650980733449463488577536, 0, 0, 0, 0, 0, 0, 0, 16668817932332287362536046592, 0, 0, 0, 0, 0, 0, 141029711875110917558501376, 797783750070436542126489600, 0, 31117861692396738872711577600, 0, 0, 31117850278473843264926515200, 0, 0, 0, 0, 0, 0, 797787554711401744721510400, 0, 0, 0, 141029711875110917558501376, 16668806499962647681041432576, 0, 158183650980733449463488577536, 0, 0, 0, 0, 0, 0, 0, 16668817932332287362536046592, 0, 0, 0, 0, 0, 0, 141029711875110917558501376, 20609413543486277338267648000, 0, 803878093720249087545049088000, 0, 0, 803877798860574284343934976000, 0, 0, 0, 0, 0, 0] }

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
  { lower := 832, upper := 896, values := [20609511830044545071972352000, 0, 0, 0, 6631800546494599191066574848, 0, 0, 24222772955983098995225395200, 0, 6631798312132723262997135360, 0, 0, 0, 0, 797783750070436542126489600, 0, 31117861692396738872711577600, 0, 0, 31117850278473843264926515200, 0, 0, 0, 0, 0, 0, 797787554711401744721510400, 0, 0, 0, 6631800546494599191066574848, 0, 0, 24222772955983098995225395200, 0, 6631798312132723262997135360, 0, 0, 0, 0, 0, 0, 0, 0, 156276167212960746483744768, 18470839635093744727640506368, 0, 175284586221893822378460315648, 0, 0, 0, 0, 0, 0, 0, 18470852303395237347675078656, 0, 0, 0, 0, 0, 0, 156276167212960746483744768, 21008305418521495609330892800] }

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
  { lower := 896, upper := 960, values := [0, 819437024566447456981404876800, 0, 0, 819436723999811205976398233600, 0, 0, 0, 0, 0, 0, 21008405607400245944333107200, 0, 0, 0, 6457279479481583422880612352, 0, 0, 23585331562404596390087884800, 0, 6457277303918704229760368640, 0, 0, 0, 0, 21008305418521495609330892800, 0, 819437024566447456981404876800, 0, 0, 819436723999811205976398233600, 0, 0, 0, 0, 0, 0, 21008405607400245944333107200, 0, 0, 0, 200175663863929086109298982912, 0, 0, 731145278434542488092724428800, 0, 200175596421479831122571427840, 0, 0, 0, 0, 0, 0, 0, 0, 6457279479481583422880612352, 0, 0, 23585331562404596390087884800, 0, 6457277303918704229760368640, 0, 0, 0] }

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
  { lower := 960, upper := 1024, values := [0, 0, 0, 0, 0, 0, 931417793311515826251104256, 152194327024562518030811136, 31236647508611031569711235072, 1592472348622861469151657984, 141058156754472577687093248, 31236636094688135961926172672, 141058156754472577687093248, 137346099997775930905853952, 5189455345861912200172535808, 137346099997775930905853952, 1592472348622861469151657984, 5189455345861912200172535808, 931421597952481028846125056, 137346099997775930905853952, 137346099997775930905853952, 152194327024562518030811136, 8387757570299081183025168384, 214927073486486201979371520, 11130152019835892602503168, 30797145829779659530942021632, 299362709499034352756981760, 8387754747947237905463771136, 299746507844545935260516352, 299746507844545935260516352, 214543275140974619475836928, 11130152019835892602503168, 0, 0, 0, 0, 8551532283637772641112162304, 0, 0, 31234628285346627651738009600, 0, 8551529402486932628601569280, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20.Parent1
