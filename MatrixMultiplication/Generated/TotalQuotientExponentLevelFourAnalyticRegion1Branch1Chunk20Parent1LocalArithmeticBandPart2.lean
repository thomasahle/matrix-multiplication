import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk20Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 1, branch 1,
parent 83; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [0, 814250415620065565432243814400, 0, 0, 0, 0, 0, 0, 20875441014948345653546188800, 0, 0, 0, 8551532283637772641112162304, 0, 0, 31234628285346627651738009600, 0, 8551529402486932628601569280, 0, 0, 0, 0, 214547786522822146068054016, 37629666070693529538934079488, 0, 0, 0, 0, 37629670582075377065526296576, 0, 0, 0, 0, 0, 0, 0, 214543275140974619475836928, 0, 1635182334984394152232353792, 193268053742810158247750664192, 0, 1834075304614449995130718912512, 0, 0, 0, 0, 0, 0, 0, 193268186296501385906161188864, 0, 0, 0, 0, 0, 0, 1635182334984394152232353792, 13296395834507275702108160000, 0, 518631028206612314545192960000, 0, 0, 518630837974564054415441920000, 0] }

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
  { lower := 576, upper := 640, values := [0, 0, 0, 0, 0, 13296459245190029078691840000, 0, 0, 0, 5328636140578515209372565504, 629810580728318417786376290304, 0, 5976776866785550333782622470144, 0, 0, 0, 0, 0, 0, 0, 629811012686501019806091706368, 0, 0, 0, 0, 0, 0, 5328636140578515209372565504, 322171671070111290262080716800, 0, 12566429813446216381430025420800, 0, 0, 12566425204123687038486157721600, 0, 0, 0, 0, 0, 0, 322173207510954404576703283200, 0, 0, 0, 114485819960538343929991397376, 0, 0, 418161554187497708970206822400, 0, 114485781388396485803318968320, 0, 0, 0, 0, 20609413543486277338267648000, 0, 803878093720249087545049088000, 0, 0, 803877798860574284343934976000, 0, 0, 0, 0] }

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
  { lower := 640, upper := 704, values := [0, 0, 20609511830044545071972352000, 0, 0, 0, 200175663863929086109298982912, 0, 0, 731145278434542488092724428800, 0, 200175596421479831122571427840, 0, 0, 0, 0, 0, 0, 0, 0, 942258266885790220909805568, 28293900748856999828130889728, 21199391112922066362008862720, 154713457339288497995328258048, 13417336147419029343043584000, 805040168845141760582615040, 21199391112922066362008862720, 21065217751447876068578426880, 13417336147419029343043584000, 325102054851963080981946040320, 20796871028499495481717555200, 28293911872243676274990514176, 21199391112922066362008862720, 805040168845141760582615040, 20796871028499495481717555200, 805040168845141760582615040, 21199391112922066362008862720, 21199391112922066362008862720, 942258266885790220909805568, 27761453033246359755373412352, 17988404668605063237847744512, 480807655859008693422652391424, 188220136654428588513089814528, 16672179936755912269224738816, 480807484650165259305876455424, 16672179936755912269224738816, 16233438359472861946350403584, 613360725041704351378320654336, 16233438359472861946350403584, 188220136654428588513089814528, 613360725041704351378320654336, 27761510102860837794298724352, 16233438359472861946350403584, 16233438359472861946350403584, 17988404668605063237847744512, 7993086676936966122349002752, 37696986629628284716806307840, 1952165379034321887120326656, 57382109550312477496698732544, 52506517091267967998408785920, 7993084618972080399127150592, 52573833138820875649688797184, 52573833138820875649688797184, 37629670582075377065526296576] }

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
  { lower := 704, upper := 768, values := [1952165379034321887120326656, 21008305418521495609330892800, 0, 819437024566447456981404876800, 0, 0, 819436723999811205976398233600, 0, 0, 0, 0, 0, 0, 21008405607400245944333107200, 0, 0, 0, 114485819960538343929991397376, 0, 0, 418161554187497708970206822400, 0, 114485781388396485803318968320, 0, 0, 0, 0, 0, 0, 0, 0, 6457279479481583422880612352, 0, 0, 23585331562404596390087884800, 0, 6457277303918704229760368640, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11130386062901327792439296, 1952165144991256451930390528, 0, 0, 0, 0, 1952165379034321887120326656, 0, 0, 0, 0, 0, 0, 0, 11130152019835892602503168, 0, 141029711875110917558501376, 16668806499962647681041432576] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20.Parent1
