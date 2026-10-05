import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk14Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 2,
parent 60; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 0, 0, 0, 0, 2834103793534947872988987392, 0, 88270326723846818657992704, 14092109892174444161535049728, 0, 140618064996580089808759554048, 0, 0, 0, 0, 0, 0, 0, 14092109892174444161535049728, 0, 0, 0, 0, 0, 0, 88260254801582573242810368, 2834046299645356138743988224, 238312804790523954598246350848, 0, 0, 0, 0, 238312747296634362864001351680, 0, 0, 0, 0, 0, 0, 0, 2834103793534947872988987392, 0, 2824650455163098197055766528, 450947516549582213169121591296, 0, 4499778079890562873880305729536, 0, 0, 0, 0, 0, 0, 0, 450947516549582213169121591296, 0, 0, 0, 0, 0, 0, 2824328153650642343769931776, 4590828137329291924311375872, 0, 169533175513404977366968565760] }

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
  { lower := 832, upper := 896, values := [0, 0, 169533133999007439483622653952, 0, 0, 0, 0, 0, 0, 4590869651726829807657287680, 0, 0, 0, 88270326723846818657992704, 14092109892174444161535049728, 0, 140618064996580089808759554048, 0, 0, 0, 0, 0, 0, 0, 14092109892174444161535049728, 0, 0, 0, 0, 0, 0, 88260254801582573242810368, 4612247242169086443398365184, 0, 170324154559346213653284126720, 0, 0, 170324112851257862995987922944, 0, 0, 0, 0, 0, 0, 4612288950257437100694568960, 0, 0, 0, 3551282166473871223498473472, 0, 0, 12704477476209962668800344064, 0, 3551280985882250506087170048, 0, 0, 0, 0, 195723490632312971845435392, 7936027619761144881934761984, 90927460303828200456192000, 106839765856998135536025600, 1261618511715616281329664000, 2836936761479439854233190400] }

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
  { lower := 896, upper := 960, values := [7936025724358191308278333440, 1261618511715616281329664000, 90927460303828200456192000, 88654273796232495444787200, 88654273796232495444787200, 88654273796232495444787200, 2836936761479439854233190400, 88654273796232495444787200, 195725386035266545501863936, 106839765856998135536025600, 181415334696379902297374720, 17596818088145894983304478720, 2896164460546662059988746240, 162347091406841202374722191360, 1527647187980656910763294720, 111390940790256233076490240, 2896164460546662059988746240, 2896164460546662059988746240, 1527647187980656910763294720, 35740579002130785641399582720, 2864338477463731707681177600, 17596818088145894983304478720, 2896164460546662059988746240, 111390940790256233076490240, 2864338477463731707681177600, 111390940790256233076490240, 2896164460546662059988746240, 2896164460546662059988746240, 197316704789078641433640960, 433196623212152279873355776, 251590724426118921053011968, 8365453588981128872029323264, 1979621752721304141969752064, 238349107351060030471274496, 8365451587509396874542972928, 238349107351060030471274496, 238349107351060030471274496, 10209286764870404638519590912, 238349107351060030471274496, 1979621752721304141969752064, 10209286764870404638519590912, 433198624683884277359706112, 238349107351060030471274496, 238349107351060030471274496, 251590724426118921053011968, 106377060410789755818606592, 16982799100825612194670444544, 0, 169462796277929851820812795904, 0, 0, 0, 0, 0, 0, 0, 16982799100825612194670444544, 0, 0, 0, 0, 0, 0, 106364922453189254933643264] }

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
  { lower := 960, upper := 1024, values := [5297658597042511054182023168, 0, 195635484029465774815382077440, 0, 0, 195635436123271415391676530688, 0, 0, 0, 0, 0, 0, 5297706503236870477887569920, 0, 0, 0, 3551282166473871223498473472, 0, 0, 12704477476209962668800344064, 0, 3551280985882250506087170048, 0, 0, 0, 0, 221330750011210030565556224, 0, 8173450141392774958594129920, 0, 0, 8173448139921042961107779584, 0, 0, 0, 0, 0, 0, 221332751482942028051906560, 0, 0, 0, 3551282166473871223498473472, 0, 0, 12704477476209962668800344064, 0, 3551280985882250506087170048, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent2
