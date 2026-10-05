import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk14Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 1, for region 1, branch 2,
parent 60; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band4

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 256, upper := 320, values := [238349107351060030471274496, 238349107351060030471274496, 10209286764870404638519590912, 238349107351060030471274496, 1979621752721304141969752064, 10209286764870404638519590912, 433198624683884277359706112, 238349107351060030471274496, 238349107351060030471274496, 251590724426118921053011968, 0, 0, 0, 0, 0, 238349107351060030471274496, 0, 2308666873689985557580480512, 0, 0, 0, 0, 238349107351060030471274496, 0, 0, 0, 0, 0, 0, 10209286764870404638519590912, 0, 98887897756387714716363915264, 0, 0, 0, 0, 10209286764870404638519590912, 0, 0, 2834046299645356138743988224, 238312804790523954598246350848, 0, 0, 0, 0, 238312747296634362864001351680, 0, 0, 0, 0, 0, 0, 0, 2834103793534947872988987392, 0, 238349107351060030471274496, 0, 2308666873689985557580480512, 0, 0, 0, 0, 238349107351060030471274496, 0] }

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
  { lower := 320, upper := 384, values := [0, 2834046299645356138743988224, 238312804790523954598246350848, 0, 0, 0, 0, 238312747296634362864001351680, 0, 0, 0, 0, 0, 0, 0, 2834103793534947872988987392, 0, 106377060410789755818606592, 16982799100825612194670444544, 0, 169462796277929851820812795904, 0, 0, 0, 0, 0, 0, 0, 16982799100825612194670444544, 0, 0, 0, 0, 0, 0, 106364922453189254933643264, 0, 0, 0, 0, 1979621752721304141969752064, 0, 19174760978702935603237879808, 0, 0, 0, 0, 1979621752721304141969752064, 0, 0, 1494881564648099941315510272, 125703457471924723304569503744, 0, 0, 0, 0, 125703427145477466126066647040, 0, 0, 0, 0, 0, 0, 0] }

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
  { lower := 384, upper := 448, values := [1494911891095357119818366976, 0, 10209286764870404638519590912, 0, 98887897756387714716363915264, 0, 0, 0, 0, 10209286764870404638519590912, 0, 0, 34973999939579504877027459072, 2940937140436905505646490681344, 0, 0, 0, 0, 2940936430924399884574434263040, 0, 0, 0, 0, 0, 0, 0, 34974709452085125949083877376, 0, 1256154649531666265517588480, 200541563850174782298768015360, 0, 2001103232643639739586193653760, 0, 0, 0, 0, 0, 0, 0, 200541563850174782298768015360, 0, 0, 0, 0, 0, 0, 1256011318330213542301532160, 2802902933715187389966581760, 235693982759858856196067819520, 0, 0, 0, 0, 235693925897770248986374963200, 0, 0, 0, 0, 0, 0, 0, 2802959795803794599659438080, 0, 2824650455163098197055766528] }

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
  { lower := 448, upper := 512, values := [450947516549582213169121591296, 0, 4499778079890562873880305729536, 0, 0, 0, 0, 0, 0, 0, 450947516549582213169121591296, 0, 0, 0, 0, 0, 0, 2824328153650642343769931776, 5297658597042511054182023168, 0, 195635484029465774815382077440, 0, 0, 195635436123271415391676530688, 0, 0, 0, 0, 0, 0, 5297706503236870477887569920, 0, 0, 0, 425293883559493490643566592, 5108502699549839389391585280, 5873198195039712791226220544, 4433794795835709658717224960, 213428010358551241335767040, 4426910021308014457383813120, 4447564344891100061384048640, 425293883559493490643566592, 5108502699549839389391585280, 213428010358551241335767040, 17640738019509652368012607488, 122693749349389461162112843776, 14517970355948946594988032000, 17058615168240012249110937600, 201436838688791634005458944000, 452960675105607133763626598400, 122693722813748111130922844160, 201436838688791634005458944000, 14517970355948946594988032000, 14155021097050222930113331200, 14155021097050222930113331200, 14155021097050222930113331200, 452960675105607133763626598400, 14155021097050222930113331200, 17640764555151002399202607104, 17058615168240012249110937600, 6769636592014972847663349760, 125045815107710098104406507520, 243531274609699348912118169600, 134224202914466725799835729920] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent2
