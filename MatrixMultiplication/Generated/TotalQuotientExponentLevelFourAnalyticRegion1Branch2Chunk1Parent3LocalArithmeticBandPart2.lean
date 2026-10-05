import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 1, branch 2,
parent 8; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [0, 0, 69678375436717756152067129344, 0, 0, 0, 70609848276266509432227102720, 0, 0, 241419855272425694612793851904, 0, 70609825469173305299580223488, 0, 0, 0, 0, 38524144395042179531682086912, 0, 1348249005078472698252687835136, 0, 0, 1348249666343519194537412001792, 0, 0, 0, 0, 0, 0, 38523813762518931389320003584, 0, 0, 0, 1102323172771523659989736488960, 0, 0, 3768917613202008773859603382272, 0, 1102322816719387078275612278784, 0, 0, 0, 0, 42109153154146069568437616640, 0, 42090112330373623191498129408, 0, 43175448627526018506329948160, 0, 0, 147619784115623354667695603712, 0, 43175434681787498781908926464, 0, 0, 0, 0, 11463208474078358014840012800, 0, 11458025065815011137589084160, 0, 0, 5829012005677838492063760384, 2891657013620230690940387328, 102923303910131144423620214784] }

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
  { lower := 576, upper := 640, values := [71553129932772942416248307712, 2276410840509543309889241088, 102923353273618285670380339200, 2337935457820612047994355712, 2337935457820612047994355712, 39560328931017198601588703232, 2153361605887405833679011840, 71553129932772942416248307712, 39560328931017198601588703232, 5828987323934267868683698176, 2276410840509543309889241088, 2153361605887405833679011840, 2891657013620230690940387328, 73224110753717775758908194816, 31013631547071595766203023360, 1265029707841078248358281216, 272027293651676564581779505152, 25545438616403709144267227136, 73224087510820242884873158656, 25586246026334066507117494272, 22933764380860837921850130432, 31013631547071595766203023360, 1265029707841078248358281216, 10840944761764112430991933440, 9729295792516069367331422208, 10840472349871756766229823488, 9824868442737248830664736768, 68810871250119591994463354880, 0, 0, 235269030934274721501639868416, 0, 68810849024098826183667351552, 0, 0, 0, 0, 42109153154146069568437616640, 0, 42090112330373623191498129408, 0, 0, 1015727333146183621568102400, 0, 1015268043806393391938273280, 0, 0, 12959064837317367559094272, 1358734575649169921496055808, 0, 14645800671887418829307904000, 0, 0, 0, 0, 0, 0, 0, 1358735612125602563051487232, 0, 0, 0, 0, 0] }

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
  { lower := 640, upper := 704, values := [0, 12959064837317367559094272, 2216785913867123861076574208, 0, 77581980074499984191834292224, 0, 0, 77582018125521322236211888128, 0, 0, 0, 0, 0, 0, 2216766888356454838887776256, 0, 0, 0, 2248721282683646797204684800, 0, 0, 7688530422688716388942479360, 0, 2248720556343098894891089920, 0, 0, 0, 0, 2096959648252684733450813440, 0, 73388359529932417478762168320, 0, 0, 73388395524141791304524759040, 0, 0, 0, 0, 0, 0, 2096941651147997820569518080, 0, 0, 0, 43175448627526018506329948160, 0, 0, 147619784115623354667695603712, 0, 43175434681787498781908926464, 0, 0, 0, 0, 1015727333146183621568102400, 0, 1015268043806393391938273280, 0, 2248721282683646797204684800, 0, 0, 7688530422688716388942479360, 0, 2248720556343098894891089920] }

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
  { lower := 704, upper := 768, values := [0, 0, 0, 0, 870623428411014532772659200, 0, 870229751834051478804234240, 0, 0, 2815917241939319499205378048, 0, 98550082797337817757194911744, 0, 0, 98550131132418976894647533568, 0, 0, 0, 0, 0, 0, 2815893074398739930479067136, 0, 0, 0, 69260615506656321353904291840, 0, 0, 236806737018812464779428364288, 0, 69260593135367445962645569536, 0, 0, 0, 0, 1015727333146183621568102400, 0, 1015268043806393391938273280, 0, 39127750318695454271361515520, 0, 0, 133780429354783665167599140864, 0, 39127737680369920771104964608, 0, 0, 0, 0, 11463208474078358014840012800, 0, 11458025065815011137589084160, 0, 0, 870623428411014532772659200, 0, 870229751834051478804234240, 0, 0, 2710530875448223360924778496, 295795339779479846843842560, 12065336227847204279156736, 9474159706488997380467195904, 243641950923624189637165056] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent3
