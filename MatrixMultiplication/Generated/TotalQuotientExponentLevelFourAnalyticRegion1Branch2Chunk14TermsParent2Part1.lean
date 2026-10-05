import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 14, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-447441237436494727172341733785600)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    10129917, 733965645, 3389374345, 13201860035, 7276308725, 435226155,
    1015527695, 13201860035, 13201860035, 435226155, 162919657355, 6528392325,
    3389374345, 13201860035, 1015527695, 6528392325, 1015527695, 13201860035,
    13201860035, 439520025, 47271987, 3975065549, 1987532295, 23636473,
    76685, 12242545, 488648755, 12242545, 306705, 5870909,
    27277521, 1813968591, 429262041, 12920931, 1813968157, 12920931,
    12920931, 1106893089, 12920931, 429262041, 1106893089, 46967489,
    12920931, 12920931, 27277521, 12920931, 62576541, 12920931,
    1106893089, 5360723679, 1106893089, 614535831, 51675852137, 25837919835,
    307274149, 12920931, 62576541, 12920931, 614535831, 51675852137,
    25837919835, 307274149, 720839, 115079923
  ]
def negativeCoefficients : Array ℕ := #[
    1494911891095357119818366976, 6769638206105079297249116160, 125045842224423886457447383040, 243531333362579223677040066560, 134224204851374853539338649600, 128456087927514315785691463680,
    9366589744714585526040002560, 243531333362579223677040066560, 243531333362579223677040066560, 128456087927514315785691463680, 3005337223804137013069406535680, 240855164864089342098171494400,
    125045842224423886457447383040, 243531333362579223677040066560, 9366589744714585526040002560, 240855164864089342098171494400, 9366589744714585526040002560, 243531333362579223677040066560,
    243531333362579223677040066560, 8107713416445423969003110400, 109001780755590620720922624, 9165877107327844407624859648, 9165874896024398571692359680, 109003992059036456653422592,
    90533668434714685803069440, 14453446043255840165676974080, 144223656406748810060266209280, 14453446043255840165676974080, 90523338258033408454164480, 433196623212152279873355776,
    251590724426118921053011968, 8365453588981128872029323264, 1979621752721304141969752064, 238349107351060030471274496, 8365451587509396874542972928, 238349107351060030471274496,
    238349107351060030471274496, 10209286764870404638519590912, 238349107351060030471274496, 1979621752721304141969752064, 10209286764870404638519590912, 433198624683884277359706112,
    238349107351060030471274496, 238349107351060030471274496, 251590724426118921053011968, 238349107351060030471274496, 2308666873689985557580480512, 238349107351060030471274496,
    10209286764870404638519590912, 98887897756387714716363915264, 10209286764870404638519590912, 2834046299645356138743988224, 238312804790523954598246350848, 238312747296634362864001351680,
    2834103793534947872988987392, 238349107351060030471274496, 2308666873689985557580480512, 238349107351060030471274496, 2834046299645356138743988224, 238312804790523954598246350848,
    238312747296634362864001351680, 2834103793534947872988987392, 106377060410789755818606592, 16982799100825612194670444544
  ]
def negativeScales : Array ℕ := #[
    23, 29, 31, 33, 32, 28,
    29, 33, 33, 28, 37, 32,
    31, 33, 29, 32, 29, 33,
    33, 28, 25, 31, 30, 24,
    16, 23, 28, 23, 18, 22,
    24, 30, 28, 23, 30, 23,
    23, 30, 23, 28, 30, 25,
    23, 23, 24, 23, 25, 23,
    30, 32, 30, 29, 35, 34,
    28, 23, 25, 23, 29, 35,
    34, 28, 19, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23272119017602419, 29451137294990206, 31658371840450832, 33620022156817283, 32760559610366941, 28697190017397742,
    29919582444845343, 33620022156817283, 33620022156817283, 28697190017397742, 37245369729009439, 32604080612944841,
    31658371840450832, 33620022156817283, 29919582444845343, 32604080612944841, 29919582444845343, 33620022156817283,
    33620022156817283, 28711353656780468, 25494482171489206, 31888331508219841, 30888331160163995, 24494511438939092,
    16226656785935189, 23545400163192394, 28864222577258193, 23545400163192394, 18226492160495302, 22485152464186640,
    24701209201481082, 30756502329956927, 28677283362203151, 23623206689415947, 30756501984785721, 23623206689415947,
    23623206689415947, 30043868737878057, 23623206689415947, 28677283362203151, 30043868737878057, 25485159129766465,
    23623206689415947, 23623206689415947, 24701209201481082, 23623206689415947, 25899118582441565, 23623206689415947,
    30043868737878057, 32319780626615186, 30043868737878057, 29194921889630073, 35588771222827226, 34588770874771403,
    28194951157079959, 23623206689415947, 25899118582441565, 23623206689415947, 29194921889630073, 35588771222827226,
    34588770874771403, 28194951157079959, 19459317542725530, 26778060920391783
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
def positiveArgument (term : PositiveTerm) : ℕ :=
  positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ :=
  positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ :=
  positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ :=
  negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ :=
  negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ :=
  negativeScales[term.val]?.getD 0
def positiveLogLowerNumerator (term : PositiveTerm) : ℕ :=
  positiveLogLowerNumerators[term.val]?.getD 0
def negativeLogUpperNumerator (term : NegativeTerm) : ℕ :=
  negativeLogUpperNumerators[term.val]?.getD 0

noncomputable def positiveLogLower (term : PositiveTerm) : ℝ :=
  (positiveLogLowerNumerator term : ℝ) / logBoundDenominator
noncomputable def negativeLogUpper (term : NegativeTerm) : ℝ :=
  (negativeLogUpperNumerator term : ℝ) / logBoundDenominator
def positiveLogLowerRat (term : PositiveTerm) : ℚ :=
  positiveLogLowerNumerator term / logBoundDenominator
def negativeLogUpperRat (term : NegativeTerm) : ℚ :=
  negativeLogUpperNumerator term / logBoundDenominator

theorem positiveScales_valid :
    ∀ term, 2 ^ positiveScale term ≤ positiveArgument term := by decide

theorem negativeScales_valid :
    ∀ term, 2 ^ negativeScale term ≤ negativeArgument term := by decide

noncomputable def positiveExact : ℝ :=
  Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ :=
  Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 2921143293 / 1000000000000

theorem positiveLogLowerRat_le_fastRat :
    ∀ term, positiveLogLowerRat term ≤
      MatrixMultiplication.RationalDyadicLog.numeratorLogLower
        (positiveArgument term) (positiveScale term) 8 := by decide +kernel

theorem negativeFastRat_le_logUpperRat :
    ∀ term, MatrixMultiplication.RationalDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpperRat term := by decide +kernel

theorem positiveLogLower_le_fast (term : PositiveTerm) :
    positiveLogLower term ≤ MatrixMultiplication.FastDyadicLog.numeratorLogLower
      (positiveArgument term) (positiveScale term) 8 := by
  simpa [positiveLogLower, positiveLogLowerRat] using
    MatrixMultiplication.RationalDyadicLog.cast_le_fastLower
      (positiveLogLowerRat_le_fastRat term)

theorem negativeFast_le_logUpper (term : NegativeTerm) :
    MatrixMultiplication.FastDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpper term := by
  simpa [negativeLogUpper, negativeLogUpperRat] using
    MatrixMultiplication.RationalDyadicLog.fastUpper_le_cast
      (negativeFastRat_le_logUpperRat term)

theorem positiveFloor_le_rationalLower : positiveFloor ≤ positiveRationalLower := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem positiveFloor_le_exact : positiveFloor ≤ positiveExact :=
  positiveFloor_le_rationalLower.trans
    (weightedLowerWithScale_le_natLogSum 8 bits
      positiveArgument positiveCoefficient positiveScale positiveLogLower
      positiveScales_valid positiveLogLower_le_fast)

theorem negativeExact_le_ceiling : negativeExact ≤ negativeCeiling :=
  (natLogSum_le_weightedUpperWithScale 8 bits
    negativeArgument negativeCoefficient negativeScale negativeLogUpper
    negativeScales_valid negativeFast_le_logUpper).trans
      negativeRationalUpper_le_ceiling

/-- Sign-separated exact form used by the directed arithmetic checker. -/
def signedForm : Form :=
  SignedDyadicLogCertificate.Form.ofSignedFamilies constantNumerator
    positiveArgument positiveCoefficient negativeArgument negativeCoefficient

/-- Exact source-order form before this shard's bounded power-of-two normalization. -/
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1494911891095357119818366976, coefficient := (-1494911891095357119818366976) }, { argument := 6769638206105079297249116160, coefficient := (-6769638206105079297249116160) }, { argument := 125045842224423886457447383040, coefficient := (-125045842224423886457447383040) }, { argument := 243531333362579223677040066560, coefficient := (-243531333362579223677040066560) }, { argument := 134224204851374853539338649600, coefficient := (-134224204851374853539338649600) }, { argument := 128456087927514315785691463680, coefficient := (-128456087927514315785691463680) }, { argument := 9366589744714585526040002560, coefficient := (-9366589744714585526040002560) }, { argument := 243531333362579223677040066560, coefficient := (-243531333362579223677040066560) }, { argument := 243531333362579223677040066560, coefficient := (-243531333362579223677040066560) }, { argument := 128456087927514315785691463680, coefficient := (-128456087927514315785691463680) }, { argument := 3005337223804137013069406535680, coefficient := (-3005337223804137013069406535680) }, { argument := 240855164864089342098171494400, coefficient := (-240855164864089342098171494400) }, { argument := 125045842224423886457447383040, coefficient := (-125045842224423886457447383040) }, { argument := 243531333362579223677040066560, coefficient := (-243531333362579223677040066560) }, { argument := 9366589744714585526040002560, coefficient := (-9366589744714585526040002560) }, { argument := 240855164864089342098171494400, coefficient := (-240855164864089342098171494400) }, { argument := 9366589744714585526040002560, coefficient := (-9366589744714585526040002560) }, { argument := 243531333362579223677040066560, coefficient := (-243531333362579223677040066560) }, { argument := 243531333362579223677040066560, coefficient := (-243531333362579223677040066560) }, { argument := 8107713416445423969003110400, coefficient := (-8107713416445423969003110400) }, { argument := 109001780755590620720922624, coefficient := (-109001780755590620720922624) }, { argument := 9165877107327844407624859648, coefficient := (-9165877107327844407624859648) }, { argument := 9165874896024398571692359680, coefficient := (-9165874896024398571692359680) }, { argument := 109003992059036456653422592, coefficient := (-109003992059036456653422592) }, { argument := 90533668434714685803069440, coefficient := (-90533668434714685803069440) }, { argument := 14453446043255840165676974080, coefficient := (-14453446043255840165676974080) }, { argument := 144223656406748810060266209280, coefficient := (-144223656406748810060266209280) }, { argument := 14453446043255840165676974080, coefficient := (-14453446043255840165676974080) }, { argument := 90523338258033408454164480, coefficient := (-90523338258033408454164480) }, { argument := 433196623212152279873355776, coefficient := (-433196623212152279873355776) }, { argument := 251590724426118921053011968, coefficient := (-251590724426118921053011968) }, { argument := 8365453588981128872029323264, coefficient := (-8365453588981128872029323264) }, { argument := 1979621752721304141969752064, coefficient := (-1979621752721304141969752064) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 8365451587509396874542972928, coefficient := (-8365451587509396874542972928) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 10209286764870404638519590912, coefficient := (-10209286764870404638519590912) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 1979621752721304141969752064, coefficient := (-1979621752721304141969752064) }, { argument := 10209286764870404638519590912, coefficient := (-10209286764870404638519590912) }, { argument := 433198624683884277359706112, coefficient := (-433198624683884277359706112) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 251590724426118921053011968, coefficient := (-251590724426118921053011968) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 2308666873689985557580480512, coefficient := (-2308666873689985557580480512) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 10209286764870404638519590912, coefficient := (-10209286764870404638519590912) }, { argument := 98887897756387714716363915264, coefficient := (-98887897756387714716363915264) }, { argument := 10209286764870404638519590912, coefficient := (-10209286764870404638519590912) }, { argument := 2834046299645356138743988224, coefficient := (-2834046299645356138743988224) }, { argument := 238312804790523954598246350848, coefficient := (-238312804790523954598246350848) }, { argument := 238312747296634362864001351680, coefficient := (-238312747296634362864001351680) }, { argument := 2834103793534947872988987392, coefficient := (-2834103793534947872988987392) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 2308666873689985557580480512, coefficient := (-2308666873689985557580480512) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 2834046299645356138743988224, coefficient := (-2834046299645356138743988224) }, { argument := 238312804790523954598246350848, coefficient := (-238312804790523954598246350848) }, { argument := 238312747296634362864001351680, coefficient := (-238312747296634362864001351680) }, { argument := 2834103793534947872988987392, coefficient := (-2834103793534947872988987392) }, { argument := 106377060410789755818606592, coefficient := (-106377060410789755818606592) }, { argument := 16982799100825612194670444544, coefficient := (-16982799100825612194670444544) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := Form.normalizePowersOfTwo rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

/-- Sign separation retains this bounded shard's exact constant. -/
theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by
  rfl

/-- Sign separation only permutes this bounded shard's exact term list. -/
theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by
  decide +kernel

/-- Rational lower endpoint contributed by this shard. -/
noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

/-- Kernel-checked lower-bound certificate before restoring source term order. -/
noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

/-- Kernel-checked lower-bound certificate in the shard's exact source order. -/
noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard2


end Parent2

namespace Parent2

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1141178209017273504898890717986816)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4593298297, 115079923, 2883027, 429262041, 2078931751, 429262041,
    20259423, 1703599521, 851799555, 10129917, 1106893089, 5360723679,
    1106893089, 7583777343, 637714087361, 318856966755, 3791965597, 8512035,
    1358922495, 54240011805, 1358922495, 34044255, 303891345, 25553992815,
    12776993325, 151948755, 598143, 95491851, 3811460289, 95491851,
    2392299, 35898331, 1325677605, 10605418243, 287189245, 184441821,
    1107729945, 2547093697, 480712995, 92559645, 1919866185, 964411785,
    184441821, 1107729945, 92559645, 3825225297, 26604965919, 393510375,
    3698997525, 43679651625, 3069380925, 26604960165, 43679651625, 393510375,
    3069380925, 3069380925, 3069380925, 3069380925, 3069380925, 3825231051,
    3698997525, 366982735, 1694686805, 6600928425
  ]
def negativeCoefficients : Array ℕ := #[
    169462796277929851820812795904, 16982799100825612194670444544, 106364922453189254933643264, 1979621752721304141969752064, 19174760978702935603237879808, 1979621752721304141969752064,
    1494881564648099941315510272, 125703457471924723304569503744, 125703427145477466126066647040, 1494911891095357119818366976, 10209286764870404638519590912, 98887897756387714716363915264,
    10209286764870404638519590912, 34973999939579504877027459072, 2940937140436905505646490681344, 2940936430924399884574434263040, 34974709452085125949083877376, 1256154649531666265517588480,
    200541563850174782298768015360, 2001103232643639739586193653760, 200541563850174782298768015360, 1256011318330213542301532160, 2802902933715187389966581760, 235693982759858856196067819520,
    235693925897770248986374963200, 2802959795803794599659438080, 2824650455163098197055766528, 450947516549582213169121591296, 4499778079890562873880305729536, 450947516549582213169121591296,
    2824328153650642343769931776, 5297658597042511054182023168, 195635484029465774815382077440, 195635436123271415391676530688, 5297706503236870477887569920, 425293883559493490643566592,
    5108502699549839389391585280, 5873198195039712791226220544, 4433794795835709658717224960, 213428010358551241335767040, 4426910021308014457383813120, 4447564344891100061384048640,
    425293883559493490643566592, 5108502699549839389391585280, 213428010358551241335767040, 17640738019509652368012607488, 122693749349389461162112843776, 14517970355948946594988032000,
    17058615168240012249110937600, 201436838688791634005458944000, 452960675105607133763626598400, 122693722813748111130922844160, 201436838688791634005458944000, 14517970355948946594988032000,
    14155021097050222930113331200, 14155021097050222930113331200, 14155021097050222930113331200, 452960675105607133763626598400, 14155021097050222930113331200, 17640764555151002399202607104,
    17058615168240012249110937600, 6769636592014972847663349760, 125045815107710098104406507520, 243531274609699348912118169600
  ]
def negativeScales : Array ℕ := #[
    32, 26, 21, 28, 30, 28,
    24, 30, 29, 23, 30, 32,
    30, 32, 39, 38, 31, 23,
    30, 35, 30, 25, 28, 34,
    33, 27, 19, 26, 31, 26,
    21, 25, 30, 33, 28, 27,
    30, 31, 28, 26, 30, 29,
    27, 30, 26, 31, 34, 28,
    31, 35, 31, 34, 35, 28,
    31, 31, 31, 31, 31, 31,
    31, 28, 30, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32096883331781654, 26778060920391783, 21459152917285642, 28677283362203151, 30953195261899076, 28677283362203151,
    24272089750152533, 30665939083377352, 29665938735321528, 23272119017602419, 30043868737878057, 32319780626615186,
    30043868737878057, 32820269462803170, 39214118795025000, 38214118446969177, 31820298730253620, 23021072652285295,
    30339816029541345, 35658638441367988, 30339816029541345, 25020908026845408, 28178980345761052, 34572829678956690,
    33572829330900867, 27179009613210937, 19190130909910075, 26508874287166488, 31827696700090859, 26508874287166488,
    21189966284470188, 25097413435446606, 30304082819316315, 33304082466036654, 28097426481533905, 27458590573806054,
    30044959061639770, 31246204885334110, 28840600564579641, 26463879995405919, 30838358613731584, 29845074041289101,
    27458590573806054, 30044959061639770, 26463879995405919, 31832897576969402, 34630976504314266, 28551826432352076,
    31784487189610238, 35346242298700778, 31515300556326005, 34630976192294766, 35346242298700778, 28551826432352076,
    31515300556326005, 31515300556326005, 31515300556326005, 31515300556326005, 31515300556326005, 31832899747105950,
    31784487189610238, 28451136951007263, 30658371527596345, 32620021808761460
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
def positiveArgument (term : PositiveTerm) : ℕ :=
  positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ :=
  positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ :=
  positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ :=
  negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ :=
  negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ :=
  negativeScales[term.val]?.getD 0
def positiveLogLowerNumerator (term : PositiveTerm) : ℕ :=
  positiveLogLowerNumerators[term.val]?.getD 0
def negativeLogUpperNumerator (term : NegativeTerm) : ℕ :=
  negativeLogUpperNumerators[term.val]?.getD 0

noncomputable def positiveLogLower (term : PositiveTerm) : ℝ :=
  (positiveLogLowerNumerator term : ℝ) / logBoundDenominator
noncomputable def negativeLogUpper (term : NegativeTerm) : ℝ :=
  (negativeLogUpperNumerator term : ℝ) / logBoundDenominator
def positiveLogLowerRat (term : PositiveTerm) : ℚ :=
  positiveLogLowerNumerator term / logBoundDenominator
def negativeLogUpperRat (term : NegativeTerm) : ℚ :=
  negativeLogUpperNumerator term / logBoundDenominator

theorem positiveScales_valid :
    ∀ term, 2 ^ positiveScale term ≤ positiveArgument term := by decide

theorem negativeScales_valid :
    ∀ term, 2 ^ negativeScale term ≤ negativeArgument term := by decide

noncomputable def positiveExact : ℝ :=
  Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ :=
  Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 7183841569 / 1000000000000

theorem positiveLogLowerRat_le_fastRat :
    ∀ term, positiveLogLowerRat term ≤
      MatrixMultiplication.RationalDyadicLog.numeratorLogLower
        (positiveArgument term) (positiveScale term) 8 := by decide +kernel

theorem negativeFastRat_le_logUpperRat :
    ∀ term, MatrixMultiplication.RationalDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpperRat term := by decide +kernel

theorem positiveLogLower_le_fast (term : PositiveTerm) :
    positiveLogLower term ≤ MatrixMultiplication.FastDyadicLog.numeratorLogLower
      (positiveArgument term) (positiveScale term) 8 := by
  simpa [positiveLogLower, positiveLogLowerRat] using
    MatrixMultiplication.RationalDyadicLog.cast_le_fastLower
      (positiveLogLowerRat_le_fastRat term)

theorem negativeFast_le_logUpper (term : NegativeTerm) :
    MatrixMultiplication.FastDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpper term := by
  simpa [negativeLogUpper, negativeLogUpperRat] using
    MatrixMultiplication.RationalDyadicLog.fastUpper_le_cast
      (negativeFastRat_le_logUpperRat term)

theorem positiveFloor_le_rationalLower : positiveFloor ≤ positiveRationalLower := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem positiveFloor_le_exact : positiveFloor ≤ positiveExact :=
  positiveFloor_le_rationalLower.trans
    (weightedLowerWithScale_le_natLogSum 8 bits
      positiveArgument positiveCoefficient positiveScale positiveLogLower
      positiveScales_valid positiveLogLower_le_fast)

theorem negativeExact_le_ceiling : negativeExact ≤ negativeCeiling :=
  (natLogSum_le_weightedUpperWithScale 8 bits
    negativeArgument negativeCoefficient negativeScale negativeLogUpper
    negativeScales_valid negativeFast_le_logUpper).trans
      negativeRationalUpper_le_ceiling

/-- Sign-separated exact form used by the directed arithmetic checker. -/
def signedForm : Form :=
  SignedDyadicLogCertificate.Form.ofSignedFamilies constantNumerator
    positiveArgument positiveCoefficient negativeArgument negativeCoefficient

/-- Exact source-order form before this shard's bounded power-of-two normalization. -/
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 169462796277929851820812795904, coefficient := (-169462796277929851820812795904) }, { argument := 16982799100825612194670444544, coefficient := (-16982799100825612194670444544) }, { argument := 106364922453189254933643264, coefficient := (-106364922453189254933643264) }, { argument := 1979621752721304141969752064, coefficient := (-1979621752721304141969752064) }, { argument := 19174760978702935603237879808, coefficient := (-19174760978702935603237879808) }, { argument := 1979621752721304141969752064, coefficient := (-1979621752721304141969752064) }, { argument := 1494881564648099941315510272, coefficient := (-1494881564648099941315510272) }, { argument := 125703457471924723304569503744, coefficient := (-125703457471924723304569503744) }, { argument := 125703427145477466126066647040, coefficient := (-125703427145477466126066647040) }, { argument := 1494911891095357119818366976, coefficient := (-1494911891095357119818366976) }, { argument := 10209286764870404638519590912, coefficient := (-10209286764870404638519590912) }, { argument := 98887897756387714716363915264, coefficient := (-98887897756387714716363915264) }, { argument := 10209286764870404638519590912, coefficient := (-10209286764870404638519590912) }, { argument := 34973999939579504877027459072, coefficient := (-34973999939579504877027459072) }, { argument := 2940937140436905505646490681344, coefficient := (-2940937140436905505646490681344) }, { argument := 2940936430924399884574434263040, coefficient := (-2940936430924399884574434263040) }, { argument := 34974709452085125949083877376, coefficient := (-34974709452085125949083877376) }, { argument := 1256154649531666265517588480, coefficient := (-1256154649531666265517588480) }, { argument := 200541563850174782298768015360, coefficient := (-200541563850174782298768015360) }, { argument := 2001103232643639739586193653760, coefficient := (-2001103232643639739586193653760) }, { argument := 200541563850174782298768015360, coefficient := (-200541563850174782298768015360) }, { argument := 1256011318330213542301532160, coefficient := (-1256011318330213542301532160) }, { argument := 2802902933715187389966581760, coefficient := (-2802902933715187389966581760) }, { argument := 235693982759858856196067819520, coefficient := (-235693982759858856196067819520) }, { argument := 235693925897770248986374963200, coefficient := (-235693925897770248986374963200) }, { argument := 2802959795803794599659438080, coefficient := (-2802959795803794599659438080) }, { argument := 2824650455163098197055766528, coefficient := (-2824650455163098197055766528) }, { argument := 450947516549582213169121591296, coefficient := (-450947516549582213169121591296) }, { argument := 4499778079890562873880305729536, coefficient := (-4499778079890562873880305729536) }, { argument := 450947516549582213169121591296, coefficient := (-450947516549582213169121591296) }, { argument := 2824328153650642343769931776, coefficient := (-2824328153650642343769931776) }, { argument := 5297658597042511054182023168, coefficient := (-5297658597042511054182023168) }, { argument := 195635484029465774815382077440, coefficient := (-195635484029465774815382077440) }, { argument := 195635436123271415391676530688, coefficient := (-195635436123271415391676530688) }, { argument := 5297706503236870477887569920, coefficient := (-5297706503236870477887569920) }, { argument := 425293883559493490643566592, coefficient := (-425293883559493490643566592) }, { argument := 5108502699549839389391585280, coefficient := (-5108502699549839389391585280) }, { argument := 5873198195039712791226220544, coefficient := (-5873198195039712791226220544) }, { argument := 4433794795835709658717224960, coefficient := (-4433794795835709658717224960) }, { argument := 213428010358551241335767040, coefficient := (-213428010358551241335767040) }, { argument := 4426910021308014457383813120, coefficient := (-4426910021308014457383813120) }, { argument := 4447564344891100061384048640, coefficient := (-4447564344891100061384048640) }, { argument := 425293883559493490643566592, coefficient := (-425293883559493490643566592) }, { argument := 5108502699549839389391585280, coefficient := (-5108502699549839389391585280) }, { argument := 213428010358551241335767040, coefficient := (-213428010358551241335767040) }, { argument := 17640738019509652368012607488, coefficient := (-17640738019509652368012607488) }, { argument := 122693749349389461162112843776, coefficient := (-122693749349389461162112843776) }, { argument := 14517970355948946594988032000, coefficient := (-14517970355948946594988032000) }, { argument := 17058615168240012249110937600, coefficient := (-17058615168240012249110937600) }, { argument := 201436838688791634005458944000, coefficient := (-201436838688791634005458944000) }, { argument := 452960675105607133763626598400, coefficient := (-452960675105607133763626598400) }, { argument := 122693722813748111130922844160, coefficient := (-122693722813748111130922844160) }, { argument := 201436838688791634005458944000, coefficient := (-201436838688791634005458944000) }, { argument := 14517970355948946594988032000, coefficient := (-14517970355948946594988032000) }, { argument := 14155021097050222930113331200, coefficient := (-14155021097050222930113331200) }, { argument := 14155021097050222930113331200, coefficient := (-14155021097050222930113331200) }, { argument := 14155021097050222930113331200, coefficient := (-14155021097050222930113331200) }, { argument := 452960675105607133763626598400, coefficient := (-452960675105607133763626598400) }, { argument := 14155021097050222930113331200, coefficient := (-14155021097050222930113331200) }, { argument := 17640764555151002399202607104, coefficient := (-17640764555151002399202607104) }, { argument := 17058615168240012249110937600, coefficient := (-17058615168240012249110937600) }, { argument := 6769636592014972847663349760, coefficient := (-6769636592014972847663349760) }, { argument := 125045815107710098104406507520, coefficient := (-125045815107710098104406507520) }, { argument := 243531274609699348912118169600, coefficient := (-243531274609699348912118169600) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := Form.normalizePowersOfTwo rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

/-- Sign separation retains this bounded shard's exact constant. -/
theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by
  rfl

/-- Sign separation only permutes this bounded shard's exact term list. -/
theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by
  decide +kernel

/-- Rational lower endpoint contributed by this shard. -/
noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

/-- Kernel-checked lower-bound certificate before restoring source term order. -/
noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

/-- Kernel-checked lower-bound certificate in the shard's exact source order. -/
noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard3


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14
