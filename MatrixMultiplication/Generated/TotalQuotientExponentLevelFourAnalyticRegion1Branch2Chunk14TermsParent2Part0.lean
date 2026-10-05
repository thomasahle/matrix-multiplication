import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
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

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-185531042354528557696757555789824)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3008053, 3008053, 3008053, 3008053, 23055123, 138464991,
    318384839, 60088581, 11569851, 239981103, 120550383, 23055123,
    138464991, 11569851, 27277521, 132106031, 27277521, 78133455,
    2873840785, 2464875, 23169825, 273601125, 19226025, 718460025,
    273601125, 2464875, 19226025, 19226025, 19226025, 19226025,
    19226025, 19533535, 23169825, 10761111, 10761111, 10761111,
    10761111, 1750670931, 5113327905, 15500271571, 2218991355, 427259205,
    8862182865, 4451765265, 1750670931, 5113327905, 427259205, 429262041,
    2078931751, 429262041, 3825225297, 26604965919, 393510375, 3698997525,
    43679651625, 3069380925, 26604960165, 43679651625, 393510375, 3069380925,
    3069380925, 3069380925, 3069380925, 3069380925
  ]
def negativeCoefficients : Array ℕ := #[
    3551282166473871223498473472, 3551282166473871223498473472, 3551282166473871223498473472, 3551282166473871223498473472, 425291953568894778781728768, 5108456504290992802246950912,
    5873163641982219724022349824, 4433754701837465451006787584, 213426080367952529473929216, 4426869989567531498443112448, 4447524126377333356134137856, 425291953568894778781728768,
    5108456504290992802246950912, 213426080367952529473929216, 251590724426118921053011968, 2436926144450540310779396096, 251590724426118921053011968, 180163480997462741782364160,
    6626625683685444459765432320, 90937836597369662078976000, 106851958001909352942796800, 1261762482788504061345792000, 2837260501837933456864051200, 6626624104182983148385075200,
    1261762482788504061345792000, 90937836597369662078976000, 88664390682435420527001600, 88664390682435420527001600, 88664390682435420527001600, 2837260501837933456864051200,
    88664390682435420527001600, 180165060499924053162721280, 106851958001909352942796800, 12704477476209962668800344064, 12704477476209962668800344064, 12704477476209962668800344064,
    12704477476209962668800344064, 8073544655359958337793818624, 188648502456984854286261288960, 142964771371616445712320954368, 163732662509835911267321118720, 7881541207771604424358625280,
    163478419245069085318148259840, 164241149039369563165666836480, 8073544655359958337793818624, 188648502456984854286261288960, 7881541207771604424358625280, 1979621752721304141969752064,
    19174760978702935603237879808, 1979621752721304141969752064, 17640738019509652368012607488, 122693749349389461162112843776, 14517970355948946594988032000, 17058615168240012249110937600,
    201436838688791634005458944000, 452960675105607133763626598400, 122693722813748111130922844160, 201436838688791634005458944000, 14517970355948946594988032000, 14155021097050222930113331200,
    14155021097050222930113331200, 14155021097050222930113331200, 452960675105607133763626598400, 14155021097050222930113331200
  ]
def negativeScales : Array ℕ := #[
    21, 21, 21, 21, 24, 27,
    28, 25, 23, 27, 26, 24,
    27, 23, 24, 26, 24, 26,
    31, 21, 24, 28, 24, 29,
    28, 21, 24, 24, 24, 24,
    24, 24, 24, 23, 23, 23,
    23, 30, 32, 33, 31, 28,
    33, 32, 30, 32, 28, 28,
    30, 28, 31, 34, 28, 31,
    35, 31, 34, 35, 28, 31,
    31, 31, 31, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    21520398555942497, 21520398555942497, 21520398555942497, 21520398555942497, 24458584026817510, 27044946015552471,
    28246196397680590, 25840587518491978, 23463866949318620, 27838345567643935, 26845060995201407, 24458584026817510,
    27044946015552471, 23463866949318620, 24701209201481082, 26977121106505271, 24701209201481082, 26219437074653603,
    31420332990571491, 21233083055094622, 24465743811884980, 28027498921444728, 24196557179069508, 29420332646695022,
    28027498921444728, 21233083055094622, 24196557179069508, 24196557179069508, 24196557179069508, 24196557179069508,
    24196557179069508, 24219449722779442, 24465743811884980, 23359323696701575, 23359323696701575, 23359323696701575,
    23359323696701575, 30705260783739095, 32251615399422179, 33851574442977583, 31047256900915993, 28670536333223874,
    33045014950129323, 32051730377495301, 30705260783739095, 32251615399422179, 28670536333223874, 28677283362203151,
    30953195261899076, 28677283362203151, 31832897576969402, 34630976504314266, 28551826432352076, 31784487189610238,
    35346242298700778, 31515300556326005, 34630976192294766, 35346242298700778, 28551826432352076, 31515300556326005,
    31515300556326005, 31515300556326005, 31515300556326005, 31515300556326005
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
noncomputable def negativeCeiling : ℝ := 139114443 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3551282166473871223498473472, coefficient := (-3551282166473871223498473472) }, { argument := 3551282166473871223498473472, coefficient := (-3551282166473871223498473472) }, { argument := 3551282166473871223498473472, coefficient := (-3551282166473871223498473472) }, { argument := 3551282166473871223498473472, coefficient := (-3551282166473871223498473472) }, { argument := 425291953568894778781728768, coefficient := (-425291953568894778781728768) }, { argument := 5108456504290992802246950912, coefficient := (-5108456504290992802246950912) }, { argument := 5873163641982219724022349824, coefficient := (-5873163641982219724022349824) }, { argument := 4433754701837465451006787584, coefficient := (-4433754701837465451006787584) }, { argument := 213426080367952529473929216, coefficient := (-213426080367952529473929216) }, { argument := 4426869989567531498443112448, coefficient := (-4426869989567531498443112448) }, { argument := 4447524126377333356134137856, coefficient := (-4447524126377333356134137856) }, { argument := 425291953568894778781728768, coefficient := (-425291953568894778781728768) }, { argument := 5108456504290992802246950912, coefficient := (-5108456504290992802246950912) }, { argument := 213426080367952529473929216, coefficient := (-213426080367952529473929216) }, { argument := 251590724426118921053011968, coefficient := (-251590724426118921053011968) }, { argument := 2436926144450540310779396096, coefficient := (-2436926144450540310779396096) }, { argument := 251590724426118921053011968, coefficient := (-251590724426118921053011968) }, { argument := 180163480997462741782364160, coefficient := (-180163480997462741782364160) }, { argument := 6626625683685444459765432320, coefficient := (-6626625683685444459765432320) }, { argument := 90937836597369662078976000, coefficient := (-90937836597369662078976000) }, { argument := 106851958001909352942796800, coefficient := (-106851958001909352942796800) }, { argument := 1261762482788504061345792000, coefficient := (-1261762482788504061345792000) }, { argument := 2837260501837933456864051200, coefficient := (-2837260501837933456864051200) }, { argument := 6626624104182983148385075200, coefficient := (-6626624104182983148385075200) }, { argument := 1261762482788504061345792000, coefficient := (-1261762482788504061345792000) }, { argument := 90937836597369662078976000, coefficient := (-90937836597369662078976000) }, { argument := 88664390682435420527001600, coefficient := (-88664390682435420527001600) }, { argument := 88664390682435420527001600, coefficient := (-88664390682435420527001600) }, { argument := 88664390682435420527001600, coefficient := (-88664390682435420527001600) }, { argument := 2837260501837933456864051200, coefficient := (-2837260501837933456864051200) }, { argument := 88664390682435420527001600, coefficient := (-88664390682435420527001600) }, { argument := 180165060499924053162721280, coefficient := (-180165060499924053162721280) }, { argument := 106851958001909352942796800, coefficient := (-106851958001909352942796800) }, { argument := 12704477476209962668800344064, coefficient := (-12704477476209962668800344064) }, { argument := 12704477476209962668800344064, coefficient := (-12704477476209962668800344064) }, { argument := 12704477476209962668800344064, coefficient := (-12704477476209962668800344064) }, { argument := 12704477476209962668800344064, coefficient := (-12704477476209962668800344064) }, { argument := 8073544655359958337793818624, coefficient := (-8073544655359958337793818624) }, { argument := 188648502456984854286261288960, coefficient := (-188648502456984854286261288960) }, { argument := 142964771371616445712320954368, coefficient := (-142964771371616445712320954368) }, { argument := 163732662509835911267321118720, coefficient := (-163732662509835911267321118720) }, { argument := 7881541207771604424358625280, coefficient := (-7881541207771604424358625280) }, { argument := 163478419245069085318148259840, coefficient := (-163478419245069085318148259840) }, { argument := 164241149039369563165666836480, coefficient := (-164241149039369563165666836480) }, { argument := 8073544655359958337793818624, coefficient := (-8073544655359958337793818624) }, { argument := 188648502456984854286261288960, coefficient := (-188648502456984854286261288960) }, { argument := 7881541207771604424358625280, coefficient := (-7881541207771604424358625280) }, { argument := 1979621752721304141969752064, coefficient := (-1979621752721304141969752064) }, { argument := 19174760978702935603237879808, coefficient := (-19174760978702935603237879808) }, { argument := 1979621752721304141969752064, coefficient := (-1979621752721304141969752064) }, { argument := 17640738019509652368012607488, coefficient := (-17640738019509652368012607488) }, { argument := 122693749349389461162112843776, coefficient := (-122693749349389461162112843776) }, { argument := 14517970355948946594988032000, coefficient := (-14517970355948946594988032000) }, { argument := 17058615168240012249110937600, coefficient := (-17058615168240012249110937600) }, { argument := 201436838688791634005458944000, coefficient := (-201436838688791634005458944000) }, { argument := 452960675105607133763626598400, coefficient := (-452960675105607133763626598400) }, { argument := 122693722813748111130922844160, coefficient := (-122693722813748111130922844160) }, { argument := 201436838688791634005458944000, coefficient := (-201436838688791634005458944000) }, { argument := 14517970355948946594988032000, coefficient := (-14517970355948946594988032000) }, { argument := 14155021097050222930113331200, coefficient := (-14155021097050222930113331200) }, { argument := 14155021097050222930113331200, coefficient := (-14155021097050222930113331200) }, { argument := 14155021097050222930113331200, coefficient := (-14155021097050222930113331200) }, { argument := 452960675105607133763626598400, coefficient := (-452960675105607133763626598400) }, { argument := 14155021097050222930113331200, coefficient := (-14155021097050222930113331200) }] }

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

end TermShard0


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1068816237437762647818052665606144)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3825231051, 3698997525, 12920931, 62576541, 12920931, 614535831,
    51675852137, 25837919835, 307274149, 19668915, 476961975, 156998205,
    8800853355, 5175765, 12076785, 156998205, 156998205, 5175765,
    1937461365, 77636475, 476961975, 156998205, 12076785, 77636475,
    12076785, 156998205, 156998205, 10696455, 752013, 752013,
    752013, 752013, 3501341025, 40906613223, 62001071299, 17751926493,
    3418072803, 70897445559, 35614113399, 3501341025, 40906613223, 3418072803,
    141440141817, 116760367959, 15706567125, 147641730975, 1743428950875, 122511223575,
    116760366315, 1743428950875, 15706567125, 122511223575, 122511223575, 122511223575,
    122511223575, 122511223575, 141440143461, 147641730975, 12920931, 62576541,
    12920931, 20259423, 1703599521, 851799555
  ]
def negativeCoefficients : Array ℕ := #[
    17640764555151002399202607104, 17058615168240012249110937600, 238349107351060030471274496, 2308666873689985557580480512, 238349107351060030471274496, 2834046299645356138743988224,
    238312804790523954598246350848, 238312747296634362864001351680, 2834103793534947872988987392, 181413720606273452711608320, 17596790971432106630263603200, 2896105707666787295066849280,
    162347089469933074635219271680, 1527616197450613078716579840, 111388681064107203656417280, 2896105707666787295066849280, 2896105707666787295066849280, 1527616197450613078716579840,
    35739853952854968487473315840, 2864280370219899522593587200, 17596790971432106630263603200, 2896105707666787295066849280, 111388681064107203656417280, 2864280370219899522593587200,
    111388681064107203656417280, 2896105707666787295066849280, 2896105707666787295066849280, 197314767880950901930721280, 3551280985882250506087170048, 3551280985882250506087170048,
    3551280985882250506087170048, 3551280985882250506087170048, 8073542725369359625931980800, 188648456261726007699116654592, 142964736818558952645117083648, 163732622415837667059610681344,
    7881539277781005712496787456, 163478379213328602359207559168, 164241108820855796460416925696, 8073542725369359625931980800, 188648456261726007699116654592, 7881539277781005712496787456,
    163069381115461455114657595392, 134615539105739366548566441984, 144867512015707510105178112000, 170219326618456324373584281600, 2010036729217941702709346304000, 4519866374890074315281557094400,
    134615537210336412974910013440, 2010036729217941702709346304000, 144867512015707510105178112000, 141245824215314822352548659200, 141245824215314822352548659200, 141245824215314822352548659200,
    4519866374890074315281557094400, 141245824215314822352548659200, 163069383010864408688314023936, 170219326618456324373584281600, 238349107351060030471274496, 2308666873689985557580480512,
    238349107351060030471274496, 1494881564648099941315510272, 125703457471924723304569503744, 125703427145477466126066647040
  ]
def negativeScales : Array ℕ := #[
    31, 31, 23, 25, 23, 29,
    35, 34, 28, 24, 28, 27,
    33, 22, 23, 27, 27, 22,
    30, 26, 28, 27, 23, 26,
    23, 27, 27, 23, 19, 19,
    19, 19, 31, 35, 35, 34,
    31, 36, 35, 31, 35, 31,
    37, 36, 33, 37, 40, 36,
    36, 40, 33, 36, 36, 36,
    36, 36, 37, 37, 23, 25,
    23, 24, 30, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31832899747105950, 31784487189610238, 23623206689415947, 25899118582441565, 23623206689415947, 29194921889630073,
    35588771222827226, 34588770874771403, 28194951157079959, 24229414040369276, 28829299014612596, 27226172823614513,
    33034996272206397, 22303340684136973, 23525733105474047, 27226172823614513, 27226172823614513, 22303340684136973,
    30851520397599496, 26210231279745491, 28829299014612596, 27226172823614513, 23525733105474047, 26210231279745491,
    23525733105474047, 27226172823614513, 27226172823614513, 23350629404639702, 19520398076331506, 19520398076331506,
    19520398076331506, 19520398076331506, 31705260438861062, 35251615046142518, 35851574094293554, 34047256547636332,
    31670535979944212, 36045014596849662, 35051730024215640, 31705260438861062, 35251615046142518, 31670535979944212,
    37041400670142703, 36764759706544214, 33870648846706565, 37103309600941087, 40665064710532033, 36834122969400972,
    36764759686230895, 40665064710532033, 33870648846706565, 36834122969400972, 36834122969400972, 36834122969400972,
    36834122969400972, 36834122969400972, 37041400686911568, 37103309600941087, 23623206689415947, 25899118582441565,
    23623206689415947, 24272089750152533, 30665939083377352, 29665938735321528
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
noncomputable def negativeCeiling : ℝ := 380709173 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 17640764555151002399202607104, coefficient := (-17640764555151002399202607104) }, { argument := 17058615168240012249110937600, coefficient := (-17058615168240012249110937600) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 2308666873689985557580480512, coefficient := (-2308666873689985557580480512) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 2834046299645356138743988224, coefficient := (-2834046299645356138743988224) }, { argument := 238312804790523954598246350848, coefficient := (-238312804790523954598246350848) }, { argument := 238312747296634362864001351680, coefficient := (-238312747296634362864001351680) }, { argument := 2834103793534947872988987392, coefficient := (-2834103793534947872988987392) }, { argument := 181413720606273452711608320, coefficient := (-181413720606273452711608320) }, { argument := 17596790971432106630263603200, coefficient := (-17596790971432106630263603200) }, { argument := 2896105707666787295066849280, coefficient := (-2896105707666787295066849280) }, { argument := 162347089469933074635219271680, coefficient := (-162347089469933074635219271680) }, { argument := 1527616197450613078716579840, coefficient := (-1527616197450613078716579840) }, { argument := 111388681064107203656417280, coefficient := (-111388681064107203656417280) }, { argument := 2896105707666787295066849280, coefficient := (-2896105707666787295066849280) }, { argument := 2896105707666787295066849280, coefficient := (-2896105707666787295066849280) }, { argument := 1527616197450613078716579840, coefficient := (-1527616197450613078716579840) }, { argument := 35739853952854968487473315840, coefficient := (-35739853952854968487473315840) }, { argument := 2864280370219899522593587200, coefficient := (-2864280370219899522593587200) }, { argument := 17596790971432106630263603200, coefficient := (-17596790971432106630263603200) }, { argument := 2896105707666787295066849280, coefficient := (-2896105707666787295066849280) }, { argument := 111388681064107203656417280, coefficient := (-111388681064107203656417280) }, { argument := 2864280370219899522593587200, coefficient := (-2864280370219899522593587200) }, { argument := 111388681064107203656417280, coefficient := (-111388681064107203656417280) }, { argument := 2896105707666787295066849280, coefficient := (-2896105707666787295066849280) }, { argument := 2896105707666787295066849280, coefficient := (-2896105707666787295066849280) }, { argument := 197314767880950901930721280, coefficient := (-197314767880950901930721280) }, { argument := 3551280985882250506087170048, coefficient := (-3551280985882250506087170048) }, { argument := 3551280985882250506087170048, coefficient := (-3551280985882250506087170048) }, { argument := 3551280985882250506087170048, coefficient := (-3551280985882250506087170048) }, { argument := 3551280985882250506087170048, coefficient := (-3551280985882250506087170048) }, { argument := 8073542725369359625931980800, coefficient := (-8073542725369359625931980800) }, { argument := 188648456261726007699116654592, coefficient := (-188648456261726007699116654592) }, { argument := 142964736818558952645117083648, coefficient := (-142964736818558952645117083648) }, { argument := 163732622415837667059610681344, coefficient := (-163732622415837667059610681344) }, { argument := 7881539277781005712496787456, coefficient := (-7881539277781005712496787456) }, { argument := 163478379213328602359207559168, coefficient := (-163478379213328602359207559168) }, { argument := 164241108820855796460416925696, coefficient := (-164241108820855796460416925696) }, { argument := 8073542725369359625931980800, coefficient := (-8073542725369359625931980800) }, { argument := 188648456261726007699116654592, coefficient := (-188648456261726007699116654592) }, { argument := 7881539277781005712496787456, coefficient := (-7881539277781005712496787456) }, { argument := 163069381115461455114657595392, coefficient := (-163069381115461455114657595392) }, { argument := 134615539105739366548566441984, coefficient := (-134615539105739366548566441984) }, { argument := 144867512015707510105178112000, coefficient := (-144867512015707510105178112000) }, { argument := 170219326618456324373584281600, coefficient := (-170219326618456324373584281600) }, { argument := 2010036729217941702709346304000, coefficient := (-2010036729217941702709346304000) }, { argument := 4519866374890074315281557094400, coefficient := (-4519866374890074315281557094400) }, { argument := 134615537210336412974910013440, coefficient := (-134615537210336412974910013440) }, { argument := 2010036729217941702709346304000, coefficient := (-2010036729217941702709346304000) }, { argument := 144867512015707510105178112000, coefficient := (-144867512015707510105178112000) }, { argument := 141245824215314822352548659200, coefficient := (-141245824215314822352548659200) }, { argument := 141245824215314822352548659200, coefficient := (-141245824215314822352548659200) }, { argument := 141245824215314822352548659200, coefficient := (-141245824215314822352548659200) }, { argument := 4519866374890074315281557094400, coefficient := (-4519866374890074315281557094400) }, { argument := 141245824215314822352548659200, coefficient := (-141245824215314822352548659200) }, { argument := 163069383010864408688314023936, coefficient := (-163069383010864408688314023936) }, { argument := 170219326618456324373584281600, coefficient := (-170219326618456324373584281600) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 2308666873689985557580480512, coefficient := (-2308666873689985557580480512) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 1494881564648099941315510272, coefficient := (-1494881564648099941315510272) }, { argument := 125703457471924723304569503744, coefficient := (-125703457471924723304569503744) }, { argument := 125703427145477466126066647040, coefficient := (-125703427145477466126066647040) }] }

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

end TermShard1


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14
