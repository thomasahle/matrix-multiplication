import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 0, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk0

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
def constantNumerator : ℤ := (-13345853348742448248397190135808)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4160097865, 45456557293, 30410849, 821060897015, 13540597, 4217563,
    3773609, 30410849, 13540597, 533854685, 13540597, 22728249611,
    3773609, 4217563, 13540597, 4217563, 30410849, 30410849,
    2136613725, 4160097865, 149315853685, 597247038439, 16656153889, 149315853685,
    1609103298249, 1118828447, 28834040860875, 498164491, 155165989, 138832727,
    1118828447, 498164491, 19640747555, 498164491, 804550629583, 138832727,
    155165989, 498164491, 155165989, 1118828447, 1118828447, 76739408505,
    45456557293, 1609103298249, 6436131830787, 182097196325, 30410849, 1118828447,
    69926855, 1900601, 597247038439, 6436131830787, 69926855, 115330029541593,
    31135315, 9697885, 8677055, 69926855, 31135315, 1227548075,
    31135315, 3218061837445, 8677055, 9697885
  ]
def negativeCoefficients : Array ℕ := #[
    9367707597319397986795520, 204718134486300402361827328, 35061321785451627753242624, 1848864774922619595752734720, 31222490933029916685369344, 4862519079734167352639488,
    34805399728623513682051072, 35061321785451627753242624, 31222490933029916685369344, 615492546671614341215682560, 31222490933029916685369344, 204717872957766441329754112,
    34805399728623513682051072, 4862519079734167352639488, 31222490933029916685369344, 4862519079734167352639488, 35061321785451627753242624, 35061321785451627753242624,
    9622452775744687413657600, 9367707597319397986795520, 336229411508136751010938880, 336220192470251587625811968, 9376581055990754724282368, 336229411508136751010938880,
    7246757014394832488711061504, 1289921376512181947724726272, 64928487838311152848207872000, 1148689109010848157827858432, 178894205501689467202699264, 1280505892012093028398268416,
    1289921376512181947724726272, 1148689109010848157827858432, 22644240222713850980131143680, 1148689109010848157827858432, 7246747831181393511197966336, 1280505892012093028398268416,
    178894205501689467202699264, 1148689109010848157827858432, 178894205501689467202699264, 1289921376512181947724726272, 1289921376512181947724726272, 345603571547750271528468480,
    204718134486300402361827328, 7246757014394832488711061504, 7246440228709930353807065088, 205023216378620513406156800, 35061321785451627753242624, 1289921376512181947724726272,
    1289922798064397127967047680, 35059900233236447510921216, 336220192470251587625811968, 7246440228709930353807065088, 1289922798064397127967047680, 64925034758518316301356630016,
    1148690374918660216145838080, 178894402651266754973532160, 1280507303188014667178967040, 1289922798064397127967047680, 1148690374918660216145838080, 22644265177699818195333939200,
    1148690374918660216145838080, 7246431045986257835770511360, 1280507303188014667178967040, 178894402651266754973532160
  ]
def negativeScales : Array ℕ := #[
    31, 35, 24, 39, 23, 22,
    21, 24, 23, 28, 23, 34,
    21, 22, 23, 22, 24, 24,
    30, 31, 37, 39, 33, 37,
    40, 30, 44, 28, 27, 27,
    30, 28, 34, 28, 39, 27,
    27, 28, 27, 30, 30, 36,
    35, 40, 42, 37, 24, 30,
    26, 20, 39, 42, 26, 46,
    24, 23, 23, 26, 24, 30,
    24, 41, 23, 23
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31953970332846185, 35403769372923942, 24858082759843787, 39578698272543525, 23690788012484870, 22007978188307374,
    21847513517765837, 24858082759843787, 23690788012484870, 28991871874307360, 23690788012484870, 34403767529871977,
    21847513517765837, 22007978188307374, 23690788012484870, 22007978188307374, 24858082759843787, 24858082759843787,
    30992678984071924, 31953970332846185, 37119576396229165, 39119536838587489, 33955336263390430, 37119576396229165,
    40549394083162197, 30059341694915224, 44712838266839070, 28892046953302166, 27209237125398283, 27048772453205037,
    30059341694915224, 28892046953302166, 34193130790612102, 28892046953302166, 39549392254953405, 27048772453205037,
    27209237125398283, 28892046953302166, 27209237125398283, 30059341694915224, 30059341694915224, 36159248593796192,
    35403769372923942, 40549394083162197, 42549331015623812, 37405917753669612, 24858082759843787, 30059341694915224,
    26059343284830112, 20858024264958768, 39119536838587489, 42549331015623812, 26059343284830112, 46712761538214299,
    24892048543217163, 23209238715313171, 23048774043119925, 26059343284830112, 24892048543217163, 30193132380526990,
    24892048543217163, 41549329187432606, 23048774043119925, 23209238715313171
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
noncomputable def negativeCeiling : ℝ := 120918881 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9367707597319397986795520, coefficient := (-9367707597319397986795520) }, { argument := 204718134486300402361827328, coefficient := (-204718134486300402361827328) }, { argument := 35061321785451627753242624, coefficient := (-35061321785451627753242624) }, { argument := 1848864774922619595752734720, coefficient := (-1848864774922619595752734720) }, { argument := 31222490933029916685369344, coefficient := (-31222490933029916685369344) }, { argument := 4862519079734167352639488, coefficient := (-4862519079734167352639488) }, { argument := 34805399728623513682051072, coefficient := (-34805399728623513682051072) }, { argument := 35061321785451627753242624, coefficient := (-35061321785451627753242624) }, { argument := 31222490933029916685369344, coefficient := (-31222490933029916685369344) }, { argument := 615492546671614341215682560, coefficient := (-615492546671614341215682560) }, { argument := 31222490933029916685369344, coefficient := (-31222490933029916685369344) }, { argument := 204717872957766441329754112, coefficient := (-204717872957766441329754112) }, { argument := 34805399728623513682051072, coefficient := (-34805399728623513682051072) }, { argument := 4862519079734167352639488, coefficient := (-4862519079734167352639488) }, { argument := 31222490933029916685369344, coefficient := (-31222490933029916685369344) }, { argument := 4862519079734167352639488, coefficient := (-4862519079734167352639488) }, { argument := 35061321785451627753242624, coefficient := (-35061321785451627753242624) }, { argument := 35061321785451627753242624, coefficient := (-35061321785451627753242624) }, { argument := 9622452775744687413657600, coefficient := (-9622452775744687413657600) }, { argument := 9367707597319397986795520, coefficient := (-9367707597319397986795520) }, { argument := 336229411508136751010938880, coefficient := (-336229411508136751010938880) }, { argument := 336220192470251587625811968, coefficient := (-336220192470251587625811968) }, { argument := 9376581055990754724282368, coefficient := (-9376581055990754724282368) }, { argument := 336229411508136751010938880, coefficient := (-336229411508136751010938880) }, { argument := 7246757014394832488711061504, coefficient := (-7246757014394832488711061504) }, { argument := 1289921376512181947724726272, coefficient := (-1289921376512181947724726272) }, { argument := 64928487838311152848207872000, coefficient := (-64928487838311152848207872000) }, { argument := 1148689109010848157827858432, coefficient := (-1148689109010848157827858432) }, { argument := 178894205501689467202699264, coefficient := (-178894205501689467202699264) }, { argument := 1280505892012093028398268416, coefficient := (-1280505892012093028398268416) }, { argument := 1289921376512181947724726272, coefficient := (-1289921376512181947724726272) }, { argument := 1148689109010848157827858432, coefficient := (-1148689109010848157827858432) }, { argument := 22644240222713850980131143680, coefficient := (-22644240222713850980131143680) }, { argument := 1148689109010848157827858432, coefficient := (-1148689109010848157827858432) }, { argument := 7246747831181393511197966336, coefficient := (-7246747831181393511197966336) }, { argument := 1280505892012093028398268416, coefficient := (-1280505892012093028398268416) }, { argument := 178894205501689467202699264, coefficient := (-178894205501689467202699264) }, { argument := 1148689109010848157827858432, coefficient := (-1148689109010848157827858432) }, { argument := 178894205501689467202699264, coefficient := (-178894205501689467202699264) }, { argument := 1289921376512181947724726272, coefficient := (-1289921376512181947724726272) }, { argument := 1289921376512181947724726272, coefficient := (-1289921376512181947724726272) }, { argument := 345603571547750271528468480, coefficient := (-345603571547750271528468480) }, { argument := 204718134486300402361827328, coefficient := (-204718134486300402361827328) }, { argument := 7246757014394832488711061504, coefficient := (-7246757014394832488711061504) }, { argument := 7246440228709930353807065088, coefficient := (-7246440228709930353807065088) }, { argument := 205023216378620513406156800, coefficient := (-205023216378620513406156800) }, { argument := 35061321785451627753242624, coefficient := (-35061321785451627753242624) }, { argument := 1289921376512181947724726272, coefficient := (-1289921376512181947724726272) }, { argument := 1289922798064397127967047680, coefficient := (-1289922798064397127967047680) }, { argument := 35059900233236447510921216, coefficient := (-35059900233236447510921216) }, { argument := 336220192470251587625811968, coefficient := (-336220192470251587625811968) }, { argument := 7246440228709930353807065088, coefficient := (-7246440228709930353807065088) }, { argument := 1289922798064397127967047680, coefficient := (-1289922798064397127967047680) }, { argument := 64925034758518316301356630016, coefficient := (-64925034758518316301356630016) }, { argument := 1148690374918660216145838080, coefficient := (-1148690374918660216145838080) }, { argument := 178894402651266754973532160, coefficient := (-178894402651266754973532160) }, { argument := 1280507303188014667178967040, coefficient := (-1280507303188014667178967040) }, { argument := 1289922798064397127967047680, coefficient := (-1289922798064397127967047680) }, { argument := 1148690374918660216145838080, coefficient := (-1148690374918660216145838080) }, { argument := 22644265177699818195333939200, coefficient := (-22644265177699818195333939200) }, { argument := 1148690374918660216145838080, coefficient := (-1148690374918660216145838080) }, { argument := 7246431045986257835770511360, coefficient := (-7246431045986257835770511360) }, { argument := 1280507303188014667178967040, coefficient := (-1280507303188014667178967040) }, { argument := 178894402651266754973532160, coefficient := (-178894402651266754973532160) }] }

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
def constantNumerator : ℤ := (-11754948678648121740987241332736)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    31135315, 9697885, 69926855, 69926855, 306949457043, 821060897015,
    28834040860875, 115330029541593, 3290151862303, 13540597, 498164491, 31135315,
    846253, 4217563, 155165989, 9697885, 263587, 3773609,
    138832727, 8677055, 235841, 30410849, 1118828447, 69926855,
    1900601, 13540597, 498164491, 31135315, 846253, 533854685,
    19640747555, 1227548075, 33364565, 13540597, 498164491, 31135315,
    846253, 16656153889, 182097196325, 1900601, 3290151862303, 846253,
    263587, 235841, 1900601, 846253, 33364565, 846253,
    91048481811, 235841, 263587, 846253, 263587, 1900601,
    1900601, 8554325013, 22728249611, 804550629583, 3218061837445, 91048481811,
    3773609, 138832727, 8677055, 235841
  ]
def negativeCoefficients : Array ℕ := #[
    1148690374918660216145838080, 178894402651266754973532160, 1289922798064397127967047680, 1289922798064397127967047680, 345594365090107717249400832, 1848864774922619595752734720,
    64928487838311152848207872000, 64925034758518316301356630016, 1852190837632516783169601536, 31222490933029916685369344, 1148689109010848157827858432, 1148690374918660216145838080,
    31221225025217858367389696, 4862519079734167352639488, 178894205501689467202699264, 178894402651266754973532160, 4862321930156879581806592, 34805399728623513682051072,
    1280505892012093028398268416, 1280507303188014667178967040, 34803988552701874901352448, 35061321785451627753242624, 1289921376512181947724726272, 1289922798064397127967047680,
    35059900233236447510921216, 31222490933029916685369344, 1148689109010848157827858432, 1148690374918660216145838080, 31221225025217858367389696, 615492546671614341215682560,
    22644240222713850980131143680, 22644265177699818195333939200, 615467591685647126012887040, 31222490933029916685369344, 1148689109010848157827858432, 1148690374918660216145838080,
    31221225025217858367389696, 9376581055990754724282368, 205023216378620513406156800, 35059900233236447510921216, 1852190837632516783169601536, 31221225025217858367389696,
    4862321930156879581806592, 34803988552701874901352448, 35059900233236447510921216, 31221225025217858367389696, 615467591685647126012887040, 31221225025217858367389696,
    205022954378334491407024128, 34803988552701874901352448, 4862321930156879581806592, 31221225025217858367389696, 4862321930156879581806592, 35059900233236447510921216,
    35059900233236447510921216, 9631313735238228337754112, 204717872957766441329754112, 7246747831181393511197966336, 7246431045986257835770511360, 205022954378334491407024128,
    34805399728623513682051072, 1280505892012093028398268416, 1280507303188014667178967040, 34803988552701874901352448
  ]
def negativeScales : Array ℕ := #[
    24, 23, 26, 26, 38, 39,
    44, 46, 41, 23, 28, 24,
    19, 22, 27, 23, 18, 21,
    27, 23, 17, 24, 30, 26,
    20, 23, 28, 24, 19, 28,
    34, 30, 24, 23, 28, 24,
    19, 33, 37, 20, 41, 19,
    18, 17, 20, 19, 24, 19,
    36, 17, 18, 19, 18, 20,
    20, 32, 34, 39, 41, 36,
    21, 27, 23, 17
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    24892048543217163, 23209238715313171, 26059343284830112, 26059343284830112, 38159210161647941, 39578698272543525,
    44712838266839070, 46712761538214299, 41581291314081844, 23690788012484870, 28892046953302166, 24892048543217163,
    19690729517602000, 22007978188307374, 27209237125398283, 23209238715313171, 18007919693424586, 21847513517765837,
    27048772453205037, 23048774043119925, 17847455022881199, 24858082759843787, 30059341694915224, 26059343284830112,
    20858024264958768, 23690788012484870, 28892046953302166, 24892048543217163, 19690729517602000, 28991871874307360,
    34193130790612102, 30193132380526990, 24991813379405015, 23690788012484870, 28892046953302166, 24892048543217163,
    19690729517602000, 33955336263390430, 37405917753669612, 20858024264958768, 41581291314081844, 19690729517602000,
    18007919693424586, 17847455022881199, 20858024264958768, 19690729517602000, 24991813379405015, 19690729517602000,
    36405915910040575, 17847455022881199, 18007919693424586, 19690729517602000, 18007919693424586, 20858024264958768,
    20858024264958768, 32994006897504857, 34403767529871977, 39549392254953405, 41549329187432606, 36405915910040575,
    21847513517765837, 27048772453205037, 23048774043119925, 17847455022881199
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
noncomputable def negativeCeiling : ℝ := 106064001 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1148690374918660216145838080, coefficient := (-1148690374918660216145838080) }, { argument := 178894402651266754973532160, coefficient := (-178894402651266754973532160) }, { argument := 1289922798064397127967047680, coefficient := (-1289922798064397127967047680) }, { argument := 1289922798064397127967047680, coefficient := (-1289922798064397127967047680) }, { argument := 345594365090107717249400832, coefficient := (-345594365090107717249400832) }, { argument := 1848864774922619595752734720, coefficient := (-1848864774922619595752734720) }, { argument := 64928487838311152848207872000, coefficient := (-64928487838311152848207872000) }, { argument := 64925034758518316301356630016, coefficient := (-64925034758518316301356630016) }, { argument := 1852190837632516783169601536, coefficient := (-1852190837632516783169601536) }, { argument := 31222490933029916685369344, coefficient := (-31222490933029916685369344) }, { argument := 1148689109010848157827858432, coefficient := (-1148689109010848157827858432) }, { argument := 1148690374918660216145838080, coefficient := (-1148690374918660216145838080) }, { argument := 31221225025217858367389696, coefficient := (-31221225025217858367389696) }, { argument := 4862519079734167352639488, coefficient := (-4862519079734167352639488) }, { argument := 178894205501689467202699264, coefficient := (-178894205501689467202699264) }, { argument := 178894402651266754973532160, coefficient := (-178894402651266754973532160) }, { argument := 4862321930156879581806592, coefficient := (-4862321930156879581806592) }, { argument := 34805399728623513682051072, coefficient := (-34805399728623513682051072) }, { argument := 1280505892012093028398268416, coefficient := (-1280505892012093028398268416) }, { argument := 1280507303188014667178967040, coefficient := (-1280507303188014667178967040) }, { argument := 34803988552701874901352448, coefficient := (-34803988552701874901352448) }, { argument := 35061321785451627753242624, coefficient := (-35061321785451627753242624) }, { argument := 1289921376512181947724726272, coefficient := (-1289921376512181947724726272) }, { argument := 1289922798064397127967047680, coefficient := (-1289922798064397127967047680) }, { argument := 35059900233236447510921216, coefficient := (-35059900233236447510921216) }, { argument := 31222490933029916685369344, coefficient := (-31222490933029916685369344) }, { argument := 1148689109010848157827858432, coefficient := (-1148689109010848157827858432) }, { argument := 1148690374918660216145838080, coefficient := (-1148690374918660216145838080) }, { argument := 31221225025217858367389696, coefficient := (-31221225025217858367389696) }, { argument := 615492546671614341215682560, coefficient := (-615492546671614341215682560) }, { argument := 22644240222713850980131143680, coefficient := (-22644240222713850980131143680) }, { argument := 22644265177699818195333939200, coefficient := (-22644265177699818195333939200) }, { argument := 615467591685647126012887040, coefficient := (-615467591685647126012887040) }, { argument := 31222490933029916685369344, coefficient := (-31222490933029916685369344) }, { argument := 1148689109010848157827858432, coefficient := (-1148689109010848157827858432) }, { argument := 1148690374918660216145838080, coefficient := (-1148690374918660216145838080) }, { argument := 31221225025217858367389696, coefficient := (-31221225025217858367389696) }, { argument := 9376581055990754724282368, coefficient := (-9376581055990754724282368) }, { argument := 205023216378620513406156800, coefficient := (-205023216378620513406156800) }, { argument := 35059900233236447510921216, coefficient := (-35059900233236447510921216) }, { argument := 1852190837632516783169601536, coefficient := (-1852190837632516783169601536) }, { argument := 31221225025217858367389696, coefficient := (-31221225025217858367389696) }, { argument := 4862321930156879581806592, coefficient := (-4862321930156879581806592) }, { argument := 34803988552701874901352448, coefficient := (-34803988552701874901352448) }, { argument := 35059900233236447510921216, coefficient := (-35059900233236447510921216) }, { argument := 31221225025217858367389696, coefficient := (-31221225025217858367389696) }, { argument := 615467591685647126012887040, coefficient := (-615467591685647126012887040) }, { argument := 31221225025217858367389696, coefficient := (-31221225025217858367389696) }, { argument := 205022954378334491407024128, coefficient := (-205022954378334491407024128) }, { argument := 34803988552701874901352448, coefficient := (-34803988552701874901352448) }, { argument := 4862321930156879581806592, coefficient := (-4862321930156879581806592) }, { argument := 31221225025217858367389696, coefficient := (-31221225025217858367389696) }, { argument := 4862321930156879581806592, coefficient := (-4862321930156879581806592) }, { argument := 35059900233236447510921216, coefficient := (-35059900233236447510921216) }, { argument := 35059900233236447510921216, coefficient := (-35059900233236447510921216) }, { argument := 9631313735238228337754112, coefficient := (-9631313735238228337754112) }, { argument := 204717872957766441329754112, coefficient := (-204717872957766441329754112) }, { argument := 7246747831181393511197966336, coefficient := (-7246747831181393511197966336) }, { argument := 7246431045986257835770511360, coefficient := (-7246431045986257835770511360) }, { argument := 205022954378334491407024128, coefficient := (-205022954378334491407024128) }, { argument := 34805399728623513682051072, coefficient := (-34805399728623513682051072) }, { argument := 1280505892012093028398268416, coefficient := (-1280505892012093028398268416) }, { argument := 1280507303188014667178967040, coefficient := (-1280507303188014667178967040) }, { argument := 34803988552701874901352448, coefficient := (-34803988552701874901352448) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk0
