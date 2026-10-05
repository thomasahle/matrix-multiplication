import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 1, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-199624188621501001096612041195520)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    207042325, 189240555, 207042325, 189240555, 375683821, 3385736457,
    7685891149, 5453671299, 168948925, 5453671299, 3642538823, 191220889,
    3385736457, 20273871, 202427919, 980365809, 202427919, 89045445,
    3112876467, 6564075, 5813895, 272127795, 74080275, 1556438787,
    272127795, 6564075, 6564075, 2813175, 6564075, 74080275,
    2813175, 44522169, 5813895, 5663133895, 5176210233, 5663133895,
    5176210233, 6072149299, 59246167323, 50112462241, 95432449161, 2956395575,
    95432449161, 63739888597, 6308660945, 59246167323, 354767469, 5009014251,
    24258839061, 5009014251, 810007575, 5452053435, 688231425, 609576405,
    28532108505, 7767183225, 340753455, 28532108505, 688231425, 688231425,
    294956325, 688231425, 7767183225, 294956325
  ]
def negativeCoefficients : Array ℕ := #[
    3819256781700796941284147200, 3490872086451756456612986880, 3819256781700796941284147200, 3490872086451756456612986880, 433133956163769374705975296, 3903488370206695258463404032,
    8861229187749527897635815424, 6287654919674257631896141824, 194784848812709344234700800, 6287654919674257631896141824, 4199561340402013461700149248, 440925350116277748475363328,
    3903488370206695258463404032, 186993454860200970465312768, 233383500947912946503122944, 2260569647154777525130887168, 233383500947912946503122944, 205324816855572478049648640,
    7177804439977772077321027584, 121085811605635025023795200, 107247433136419593592504320, 5019871789707897751700766720, 1366539873835023853839974400, 7177806992545983276880232448,
    5019871789707897751700766720, 121085811605635025023795200, 121085811605635025023795200, 103787838519115735734681600, 121085811605635025023795200, 1366539873835023853839974400,
    103787838519115735734681600, 205322264287361278490443776, 107247433136419593592504320, 13058297702026867517727703040, 11935528179983435918072610816, 13058297702026867517727703040,
    11935528179983435918072610816, 7000711506000491135918669824, 136612360744444342543105130496, 231102941465790106539460132864, 220052245750033102659253174272, 6816984069084049029097062400,
    220052245750033102659253174272, 146974176529452097067332665344, 7273390868763853097082552320, 136612360744444342543105130496, 6544304706320687067933179904, 5775000246860058654960254976,
    55937074460446941738877059072, 5775000246860058654960254976, 14942002433791095158813491200, 201145268783268108160645201920, 12695628960459429744790732800, 11244699936406923488243220480,
    526324503475046644562610094080, 143279241125184992834066841600, 201145336851753740148890664960, 526324503475046644562610094080, 12695628960459429744790732800, 12695628960459429744790732800,
    10881967680393796924106342400, 12695628960459429744790732800, 143279241125184992834066841600, 10881967680393796924106342400
  ]
def negativeScales : Array ℕ := #[
    27, 27, 27, 27, 28, 31,
    32, 32, 27, 32, 31, 27,
    31, 24, 27, 29, 27, 26,
    31, 22, 22, 28, 26, 30,
    28, 22, 22, 21, 22, 26,
    21, 25, 22, 32, 32, 32,
    32, 32, 35, 35, 36, 31,
    36, 35, 32, 35, 28, 32,
    34, 32, 29, 32, 29, 29,
    34, 32, 28, 34, 29, 29,
    28, 29, 32, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    27625350482515018, 27495646056167742, 27625350482515018, 27495646056167742, 28484943746077780, 31656822533395024,
    32839565399861900, 32344580603452276, 27332011929949220, 32344580603452276, 31762297203220530, 27510664891259963,
    31656822533395024, 24273118240895651, 27592833040366447, 29868744931565702, 27592833040366447, 26408038478301092,
    31535601179273895, 22646160292276457, 22471073585699149, 28019709079378918, 26142586118376639, 30535601692324491,
    28019709079378918, 22646160292276457, 22646160292276457, 21423767870920709, 22646160292276457, 26142586118376639,
    21423767870920709, 25408020542815031, 22471073585699149, 32398953494242435, 32269249067906154, 32398953494242435,
    32269249067906154, 32499560117447237, 35786002777411928, 35544450374201802, 36473760847010287, 31461192173507191,
    36473760847010287, 35891477450230651, 32554686670127911, 35786002777411928, 28402298484453560, 32221879570157397,
    34497791458894778, 32221879570157397, 29593360158908065, 32344152555900429, 29358318526873585, 29183231820315493,
    34731867314145879, 32854744354888868, 28344153044114994, 34731867314145879, 29358318526873585, 29358318526873585,
    28135926105537136, 29358318526873585, 32854744354888868, 28135926105537136
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
noncomputable def negativeCeiling : ℝ := 258998039 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3819256781700796941284147200, coefficient := (-3819256781700796941284147200) }, { argument := 3490872086451756456612986880, coefficient := (-3490872086451756456612986880) }, { argument := 3819256781700796941284147200, coefficient := (-3819256781700796941284147200) }, { argument := 3490872086451756456612986880, coefficient := (-3490872086451756456612986880) }, { argument := 433133956163769374705975296, coefficient := (-433133956163769374705975296) }, { argument := 3903488370206695258463404032, coefficient := (-3903488370206695258463404032) }, { argument := 8861229187749527897635815424, coefficient := (-8861229187749527897635815424) }, { argument := 6287654919674257631896141824, coefficient := (-6287654919674257631896141824) }, { argument := 194784848812709344234700800, coefficient := (-194784848812709344234700800) }, { argument := 6287654919674257631896141824, coefficient := (-6287654919674257631896141824) }, { argument := 4199561340402013461700149248, coefficient := (-4199561340402013461700149248) }, { argument := 440925350116277748475363328, coefficient := (-440925350116277748475363328) }, { argument := 3903488370206695258463404032, coefficient := (-3903488370206695258463404032) }, { argument := 186993454860200970465312768, coefficient := (-186993454860200970465312768) }, { argument := 233383500947912946503122944, coefficient := (-233383500947912946503122944) }, { argument := 2260569647154777525130887168, coefficient := (-2260569647154777525130887168) }, { argument := 233383500947912946503122944, coefficient := (-233383500947912946503122944) }, { argument := 205324816855572478049648640, coefficient := (-205324816855572478049648640) }, { argument := 7177804439977772077321027584, coefficient := (-7177804439977772077321027584) }, { argument := 121085811605635025023795200, coefficient := (-121085811605635025023795200) }, { argument := 107247433136419593592504320, coefficient := (-107247433136419593592504320) }, { argument := 5019871789707897751700766720, coefficient := (-5019871789707897751700766720) }, { argument := 1366539873835023853839974400, coefficient := (-1366539873835023853839974400) }, { argument := 7177806992545983276880232448, coefficient := (-7177806992545983276880232448) }, { argument := 5019871789707897751700766720, coefficient := (-5019871789707897751700766720) }, { argument := 121085811605635025023795200, coefficient := (-121085811605635025023795200) }, { argument := 121085811605635025023795200, coefficient := (-121085811605635025023795200) }, { argument := 103787838519115735734681600, coefficient := (-103787838519115735734681600) }, { argument := 121085811605635025023795200, coefficient := (-121085811605635025023795200) }, { argument := 1366539873835023853839974400, coefficient := (-1366539873835023853839974400) }, { argument := 103787838519115735734681600, coefficient := (-103787838519115735734681600) }, { argument := 205322264287361278490443776, coefficient := (-205322264287361278490443776) }, { argument := 107247433136419593592504320, coefficient := (-107247433136419593592504320) }, { argument := 13058297702026867517727703040, coefficient := (-13058297702026867517727703040) }, { argument := 11935528179983435918072610816, coefficient := (-11935528179983435918072610816) }, { argument := 13058297702026867517727703040, coefficient := (-13058297702026867517727703040) }, { argument := 11935528179983435918072610816, coefficient := (-11935528179983435918072610816) }, { argument := 7000711506000491135918669824, coefficient := (-7000711506000491135918669824) }, { argument := 136612360744444342543105130496, coefficient := (-136612360744444342543105130496) }, { argument := 231102941465790106539460132864, coefficient := (-231102941465790106539460132864) }, { argument := 220052245750033102659253174272, coefficient := (-220052245750033102659253174272) }, { argument := 6816984069084049029097062400, coefficient := (-6816984069084049029097062400) }, { argument := 220052245750033102659253174272, coefficient := (-220052245750033102659253174272) }, { argument := 146974176529452097067332665344, coefficient := (-146974176529452097067332665344) }, { argument := 7273390868763853097082552320, coefficient := (-7273390868763853097082552320) }, { argument := 136612360744444342543105130496, coefficient := (-136612360744444342543105130496) }, { argument := 6544304706320687067933179904, coefficient := (-6544304706320687067933179904) }, { argument := 5775000246860058654960254976, coefficient := (-5775000246860058654960254976) }, { argument := 55937074460446941738877059072, coefficient := (-55937074460446941738877059072) }, { argument := 5775000246860058654960254976, coefficient := (-5775000246860058654960254976) }, { argument := 14942002433791095158813491200, coefficient := (-14942002433791095158813491200) }, { argument := 201145268783268108160645201920, coefficient := (-201145268783268108160645201920) }, { argument := 12695628960459429744790732800, coefficient := (-12695628960459429744790732800) }, { argument := 11244699936406923488243220480, coefficient := (-11244699936406923488243220480) }, { argument := 526324503475046644562610094080, coefficient := (-526324503475046644562610094080) }, { argument := 143279241125184992834066841600, coefficient := (-143279241125184992834066841600) }, { argument := 201145336851753740148890664960, coefficient := (-201145336851753740148890664960) }, { argument := 526324503475046644562610094080, coefficient := (-526324503475046644562610094080) }, { argument := 12695628960459429744790732800, coefficient := (-12695628960459429744790732800) }, { argument := 12695628960459429744790732800, coefficient := (-12695628960459429744790732800) }, { argument := 10881967680393796924106342400, coefficient := (-10881967680393796924106342400) }, { argument := 12695628960459429744790732800, coefficient := (-12695628960459429744790732800) }, { argument := 143279241125184992834066841600, coefficient := (-143279241125184992834066841600) }, { argument := 10881967680393796924106342400, coefficient := (-10881967680393796924106342400) }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1153418250041972176882436300341248)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    810003885, 609576405, 159358149, 771777339, 159358149, 1863175095,
    156002038857, 78001047657, 931559319, 2783165, 3206028805, 954309195,
    58389635325, 979258455, 31186575, 954309195, 542646405, 979258455,
    15287659065, 18711945, 1603015435, 954309195, 31186575, 18711945,
    31186575, 480273255, 542646405, 2783165, 1656338065, 1513923951,
    1656338065, 1513923951, 6072152199, 59246196381, 25056243315, 95432495967,
    2956397025, 95432495967, 63739919859, 6308663961, 59246196381, 354767643,
    118756038075, 127184545845, 7418446875, 6570624375, 307547611875, 83722471875,
    63592273845, 307547611875, 7418446875, 7418446875, 3179334375, 7418446875,
    83722471875, 3179334375, 59378018115, 6570624375, 81832563, 396318093,
    81832563, 1911885555, 160080523533, 80040290733
  ]
def negativeCoefficients : Array ℕ := #[
    14941934365305463170568028160, 11244699936406923488243220480, 183727436916442106821607424, 1779597381802697200634953728, 183727436916442106821607424, 2148094633873405052159262720,
    179858105360748246458204946432, 179858170451237632046964670464, 2148029543384019463399538688, 205361329879623376893378560, 14785198214693966421132574720, 2200487185919097858309488640,
    134637332424688204853438054400, 2258016262675152704278364160, 71911345945068557461094400, 2200487185919097858309488640, 1251257419444192899823042560, 2258016262675152704278364160,
    35250941782272606867428474880, 1380697842145316303253012480, 14785207737825594473688596480, 2200487185919097858309488640, 71911345945068557461094400, 1380697842145316303253012480,
    71911345945068557461094400, 2214869455108111569801707520, 1251257419444192899823042560, 205361329879623376893378560, 3819255548074787011957882880, 3490870958894524951116644352,
    3819255548074787011957882880, 3490870958894524951116644352, 7000714849472854495774900224, 136612427747630504274623987712, 231103053940200409965023723520, 220052353677320991915412291584,
    6816987412556412388953292800, 220052353677320991915412291584, 146974248614716251105832992768, 7273394345975110991333031936, 136612427747630504274623987712, 6544307916054155893395161088,
    136916390098577007387554611200, 146633797958355907919971614720, 136846190927535392843366400000, 121206626250102776518410240000, 5673252086738681571877847040000, 1544407011896470862089420800000,
    146633800085496083919604285440, 5673252086738681571877847040000, 136846190927535392843366400000, 136846190927535392843366400000, 117296735080744622437171200000, 136846190927535392843366400000,
    1544407011896470862089420800000, 117296735080744622437171200000, 136916387971436831387921940480, 121206626250102776518410240000, 188693043319589190789758976, 1827694608337905233084547072,
    188693043319589190789758976, 2204253970706696687509831680, 184560278049918135254497886208, 184560344842119661642963746816
  ]
def negativeScales : Array ℕ := #[
    29, 29, 27, 29, 27, 30,
    37, 36, 29, 21, 31, 29,
    35, 29, 24, 29, 29, 29,
    33, 24, 30, 29, 24, 24,
    24, 28, 29, 21, 30, 30,
    30, 30, 32, 35, 34, 36,
    31, 36, 35, 32, 35, 28,
    36, 36, 32, 32, 38, 36,
    35, 38, 32, 32, 31, 32,
    36, 31, 35, 32, 26, 28,
    26, 30, 37, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29593353586677148, 29183231820315493, 27247697554313128, 29523609443050843, 27247697554313128, 30795116114904183,
    37182773928166852, 36182774450276818, 29795072398417646, 21408295010737278, 31578140241628988, 29829881533654097,
    35764993249928696, 29867114441072068, 24894421788625556, 29829881533654097, 29015437185636323, 29867114441072068,
    33831648459869585, 24157456190508751, 30578141170867145, 29829881533654097, 24894421788625556, 24157456190508751,
    24894421788625556, 28839280231892101, 29015437185636323, 21408295010737278, 30625350016522151, 30495645590174876,
    30625350016522151, 30495645590174876, 32499560806464323, 35786003484999009, 34544451076340136, 36473761554597361,
    31461192881094266, 36473761554597361, 35891478157817773, 32554687359841186, 35786003484999009, 28402299192040634,
    36789209912496092, 36888132427127703, 32788470030523521, 32613383323463827, 38162018817135542, 36284895856133262,
    35888132448056131, 38162018817135542, 32788470030523521, 32788470030523521, 31566077608679464, 32788470030523521,
    36284895856133262, 31566077608679464, 35789209890082306, 32613383323463827, 26286171702127764, 28562083590866803,
    26286171702127764, 30832349021750443, 37220006834365827, 36220007356475793
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
noncomputable def negativeCeiling : ℝ := 1015129063 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 14941934365305463170568028160, coefficient := (-14941934365305463170568028160) }, { argument := 11244699936406923488243220480, coefficient := (-11244699936406923488243220480) }, { argument := 183727436916442106821607424, coefficient := (-183727436916442106821607424) }, { argument := 1779597381802697200634953728, coefficient := (-1779597381802697200634953728) }, { argument := 183727436916442106821607424, coefficient := (-183727436916442106821607424) }, { argument := 2148094633873405052159262720, coefficient := (-2148094633873405052159262720) }, { argument := 179858105360748246458204946432, coefficient := (-179858105360748246458204946432) }, { argument := 179858170451237632046964670464, coefficient := (-179858170451237632046964670464) }, { argument := 2148029543384019463399538688, coefficient := (-2148029543384019463399538688) }, { argument := 205361329879623376893378560, coefficient := (-205361329879623376893378560) }, { argument := 14785198214693966421132574720, coefficient := (-14785198214693966421132574720) }, { argument := 2200487185919097858309488640, coefficient := (-2200487185919097858309488640) }, { argument := 134637332424688204853438054400, coefficient := (-134637332424688204853438054400) }, { argument := 2258016262675152704278364160, coefficient := (-2258016262675152704278364160) }, { argument := 71911345945068557461094400, coefficient := (-71911345945068557461094400) }, { argument := 2200487185919097858309488640, coefficient := (-2200487185919097858309488640) }, { argument := 1251257419444192899823042560, coefficient := (-1251257419444192899823042560) }, { argument := 2258016262675152704278364160, coefficient := (-2258016262675152704278364160) }, { argument := 35250941782272606867428474880, coefficient := (-35250941782272606867428474880) }, { argument := 1380697842145316303253012480, coefficient := (-1380697842145316303253012480) }, { argument := 14785207737825594473688596480, coefficient := (-14785207737825594473688596480) }, { argument := 2200487185919097858309488640, coefficient := (-2200487185919097858309488640) }, { argument := 71911345945068557461094400, coefficient := (-71911345945068557461094400) }, { argument := 1380697842145316303253012480, coefficient := (-1380697842145316303253012480) }, { argument := 71911345945068557461094400, coefficient := (-71911345945068557461094400) }, { argument := 2214869455108111569801707520, coefficient := (-2214869455108111569801707520) }, { argument := 1251257419444192899823042560, coefficient := (-1251257419444192899823042560) }, { argument := 205361329879623376893378560, coefficient := (-205361329879623376893378560) }, { argument := 3819255548074787011957882880, coefficient := (-3819255548074787011957882880) }, { argument := 3490870958894524951116644352, coefficient := (-3490870958894524951116644352) }, { argument := 3819255548074787011957882880, coefficient := (-3819255548074787011957882880) }, { argument := 3490870958894524951116644352, coefficient := (-3490870958894524951116644352) }, { argument := 7000714849472854495774900224, coefficient := (-7000714849472854495774900224) }, { argument := 136612427747630504274623987712, coefficient := (-136612427747630504274623987712) }, { argument := 231103053940200409965023723520, coefficient := (-231103053940200409965023723520) }, { argument := 220052353677320991915412291584, coefficient := (-220052353677320991915412291584) }, { argument := 6816987412556412388953292800, coefficient := (-6816987412556412388953292800) }, { argument := 220052353677320991915412291584, coefficient := (-220052353677320991915412291584) }, { argument := 146974248614716251105832992768, coefficient := (-146974248614716251105832992768) }, { argument := 7273394345975110991333031936, coefficient := (-7273394345975110991333031936) }, { argument := 136612427747630504274623987712, coefficient := (-136612427747630504274623987712) }, { argument := 6544307916054155893395161088, coefficient := (-6544307916054155893395161088) }, { argument := 136916390098577007387554611200, coefficient := (-136916390098577007387554611200) }, { argument := 146633797958355907919971614720, coefficient := (-146633797958355907919971614720) }, { argument := 136846190927535392843366400000, coefficient := (-136846190927535392843366400000) }, { argument := 121206626250102776518410240000, coefficient := (-121206626250102776518410240000) }, { argument := 5673252086738681571877847040000, coefficient := (-5673252086738681571877847040000) }, { argument := 1544407011896470862089420800000, coefficient := (-1544407011896470862089420800000) }, { argument := 146633800085496083919604285440, coefficient := (-146633800085496083919604285440) }, { argument := 5673252086738681571877847040000, coefficient := (-5673252086738681571877847040000) }, { argument := 136846190927535392843366400000, coefficient := (-136846190927535392843366400000) }, { argument := 136846190927535392843366400000, coefficient := (-136846190927535392843366400000) }, { argument := 117296735080744622437171200000, coefficient := (-117296735080744622437171200000) }, { argument := 136846190927535392843366400000, coefficient := (-136846190927535392843366400000) }, { argument := 1544407011896470862089420800000, coefficient := (-1544407011896470862089420800000) }, { argument := 117296735080744622437171200000, coefficient := (-117296735080744622437171200000) }, { argument := 136916387971436831387921940480, coefficient := (-136916387971436831387921940480) }, { argument := 121206626250102776518410240000, coefficient := (-121206626250102776518410240000) }, { argument := 188693043319589190789758976, coefficient := (-188693043319589190789758976) }, { argument := 1827694608337905233084547072, coefficient := (-1827694608337905233084547072) }, { argument := 188693043319589190789758976, coefficient := (-188693043319589190789758976) }, { argument := 2204253970706696687509831680, coefficient := (-2204253970706696687509831680) }, { argument := 184560278049918135254497886208, coefficient := (-184560278049918135254497886208) }, { argument := 184560344842119661642963746816, coefficient := (-184560344842119661642963746816) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1
