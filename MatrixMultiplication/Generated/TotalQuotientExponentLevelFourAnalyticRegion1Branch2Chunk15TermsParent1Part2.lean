import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 15, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1389967553558732945999617056571392)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    9345, 525, 203437809, 3559908051, 3559909797, 203436063,
    932036511, 293433, 16485, 1582958153, 891289, 932036511,
    891289, 891289, 293433, 16485, 5290023542602845, 5290021561287587,
    2174058579, 9345, 525, 3688080557, 28385, 2174058579,
    28385, 28385, 9345, 525, 2055, 2055,
    5068833, 17031, 28385, 868581, 28385, 891289,
    28385, 868581, 493899, 891289, 13914327, 17031,
    28385, 868581, 28385, 17031, 28385, 437129,
    493899, 17031, 203437809, 3559908051, 3559909797, 203436063,
    17031, 28385, 868581, 28385, 891289, 28385,
    868581, 493899, 891289, 13914327
  ]
def negativeCoefficients : Array ℕ := #[
    88261029564833669043978240, 4958484807013127474380800, 3752765197539205683131449344, 131337425485470340466796920832, 131337489901500645860551163904, 3752732989524052986254327808,
    275088623772322837048816828416, 2771396328335777207980916736, 155696422940212202695557120, 934413565689054965904688807936, 4208993300150403212869894144, 275088623772322837048816828416,
    4208993300150403212869894144, 4208993300150403212869894144, 2771396328335777207980916736, 155696422940212202695557120, 11912074027623661956789499330560, 11912069566098333140650427416576,
    20052151104032829522504056832, 88261029564833669043978240, 4958484807013127474380800, 68033078158203172180157530112, 134044372616254879390760960, 20052151104032829522504056832,
    134044372616254879390760960, 134044372616254879390760960, 88261029564833669043978240, 4958484807013127474380800, 79498961897858014528678133760, 79498961897858014528678133760,
    23936887066463592357474336768, 160853247139505855268913152, 4289419923720156140504350720, 4101757802057399309357285376, 134044372616254879390760960, 4208993300150403212869894144,
    134044372616254879390760960, 4101757802057399309357285376, 2332372083522834901399240704, 4208993300150403212869894144, 65708551456488141877351022592, 2573651954232093684302610432,
    4289419923720156140504350720, 4101757802057399309357285376, 134044372616254879390760960, 2573651954232093684302610432, 134044372616254879390760960, 4128566676580650285235437568,
    2332372083522834901399240704, 160853247139505855268913152, 3752765197539205683131449344, 131337425485470340466796920832, 131337489901500645860551163904, 3752732989524052986254327808,
    160853247139505855268913152, 4289419923720156140504350720, 4101757802057399309357285376, 134044372616254879390760960, 4208993300150403212869894144, 134044372616254879390760960,
    4101757802057399309357285376, 2332372083522834901399240704, 4208993300150403212869894144, 65708551456488141877351022592
  ]
def negativeScales : Array ℕ := #[
    13, 9, 27, 31, 31, 27,
    29, 18, 14, 30, 19, 29,
    19, 19, 18, 14, 52, 52,
    31, 13, 9, 31, 14, 31,
    14, 14, 13, 9, 11, 11,
    22, 14, 14, 19, 14, 19,
    14, 19, 18, 19, 23, 14,
    14, 19, 14, 14, 14, 18,
    18, 14, 27, 31, 31, 27,
    14, 14, 19, 14, 19, 14,
    19, 18, 19, 23
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13189978948632521, 9036173612553486, 27600012588682020, 31729192832375999, 31729193539963075, 27600000206734123,
    29795811230887892, 18162671602636786, 14008866266557750, 30559975970955651, 19765533775481114, 29795811230887892,
    19765533775481114, 19765533775481114, 18162671602636786, 14008866266557750, 52232195566201872, 52232195025857541,
    31017743667623897, 13189978948632521, 9036173612553486, 31780223022632694, 14792841121720145, 31017743667623897,
    14792841121720145, 14792841121720145, 13189978948632521, 9036173612553486, 11004922678569046, 11004922678569046,
    22273222202369600, 14055875526996034, 14792841121720145, 19728300869106443, 14792841121720145, 19765533775481114,
    14792841121720145, 19728300869106443, 18913856527711209, 19765533775481114, 23730067795286271, 14055875526996034,
    14792841121720145, 19728300869106443, 14792841121720145, 14055875526996034, 14792841121720145, 18737699567141241,
    18913856527711209, 14055875526996034, 27600012588682020, 31729192832375999, 31729193539963075, 27600000206734123,
    14055875526996034, 14792841121720145, 19728300869106443, 14792841121720145, 19765533775481114, 14792841121720145,
    19728300869106443, 18913856527711209, 19765533775481114, 23730067795286271
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
noncomputable def negativeCeiling : ℝ := 247666191 / 15625000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 88261029564833669043978240, coefficient := (-88261029564833669043978240) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 3752765197539205683131449344, coefficient := (-3752765197539205683131449344) }, { argument := 131337425485470340466796920832, coefficient := (-131337425485470340466796920832) }, { argument := 131337489901500645860551163904, coefficient := (-131337489901500645860551163904) }, { argument := 3752732989524052986254327808, coefficient := (-3752732989524052986254327808) }, { argument := 275088623772322837048816828416, coefficient := (-275088623772322837048816828416) }, { argument := 2771396328335777207980916736, coefficient := (-2771396328335777207980916736) }, { argument := 155696422940212202695557120, coefficient := (-155696422940212202695557120) }, { argument := 934413565689054965904688807936, coefficient := (-934413565689054965904688807936) }, { argument := 4208993300150403212869894144, coefficient := (-4208993300150403212869894144) }, { argument := 275088623772322837048816828416, coefficient := (-275088623772322837048816828416) }, { argument := 4208993300150403212869894144, coefficient := (-4208993300150403212869894144) }, { argument := 4208993300150403212869894144, coefficient := (-4208993300150403212869894144) }, { argument := 2771396328335777207980916736, coefficient := (-2771396328335777207980916736) }, { argument := 155696422940212202695557120, coefficient := (-155696422940212202695557120) }, { argument := 11912074027623661956789499330560, coefficient := (-11912074027623661956789499330560) }, { argument := 11912069566098333140650427416576, coefficient := (-11912069566098333140650427416576) }, { argument := 20052151104032829522504056832, coefficient := (-20052151104032829522504056832) }, { argument := 88261029564833669043978240, coefficient := (-88261029564833669043978240) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 68033078158203172180157530112, coefficient := (-68033078158203172180157530112) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 20052151104032829522504056832, coefficient := (-20052151104032829522504056832) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 88261029564833669043978240, coefficient := (-88261029564833669043978240) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 79498961897858014528678133760, coefficient := (-79498961897858014528678133760) }, { argument := 79498961897858014528678133760, coefficient := (-79498961897858014528678133760) }, { argument := 23936887066463592357474336768, coefficient := (-23936887066463592357474336768) }, { argument := 160853247139505855268913152, coefficient := (-160853247139505855268913152) }, { argument := 4289419923720156140504350720, coefficient := (-4289419923720156140504350720) }, { argument := 4101757802057399309357285376, coefficient := (-4101757802057399309357285376) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 4208993300150403212869894144, coefficient := (-4208993300150403212869894144) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 4101757802057399309357285376, coefficient := (-4101757802057399309357285376) }, { argument := 2332372083522834901399240704, coefficient := (-2332372083522834901399240704) }, { argument := 4208993300150403212869894144, coefficient := (-4208993300150403212869894144) }, { argument := 65708551456488141877351022592, coefficient := (-65708551456488141877351022592) }, { argument := 2573651954232093684302610432, coefficient := (-2573651954232093684302610432) }, { argument := 4289419923720156140504350720, coefficient := (-4289419923720156140504350720) }, { argument := 4101757802057399309357285376, coefficient := (-4101757802057399309357285376) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 2573651954232093684302610432, coefficient := (-2573651954232093684302610432) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 4128566676580650285235437568, coefficient := (-4128566676580650285235437568) }, { argument := 2332372083522834901399240704, coefficient := (-2332372083522834901399240704) }, { argument := 160853247139505855268913152, coefficient := (-160853247139505855268913152) }, { argument := 3752765197539205683131449344, coefficient := (-3752765197539205683131449344) }, { argument := 131337425485470340466796920832, coefficient := (-131337425485470340466796920832) }, { argument := 131337489901500645860551163904, coefficient := (-131337489901500645860551163904) }, { argument := 3752732989524052986254327808, coefficient := (-3752732989524052986254327808) }, { argument := 160853247139505855268913152, coefficient := (-160853247139505855268913152) }, { argument := 4289419923720156140504350720, coefficient := (-4289419923720156140504350720) }, { argument := 4101757802057399309357285376, coefficient := (-4101757802057399309357285376) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 4208993300150403212869894144, coefficient := (-4208993300150403212869894144) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 4101757802057399309357285376, coefficient := (-4101757802057399309357285376) }, { argument := 2332372083522834901399240704, coefficient := (-2332372083522834901399240704) }, { argument := 4208993300150403212869894144, coefficient := (-4208993300150403212869894144) }, { argument := 65708551456488141877351022592, coefficient := (-65708551456488141877351022592) }] }

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

end TermShard4


end Parent1

namespace Parent1

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1306020113861791307882734945304576)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    17031, 28385, 868581, 28385, 17031, 28385,
    437129, 493899, 17031, 17427838971, 304965456369, 304965605943,
    17427689397, 28263998007, 285957, 16065, 47954836041, 868581,
    28263998007, 868581, 868581, 285957, 16065, 203437809,
    3559908051, 3559909797, 203436063, 28260449847, 162603, 9135,
    47926746441, 493899, 28260449847, 493899, 493899, 162603,
    9135, 4809, 4809, 5607, 9345, 285957,
    9345, 293433, 9345, 285957, 162603, 293433,
    4580919, 5607, 9345, 285957, 9345, 5607,
    9345, 143913, 162603, 5607, 6758656099, 118268056361,
    118268114367, 6758598093, 932036511, 293433
  ]
def negativeCoefficients : Array ℕ := #[
    2573651954232093684302610432, 4289419923720156140504350720, 4101757802057399309357285376, 134044372616254879390760960, 2573651954232093684302610432, 134044372616254879390760960,
    4128566676580650285235437568, 2332372083522834901399240704, 160853247139505855268913152, 160743442627929310094130413568, 5625619724960979583327801442304, 5625622484114277664360274853888,
    160742063051280269577893707776, 521378737734965827971487629312, 2700787504683910272745734144, 151729635094601700716052480, 1769221175090059932801813184512, 4101757802057399309357285376,
    521378737734965827971487629312, 4101757802057399309357285376, 4101757802057399309357285376, 2700787504683910272745734144, 151729635094601700716052480, 3752765197539205683131449344,
    131337425485470340466796920832, 131337489901500645860551163904, 3752732989524052986254327808, 521313285735513254688825802752, 1535741914428105841365221376, 86277635642028418054225920,
    1768184851765394189159667597312, 2332372083522834901399240704, 521313285735513254688825802752, 2332372083522834901399240704, 2332372083522834901399240704, 1535741914428105841365221376,
    86277635642028418054225920, 93019588264428027218592006144, 93019588264428027218592006144, 105913235477800402852773888, 2824352946074677409407303680, 2700787504683910272745734144,
    88261029564833669043978240, 2771396328335777207980916736, 88261029564833669043978240, 2700787504683910272745734144, 1535741914428105841365221376, 2771396328335777207980916736,
    43265556692681464565358133248, 1694611767644806445644382208, 2824352946074677409407303680, 2700787504683910272745734144, 88261029564833669043978240, 1694611767644806445644382208,
    88261029564833669043978240, 2718439710596877006554529792, 1535741914428105841365221376, 105913235477800402852773888, 31168799835117291646008426496, 1090830283893211994432563314688,
    1090830818904130364230688833536, 31168532329658106746945667072, 275088623772322837048816828416, 2771396328335777207980916736
  ]
def negativeScales : Array ℕ := #[
    14, 14, 19, 14, 14, 14,
    18, 18, 14, 34, 38, 38,
    34, 34, 18, 13, 35, 19,
    34, 19, 19, 18, 13, 27,
    31, 31, 27, 34, 17, 13,
    35, 18, 34, 18, 18, 17,
    13, 12, 12, 12, 13, 18,
    13, 18, 13, 18, 17, 18,
    22, 12, 13, 18, 13, 12,
    13, 17, 17, 12, 32, 36,
    36, 32, 29, 18
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14055875526996034, 14792841121720145, 19728300869106443, 14792841121720145, 14055875526996034, 14792841121720145,
    18737699567141241, 18913856527711209, 14055875526996034, 34020674637149085, 38149854880706986, 38149855588294061,
    34020662255201190, 34718246501595563, 18125438696437810, 13971633375310864, 35480957261104856, 19728300869106443,
    34718246501595563, 19728300869106443, 19728300869106443, 18125438696437810, 13971633375310864, 27600012588682020,
    31729192832375999, 31729193539963075, 27600000206734123, 34718065379512986, 17310994349593887, 13157189013514852,
    35480111953242155, 18913856527711209, 34718065379512986, 18913856527711209, 18913856527711209, 17310994349593887,
    13157189013514852, 12231521210875705, 12231521210875705, 12453013354466367, 13189978948632521, 18125438696437810,
    13189978948632521, 18162671602636786, 13189978948632521, 18125438696437810, 17310994349593887, 18162671602636786,
    22127205622611998, 12453013354466367, 13189978948632521, 18125438696437810, 13189978948632521, 12453013354466367,
    13189978948632521, 17134837394440060, 17310994349593887, 12453013354466367, 32654089261455790, 36783269505447589,
    36783270213034671, 32654076879507888, 29795811230887892, 18162671602636786
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
noncomputable def negativeCeiling : ℝ := 8928299313 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2573651954232093684302610432, coefficient := (-2573651954232093684302610432) }, { argument := 4289419923720156140504350720, coefficient := (-4289419923720156140504350720) }, { argument := 4101757802057399309357285376, coefficient := (-4101757802057399309357285376) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 2573651954232093684302610432, coefficient := (-2573651954232093684302610432) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 4128566676580650285235437568, coefficient := (-4128566676580650285235437568) }, { argument := 2332372083522834901399240704, coefficient := (-2332372083522834901399240704) }, { argument := 160853247139505855268913152, coefficient := (-160853247139505855268913152) }, { argument := 160743442627929310094130413568, coefficient := (-160743442627929310094130413568) }, { argument := 5625619724960979583327801442304, coefficient := (-5625619724960979583327801442304) }, { argument := 5625622484114277664360274853888, coefficient := (-5625622484114277664360274853888) }, { argument := 160742063051280269577893707776, coefficient := (-160742063051280269577893707776) }, { argument := 521378737734965827971487629312, coefficient := (-521378737734965827971487629312) }, { argument := 2700787504683910272745734144, coefficient := (-2700787504683910272745734144) }, { argument := 151729635094601700716052480, coefficient := (-151729635094601700716052480) }, { argument := 1769221175090059932801813184512, coefficient := (-1769221175090059932801813184512) }, { argument := 4101757802057399309357285376, coefficient := (-4101757802057399309357285376) }, { argument := 521378737734965827971487629312, coefficient := (-521378737734965827971487629312) }, { argument := 4101757802057399309357285376, coefficient := (-4101757802057399309357285376) }, { argument := 4101757802057399309357285376, coefficient := (-4101757802057399309357285376) }, { argument := 2700787504683910272745734144, coefficient := (-2700787504683910272745734144) }, { argument := 151729635094601700716052480, coefficient := (-151729635094601700716052480) }, { argument := 3752765197539205683131449344, coefficient := (-3752765197539205683131449344) }, { argument := 131337425485470340466796920832, coefficient := (-131337425485470340466796920832) }, { argument := 131337489901500645860551163904, coefficient := (-131337489901500645860551163904) }, { argument := 3752732989524052986254327808, coefficient := (-3752732989524052986254327808) }, { argument := 521313285735513254688825802752, coefficient := (-521313285735513254688825802752) }, { argument := 1535741914428105841365221376, coefficient := (-1535741914428105841365221376) }, { argument := 86277635642028418054225920, coefficient := (-86277635642028418054225920) }, { argument := 1768184851765394189159667597312, coefficient := (-1768184851765394189159667597312) }, { argument := 2332372083522834901399240704, coefficient := (-2332372083522834901399240704) }, { argument := 521313285735513254688825802752, coefficient := (-521313285735513254688825802752) }, { argument := 2332372083522834901399240704, coefficient := (-2332372083522834901399240704) }, { argument := 2332372083522834901399240704, coefficient := (-2332372083522834901399240704) }, { argument := 1535741914428105841365221376, coefficient := (-1535741914428105841365221376) }, { argument := 86277635642028418054225920, coefficient := (-86277635642028418054225920) }, { argument := 93019588264428027218592006144, coefficient := (-93019588264428027218592006144) }, { argument := 93019588264428027218592006144, coefficient := (-93019588264428027218592006144) }, { argument := 105913235477800402852773888, coefficient := (-105913235477800402852773888) }, { argument := 2824352946074677409407303680, coefficient := (-2824352946074677409407303680) }, { argument := 2700787504683910272745734144, coefficient := (-2700787504683910272745734144) }, { argument := 88261029564833669043978240, coefficient := (-88261029564833669043978240) }, { argument := 2771396328335777207980916736, coefficient := (-2771396328335777207980916736) }, { argument := 88261029564833669043978240, coefficient := (-88261029564833669043978240) }, { argument := 2700787504683910272745734144, coefficient := (-2700787504683910272745734144) }, { argument := 1535741914428105841365221376, coefficient := (-1535741914428105841365221376) }, { argument := 2771396328335777207980916736, coefficient := (-2771396328335777207980916736) }, { argument := 43265556692681464565358133248, coefficient := (-43265556692681464565358133248) }, { argument := 1694611767644806445644382208, coefficient := (-1694611767644806445644382208) }, { argument := 2824352946074677409407303680, coefficient := (-2824352946074677409407303680) }, { argument := 2700787504683910272745734144, coefficient := (-2700787504683910272745734144) }, { argument := 88261029564833669043978240, coefficient := (-88261029564833669043978240) }, { argument := 1694611767644806445644382208, coefficient := (-1694611767644806445644382208) }, { argument := 88261029564833669043978240, coefficient := (-88261029564833669043978240) }, { argument := 2718439710596877006554529792, coefficient := (-2718439710596877006554529792) }, { argument := 1535741914428105841365221376, coefficient := (-1535741914428105841365221376) }, { argument := 105913235477800402852773888, coefficient := (-105913235477800402852773888) }, { argument := 31168799835117291646008426496, coefficient := (-31168799835117291646008426496) }, { argument := 1090830283893211994432563314688, coefficient := (-1090830283893211994432563314688) }, { argument := 1090830818904130364230688833536, coefficient := (-1090830818904130364230688833536) }, { argument := 31168532329658106746945667072, coefficient := (-31168532329658106746945667072) }, { argument := 275088623772322837048816828416, coefficient := (-275088623772322837048816828416) }, { argument := 2771396328335777207980916736, coefficient := (-2771396328335777207980916736) }] }

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

end TermShard5


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15
