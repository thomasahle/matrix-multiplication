import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 13, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-472642296234588976158814630183960576)
def positiveArguments : Array ℕ := #[
    3885, 3675, 4935, 135404051, 15800103717, 23103,
    82570631121, 23707, 755, 23103, 13137, 23707,
    370101, 453, 7900055005, 23103, 755, 453,
    755, 11627, 13137, 33850843, 5232295, 358489433,
    945, 837, 39177, 10665, 358489503, 39177,
    945, 945, 405, 945, 10665, 405,
    5232225, 837
  ]
def positiveCoefficients : Array ℕ := #[
    75146828947245349499735900160, 71084838193340195472723148800, 95456782716771119634799656960, 639427552087172066867199082496, 74613880219024898167389428908032, 893754022737816890343577092096,
    779857561750407280936471266066432, 917120140979328443032298061824, 29207647801889440860901212160, 893754022737816890343577092096, 508213071752876270979681091584, 917120140979328443032298061824,
    14317588952486203910013774200832, 560786837796277264529303273472, 74613909936877174866066758696960, 893754022737816890343577092096, 29207647801889440860901212160, 560786837796277264529303273472,
    29207647801889440860901212160, 899595552298194778515757334528, 508213071752876270979681091584, 639424345600330198378098982912, 197670516291891442427164098560, 13543347862897146604552342994944,
    36557916785146386243114762240, 32379869152558227815330217984, 1515586778721354469678843428864, 412582203718080644743723745280, 13543350507422377011553662664704, 1515586778721354469678843428864,
    36557916785146386243114762240, 36557916785146386243114762240, 31335357244411188208384081920, 36557916785146386243114762240, 412582203718080644743723745280, 31335357244411188208384081920,
    197667871766661035425844428800, 32379869152558227815330217984
  ]
def positiveScales : Array ℕ := #[
    11, 11, 12, 27, 33, 14,
    36, 14, 9, 14, 13, 14,
    18, 8, 32, 14, 9, 8,
    9, 13, 13, 25, 22, 28,
    9, 9, 15, 13, 28, 15,
    9, 9, 8, 9, 13, 8,
    22, 9
  ]
def negativeArguments : Array ℕ := #[
    29175, 3005, 399
  ]
def negativeCoefficients : Array ℕ := #[
    4622963282707324098583289502105600, 952322513421457337874398283038720, 31612036843191470699824036184064
  ]
def negativeScales : Array ℕ := #[
    14, 11, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11923698882884927, 11843528534516384, 12268834369343759, 27012695661011693, 33879214977439575, 14495792582017715,
    36264909681240167, 14533025488216656, 9560332834212327, 14495792582017715, 13681348235170925, 14533025488216656,
    18497559508191902, 8823367239982289, 32879215552048339, 14495792582017715, 9560332834212327, 8823367239982289,
    9560332834212327, 13505191280019959, 13681348235170925, 25012688426424680, 22319012452484171, 28417355353107866,
    9884170518905654, 9709083812544787, 15257719306230212, 13380596345227933, 28417355634813919, 15257719306230212,
    9884170518905654, 9884170518905654, 8661778097770205, 9884170518905654, 13380596345227933, 8661778097770205,
    22318993151330776, 9709083812544787
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    14832445036716284, 11553149275600011, 8640244936238936
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 3
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
noncomputable def positiveFloor : ℝ := 51916394419 / 125000000000
noncomputable def negativeCeiling : ℝ := 48055147167 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 75146828947245349499735900160, coefficient := 75146828947245349499735900160 }, { argument := 71084838193340195472723148800, coefficient := 71084838193340195472723148800 }, { argument := 95456782716771119634799656960, coefficient := 95456782716771119634799656960 }, { argument := 4622963282707324098583289502105600, coefficient := (-4622963282707324098583289502105600) }, { argument := 639427552087172066867199082496, coefficient := 639427552087172066867199082496 }, { argument := 74613880219024898167389428908032, coefficient := 74613880219024898167389428908032 }, { argument := 893754022737816890343577092096, coefficient := 893754022737816890343577092096 }, { argument := 779857561750407280936471266066432, coefficient := 779857561750407280936471266066432 }, { argument := 917120140979328443032298061824, coefficient := 917120140979328443032298061824 }, { argument := 29207647801889440860901212160, coefficient := 29207647801889440860901212160 }, { argument := 893754022737816890343577092096, coefficient := 893754022737816890343577092096 }, { argument := 508213071752876270979681091584, coefficient := 508213071752876270979681091584 }, { argument := 917120140979328443032298061824, coefficient := 917120140979328443032298061824 }, { argument := 14317588952486203910013774200832, coefficient := 14317588952486203910013774200832 }, { argument := 560786837796277264529303273472, coefficient := 560786837796277264529303273472 }, { argument := 74613909936877174866066758696960, coefficient := 74613909936877174866066758696960 }, { argument := 893754022737816890343577092096, coefficient := 893754022737816890343577092096 }, { argument := 29207647801889440860901212160, coefficient := 29207647801889440860901212160 }, { argument := 560786837796277264529303273472, coefficient := 560786837796277264529303273472 }, { argument := 29207647801889440860901212160, coefficient := 29207647801889440860901212160 }, { argument := 899595552298194778515757334528, coefficient := 899595552298194778515757334528 }, { argument := 508213071752876270979681091584, coefficient := 508213071752876270979681091584 }, { argument := 639424345600330198378098982912, coefficient := 639424345600330198378098982912 }, { argument := 952322513421457337874398283038720, coefficient := (-952322513421457337874398283038720) }, { argument := 197670516291891442427164098560, coefficient := 197670516291891442427164098560 }, { argument := 13543347862897146604552342994944, coefficient := 13543347862897146604552342994944 }, { argument := 36557916785146386243114762240, coefficient := 36557916785146386243114762240 }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 1515586778721354469678843428864, coefficient := 1515586778721354469678843428864 }, { argument := 412582203718080644743723745280, coefficient := 412582203718080644743723745280 }, { argument := 13543350507422377011553662664704, coefficient := 13543350507422377011553662664704 }, { argument := 1515586778721354469678843428864, coefficient := 1515586778721354469678843428864 }, { argument := 36557916785146386243114762240, coefficient := 36557916785146386243114762240 }, { argument := 36557916785146386243114762240, coefficient := 36557916785146386243114762240 }, { argument := 31335357244411188208384081920, coefficient := 31335357244411188208384081920 }, { argument := 36557916785146386243114762240, coefficient := 36557916785146386243114762240 }, { argument := 412582203718080644743723745280, coefficient := 412582203718080644743723745280 }, { argument := 31335357244411188208384081920, coefficient := 31335357244411188208384081920 }, { argument := 197667871766661035425844428800, coefficient := 197667871766661035425844428800 }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 31612036843191470699824036184064, coefficient := (-31612036843191470699824036184064) }] }

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

end TermShard8


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13
