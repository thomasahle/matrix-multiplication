import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 3, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 90822593073116651490112765427712
def positiveArguments : Array ℕ := #[
    15, 5, 1, 1, 1, 1,
    22835, 1686305, 17576075, 1686305, 22835
  ]
def positiveCoefficients : Array ℕ := #[
    1188422437713965063903159255040, 792281625142643375935439503360, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168,
    431340954545313393818992640, 63706801695163976576653066240, 664005339843224795994495385600, 63706801695163976576653066240, 431340954545313393818992640
  ]
def positiveScales : Array ℕ := #[
    3, 2, 0, 0, 0, 0,
    14, 20, 24, 20, 14
  ]
def negativeArguments : Array ℕ := #[
    22835, 1686305, 51717035, 49449557, 51717035, 49449557,
    17576075, 4339719253, 4149048747, 4339719253, 4149048747, 2061116764281,
    9982063808391, 2061116764281, 1686305, 2169859743, 2074524513, 2169859743,
    2074524513, 9982063808391, 48343499796601, 9982063808391, 51717035, 4339719253,
    2169859743, 25858401, 49449557, 4149048747, 2074524513, 24724639,
    22835, 25858401, 24724639, 25858401, 24724639, 2061116764281,
    9982063808391, 2061116764281, 51717035, 4339719253, 2169859743, 25858401,
    49449557, 4149048747, 2074524513, 24724639, 22835, 1686305,
    17576075, 1686305, 22835, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    215670477272656696909496320, 31853400847581988288326533120, 238502727224019865189744640, 228045830634328168519958528, 238502727224019865189744640, 228045830634328168519958528,
    332002669921612397997247692800, 20013422602960248069488115712, 19134110096313572693574156288, 20013422602960248069488115712, 19134110096313572693574156288, 580152793223937127492878336,
    5619402355982277722863828992, 580152793223937127492878336, 31853400847581988288326533120, 20013423677483090363069497344, 19134111382973971834815381504, 20013423677483090363069497344,
    19134111382973971834815381504, 5619402355982277722863828992, 54429941917439478192117121024, 5619402355982277722863828992, 238502727224019865189744640, 20013422602960248069488115712,
    20013423677483090363069497344, 238501652701177571608363008, 228045830634328168519958528, 19134110096313572693574156288, 19134111382973971834815381504, 228044543973929027278733312,
    215670477272656696909496320, 238501652701177571608363008, 228044543973929027278733312, 238501652701177571608363008, 228044543973929027278733312, 580152793223937127492878336,
    5619402355982277722863828992, 580152793223937127492878336, 238502727224019865189744640, 20013422602960248069488115712, 20013423677483090363069497344, 238501652701177571608363008,
    228045830634328168519958528, 19134110096313572693574156288, 19134111382973971834815381504, 228044543973929027278733312, 215670477272656696909496320, 31853400847581988288326533120,
    332002669921612397997247692800, 31853400847581988288326533120, 215670477272656696909496320, 792281625142643375935439503360, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    14, 20, 25, 25, 25, 25,
    24, 32, 31, 32, 31, 40,
    43, 40, 20, 31, 30, 31,
    30, 43, 45, 43, 25, 32,
    31, 24, 25, 31, 30, 24,
    14, 24, 24, 24, 24, 40,
    43, 40, 25, 32, 31, 24,
    25, 31, 30, 24, 14, 20,
    24, 20, 14, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3906890595303263, 2321928094887362, 0, 0, 0, 0,
    14478959169265707, 20685434067755166, 24067109595315291, 20685434067755166, 14478959169265707
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    14478959169265849, 20685434067809537, 25624136230294526, 25559454260692818, 25624136230294526, 25559454260692818,
    24067109595315292, 32014954568221541, 31950133471906594, 32014954568221541, 31950133471906594, 40906563380836736,
    43182475264663173, 40906563380836736, 20685434067809537, 31014954645679993, 30950133568919668, 31014954645679993,
    30950133568919668, 43182475264663173, 45458387153400366, 43182475264663173, 25624136230294526, 32014954568221541,
    31014954645679993, 24624129730527054, 25559454260692818, 31950133471906594, 30950133568919668, 24559446120821071,
    14478959169265849, 24624129730527054, 24559446120821071, 24624129730527054, 24559446120821071, 40906563380836736,
    43182475264663173, 40906563380836736, 25624136230294526, 32014954568221541, 31014954645679993, 24624129730527054,
    25559454260692818, 31950133471906594, 30950133568919668, 24559446120821071, 14478959169265849, 20685434067809537,
    24067109595315292, 20685434067809537, 14478959169265849, 2321928094887363, 0
  ]

abbrev PositiveTerm := Fin 11
abbrev NegativeTerm := Fin 53
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
noncomputable def positiveFloor : ℝ := 302268001 / 1000000000000
noncomputable def negativeCeiling : ℝ := 408801087 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 215670477272656696909496320, coefficient := (-215670477272656696909496320) }, { argument := 31853400847581988288326533120, coefficient := (-31853400847581988288326533120) }, { argument := 238502727224019865189744640, coefficient := (-238502727224019865189744640) }, { argument := 228045830634328168519958528, coefficient := (-228045830634328168519958528) }, { argument := 238502727224019865189744640, coefficient := (-238502727224019865189744640) }, { argument := 228045830634328168519958528, coefficient := (-228045830634328168519958528) }, { argument := 332002669921612397997247692800, coefficient := (-332002669921612397997247692800) }, { argument := 20013422602960248069488115712, coefficient := (-20013422602960248069488115712) }, { argument := 19134110096313572693574156288, coefficient := (-19134110096313572693574156288) }, { argument := 20013422602960248069488115712, coefficient := (-20013422602960248069488115712) }, { argument := 19134110096313572693574156288, coefficient := (-19134110096313572693574156288) }, { argument := 580152793223937127492878336, coefficient := (-580152793223937127492878336) }, { argument := 5619402355982277722863828992, coefficient := (-5619402355982277722863828992) }, { argument := 580152793223937127492878336, coefficient := (-580152793223937127492878336) }, { argument := 31853400847581988288326533120, coefficient := (-31853400847581988288326533120) }, { argument := 20013423677483090363069497344, coefficient := (-20013423677483090363069497344) }, { argument := 19134111382973971834815381504, coefficient := (-19134111382973971834815381504) }, { argument := 20013423677483090363069497344, coefficient := (-20013423677483090363069497344) }, { argument := 19134111382973971834815381504, coefficient := (-19134111382973971834815381504) }, { argument := 5619402355982277722863828992, coefficient := (-5619402355982277722863828992) }, { argument := 54429941917439478192117121024, coefficient := (-54429941917439478192117121024) }, { argument := 5619402355982277722863828992, coefficient := (-5619402355982277722863828992) }, { argument := 238502727224019865189744640, coefficient := (-238502727224019865189744640) }, { argument := 20013422602960248069488115712, coefficient := (-20013422602960248069488115712) }, { argument := 20013423677483090363069497344, coefficient := (-20013423677483090363069497344) }, { argument := 238501652701177571608363008, coefficient := (-238501652701177571608363008) }, { argument := 228045830634328168519958528, coefficient := (-228045830634328168519958528) }, { argument := 19134110096313572693574156288, coefficient := (-19134110096313572693574156288) }, { argument := 19134111382973971834815381504, coefficient := (-19134111382973971834815381504) }, { argument := 228044543973929027278733312, coefficient := (-228044543973929027278733312) }, { argument := 215670477272656696909496320, coefficient := (-215670477272656696909496320) }, { argument := 238501652701177571608363008, coefficient := (-238501652701177571608363008) }, { argument := 228044543973929027278733312, coefficient := (-228044543973929027278733312) }, { argument := 238501652701177571608363008, coefficient := (-238501652701177571608363008) }, { argument := 228044543973929027278733312, coefficient := (-228044543973929027278733312) }, { argument := 580152793223937127492878336, coefficient := (-580152793223937127492878336) }, { argument := 5619402355982277722863828992, coefficient := (-5619402355982277722863828992) }, { argument := 580152793223937127492878336, coefficient := (-580152793223937127492878336) }, { argument := 238502727224019865189744640, coefficient := (-238502727224019865189744640) }, { argument := 20013422602960248069488115712, coefficient := (-20013422602960248069488115712) }, { argument := 20013423677483090363069497344, coefficient := (-20013423677483090363069497344) }, { argument := 238501652701177571608363008, coefficient := (-238501652701177571608363008) }, { argument := 228045830634328168519958528, coefficient := (-228045830634328168519958528) }, { argument := 19134110096313572693574156288, coefficient := (-19134110096313572693574156288) }, { argument := 19134111382973971834815381504, coefficient := (-19134111382973971834815381504) }, { argument := 228044543973929027278733312, coefficient := (-228044543973929027278733312) }, { argument := 215670477272656696909496320, coefficient := (-215670477272656696909496320) }, { argument := 31853400847581988288326533120, coefficient := (-31853400847581988288326533120) }, { argument := 332002669921612397997247692800, coefficient := (-332002669921612397997247692800) }, { argument := 31853400847581988288326533120, coefficient := (-31853400847581988288326533120) }, { argument := 215670477272656696909496320, coefficient := (-215670477272656696909496320) }, { argument := 1188422437713965063903159255040, coefficient := 1188422437713965063903159255040 }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 431340954545313393818992640, coefficient := 431340954545313393818992640 }, { argument := 63706801695163976576653066240, coefficient := 63706801695163976576653066240 }, { argument := 664005339843224795994495385600, coefficient := 664005339843224795994495385600 }, { argument := 63706801695163976576653066240, coefficient := 63706801695163976576653066240 }, { argument := 431340954545313393818992640, coefficient := 431340954545313393818992640 }] }

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


end Parent1

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-90030311447974008114177325924352)
def positiveArguments : Array ℕ := #[
    197591, 16579625, 8289813, 98795, 1435659, 6952949,
    1435659, 535, 489, 535, 489
  ]
def positiveCoefficients : Array ℕ := #[
    1866194231433392134838812672, 156590130797095283052249088000, 156590140241828248791539515392, 1866184786700426395548385280, 13559415884860303955699171328, 131337493258808067275689558016,
    13559415884860303955699171328, 41393620063604902941939466240, 37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096
  ]
def positiveScales : Array ℕ := #[
    17, 23, 22, 16, 20, 22,
    20, 9, 8, 9, 8
  ]
def negativeArguments : Array ℕ := #[
    5, 1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    792281625142643375935439503360, 316912650057057350374175801344, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    2, 0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    17592157710068273, 23982908039251116, 22982908126267256, 16592150408628979, 20453281687963018, 22729193576691355,
    20453281687963018, 9063395081288509, 8933690654464738, 9063395081288509, 8933690654464738
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2321928094887363, 0, 0, 0
  ]

abbrev PositiveTerm := Fin 11
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 149071551 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1383977 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 1866194231433392134838812672, coefficient := 1866194231433392134838812672 }, { argument := 156590130797095283052249088000, coefficient := 156590130797095283052249088000 }, { argument := 156590140241828248791539515392, coefficient := 156590140241828248791539515392 }, { argument := 1866184786700426395548385280, coefficient := 1866184786700426395548385280 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 13559415884860303955699171328, coefficient := 13559415884860303955699171328 }, { argument := 131337493258808067275689558016, coefficient := 131337493258808067275689558016 }, { argument := 13559415884860303955699171328, coefficient := 13559415884860303955699171328 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3
