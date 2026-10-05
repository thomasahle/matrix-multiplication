import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 9, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk9

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
def constantNumerator : ℤ := (-26792816205139266426336444416)
def positiveArguments : Array ℕ := #[
    9, 8386541, 8390675, 15337113, 26599637, 15349693,
    405827, 8186471, 16369865, 202899
  ]
def positiveCoefficients : Array ℕ := #[
    713053462628379038341895553024, 158417280502448308960461062144, 158495369554609041413714739200, 144854936750368625824729399296, 502452936901197124012404113408, 144973751491077626098305990656,
    3832927645287079016277213184, 154638065053537389288844427264, 154609003610201809492199342080, 3832653748031072576854818816
  ]
def positiveScales : Array ℕ := #[
    3, 22, 23, 23, 24, 23,
    18, 22, 23, 17
  ]
def negativeArguments : Array ℕ := #[
    3403622778223, 68656104133723, 137286409011213, 1701689821415, 11761057077627, 163187075389359,
    47082753917541, 3403622778223, 3405024459409, 3405024459409, 68690088111013, 137354351984627,
    1702390527769, 163187075389359, 283013801998945, 163321031553935, 68656104133723, 68690088111013,
    47082753917541, 163321031553935, 11780332380803, 137286409011213, 137354351984627, 1701689821415,
    1702390527769, 1, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    958034642232177196728844288, 38649950624168109109806104576, 38642688779120773188160585728, 957966205703094985534996480, 13241773068071022962040373248, 45933078244699889428284309504,
    13252617062413400522040016896, 958034642232177196728844288, 958429180411362311409762304, 958429180411362311409762304, 38669081902600585534616109056, 38661813025980131557939085312,
    958360668312441302892412928, 45933078244699889428284309504, 159322606652894504747364515840, 45970783553004167830553231360, 38649950624168109109806104576, 38669081902600585534616109056,
    13252617062413400522040016896, 45970783553004167830553231360, 13263475130121244696559747072, 38642688779120773188160585728, 38661813025980131557939085312, 957966205703094985534996480,
    958360668312441302892412928, 316912650057057350374175801344, 792281625142643375935439503360, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    41, 45, 46, 40, 43, 47,
    45, 41, 41, 41, 45, 46,
    40, 47, 48, 47, 45, 45,
    45, 47, 43, 46, 46, 40,
    40, 0, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 22999644466604992, 23000355444349392, 23870523605006391, 24664903221895728, 23871706465456408,
    18630505326396762, 22964810241610830, 23964539087546770, 17630402229138292
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    41630208291389029, 45964453241213341, 46964182151229763, 40630105229804997, 43419082968209435, 47213520127092401,
    45420263941061253, 41630208291389029, 41630802300288190, 41630802300288190, 45965167182045256, 46964895963805081,
    40630699167369894, 47213520127092401, 48007865740455104, 47214703913351081, 45964453241213341, 45965167182045256,
    45420263941061253, 47214703913351081, 43421445478762780, 46964182151229763, 46964895963805081, 40630105229804997,
    40630699167369894, 0, 2321928094887363, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 28
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
noncomputable def positiveFloor : ℝ := 218208777 / 500000000000
noncomputable def negativeCeiling : ℝ := 423773877 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 958034642232177196728844288, coefficient := (-958034642232177196728844288) }, { argument := 38649950624168109109806104576, coefficient := (-38649950624168109109806104576) }, { argument := 38642688779120773188160585728, coefficient := (-38642688779120773188160585728) }, { argument := 957966205703094985534996480, coefficient := (-957966205703094985534996480) }, { argument := 13241773068071022962040373248, coefficient := (-13241773068071022962040373248) }, { argument := 45933078244699889428284309504, coefficient := (-45933078244699889428284309504) }, { argument := 13252617062413400522040016896, coefficient := (-13252617062413400522040016896) }, { argument := 958034642232177196728844288, coefficient := (-958034642232177196728844288) }, { argument := 958429180411362311409762304, coefficient := (-958429180411362311409762304) }, { argument := 958429180411362311409762304, coefficient := (-958429180411362311409762304) }, { argument := 38669081902600585534616109056, coefficient := (-38669081902600585534616109056) }, { argument := 38661813025980131557939085312, coefficient := (-38661813025980131557939085312) }, { argument := 958360668312441302892412928, coefficient := (-958360668312441302892412928) }, { argument := 45933078244699889428284309504, coefficient := (-45933078244699889428284309504) }, { argument := 159322606652894504747364515840, coefficient := (-159322606652894504747364515840) }, { argument := 45970783553004167830553231360, coefficient := (-45970783553004167830553231360) }, { argument := 38649950624168109109806104576, coefficient := (-38649950624168109109806104576) }, { argument := 38669081902600585534616109056, coefficient := (-38669081902600585534616109056) }, { argument := 13252617062413400522040016896, coefficient := (-13252617062413400522040016896) }, { argument := 45970783553004167830553231360, coefficient := (-45970783553004167830553231360) }, { argument := 13263475130121244696559747072, coefficient := (-13263475130121244696559747072) }, { argument := 38642688779120773188160585728, coefficient := (-38642688779120773188160585728) }, { argument := 38661813025980131557939085312, coefficient := (-38661813025980131557939085312) }, { argument := 957966205703094985534996480, coefficient := (-957966205703094985534996480) }, { argument := 958360668312441302892412928, coefficient := (-958360668312441302892412928) }, { argument := 713053462628379038341895553024, coefficient := 713053462628379038341895553024 }, { argument := 158417280502448308960461062144, coefficient := 158417280502448308960461062144 }, { argument := 158495369554609041413714739200, coefficient := 158495369554609041413714739200 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 144854936750368625824729399296, coefficient := 144854936750368625824729399296 }, { argument := 502452936901197124012404113408, coefficient := 502452936901197124012404113408 }, { argument := 144973751491077626098305990656, coefficient := 144973751491077626098305990656 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 3832927645287079016277213184, coefficient := 3832927645287079016277213184 }, { argument := 154638065053537389288844427264, coefficient := 154638065053537389288844427264 }, { argument := 154609003610201809492199342080, coefficient := 154609003610201809492199342080 }, { argument := 3832653748031072576854818816, coefficient := 3832653748031072576854818816 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk9
