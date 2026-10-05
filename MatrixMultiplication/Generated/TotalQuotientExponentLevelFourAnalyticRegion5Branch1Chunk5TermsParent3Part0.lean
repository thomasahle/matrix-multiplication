import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 5, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk5

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 2712392264552167345090788851712
def positiveArguments : Array ℕ := #[
    3, 714031, 1528235, 12225903, 714051, 32615,
    978897, 660057, 1959299, 61677
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 6743832124259791283161137152, 230940343742345352100886609920, 230940778200061776108246269952, 6744021018919106068969684992, 1232159862710347829157560320,
    36981683063853176726010986496, 398979974858686644584517206016, 37010111710080051990197436416, 1165045590255804431380512768
  ]
def positiveScales : Array ℕ := #[
    1, 19, 20, 23, 19, 14,
    19, 19, 20, 15
  ]
def negativeArguments : Array ℕ := #[
    7824990605, 466333068773, 5026210931483, 58344960961, 7386244847, 7824990605,
    8305284175, 132884785265, 7825245105, 8305284175, 1994601470789, 21519532327649,
    1996126247281, 62826374641, 466333068773, 1994601470789, 7978420826355, 466346333709,
    132884785265, 7978420826355, 86078291430825, 3992259965569, 1963327767, 5026210931483,
    21519532327649, 86078291430825, 5026351147659, 7825245105, 466346333709, 5026351147659,
    116693250843, 7386478029, 58344960961, 1996126247281, 3992259965569, 116693250843,
    7386244847, 62826374641, 1963327767, 7386478029, 3, 3
  ]
def negativeCoefficients : Array ℕ := #[
    8810156193213908013547520, 262522179344577835539890176, 2829505209764044050263965696, 262762344442905736203206656, 8316172385154111559958528, 8810156193213908013547520,
    299229397725888618325606400, 299229934701331188778270720, 8810442734740199461355520, 299229397725888618325606400, 8982886440597983662224441344, 96915357771987378836187643904,
    8989753423439178154299621376, 282944837422246779405991936, 262522179344577835539890176, 8982886440597983662224441344, 8982903265144345693016555520, 262529646839681172224606208,
    299229934701331188778270720, 8982903265144345693016555520, 96915540303138107241057484800, 8989770246651348795483226112, 282945350395755135787597824, 2829505209764044050263965696,
    96915357771987378836187643904, 96915540303138107241057484800, 2829584144453792164749508608, 8810442734740199461355520, 262529646839681172224606208, 2829584144453792164749508608,
    262769840506593309112664064, 8316434924746188936708096, 262762344442905736203206656, 8989753423439178154299621376, 8989770246651348795483226112, 262769840506593309112664064,
    8316172385154111559958528, 282944837422246779405991936, 282945350395755135787597824, 8316434924746188936708096, 475368975085586025561263702016, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    32, 38, 42, 35, 32, 32,
    32, 36, 32, 32, 40, 44,
    40, 35, 38, 40, 42, 38,
    36, 42, 46, 41, 30, 42,
    44, 46, 42, 32, 38, 42,
    36, 32, 35, 40, 41, 36,
    32, 35, 30, 32, 1, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 19445627185351416, 20543434976091961, 23543437690166917, 19445667594656792, 14993248006760339,
    19900797540930961, 19332231089917808, 20901906146793853, 15912444972766835
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32865441876193758, 38762569782254799, 42192608355712326, 35763889010242795, 32782193941739935, 32865441876193758,
    32951382397184618, 36951384986138973, 32865488797647298, 32951382397184618, 40859237659815702, 44290711958460312,
    40860340109209601, 35870651284046486, 38762569782254799, 40859237659815702, 42859240361916856, 38762610819416028,
    36951384986138973, 42859240361916856, 46290714675640994, 41860342809032598, 30870653899622397, 42192608355712326,
    44290711958460312, 46290714675640994, 42192648602005796, 32865488797647298, 38762610819416028, 42192648602005796,
    36763930166747722, 32782239486562108, 35763889010242795, 40860340109209601, 41860342809032598, 36763930166747722,
    32782193941739935, 35870651284046486, 30870653899622397, 32782239486562108, 1584962500724866, 1584962500724866
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 246241007 / 1000000000000
noncomputable def negativeCeiling : ℝ := 68292049 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8810156193213908013547520, coefficient := (-8810156193213908013547520) }, { argument := 262522179344577835539890176, coefficient := (-262522179344577835539890176) }, { argument := 2829505209764044050263965696, coefficient := (-2829505209764044050263965696) }, { argument := 262762344442905736203206656, coefficient := (-262762344442905736203206656) }, { argument := 8316172385154111559958528, coefficient := (-8316172385154111559958528) }, { argument := 8810156193213908013547520, coefficient := (-8810156193213908013547520) }, { argument := 299229397725888618325606400, coefficient := (-299229397725888618325606400) }, { argument := 299229934701331188778270720, coefficient := (-299229934701331188778270720) }, { argument := 8810442734740199461355520, coefficient := (-8810442734740199461355520) }, { argument := 299229397725888618325606400, coefficient := (-299229397725888618325606400) }, { argument := 8982886440597983662224441344, coefficient := (-8982886440597983662224441344) }, { argument := 96915357771987378836187643904, coefficient := (-96915357771987378836187643904) }, { argument := 8989753423439178154299621376, coefficient := (-8989753423439178154299621376) }, { argument := 282944837422246779405991936, coefficient := (-282944837422246779405991936) }, { argument := 262522179344577835539890176, coefficient := (-262522179344577835539890176) }, { argument := 8982886440597983662224441344, coefficient := (-8982886440597983662224441344) }, { argument := 8982903265144345693016555520, coefficient := (-8982903265144345693016555520) }, { argument := 262529646839681172224606208, coefficient := (-262529646839681172224606208) }, { argument := 299229934701331188778270720, coefficient := (-299229934701331188778270720) }, { argument := 8982903265144345693016555520, coefficient := (-8982903265144345693016555520) }, { argument := 96915540303138107241057484800, coefficient := (-96915540303138107241057484800) }, { argument := 8989770246651348795483226112, coefficient := (-8989770246651348795483226112) }, { argument := 282945350395755135787597824, coefficient := (-282945350395755135787597824) }, { argument := 2829505209764044050263965696, coefficient := (-2829505209764044050263965696) }, { argument := 96915357771987378836187643904, coefficient := (-96915357771987378836187643904) }, { argument := 96915540303138107241057484800, coefficient := (-96915540303138107241057484800) }, { argument := 2829584144453792164749508608, coefficient := (-2829584144453792164749508608) }, { argument := 8810442734740199461355520, coefficient := (-8810442734740199461355520) }, { argument := 262529646839681172224606208, coefficient := (-262529646839681172224606208) }, { argument := 2829584144453792164749508608, coefficient := (-2829584144453792164749508608) }, { argument := 262769840506593309112664064, coefficient := (-262769840506593309112664064) }, { argument := 8316434924746188936708096, coefficient := (-8316434924746188936708096) }, { argument := 262762344442905736203206656, coefficient := (-262762344442905736203206656) }, { argument := 8989753423439178154299621376, coefficient := (-8989753423439178154299621376) }, { argument := 8989770246651348795483226112, coefficient := (-8989770246651348795483226112) }, { argument := 262769840506593309112664064, coefficient := (-262769840506593309112664064) }, { argument := 8316172385154111559958528, coefficient := (-8316172385154111559958528) }, { argument := 282944837422246779405991936, coefficient := (-282944837422246779405991936) }, { argument := 282945350395755135787597824, coefficient := (-282945350395755135787597824) }, { argument := 8316434924746188936708096, coefficient := (-8316434924746188936708096) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 6743832124259791283161137152, coefficient := 6743832124259791283161137152 }, { argument := 230940343742345352100886609920, coefficient := 230940343742345352100886609920 }, { argument := 230940778200061776108246269952, coefficient := 230940778200061776108246269952 }, { argument := 6744021018919106068969684992, coefficient := 6744021018919106068969684992 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 1232159862710347829157560320, coefficient := 1232159862710347829157560320 }, { argument := 36981683063853176726010986496, coefficient := 36981683063853176726010986496 }, { argument := 398979974858686644584517206016, coefficient := 398979974858686644584517206016 }, { argument := 37010111710080051990197436416, coefficient := 37010111710080051990197436416 }, { argument := 1165045590255804431380512768, coefficient := 1165045590255804431380512768 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk5
