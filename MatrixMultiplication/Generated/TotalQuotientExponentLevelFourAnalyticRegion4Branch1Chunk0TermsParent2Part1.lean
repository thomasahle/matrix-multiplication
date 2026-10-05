import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 4, branch 1,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 25030238991804120958229240872960
def positiveArguments : Array ℕ := #[
    3, 17, 17, 137, 19, 61,
    19, 17, 137, 61, 2405, 61,
    17, 17, 19, 61, 19, 137,
    137, 9, 686545, 24479295, 12239217, 343687,
    38367, 649691, 14101729, 324845, 19179
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 657655645870358271040159744, 5261245166962866168321277952, 5299930793190534301911875584, 735026898325694538221355008, 4719646399775512298052911104,
    735026898325694538221355008, 5261245166962866168321277952, 5299930793190534301911875584, 4719646399775512298052911104, 93038931077541861285387304960, 4719646399775512298052911104,
    5261245166962866168321277952, 5261245166962866168321277952, 735026898325694538221355008, 4719646399775512298052911104, 735026898325694538221355008, 5299930793190534301911875584,
    5299930793190534301911875584, 696341272098026404630757376, 6484234193963481146473840640, 231200404464556983462804848640, 231192272549473481933746864128, 6492063877592079018238148608,
    724732139393038711655497728, 24544632020976501348250943488, 266374129520443516518752321536, 24544594242044638391089233920, 724562134199655404427804672
  ]
def positiveScales : Array ℕ := #[
    1, 4, 4, 7, 4, 5,
    4, 4, 7, 5, 11, 5,
    4, 4, 4, 5, 4, 7,
    7, 3, 19, 24, 23, 18,
    15, 19, 23, 18, 14
  ]
def negativeArguments : Array ℕ := #[
    4217563, 155165989, 9697885, 263587, 13540597, 498164491,
    31135315, 846253, 4217563, 155165989, 9697885, 263587,
    30410849, 1118828447, 69926855, 1900601, 30410849, 1118828447,
    69926855, 1900601, 2136613725, 76739408505, 306949457043, 8554325013,
    1, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    4862519079734167352639488, 178894205501689467202699264, 178894402651266754973532160, 4862321930156879581806592, 31222490933029916685369344, 1148689109010848157827858432,
    1148690374918660216145838080, 31221225025217858367389696, 4862519079734167352639488, 178894205501689467202699264, 178894402651266754973532160, 4862321930156879581806592,
    35061321785451627753242624, 1289921376512181947724726272, 1289922798064397127967047680, 35059900233236447510921216, 35061321785451627753242624, 1289921376512181947724726272,
    1289922798064397127967047680, 35059900233236447510921216, 9622452775744687413657600, 345603571547750271528468480, 345594365090107717249400832, 9631313735238228337754112,
    158456325028528675187087900672, 475368975085586025561263702016, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    22, 27, 23, 18, 23, 28,
    24, 19, 22, 27, 23, 18,
    24, 30, 26, 20, 24, 30,
    26, 20, 30, 36, 38, 32,
    0, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 4087462841250339, 4087462841250339, 7098032082960526, 4247927513443585, 5930737337099561,
    4247927513443585, 4087462841250339, 7098032082960526, 5930737337099561, 11231821178657404, 5930737337099561,
    4087462841250339, 4087462841250339, 4247927513443585, 5930737337099561, 4247927513443585, 7098032082960526,
    7098032082960526, 3169925001442312, 19388994760212161, 24545058673440973, 23545007929239569, 18390735757074478,
    15227578341406248, 19309394194481380, 23749368725176471, 18309391973893206, 14227239879225015
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    22007978188307374, 27209237125398283, 23209238715313171, 18007919693424586, 23690788012484870, 28892046953302166,
    24892048543217163, 19690729517602000, 22007978188307374, 27209237125398283, 23209238715313171, 18007919693424586,
    24858082759843787, 30059341694915224, 26059343284830112, 20858024264958768, 24858082759843787, 30059341694915224,
    26059343284830112, 20858024264958768, 30992678984071924, 36159248593796192, 38159210161647941, 32994006897504857,
    0, 1584962500724866, 0
  ]

abbrev PositiveTerm := Fin 29
abbrev NegativeTerm := Fin 27
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
noncomputable def positiveFloor : ℝ := 3911773 / 15625000000
noncomputable def negativeCeiling : ℝ := 12148881 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4862519079734167352639488, coefficient := (-4862519079734167352639488) }, { argument := 178894205501689467202699264, coefficient := (-178894205501689467202699264) }, { argument := 178894402651266754973532160, coefficient := (-178894402651266754973532160) }, { argument := 4862321930156879581806592, coefficient := (-4862321930156879581806592) }, { argument := 31222490933029916685369344, coefficient := (-31222490933029916685369344) }, { argument := 1148689109010848157827858432, coefficient := (-1148689109010848157827858432) }, { argument := 1148690374918660216145838080, coefficient := (-1148690374918660216145838080) }, { argument := 31221225025217858367389696, coefficient := (-31221225025217858367389696) }, { argument := 4862519079734167352639488, coefficient := (-4862519079734167352639488) }, { argument := 178894205501689467202699264, coefficient := (-178894205501689467202699264) }, { argument := 178894402651266754973532160, coefficient := (-178894402651266754973532160) }, { argument := 4862321930156879581806592, coefficient := (-4862321930156879581806592) }, { argument := 35061321785451627753242624, coefficient := (-35061321785451627753242624) }, { argument := 1289921376512181947724726272, coefficient := (-1289921376512181947724726272) }, { argument := 1289922798064397127967047680, coefficient := (-1289922798064397127967047680) }, { argument := 35059900233236447510921216, coefficient := (-35059900233236447510921216) }, { argument := 35061321785451627753242624, coefficient := (-35061321785451627753242624) }, { argument := 1289921376512181947724726272, coefficient := (-1289921376512181947724726272) }, { argument := 1289922798064397127967047680, coefficient := (-1289922798064397127967047680) }, { argument := 35059900233236447510921216, coefficient := (-35059900233236447510921216) }, { argument := 9622452775744687413657600, coefficient := (-9622452775744687413657600) }, { argument := 345603571547750271528468480, coefficient := (-345603571547750271528468480) }, { argument := 345594365090107717249400832, coefficient := (-345594365090107717249400832) }, { argument := 9631313735238228337754112, coefficient := (-9631313735238228337754112) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 657655645870358271040159744, coefficient := 657655645870358271040159744 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 5299930793190534301911875584, coefficient := 5299930793190534301911875584 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 5299930793190534301911875584, coefficient := 5299930793190534301911875584 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 93038931077541861285387304960, coefficient := 93038931077541861285387304960 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 5299930793190534301911875584, coefficient := 5299930793190534301911875584 }, { argument := 5299930793190534301911875584, coefficient := 5299930793190534301911875584 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 6484234193963481146473840640, coefficient := 6484234193963481146473840640 }, { argument := 231200404464556983462804848640, coefficient := 231200404464556983462804848640 }, { argument := 231192272549473481933746864128, coefficient := 231192272549473481933746864128 }, { argument := 6492063877592079018238148608, coefficient := 6492063877592079018238148608 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 724732139393038711655497728, coefficient := 724732139393038711655497728 }, { argument := 24544632020976501348250943488, coefficient := 24544632020976501348250943488 }, { argument := 266374129520443516518752321536, coefficient := 266374129520443516518752321536 }, { argument := 24544594242044638391089233920, coefficient := 24544594242044638391089233920 }, { argument := 724562134199655404427804672, coefficient := 724562134199655404427804672 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk0
