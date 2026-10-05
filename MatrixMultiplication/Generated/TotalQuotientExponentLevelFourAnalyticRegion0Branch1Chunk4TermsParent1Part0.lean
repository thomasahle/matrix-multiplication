import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 4, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk4

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
def constantNumerator : ℤ := (-623738196060970887611898920960)
def positiveArguments : Array ℕ := #[
    11, 41927969, 41958111, 18840933, 62973727, 4712159,
    1143023, 10197149, 5099995, 1154501
  ]
def positiveCoefficients : Array ℕ := #[
    1743019575313815427057966907392, 395998471000795031121688526848, 396283154141848344813750976512, 355895162020770532820068073472, 1189540070744732857096594259968, 356040667576840712328392474624,
    10795547008698220962188886016, 385237397267421758569559621632, 385344727212844419865976504320, 10903953653678976537714491392
  ]
def positiveScales : Array ℕ := #[
    3, 25, 25, 24, 25, 22,
    20, 23, 22, 20
  ]
def negativeArguments : Array ℕ := #[
    9584947115687, 85509145447367, 85532967777143, 9681192340577, 59153487977855, 49441860800047,
    59177471404485, 9584947115687, 9591796648281, 9591796648281, 85570625909817, 85594467650697,
    9688120308639, 49441860800047, 660907669413673, 197848707590171, 85509145447367, 85570625909817,
    59177471404485, 197848707590171, 1850045577585, 85532967777143, 85594467650697, 9681192340577,
    9688120308639, 5, 3, 5
  ]
def negativeCoefficients : Array ℕ := #[
    2697922766160867725957660672, 96274738893382891420944171008, 96301560452258464088805343232, 2725013388595292325137088512, 33300453301841611617741045760, 111333172937797801220721606656,
    33313954770745853571571384320, 2697922766160867725957660672, 2699850738188242755136782336, 2699850738188242755136782336, 96343959740327987863835639808, 96370803154163745844182908928,
    2726963438244195943720157184, 111333172937797801220721606656, 372057941712215084923382398976, 111378920722353542404193124352, 96274738893382891420944171008, 96343959740327987863835639808,
    33313954770745853571571384320, 111378920722353542404193124352, 33327458295320960188431728640, 96301560452258464088805343232, 96370803154163745844182908928, 2725013388595292325137088512,
    2726963438244195943720157184, 792281625142643375935439503360, 1901475900342344102245054808064, 792281625142643375935439503360
  ]
def negativeScales : Array ℕ := #[
    43, 46, 46, 43, 45, 45,
    45, 43, 43, 43, 46, 46,
    43, 45, 49, 47, 46, 46,
    45, 47, 40, 46, 46, 43,
    43, 2, 1, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3459431618637292, 25321409611624682, 25322446391881764, 24167367072959732, 25908246717391123, 22167956789443606,
    20124423003193356, 23281662512634004, 22282064402000710, 20138837992063240
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    43123907610589079, 46281143962142025, 46281545832261665, 43138321880146543, 45749528473160086, 45490798275250708,
    45750113286660905, 43123907610589079, 43124938211743022, 43124938211743022, 46282180876809409, 46282582785409354,
    43139353919411304, 45490798275250708, 49231442065839666, 47491390969628047, 46281143962142025, 46282180876809409,
    45750113286660905, 47491390969628047, 40750697952183615, 46281545832261665, 46282582785409354, 43138321880146543,
    43139353919411304, 2321928094887363, 1584962500724866, 2321928094887363
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
noncomputable def positiveFloor : ℝ := 220029519 / 200000000000
noncomputable def negativeCeiling : ℝ := 1062247293 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2697922766160867725957660672, coefficient := (-2697922766160867725957660672) }, { argument := 96274738893382891420944171008, coefficient := (-96274738893382891420944171008) }, { argument := 96301560452258464088805343232, coefficient := (-96301560452258464088805343232) }, { argument := 2725013388595292325137088512, coefficient := (-2725013388595292325137088512) }, { argument := 33300453301841611617741045760, coefficient := (-33300453301841611617741045760) }, { argument := 111333172937797801220721606656, coefficient := (-111333172937797801220721606656) }, { argument := 33313954770745853571571384320, coefficient := (-33313954770745853571571384320) }, { argument := 2697922766160867725957660672, coefficient := (-2697922766160867725957660672) }, { argument := 2699850738188242755136782336, coefficient := (-2699850738188242755136782336) }, { argument := 2699850738188242755136782336, coefficient := (-2699850738188242755136782336) }, { argument := 96343959740327987863835639808, coefficient := (-96343959740327987863835639808) }, { argument := 96370803154163745844182908928, coefficient := (-96370803154163745844182908928) }, { argument := 2726963438244195943720157184, coefficient := (-2726963438244195943720157184) }, { argument := 111333172937797801220721606656, coefficient := (-111333172937797801220721606656) }, { argument := 372057941712215084923382398976, coefficient := (-372057941712215084923382398976) }, { argument := 111378920722353542404193124352, coefficient := (-111378920722353542404193124352) }, { argument := 96274738893382891420944171008, coefficient := (-96274738893382891420944171008) }, { argument := 96343959740327987863835639808, coefficient := (-96343959740327987863835639808) }, { argument := 33313954770745853571571384320, coefficient := (-33313954770745853571571384320) }, { argument := 111378920722353542404193124352, coefficient := (-111378920722353542404193124352) }, { argument := 33327458295320960188431728640, coefficient := (-33327458295320960188431728640) }, { argument := 96301560452258464088805343232, coefficient := (-96301560452258464088805343232) }, { argument := 96370803154163745844182908928, coefficient := (-96370803154163745844182908928) }, { argument := 2725013388595292325137088512, coefficient := (-2725013388595292325137088512) }, { argument := 2726963438244195943720157184, coefficient := (-2726963438244195943720157184) }, { argument := 1743019575313815427057966907392, coefficient := 1743019575313815427057966907392 }, { argument := 395998471000795031121688526848, coefficient := 395998471000795031121688526848 }, { argument := 396283154141848344813750976512, coefficient := 396283154141848344813750976512 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 355895162020770532820068073472, coefficient := 355895162020770532820068073472 }, { argument := 1189540070744732857096594259968, coefficient := 1189540070744732857096594259968 }, { argument := 356040667576840712328392474624, coefficient := 356040667576840712328392474624 }, { argument := 1901475900342344102245054808064, coefficient := (-1901475900342344102245054808064) }, { argument := 10795547008698220962188886016, coefficient := 10795547008698220962188886016 }, { argument := 385237397267421758569559621632, coefficient := 385237397267421758569559621632 }, { argument := 385344727212844419865976504320, coefficient := 385344727212844419865976504320 }, { argument := 10903953653678976537714491392, coefficient := 10903953653678976537714491392 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk4
