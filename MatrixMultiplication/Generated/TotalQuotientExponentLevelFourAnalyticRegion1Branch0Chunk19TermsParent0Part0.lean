import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 19, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk19

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    43, 191, 257, 527, 1055, 2255,
    4505, 7095, 9595, 9605, 30259, 30445,
    42327, 61165
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 294887220878091864523170583150592, 133895594649106730533089276067840, 4357548938284538567644917268480, 4436777100798802905238461218816, 5070602400912917605986812821504,
    4991374238398653268393268871168, 1124247626077410950452388655267840, 114009325858026381797109744533504, 114009325858026381797109744533504, 111632480982598451669303426023424, 112187078120198302032458233675776,
    325152378958540841483904372178944, 328242277296597150650052586242048
  ]
def positiveScales : Array ℕ := #[
    5, 7, 8, 9, 10, 11,
    12, 12, 13, 13, 14, 14,
    15, 15
  ]
def negativeArguments : Array ℕ := #[
    7, 9, 23, 27, 47, 53,
    55, 401, 513, 583, 779, 787,
    803, 1269, 1439, 2781380967823
  ]
def negativeCoefficients : Array ℕ := #[
    4436777100798802905238461218816, 1426106925256758076683791106048, 3644495475656159529303021715456, 4278320775770274230051373318144, 3723723638170423866896565665792, 4199092613256009892457829367808,
    4357548938284538567644917268480, 63540986336439998750022248169472, 325152378958540841483904372178944, 92380037491632217634072246091776, 61718738598611918985370737311744, 62352563898726033686119088914432,
    63620214498954263087615792119808, 201081076461202888812414545952768, 228018651716052763594219489067008, 562123813038705475226194327633920
  ]
def negativeScales : Array ℕ := #[
    2, 3, 4, 4, 5, 5,
    5, 8, 9, 9, 9, 9,
    9, 10, 10, 41
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5426264754702096, 7577428828035562, 8005624549193878, 9041659151637214, 10043027283594547, 11138911718142743,
    12137311390700900, 12792586968913521, 13228067091082742, 13229569898552889, 14885076689472963, 14893917692249923,
    15369290618300293, 15900418725484992
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2807354922807594, 3169925001442313, 4523561956057598, 4754887502413606, 5554588851679165, 5727920454700926,
    5781359713964302, 8647458426474890, 9002815015607055, 9187352073200497, 9605479518068246, 9620219825517287,
    9649256177538221, 10309476353841107, 10490850876740497, 41338938503881782
  ]

abbrev PositiveTerm := Fin 14
abbrev NegativeTerm := Fin 16
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
noncomputable def positiveFloor : ℝ := 207373620303 / 500000000000
noncomputable def negativeCeiling : ℝ := 204380525731 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7, coefficient := (-4436777100798802905238461218816) }, { argument := 9, coefficient := (-1426106925256758076683791106048) }, { argument := 23, coefficient := (-3644495475656159529303021715456) }, { argument := 27, coefficient := (-4278320775770274230051373318144) }, { argument := 43, coefficient := 158456325028528675187087900672 }, { argument := 47, coefficient := (-3723723638170423866896565665792) }, { argument := 53, coefficient := (-4199092613256009892457829367808) }, { argument := 55, coefficient := (-4357548938284538567644917268480) }, { argument := 191, coefficient := 294887220878091864523170583150592 }, { argument := 257, coefficient := 133895594649106730533089276067840 }, { argument := 401, coefficient := (-63540986336439998750022248169472) }, { argument := 513, coefficient := (-325152378958540841483904372178944) }, { argument := 527, coefficient := 4357548938284538567644917268480 }, { argument := 583, coefficient := (-92380037491632217634072246091776) }, { argument := 779, coefficient := (-61718738598611918985370737311744) }, { argument := 787, coefficient := (-62352563898726033686119088914432) }, { argument := 803, coefficient := (-63620214498954263087615792119808) }, { argument := 1055, coefficient := 4436777100798802905238461218816 }, { argument := 1269, coefficient := (-201081076461202888812414545952768) }, { argument := 1439, coefficient := (-228018651716052763594219489067008) }, { argument := 2255, coefficient := 5070602400912917605986812821504 }, { argument := 4505, coefficient := 4991374238398653268393268871168 }, { argument := 7095, coefficient := 1124247626077410950452388655267840 }, { argument := 9595, coefficient := 114009325858026381797109744533504 }, { argument := 9605, coefficient := 114009325858026381797109744533504 }, { argument := 30259, coefficient := 111632480982598451669303426023424 }, { argument := 30445, coefficient := 112187078120198302032458233675776 }, { argument := 42327, coefficient := 325152378958540841483904372178944 }, { argument := 61165, coefficient := 328242277296597150650052586242048 }, { argument := 2781380967823, coefficient := (-562123813038705475226194327633920) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  rfl

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk19
