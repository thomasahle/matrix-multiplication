import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 10, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk10

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    547, 689, 831, 833, 941, 1819,
    2729, 7263, 10423, 11469, 23213, 34045,
    137045
  ]
def positiveCoefficients : Array ℕ := #[
    1429909877057442764888281215664128, 305186882004946228410331296694272, 800283669556584074032387442343936, 801234407506755246083509969747968, 5149830563427181943580356771840, 1336975242428210696891054161920000,
    303443862429632412983273329786880, 1338322121190953190630144409075712, 6606361103089417525900068754817024, 158377096866014410849494356721664, 160595485416413812302113587331072, 1485211134492399272528574892998656,
    1488301032830455581694723107061760
  ]
def positiveScales : Array ℕ := #[
    9, 9, 9, 9, 9, 10,
    11, 12, 13, 13, 14, 15,
    17
  ]
def negativeArguments : Array ℕ := #[
    3, 27, 33, 49, 67, 209,
    409, 463, 471, 507, 719, 1005,
    1165, 1167, 1445, 1671, 6683, 8741,
    8759, 10101, 10113, 18595, 5189033793941
  ]
def negativeCoefficients : Array ℕ := #[
    4753689750855860255612637020160, 4278320775770274230051373318144, 13072646814853615702934751805440, 3882179963198952542083653566464, 42466295107645684950139557380096, 33117371930962493114101371240448,
    32404318468334114075759475687424, 73365278488208776611621698011136, 69403870362495559731944500494336, 80337356789464038319853565640704, 113930097695512117459516200583168, 79624303326835659281511670087680,
    184601618658235906592957404282880, 184918531308292963943331580084224, 114484694833111967822671008235520, 529561038245342832475247764045824, 529481810082828568137654220095488, 692533368537184574905167669886976,
    693959475462441332981851460993024, 800283669556584074032387442343936, 801234407506755246083509969747968, 1473247681952745357551949756497920, 3303180551544708762950034377408512
  ]
def negativeScales : Array ℕ := #[
    1, 4, 5, 5, 6, 7,
    8, 8, 8, 8, 9, 9,
    10, 10, 10, 10, 12, 13,
    13, 13, 13, 14, 42
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9095397022792556, 9428360172704289, 9698704666765984, 9702172685360817, 9878050912547269, 10828929827580148,
    11414156679274139, 12826349864652276, 13347482960639703, 13485451985555794, 14502645365197540, 15055155312738924,
    17064290167746122
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 4754887502413606, 5044394119358454, 5614709844123661, 6066089190457773, 7707359132166870,
    8675957032982435, 8854868385160488, 8879583252627603, 8985841955861171, 9489847960439491, 9972979801353332,
    10186114239541643, 10188588845707349, 10496853777388286, 10706496018145465, 12706280158933015, 13093582623027909,
    13096550453872924, 13302210506548803, 13303923412705367, 14182627127499351, 42238603070206709
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 23
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
noncomputable def positiveFloor : ℝ := 311423906727 / 125000000000
noncomputable def negativeCeiling : ℝ := 2672395353521 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-4753689750855860255612637020160) }, { argument := 27, coefficient := (-4278320775770274230051373318144) }, { argument := 33, coefficient := (-13072646814853615702934751805440) }, { argument := 49, coefficient := (-3882179963198952542083653566464) }, { argument := 67, coefficient := (-42466295107645684950139557380096) }, { argument := 209, coefficient := (-33117371930962493114101371240448) }, { argument := 409, coefficient := (-32404318468334114075759475687424) }, { argument := 463, coefficient := (-73365278488208776611621698011136) }, { argument := 471, coefficient := (-69403870362495559731944500494336) }, { argument := 507, coefficient := (-80337356789464038319853565640704) }, { argument := 547, coefficient := 1429909877057442764888281215664128 }, { argument := 689, coefficient := 305186882004946228410331296694272 }, { argument := 719, coefficient := (-113930097695512117459516200583168) }, { argument := 831, coefficient := 800283669556584074032387442343936 }, { argument := 833, coefficient := 801234407506755246083509969747968 }, { argument := 941, coefficient := 5149830563427181943580356771840 }, { argument := 1005, coefficient := (-79624303326835659281511670087680) }, { argument := 1165, coefficient := (-184601618658235906592957404282880) }, { argument := 1167, coefficient := (-184918531308292963943331580084224) }, { argument := 1445, coefficient := (-114484694833111967822671008235520) }, { argument := 1671, coefficient := (-529561038245342832475247764045824) }, { argument := 1819, coefficient := 1336975242428210696891054161920000 }, { argument := 2729, coefficient := 303443862429632412983273329786880 }, { argument := 6683, coefficient := (-529481810082828568137654220095488) }, { argument := 7263, coefficient := 1338322121190953190630144409075712 }, { argument := 8741, coefficient := (-692533368537184574905167669886976) }, { argument := 8759, coefficient := (-693959475462441332981851460993024) }, { argument := 10101, coefficient := (-800283669556584074032387442343936) }, { argument := 10113, coefficient := (-801234407506755246083509969747968) }, { argument := 10423, coefficient := 6606361103089417525900068754817024 }, { argument := 11469, coefficient := 158377096866014410849494356721664 }, { argument := 18595, coefficient := (-1473247681952745357551949756497920) }, { argument := 23213, coefficient := 160595485416413812302113587331072 }, { argument := 34045, coefficient := 1485211134492399272528574892998656 }, { argument := 137045, coefficient := 1488301032830455581694723107061760 }, { argument := 5189033793941, coefficient := (-3303180551544708762950034377408512) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk10
