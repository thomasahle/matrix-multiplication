import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 2, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk2

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
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    1, 25557, 1288241, 7074807, 644125, 12777,
    39689, 8229809, 8231331, 19665
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 241379040405399045452857344, 12167092240516949239473897472, 133639325798286184181491826688, 12167177243113640893087744000, 241350706206501827581575168,
    1499408026708906791091044352, 77728348364037904012964528128, 77742723247611759212995018752, 1485845390170105170037309440
  ]
def positiveScales : Array ℕ := #[
    0, 14, 20, 22, 19, 13,
    15, 22, 22, 14
  ]
def negativeArguments : Array ℕ := #[
    1014331773, 210329228613, 210368126367, 502578405, 51128997049, 10601977375969,
    10603938078771, 25333259265, 1014331773, 51128997049, 280792015023, 25564677125,
    507106353, 280792015023, 58224310321863, 58235078178117, 139126079655, 210329228613,
    10601977375969, 58224310321863, 5301025722125, 105152269593, 25564677125, 5301025722125,
    5302006080375, 12666718125, 210368126367, 10603938078771, 58235078178117, 5302006080375,
    105171716187, 507106353, 105152269593, 105171716187, 251259705, 502578405,
    25333259265, 139126079655, 12666718125, 251259705, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1142036048728213633892352, 59202414725414416577200128, 59213363469815663403466752, 1131705958741229111869440, 57566133014425897403416576, 2984191334987776085840625664,
    2984743223763305553803083776, 57045428492967082689822720, 1142036048728213633892352, 57566133014425897403416576, 632287407113096757409480704, 57566535186998521495552000,
    1141901991204005603180544, 632287407113096757409480704, 32777372783680791352763744256, 32783434547857428035879829504, 626568160491775944692858880, 59202414725414416577200128,
    2984191334987776085840625664, 32777372783680791352763744256, 2984212183355445559164928000, 59195465269524592135766016, 57566535186998521495552000, 2984212183355445559164928000,
    2984764075986619258109952000, 57045827027757107773440000, 59213363469815663403466752, 2984743223763305553803083776, 32783434547857428035879829504, 2984764075986619258109952000,
    59206412728711095301177344, 1141901991204005603180544, 59195465269524592135766016, 59206412728711095301177344, 1131573113811220750663680, 1131705958741229111869440,
    57045428492967082689822720, 626568160491775944692858880, 57045827027757107773440000, 1131573113811220750663680, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    29, 37, 37, 28, 35, 43,
    43, 34, 29, 35, 38, 34,
    28, 38, 45, 45, 37, 37,
    43, 45, 42, 36, 34, 42,
    42, 33, 37, 43, 45, 42,
    36, 28, 36, 36, 27, 28,
    34, 37, 33, 27, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 14641430875491424, 20296971082792624, 22754259361219359, 19296981161815115, 13641261515270434,
    15276451592347871, 22972427516903994, 22972694300592695, 14263342565830272
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    29917882473837897, 37613858393339338, 37614125177032202, 28904773446079424, 35573422675143161, 43269398600631214,
    43269665384324019, 34560313648624711, 29917882473837897, 35573422675143161, 38030710953582536, 34573432754165652,
    28917713113599108, 38030710953582536, 45726686879207195, 45726953662900810, 37017601927064937, 37613858393339338,
    43269398600631214, 45726686879207195, 42269408679653705, 36613689033118305, 34573432754165652, 42269408679653705,
    42269675463346510, 33560323727647202, 37614125177032202, 43269665384324019, 45726953662900810, 42269675463346510,
    36613955816811169, 28917713113599108, 36613689033118305, 36613955816811169, 27904604085844091, 28904773446079424,
    34560313648624711, 37017601927064937, 33560323727647202, 27904604085844091, 0, 0
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
noncomputable def positiveFloor : ℝ := 21501511 / 250000000000
noncomputable def negativeCeiling : ℝ := 17201209 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1142036048728213633892352, coefficient := (-1142036048728213633892352) }, { argument := 59202414725414416577200128, coefficient := (-59202414725414416577200128) }, { argument := 59213363469815663403466752, coefficient := (-59213363469815663403466752) }, { argument := 1131705958741229111869440, coefficient := (-1131705958741229111869440) }, { argument := 57566133014425897403416576, coefficient := (-57566133014425897403416576) }, { argument := 2984191334987776085840625664, coefficient := (-2984191334987776085840625664) }, { argument := 2984743223763305553803083776, coefficient := (-2984743223763305553803083776) }, { argument := 57045428492967082689822720, coefficient := (-57045428492967082689822720) }, { argument := 1142036048728213633892352, coefficient := (-1142036048728213633892352) }, { argument := 57566133014425897403416576, coefficient := (-57566133014425897403416576) }, { argument := 632287407113096757409480704, coefficient := (-632287407113096757409480704) }, { argument := 57566535186998521495552000, coefficient := (-57566535186998521495552000) }, { argument := 1141901991204005603180544, coefficient := (-1141901991204005603180544) }, { argument := 632287407113096757409480704, coefficient := (-632287407113096757409480704) }, { argument := 32777372783680791352763744256, coefficient := (-32777372783680791352763744256) }, { argument := 32783434547857428035879829504, coefficient := (-32783434547857428035879829504) }, { argument := 626568160491775944692858880, coefficient := (-626568160491775944692858880) }, { argument := 59202414725414416577200128, coefficient := (-59202414725414416577200128) }, { argument := 2984191334987776085840625664, coefficient := (-2984191334987776085840625664) }, { argument := 32777372783680791352763744256, coefficient := (-32777372783680791352763744256) }, { argument := 2984212183355445559164928000, coefficient := (-2984212183355445559164928000) }, { argument := 59195465269524592135766016, coefficient := (-59195465269524592135766016) }, { argument := 57566535186998521495552000, coefficient := (-57566535186998521495552000) }, { argument := 2984212183355445559164928000, coefficient := (-2984212183355445559164928000) }, { argument := 2984764075986619258109952000, coefficient := (-2984764075986619258109952000) }, { argument := 57045827027757107773440000, coefficient := (-57045827027757107773440000) }, { argument := 59213363469815663403466752, coefficient := (-59213363469815663403466752) }, { argument := 2984743223763305553803083776, coefficient := (-2984743223763305553803083776) }, { argument := 32783434547857428035879829504, coefficient := (-32783434547857428035879829504) }, { argument := 2984764075986619258109952000, coefficient := (-2984764075986619258109952000) }, { argument := 59206412728711095301177344, coefficient := (-59206412728711095301177344) }, { argument := 1141901991204005603180544, coefficient := (-1141901991204005603180544) }, { argument := 59195465269524592135766016, coefficient := (-59195465269524592135766016) }, { argument := 59206412728711095301177344, coefficient := (-59206412728711095301177344) }, { argument := 1131573113811220750663680, coefficient := (-1131573113811220750663680) }, { argument := 1131705958741229111869440, coefficient := (-1131705958741229111869440) }, { argument := 57045428492967082689822720, coefficient := (-57045428492967082689822720) }, { argument := 626568160491775944692858880, coefficient := (-626568160491775944692858880) }, { argument := 57045827027757107773440000, coefficient := (-57045827027757107773440000) }, { argument := 1131573113811220750663680, coefficient := (-1131573113811220750663680) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 241379040405399045452857344, coefficient := 241379040405399045452857344 }, { argument := 12167092240516949239473897472, coefficient := 12167092240516949239473897472 }, { argument := 133639325798286184181491826688, coefficient := 133639325798286184181491826688 }, { argument := 12167177243113640893087744000, coefficient := 12167177243113640893087744000 }, { argument := 241350706206501827581575168, coefficient := 241350706206501827581575168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1499408026708906791091044352, coefficient := 1499408026708906791091044352 }, { argument := 77728348364037904012964528128, coefficient := 77728348364037904012964528128 }, { argument := 77742723247611759212995018752, coefficient := 77742723247611759212995018752 }, { argument := 1485845390170105170037309440, coefficient := 1485845390170105170037309440 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk2
