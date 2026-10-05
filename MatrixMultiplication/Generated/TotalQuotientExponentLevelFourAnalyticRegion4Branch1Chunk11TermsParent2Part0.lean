import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 11, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk11

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 475368975085586025561263702016
def positiveArguments : Array ℕ := #[
    1, 8388629, 8388587, 3084695, 10607475, 1542523,
    203781, 2046205, 8186411, 50551
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 79228360853656618118642925568, 79227964174872057068444975104, 58268241111502320969847930880, 200369537631510759452599910400, 58274871314044269951727960064,
    1924657128491318342584369152, 77303439272642259075926589440, 77318465842790750286996570112, 1909762784604347481580371968
  ]
def positiveScales : Array ℕ := #[
    0, 23, 22, 21, 23, 20,
    17, 20, 22, 15
  ]
def negativeArguments : Array ℕ := #[
    1709443206249, 17164854602945, 68672764720519, 424053584579, 9515108234125, 32721289624785,
    4758098225105, 1709443206249, 1709434647447, 1709434647447, 17164768662335, 68672420891257,
    424051461437, 32721289624785, 112517607664421, 16362501000197, 17164854602945, 17164768662335,
    4758098225105, 16362501000197, 2379321165333, 68672764720519, 68672420891257, 424053584579,
    424051461437, 1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    481165486667126396204089344, 19325908198422961268121927680, 19329664850364444517769150464, 477441891373776877226295296, 5356529737199411026460672000, 18420448470157975359502417920,
    5357142348393774098960875520, 481165486667126396204089344, 481163077578532775088095232, 481163077578532775088095232, 19325811437898168269841367040, 19329568071030930625729134592,
    477439500928396863563890688, 18420448470157975359502417920, 63341781993763260042525540352, 18422538351834144324271996928, 19325908198422961268121927680, 19325811437898168269841367040,
    5357142348393774098960875520, 18422538351834144324271996928, 5357754956794216552631107584, 19329664850364444517769150464, 19329568071030930625729134592, 477441891373776877226295296,
    477439500928396863563890688, 158456325028528675187087900672, 316912650057057350374175801344, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    40, 43, 45, 38, 43, 44,
    42, 40, 40, 40, 43, 45,
    38, 44, 46, 43, 43, 43,
    42, 43, 41, 45, 45, 38,
    38, 0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 23000003611631147, 22999996386900313, 21556696418912575, 23338577942659320, 20556860570360714,
    17636660019150534, 20964519257901833, 22964799667821649, 15625452011355991
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40636663630797741, 43964522883646826, 45964803293632487, 38625455622999106, 43113357205862023, 44895294847033379,
    42113522193389362, 40636663630797741, 40636656407526402, 40636656407526402, 43964515660373896, 45964796070359549,
    38625448399727768, 44895294847033379, 46677144112151219, 43895458517919594, 43964522883646826, 43964515660373896,
    42113522193389362, 43895458517919594, 41113687161298454, 45964803293632487, 45964796070359549, 38625455622999106,
    38625448399727768, 0, 0, 0
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
noncomputable def positiveFloor : ℝ := 171346047 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1338641 / 7812500000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 481165486667126396204089344, coefficient := (-481165486667126396204089344) }, { argument := 19325908198422961268121927680, coefficient := (-19325908198422961268121927680) }, { argument := 19329664850364444517769150464, coefficient := (-19329664850364444517769150464) }, { argument := 477441891373776877226295296, coefficient := (-477441891373776877226295296) }, { argument := 5356529737199411026460672000, coefficient := (-5356529737199411026460672000) }, { argument := 18420448470157975359502417920, coefficient := (-18420448470157975359502417920) }, { argument := 5357142348393774098960875520, coefficient := (-5357142348393774098960875520) }, { argument := 481165486667126396204089344, coefficient := (-481165486667126396204089344) }, { argument := 481163077578532775088095232, coefficient := (-481163077578532775088095232) }, { argument := 481163077578532775088095232, coefficient := (-481163077578532775088095232) }, { argument := 19325811437898168269841367040, coefficient := (-19325811437898168269841367040) }, { argument := 19329568071030930625729134592, coefficient := (-19329568071030930625729134592) }, { argument := 477439500928396863563890688, coefficient := (-477439500928396863563890688) }, { argument := 18420448470157975359502417920, coefficient := (-18420448470157975359502417920) }, { argument := 63341781993763260042525540352, coefficient := (-63341781993763260042525540352) }, { argument := 18422538351834144324271996928, coefficient := (-18422538351834144324271996928) }, { argument := 19325908198422961268121927680, coefficient := (-19325908198422961268121927680) }, { argument := 19325811437898168269841367040, coefficient := (-19325811437898168269841367040) }, { argument := 5357142348393774098960875520, coefficient := (-5357142348393774098960875520) }, { argument := 18422538351834144324271996928, coefficient := (-18422538351834144324271996928) }, { argument := 5357754956794216552631107584, coefficient := (-5357754956794216552631107584) }, { argument := 19329664850364444517769150464, coefficient := (-19329664850364444517769150464) }, { argument := 19329568071030930625729134592, coefficient := (-19329568071030930625729134592) }, { argument := 477441891373776877226295296, coefficient := (-477441891373776877226295296) }, { argument := 477439500928396863563890688, coefficient := (-477439500928396863563890688) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 79228360853656618118642925568, coefficient := 79228360853656618118642925568 }, { argument := 79227964174872057068444975104, coefficient := 79227964174872057068444975104 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 58268241111502320969847930880, coefficient := 58268241111502320969847930880 }, { argument := 200369537631510759452599910400, coefficient := 200369537631510759452599910400 }, { argument := 58274871314044269951727960064, coefficient := 58274871314044269951727960064 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 1924657128491318342584369152, coefficient := 1924657128491318342584369152 }, { argument := 77303439272642259075926589440, coefficient := 77303439272642259075926589440 }, { argument := 77318465842790750286996570112, coefficient := 77318465842790750286996570112 }, { argument := 1909762784604347481580371968, coefficient := 1909762784604347481580371968 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk11
