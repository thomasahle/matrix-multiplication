import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 1, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk1

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
def constantNumerator : ℤ := 516455306043463558715064451072
def positiveArguments : Array ℕ := #[
    3, 2268853, 32180909, 9075327, 523711, 24642107,
    6161497, 259921
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 85714842894065945216238485504, 303940092099756222968473059328, 85714040091763857376552157184, 4946310546220289529019891712, 232738120328174928815869394944,
    232774775336814963002018103296, 4909768874375844214356312064
  ]
def positiveScales : Array ℕ := #[
    1, 21, 24, 23, 18, 24,
    22, 17
  ]
def negativeArguments : Array ℕ := #[
    396194519119, 18636319369799, 9319629803763, 98315839201, 396194519119, 5616877895553,
    1584756596547, 5616877895553, 264336088427301, 66094419823171, 2787707876903, 18636319369799,
    264336088427301, 74544585927615, 1584756596547, 74544585927615, 18639086621655, 786516169425,
    9319629803763, 66094419823171, 18639086621655, 98315839201, 2787707876903, 786516169425,
    3, 3
  ]
def negativeCoefficients : Array ℕ := #[
    446075372167640313292128256, 20982630242346083311551512576, 20985940655729007780087988224, 442775176790241203187613696, 446075372167640313292128256, 1581010574837379159470112768,
    446069326105125291747704832, 1581010574837379159470112768, 74403994333860453977168019456, 74415701121725509931005640704, 1569340019454768416592756736, 20982630242346083311551512576,
    74403994333860453977168019456, 20982435587880927119215165440, 446069326105125291747704832, 20982435587880927119215165440, 20985745890952963789915422720, 442769240942912487397785600,
    20985940655729007780087988224, 74415701121725509931005640704, 20985745890952963789915422720, 442775176790241203187613696, 1569340019454768416592756736, 442769240942912487397785600,
    475368975085586025561263702016, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    38, 44, 43, 36, 38, 42,
    40, 42, 47, 45, 41, 44,
    47, 46, 40, 46, 44, 39,
    43, 45, 44, 36, 41, 39,
    1, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 21113531708505813, 24939701741481158, 23113518196209870, 18998411380414651, 24554622281790181,
    22554849480648860, 17987713672542408
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    38527417966153277, 44083182192709081, 43083409787639218, 36516704809955881, 38527417966153277, 42352905579379561,
    40527398411871501, 42352905579379561, 47909366735638710, 45909593712670597, 41342216528181757, 44083182192709081,
    47909366735638710, 46083168808861063, 40527398411871501, 46083168808861063, 44083396398318956, 39516685469045739,
    43083409787639218, 45909593712670597, 44083396398318956, 36516704809955881, 41342216528181757, 39516685469045739,
    1584962500724866, 1584962500724866
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 280124073 / 1000000000000
noncomputable def negativeCeiling : ℝ := 280618633 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 446075372167640313292128256, coefficient := (-446075372167640313292128256) }, { argument := 20982630242346083311551512576, coefficient := (-20982630242346083311551512576) }, { argument := 20985940655729007780087988224, coefficient := (-20985940655729007780087988224) }, { argument := 442775176790241203187613696, coefficient := (-442775176790241203187613696) }, { argument := 446075372167640313292128256, coefficient := (-446075372167640313292128256) }, { argument := 1581010574837379159470112768, coefficient := (-1581010574837379159470112768) }, { argument := 446069326105125291747704832, coefficient := (-446069326105125291747704832) }, { argument := 1581010574837379159470112768, coefficient := (-1581010574837379159470112768) }, { argument := 74403994333860453977168019456, coefficient := (-74403994333860453977168019456) }, { argument := 74415701121725509931005640704, coefficient := (-74415701121725509931005640704) }, { argument := 1569340019454768416592756736, coefficient := (-1569340019454768416592756736) }, { argument := 20982630242346083311551512576, coefficient := (-20982630242346083311551512576) }, { argument := 74403994333860453977168019456, coefficient := (-74403994333860453977168019456) }, { argument := 20982435587880927119215165440, coefficient := (-20982435587880927119215165440) }, { argument := 446069326105125291747704832, coefficient := (-446069326105125291747704832) }, { argument := 20982435587880927119215165440, coefficient := (-20982435587880927119215165440) }, { argument := 20985745890952963789915422720, coefficient := (-20985745890952963789915422720) }, { argument := 442769240942912487397785600, coefficient := (-442769240942912487397785600) }, { argument := 20985940655729007780087988224, coefficient := (-20985940655729007780087988224) }, { argument := 74415701121725509931005640704, coefficient := (-74415701121725509931005640704) }, { argument := 20985745890952963789915422720, coefficient := (-20985745890952963789915422720) }, { argument := 442775176790241203187613696, coefficient := (-442775176790241203187613696) }, { argument := 1569340019454768416592756736, coefficient := (-1569340019454768416592756736) }, { argument := 442769240942912487397785600, coefficient := (-442769240942912487397785600) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 85714842894065945216238485504, coefficient := 85714842894065945216238485504 }, { argument := 303940092099756222968473059328, coefficient := 303940092099756222968473059328 }, { argument := 85714040091763857376552157184, coefficient := 85714040091763857376552157184 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 4946310546220289529019891712, coefficient := 4946310546220289529019891712 }, { argument := 232738120328174928815869394944, coefficient := 232738120328174928815869394944 }, { argument := 232774775336814963002018103296, coefficient := 232774775336814963002018103296 }, { argument := 4909768874375844214356312064, coefficient := 4909768874375844214356312064 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk1
