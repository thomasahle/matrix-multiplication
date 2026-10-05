import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 21, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk21

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    33, 129, 205, 343, 375, 409,
    1917, 2387, 2747, 3819, 8501, 8621
  ]
def positiveCoefficients : Array ℕ := #[
    1584563250285286751870879006720, 47061528533473016530565106499584, 10141204801825835211973625643008, 12834962327310822690154119954432, 95549163992202791137814004105216, 9982748476797306536786537742336,
    83744167777577404836375955505152, 378235247843097947671578818904064, 12914190489825087027747663904768, 83506483290034611823595323654144, 80812725764549624345414829342720, 81921920039749325071724444647424
  ]
def positiveScales : Array ℕ := #[
    5, 7, 7, 8, 8, 8,
    10, 11, 11, 11, 13, 13
  ]
def negativeArguments : Array ℕ := #[
    5, 9, 11, 19, 29, 35,
    37, 63, 87, 93, 189, 527,
    569, 1057, 52662219273
  ]
def negativeCoefficients : Array ℕ := #[
    1584563250285286751870879006720, 1426106925256758076683791106048, 6972078301255261708231867629568, 3010670175542044828554670112768, 18380933703309326321702196477952, 44367771007988029052384612188160,
    2931442013027780490961126162432, 9982748476797306536786537742336, 6892850138740997370638323679232, 29472876455306333584798349524992, 29948245430391919610359613227008, 83506483290034611823595323654144,
    45080824470616408090726507741184, 83744167777577404836375955505152, 189117623921548973835789409452032
  ]
def negativeScales : Array ℕ := #[
    2, 3, 3, 4, 4, 5,
    5, 5, 6, 6, 7, 9,
    9, 10, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5044394119358453, 7011227255423254, 7679480099502692, 8422064766172810, 8550746785383158, 8675957032939221,
    10904634621374895, 11220982851081776, 11423641195075854, 11898979204357438, 13053416844757500, 13073639510283229
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2321928094887363, 3169925001442313, 3459431618637364, 4247927513443586, 4857980997143165, 5129283016944967,
    5209453365628950, 5977279939904027, 6442943495848765, 6539158811108986, 7562242424222992, 9041659151637215,
    9152284842306582, 10045759661382684, 35616049269102051
  ]

abbrev PositiveTerm := Fin 12
abbrev NegativeTerm := Fin 15
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
noncomputable def positiveFloor : ℝ := 3705908447 / 31250000000
noncomputable def negativeCeiling : ℝ := 116098168139 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5, coefficient := (-1584563250285286751870879006720) }, { argument := 9, coefficient := (-1426106925256758076683791106048) }, { argument := 11, coefficient := (-6972078301255261708231867629568) }, { argument := 19, coefficient := (-3010670175542044828554670112768) }, { argument := 29, coefficient := (-18380933703309326321702196477952) }, { argument := 33, coefficient := 1584563250285286751870879006720 }, { argument := 35, coefficient := (-44367771007988029052384612188160) }, { argument := 37, coefficient := (-2931442013027780490961126162432) }, { argument := 63, coefficient := (-9982748476797306536786537742336) }, { argument := 87, coefficient := (-6892850138740997370638323679232) }, { argument := 93, coefficient := (-29472876455306333584798349524992) }, { argument := 129, coefficient := 47061528533473016530565106499584 }, { argument := 189, coefficient := (-29948245430391919610359613227008) }, { argument := 205, coefficient := 10141204801825835211973625643008 }, { argument := 343, coefficient := 12834962327310822690154119954432 }, { argument := 375, coefficient := 95549163992202791137814004105216 }, { argument := 409, coefficient := 9982748476797306536786537742336 }, { argument := 527, coefficient := (-83506483290034611823595323654144) }, { argument := 569, coefficient := (-45080824470616408090726507741184) }, { argument := 1057, coefficient := (-83744167777577404836375955505152) }, { argument := 1917, coefficient := 83744167777577404836375955505152 }, { argument := 2387, coefficient := 378235247843097947671578818904064 }, { argument := 2747, coefficient := 12914190489825087027747663904768 }, { argument := 3819, coefficient := 83506483290034611823595323654144 }, { argument := 8501, coefficient := 80812725764549624345414829342720 }, { argument := 8621, coefficient := 81921920039749325071724444647424 }, { argument := 52662219273, coefficient := (-189117623921548973835789409452032) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk21
