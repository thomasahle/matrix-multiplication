import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 9, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk9

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
def constantNumerator : ℤ := 3169126500570573503741758013440
def positiveArguments : Array ℕ := #[
    5, 1, 75497537, 75497407, 27174973, 96643133,
    13588419, 228745, 8159865, 8159865, 228741
  ]
def positiveCoefficients : Array ℕ := #[
    1584563250285286751870879006720, 158456325028528675187087900672, 713054076536021811395773333504, 713052848720736265288017772544, 256660363336175142403536060416, 912768584157426688100071899136,
    256677977763156246180183146496, 2160435442248033988813783040, 77067745961482235083311022080, 77067745961482235083311022080, 2160397663316171031652073472
  ]
def positiveScales : Array ℕ := #[
    2, 0, 26, 26, 24, 26,
    23, 17, 22, 22, 17
  ]
def negativeArguments : Array ℕ := #[
    228745, 8159865, 8159865, 228741, 227960391999999, 810702056783599,
    113988018466697, 227960391999999, 227959999815169, 228745, 227959999815169, 810700660474129,
    113987822194807, 810702056783599, 810700660474129, 8159865, 113988018466697, 113987822194807,
    8159865, 228741, 1, 9, 9, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1080217721124016994406891520, 38533872980741117541655511040, 38533872980741117541655511040, 1080198831658085515826036736, 64165146029151730862175289344, 228192342552444446584229330944,
    64169549686414728251482046464, 64165146029151730862175289344, 64165035638935840339592740864, 1080217721124016994406891520, 64165035638935840339592740864, 228191949526268897465806618624,
    64169439195163394838609526784, 228192342552444446584229330944, 228191949526268897465806618624, 38533872980741117541655511040, 64169549686414728251482046464, 64169439195163394838609526784,
    38533872980741117541655511040, 1080198831658085515826036736, 158456325028528675187087900672, 1426106925256758076683791106048, 1426106925256758076683791106048, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    17, 22, 22, 17, 47, 49,
    46, 47, 47, 17, 47, 49,
    46, 49, 49, 22, 46, 46,
    22, 17, 0, 3, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 0, 26169926243538700, 26169923759344854, 24695775266054883, 26526163889262502,
    23695874273841470, 17803380683128142, 22960113852444661, 22960113852444661, 17803355454901885
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    17803380683863038, 22960113865559938, 22960113865559938, 17803355455636405, 47695776507136887, 49526165131673752,
    46695875515974241, 47695776507136887, 47695774025110988, 17803380683863038, 47695774025110988, 49526162646851534,
    46695873031847133, 49526165131673752, 49526162646851534, 22960113865559938, 46695875515974241, 46695873031847133,
    22960113865559938, 17803355455636405, 0, 3169925001442313, 3169925001442313, 0
  ]

abbrev PositiveTerm := Fin 11
abbrev NegativeTerm := Fin 24
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
noncomputable def positiveFloor : ℝ := 978000849 / 1000000000000
noncomputable def negativeCeiling : ℝ := 197625791 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1080217721124016994406891520, coefficient := (-1080217721124016994406891520) }, { argument := 38533872980741117541655511040, coefficient := (-38533872980741117541655511040) }, { argument := 38533872980741117541655511040, coefficient := (-38533872980741117541655511040) }, { argument := 1080198831658085515826036736, coefficient := (-1080198831658085515826036736) }, { argument := 64165146029151730862175289344, coefficient := (-64165146029151730862175289344) }, { argument := 228192342552444446584229330944, coefficient := (-228192342552444446584229330944) }, { argument := 64169549686414728251482046464, coefficient := (-64169549686414728251482046464) }, { argument := 64165146029151730862175289344, coefficient := (-64165146029151730862175289344) }, { argument := 64165035638935840339592740864, coefficient := (-64165035638935840339592740864) }, { argument := 1080217721124016994406891520, coefficient := (-1080217721124016994406891520) }, { argument := 64165035638935840339592740864, coefficient := (-64165035638935840339592740864) }, { argument := 228191949526268897465806618624, coefficient := (-228191949526268897465806618624) }, { argument := 64169439195163394838609526784, coefficient := (-64169439195163394838609526784) }, { argument := 228192342552444446584229330944, coefficient := (-228192342552444446584229330944) }, { argument := 228191949526268897465806618624, coefficient := (-228191949526268897465806618624) }, { argument := 38533872980741117541655511040, coefficient := (-38533872980741117541655511040) }, { argument := 64169549686414728251482046464, coefficient := (-64169549686414728251482046464) }, { argument := 64169439195163394838609526784, coefficient := (-64169439195163394838609526784) }, { argument := 38533872980741117541655511040, coefficient := (-38533872980741117541655511040) }, { argument := 1080198831658085515826036736, coefficient := (-1080198831658085515826036736) }, { argument := 1584563250285286751870879006720, coefficient := 1584563250285286751870879006720 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 713054076536021811395773333504, coefficient := 713054076536021811395773333504 }, { argument := 713052848720736265288017772544, coefficient := 713052848720736265288017772544 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 256660363336175142403536060416, coefficient := 256660363336175142403536060416 }, { argument := 912768584157426688100071899136, coefficient := 912768584157426688100071899136 }, { argument := 256677977763156246180183146496, coefficient := 256677977763156246180183146496 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 2160435442248033988813783040, coefficient := 2160435442248033988813783040 }, { argument := 77067745961482235083311022080, coefficient := 77067745961482235083311022080 }, { argument := 77067745961482235083311022080, coefficient := 77067745961482235083311022080 }, { argument := 2160397663316171031652073472, coefficient := 2160397663316171031652073472 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk9
