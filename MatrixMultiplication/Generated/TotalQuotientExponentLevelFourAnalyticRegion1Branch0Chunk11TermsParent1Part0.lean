import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 11, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk11

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    33, 35, 127, 211, 421, 559,
    785, 1021, 2131, 3597, 4297
  ]
def positiveCoefficients : Array ℕ := #[
    3406810988113366516522389864448, 111711709145112716006896969973760, 68453132412324387680821973090304, 15053350877710224142773350563840, 14894894552681695467586262663168, 111394796495055658656522794172416,
    132311031398821443781218397061120, 68770045062381445031196148891648, 125101268610023389060205897580544, 569967401127617644647955178717184, 126052006560194561111328424984576
  ]
def positiveScales : Array ℕ := #[
    5, 5, 6, 7, 8, 9,
    9, 9, 11, 11, 12
  ]
def negativeArguments : Array ℕ := #[
    3, 7, 9, 27, 29, 45,
    49, 59, 69, 97, 123, 217,
    243, 257, 383, 521, 763, 835,
    4328759059
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 4991374238398653268393268871168, 5704427701027032306735164424192, 68453132412324387680821973090304, 6892850138740997370638323679232, 14261069252567580766837911060480,
    7764359926397905084167307132928, 4674461588341595918019093069824, 5466743213484239293954532573184, 7685131763883640746573763182592, 19490127978509027048011811782656, 68770045062381445031196148891648,
    19252443490966234035231179931648, 40723275532331869523081590472704, 60688772485926482596654665957376, 41277872669931719886236398125056, 60451087998383689583874034106368, 132311031398821443781218397061120,
    284983700563808822323977589358592
  ]
def negativeScales : Array ℕ := #[
    1, 2, 3, 4, 4, 5,
    5, 5, 6, 6, 6, 7,
    7, 8, 8, 9, 9, 9,
    32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5044394119358453, 5129283016944966, 6988684685554546, 7721099188699862, 8717676423059623, 9126704472843189,
    9616548843778436, 9995767149513532, 11057314877782703, 11812578444083777, 12069114061773938
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2807354922807594, 3169925001442313, 4754887502413606, 4857980997143165, 5491853096329881,
    5614709844123661, 5882643052550791, 6108524456778170, 6599912842192769, 6942514514520450, 7761551232733342,
    7924812510375204, 8005624549193879, 8581200581928289, 9025139562278509, 9575539246837362, 9705632387444012,
    32011306355608465
  ]

abbrev PositiveTerm := Fin 11
abbrev NegativeTerm := Fin 19
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
noncomputable def positiveFloor : ℝ := 33531687263 / 200000000000
noncomputable def negativeCeiling : ℝ := 32866100317 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-475368975085586025561263702016) }, { argument := 7, coefficient := (-4991374238398653268393268871168) }, { argument := 9, coefficient := (-5704427701027032306735164424192) }, { argument := 27, coefficient := (-68453132412324387680821973090304) }, { argument := 29, coefficient := (-6892850138740997370638323679232) }, { argument := 33, coefficient := 3406810988113366516522389864448 }, { argument := 35, coefficient := 111711709145112716006896969973760 }, { argument := 45, coefficient := (-14261069252567580766837911060480) }, { argument := 49, coefficient := (-7764359926397905084167307132928) }, { argument := 59, coefficient := (-4674461588341595918019093069824) }, { argument := 69, coefficient := (-5466743213484239293954532573184) }, { argument := 97, coefficient := (-7685131763883640746573763182592) }, { argument := 123, coefficient := (-19490127978509027048011811782656) }, { argument := 127, coefficient := 68453132412324387680821973090304 }, { argument := 211, coefficient := 15053350877710224142773350563840 }, { argument := 217, coefficient := (-68770045062381445031196148891648) }, { argument := 243, coefficient := (-19252443490966234035231179931648) }, { argument := 257, coefficient := (-40723275532331869523081590472704) }, { argument := 383, coefficient := (-60688772485926482596654665957376) }, { argument := 421, coefficient := 14894894552681695467586262663168 }, { argument := 521, coefficient := (-41277872669931719886236398125056) }, { argument := 559, coefficient := 111394796495055658656522794172416 }, { argument := 763, coefficient := (-60451087998383689583874034106368) }, { argument := 785, coefficient := 132311031398821443781218397061120 }, { argument := 835, coefficient := (-132311031398821443781218397061120) }, { argument := 1021, coefficient := 68770045062381445031196148891648 }, { argument := 2131, coefficient := 125101268610023389060205897580544 }, { argument := 3597, coefficient := 569967401127617644647955178717184 }, { argument := 4297, coefficient := 126052006560194561111328424984576 }, { argument := 4328759059, coefficient := (-284983700563808822323977589358592) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk11
