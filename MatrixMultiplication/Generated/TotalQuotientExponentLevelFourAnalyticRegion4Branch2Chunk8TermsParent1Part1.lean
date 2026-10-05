import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 4, branch 2,
parent chunk 8, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk8

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 24727756758656964794058293641216
def positiveArguments : Array ℕ := #[
    3, 1, 135, 17, 17, 29,
    17, 135, 135, 29, 2451, 29,
    135, 135, 17, 29, 17, 135,
    135, 1, 585109, 24580747, 24580721, 585071,
    33993, 1187969, 14333263, 1187997, 16997
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 618970019642690137449562112, 5222559540735198034730680320, 5261245166962866168321277952, 657655645870358271040159744, 4487532642409503496509325312,
    657655645870358271040159744, 5222559540735198034730680320, 5222559540735198034730680320, 4487532642409503496509325312, 94818469884014595430554796032, 4487532642409503496509325312,
    5222559540735198034730680320, 5222559540735198034730680320, 657655645870358271040159744, 4487532642409503496509325312, 657655645870358271040159744, 5222559540735198034730680320,
    5222559540735198034730680320, 618970019642690137449562112, 5526198260850750482680905728, 232158591513397165955244621824, 232158345950340056733693509632, 5525839360998052389644664832,
    642109615408751398996672512, 22440099953152678219476893696, 270747683125422478258383880192, 22440628858198759619740827648, 642128504874682877577527296
  ]
def positiveScales : Array ℕ := #[
    1, 0, 7, 4, 4, 4,
    4, 7, 7, 4, 11, 4,
    7, 7, 4, 4, 4, 7,
    7, 0, 19, 24, 24, 19,
    15, 20, 23, 20, 14
  ]
def negativeArguments : Array ℕ := #[
    3888665, 138717705, 138717705, 3888597, 6633605, 236636085,
    236636085, 6633489, 3888665, 138717705, 138717705, 3888597,
    30880575, 1101581775, 1101581775, 30880035, 30880575, 1101581775,
    1101581775, 30880035, 3388158767, 273244093837, 68310968219, 6775963049,
    1, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    4483325502711984595927040, 159930625164208739796910080, 159930625164208739796910080, 4483247104049671330332672, 30592103430270012536913920, 1091291324649894930378915840,
    1091291324649894930378915840, 30591568474691874959917056, 4483325502711984595927040, 159930625164208739796910080, 159930625164208739796910080, 4483247104049671330332672,
    35602878992124583555891200, 1270037317480481168975462400, 1270037317480481168975462400, 35602256414512095858524160, 35602878992124583555891200, 1270037317480481168975462400,
    1270037317480481168975462400, 35602256414512095858524160, 7629455280266639589769216, 307645499796375510647308288, 307645251016406194794266624, 7629056165638162482200576,
    158456325028528675187087900672, 475368975085586025561263702016, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    21, 27, 27, 21, 22, 27,
    27, 22, 21, 27, 27, 21,
    24, 30, 30, 24, 24, 30,
    30, 24, 31, 37, 35, 32,
    0, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 0, 7076815597050830, 4087462841250339, 4087462841250339, 4857980995002857,
    4087462841250339, 7076815597050830, 7076815597050830, 4857980995002857, 11259154768866839, 4857980995002857,
    7076815597050830, 7076815597050830, 4087462841250339, 4857980995002857, 4087462841250339, 7076815597050830,
    7076815597050830, 0, 19158345883938221, 24551025423568079, 24551023897573328, 19158252184829412,
    15052950069882485, 20180065758888953, 23772863743993937, 20180099762288957, 14052992510203163
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    21890843528124315, 27047576694457359, 27047576694457359, 21890818299896343, 22661361678326961, 27818094849264711,
    27818094849264711, 22661336450100665, 21890843528124315, 27047576694457359, 27047576694457359, 21890818299896343,
    24880196283270827, 30036929450257850, 30036929450257850, 24880171055043135, 24880196283270827, 30036929450257850,
    30036929450257850, 24880171055043135, 31657854334053330, 37991399376813264, 35991398210165637, 32657778861331394,
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
noncomputable def positiveFloor : ℝ := 63709821 / 250000000000
noncomputable def negativeCeiling : ℝ := 12189039 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4483325502711984595927040, coefficient := (-4483325502711984595927040) }, { argument := 159930625164208739796910080, coefficient := (-159930625164208739796910080) }, { argument := 159930625164208739796910080, coefficient := (-159930625164208739796910080) }, { argument := 4483247104049671330332672, coefficient := (-4483247104049671330332672) }, { argument := 30592103430270012536913920, coefficient := (-30592103430270012536913920) }, { argument := 1091291324649894930378915840, coefficient := (-1091291324649894930378915840) }, { argument := 1091291324649894930378915840, coefficient := (-1091291324649894930378915840) }, { argument := 30591568474691874959917056, coefficient := (-30591568474691874959917056) }, { argument := 4483325502711984595927040, coefficient := (-4483325502711984595927040) }, { argument := 159930625164208739796910080, coefficient := (-159930625164208739796910080) }, { argument := 159930625164208739796910080, coefficient := (-159930625164208739796910080) }, { argument := 4483247104049671330332672, coefficient := (-4483247104049671330332672) }, { argument := 35602878992124583555891200, coefficient := (-35602878992124583555891200) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 35602256414512095858524160, coefficient := (-35602256414512095858524160) }, { argument := 35602878992124583555891200, coefficient := (-35602878992124583555891200) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 35602256414512095858524160, coefficient := (-35602256414512095858524160) }, { argument := 7629455280266639589769216, coefficient := (-7629455280266639589769216) }, { argument := 307645499796375510647308288, coefficient := (-307645499796375510647308288) }, { argument := 307645251016406194794266624, coefficient := (-307645251016406194794266624) }, { argument := 7629056165638162482200576, coefficient := (-7629056165638162482200576) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 618970019642690137449562112, coefficient := 618970019642690137449562112 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 657655645870358271040159744, coefficient := 657655645870358271040159744 }, { argument := 4487532642409503496509325312, coefficient := 4487532642409503496509325312 }, { argument := 657655645870358271040159744, coefficient := 657655645870358271040159744 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 4487532642409503496509325312, coefficient := 4487532642409503496509325312 }, { argument := 94818469884014595430554796032, coefficient := 94818469884014595430554796032 }, { argument := 4487532642409503496509325312, coefficient := 4487532642409503496509325312 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 657655645870358271040159744, coefficient := 657655645870358271040159744 }, { argument := 4487532642409503496509325312, coefficient := 4487532642409503496509325312 }, { argument := 657655645870358271040159744, coefficient := 657655645870358271040159744 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 618970019642690137449562112, coefficient := 618970019642690137449562112 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 5526198260850750482680905728, coefficient := 5526198260850750482680905728 }, { argument := 232158591513397165955244621824, coefficient := 232158591513397165955244621824 }, { argument := 232158345950340056733693509632, coefficient := 232158345950340056733693509632 }, { argument := 5525839360998052389644664832, coefficient := 5525839360998052389644664832 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 642109615408751398996672512, coefficient := 642109615408751398996672512 }, { argument := 22440099953152678219476893696, coefficient := 22440099953152678219476893696 }, { argument := 270747683125422478258383880192, coefficient := 270747683125422478258383880192 }, { argument := 22440628858198759619740827648, coefficient := 22440628858198759619740827648 }, { argument := 642128504874682877577527296, coefficient := 642128504874682877577527296 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk8
