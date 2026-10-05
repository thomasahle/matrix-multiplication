import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 17, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-155554354913151300125320209416323072)
def positiveArguments : Array ℕ := #[
    163553, 421737, 547, 4923, 4923, 10393,
    915, 16287, 915, 28975, 49471, 915,
    49471, 49471, 16287, 915, 483, 541,
    483, 541, 115, 28919729825, 28919722335, 12497801343,
    356032119953, 99982407543, 7044661817, 131144187589, 262276616559, 3528210279,
    6700301, 4130676839, 153, 83801267175, 157, 5,
    153, 87, 157, 2451, 3, 2065338439,
    153, 5, 3, 5, 77, 87,
    53598663, 6160039, 505835865, 35, 31, 1451,
    395, 252917889
  ]
def positiveCoefficients : Array ℕ := #[
    6327150226413806253143014506496, 32630319896756151312195747053568, 677153201489103010369820950528, 761797351675240886666048569344, 761797351675240886666048569344, 804119426768309824814162378752,
    35397347998316342235396833280, 630072794370030891790063632384, 35397347998316342235396833280, 560458009973342085393783193600, 956908307554485118430227726336, 35397347998316342235396833280,
    956908307554485118430227726336, 956908307554485118430227726336, 630072794370030891790063632384, 35397347998316342235396833280, 37370314935927417048517312512, 41857847578336920545026637824,
    37370314935927417048517312512, 41857847578336920545026637824, 18222477378280797646515108577280, 273139125638451260547385419366400, 273139054897401347160100118200320, 472153585373971507565307126349824,
    1681314150091072244385166590476288, 472153570257676395899572797308928, 33267474847752374225261016645632, 1238621831786925813877648432037888, 1238566303278675379692915407192064, 33323003932131519320090757562368,
    253130214940303733559780179968, 39013139712119067480722545573888, 5918900812833224439361437696, 395740295329224199250398465228800, 6073643317743896973723828224, 193428131138340667952988160,
    5918900812833224439361437696, 3365649481807127622381993984, 6073643317743896973723828224, 94818469884014595430554796032, 3713820117856140824697372672, 39013140080463653144554872242176,
    5918900812833224439361437696, 193428131138340667952988160, 3713820117856140824697372672, 193428131138340667952988160, 5957586439060892572952035328, 3365649481807127622381993984,
    253112529677825386738454888448, 58179923413539692865061388288, 4777484669418749337826052014080, 1353996917968384675670917120, 1199254413057712141308526592, 56132843656346461839957164032,
    15280822359928912768286064640, 4777483847726981318507784830976
  ]
def positiveScales : Array ℕ := #[
    17, 18, 9, 12, 12, 13,
    9, 13, 9, 14, 15, 9,
    15, 15, 13, 9, 8, 9,
    8, 9, 6, 34, 34, 33,
    38, 36, 32, 36, 37, 31,
    22, 31, 7, 36, 7, 2,
    7, 6, 7, 11, 1, 30,
    7, 2, 1, 2, 6, 6,
    25, 22, 28, 5, 4, 10,
    8, 27
  ]
def negativeArguments : Array ℕ := #[
    547, 61, 1, 115, 6895, 8285,
    32107, 1497
  ]
def negativeCoefficients : Array ℕ := #[
    86675609790605185327337081667584, 4832917913370124593206180970496, 158456325028528675187087900672, 18222477378280797646515108577280, 546278180535852607707485537566720, 2625621305722720147850046514135040,
    2543778613845485087115915613437952, 474418237135414853510141174611968
  ]
def negativeScales : Array ℕ := #[
    9, 5, 0, 6, 12, 13,
    14, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    17319398696990661, 18685984072704368, 9095397022792556, 12265322024234868, 12265322024234868, 13343324536236141,
    9837627933086892, 13991433267977741, 9837627933086892, 14822521040718310, 15594295441779858, 9837627933086892,
    15594295441779858, 15594295441779858, 13991433267977741, 9837627933086892, 8915879378478017, 9079484783826815,
    8915879378478017, 9079484783826815, 6845490050846035, 34751335023210763, 34751334649563176, 33540955262117075,
    38373216445645243, 36540955215928282, 32713883304780733, 36932362910953356, 37932298232214020, 31716289401108139,
    22675794477049253, 31943731049643941, 7257387842692651, 36286253008231024, 7294620748891626, 2321928094887362,
    7257387842692651, 6442943495848725, 7294620748891626, 11259154768866839, 1584962500720924, 30943731063265221,
    7257387842692651, 2321928094887362, 1584962500720924, 2321928094887362, 6266786540694901, 6442943495848725,
    25675693677815073, 22554508054161216, 28914094089986783, 5129283016944966, 4954196309696329, 10502831804066725,
    8625708843063759, 27914093841853965
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    9095397022792557, 5930737345064576, 0, 6845490052533228, 12751334836632874, 13016285982108815,
    14970600263694069, 10547858506059663
  ]

abbrev PositiveTerm := Fin 56
abbrev NegativeTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 10791815131 / 3906250000
noncomputable def negativeCeiling : ℝ := 128148604939 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6327150226413806253143014506496, coefficient := 6327150226413806253143014506496 }, { argument := 32630319896756151312195747053568, coefficient := 32630319896756151312195747053568 }, { argument := 677153201489103010369820950528, coefficient := 677153201489103010369820950528 }, { argument := 761797351675240886666048569344, coefficient := 761797351675240886666048569344 }, { argument := 761797351675240886666048569344, coefficient := 761797351675240886666048569344 }, { argument := 804119426768309824814162378752, coefficient := 804119426768309824814162378752 }, { argument := 86675609790605185327337081667584, coefficient := (-86675609790605185327337081667584) }, { argument := 35397347998316342235396833280, coefficient := 35397347998316342235396833280 }, { argument := 630072794370030891790063632384, coefficient := 630072794370030891790063632384 }, { argument := 35397347998316342235396833280, coefficient := 35397347998316342235396833280 }, { argument := 560458009973342085393783193600, coefficient := 560458009973342085393783193600 }, { argument := 956908307554485118430227726336, coefficient := 956908307554485118430227726336 }, { argument := 35397347998316342235396833280, coefficient := 35397347998316342235396833280 }, { argument := 956908307554485118430227726336, coefficient := 956908307554485118430227726336 }, { argument := 956908307554485118430227726336, coefficient := 956908307554485118430227726336 }, { argument := 630072794370030891790063632384, coefficient := 630072794370030891790063632384 }, { argument := 35397347998316342235396833280, coefficient := 35397347998316342235396833280 }, { argument := 4832917913370124593206180970496, coefficient := (-4832917913370124593206180970496) }, { argument := 37370314935927417048517312512, coefficient := 37370314935927417048517312512 }, { argument := 41857847578336920545026637824, coefficient := 41857847578336920545026637824 }, { argument := 37370314935927417048517312512, coefficient := 37370314935927417048517312512 }, { argument := 41857847578336920545026637824, coefficient := 41857847578336920545026637824 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 18222477378280797646515108577280, coefficient := 18222477378280797646515108577280 }, { argument := 18222477378280797646515108577280, coefficient := (-18222477378280797646515108577280) }, { argument := 273139125638451260547385419366400, coefficient := 273139125638451260547385419366400 }, { argument := 273139054897401347160100118200320, coefficient := 273139054897401347160100118200320 }, { argument := 546278180535852607707485537566720, coefficient := (-546278180535852607707485537566720) }, { argument := 472153585373971507565307126349824, coefficient := 472153585373971507565307126349824 }, { argument := 1681314150091072244385166590476288, coefficient := 1681314150091072244385166590476288 }, { argument := 472153570257676395899572797308928, coefficient := 472153570257676395899572797308928 }, { argument := 2625621305722720147850046514135040, coefficient := (-2625621305722720147850046514135040) }, { argument := 33267474847752374225261016645632, coefficient := 33267474847752374225261016645632 }, { argument := 1238621831786925813877648432037888, coefficient := 1238621831786925813877648432037888 }, { argument := 1238566303278675379692915407192064, coefficient := 1238566303278675379692915407192064 }, { argument := 33323003932131519320090757562368, coefficient := 33323003932131519320090757562368 }, { argument := 2543778613845485087115915613437952, coefficient := (-2543778613845485087115915613437952) }, { argument := 253130214940303733559780179968, coefficient := 253130214940303733559780179968 }, { argument := 39013139712119067480722545573888, coefficient := 39013139712119067480722545573888 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 395740295329224199250398465228800, coefficient := 395740295329224199250398465228800 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 94818469884014595430554796032, coefficient := 94818469884014595430554796032 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 39013140080463653144554872242176, coefficient := 39013140080463653144554872242176 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5957586439060892572952035328, coefficient := 5957586439060892572952035328 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 253112529677825386738454888448, coefficient := 253112529677825386738454888448 }, { argument := 474418237135414853510141174611968, coefficient := (-474418237135414853510141174611968) }, { argument := 58179923413539692865061388288, coefficient := 58179923413539692865061388288 }, { argument := 4777484669418749337826052014080, coefficient := 4777484669418749337826052014080 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1199254413057712141308526592, coefficient := 1199254413057712141308526592 }, { argument := 56132843656346461839957164032, coefficient := 56132843656346461839957164032 }, { argument := 15280822359928912768286064640, coefficient := 15280822359928912768286064640 }, { argument := 4777483847726981318507784830976, coefficient := 4777483847726981318507784830976 }] }

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

end TermShard6


end Parent2

namespace Parent2

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-951758270453637441699844303355904)
def positiveArguments : Array ℕ := #[
    1451, 35, 35, 15, 35, 395,
    15, 3080063, 31
  ]
def positiveCoefficients : Array ℕ := #[
    56132843656346461839957164032, 1353996917968384675670917120, 1353996917968384675670917120, 1160568786830044007717928960, 1353996917968384675670917120, 15280822359928912768286064640,
    1160568786830044007717928960, 58180745105307712183328571392, 1199254413057712141308526592
  ]
def positiveScales : Array ℕ := #[
    10, 5, 5, 3, 5, 8,
    3, 21, 4
  ]
def negativeArguments : Array ℕ := #[
    31
  ]
def negativeCoefficients : Array ℕ := #[
    9824292151768777861599449841664
  ]
def negativeScales : Array ℕ := #[
    4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10502831804066725, 5129283016944966, 5129283016944966, 3906890595303263, 5129283016944966, 8625708843063759,
    3906890595303263, 21554528429613746, 4954196309696329
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4954196321574415
  ]

abbrev PositiveTerm := Fin 9
abbrev NegativeTerm := Fin 1
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
noncomputable def positiveFloor : ℝ := 24209723 / 1000000000000
noncomputable def negativeCeiling : ℝ := 292930767 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 56132843656346461839957164032, coefficient := 56132843656346461839957164032 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 15280822359928912768286064640, coefficient := 15280822359928912768286064640 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 58180745105307712183328571392, coefficient := 58180745105307712183328571392 }, { argument := 1199254413057712141308526592, coefficient := 1199254413057712141308526592 }, { argument := 9824292151768777861599449841664, coefficient := (-9824292151768777861599449841664) }] }

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

end TermShard7


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17
