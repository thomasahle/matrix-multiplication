import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 7, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk7

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
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    1, 220087, 127633, 4084267, 220083, 6015,
    1318507, 14043967, 1322055, 44567
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 2078662944230663212293423104, 77149414567436982727636680704, 77149622351562228992026083328, 2078625165298800255131713536, 454480550311374655366103040,
    12452946528458014603549343744, 132641518094654725365709144064, 12486456441020457605985730560, 420923414084102956477579264
  ]
def positiveScales : Array ℕ := #[
    0, 17, 16, 21, 17, 12,
    20, 23, 20, 15
  ]
def negativeArguments : Array ℕ := #[
    1323823305, 290186250109, 3090894565129, 290967118785, 9808617329, 1323823305,
    767712495, 24566866005, 1323799245, 767712495, 168285003931, 1792473640111,
    168737845815, 5688219911, 290186250109, 168285003931, 5385134629369, 290180976081,
    24566866005, 5385134629369, 57359310967189, 5399625608685, 182023527389, 3090894565129,
    1792473640111, 57359310967189, 3090838389261, 1323799245, 290180976081, 3090838389261,
    290961830565, 9808439061, 290967118785, 168737845815, 5399625608685, 290961830565,
    9808617329, 5688219911, 182023527389, 9808439061, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    2980985071551189237104640, 81680167991183372141461504, 870009475734778479980314624, 81899962983574552927272960, 2760880334244011860557824, 2980985071551189237104640,
    110639030605109560753520640, 110639328585778905722388480, 2980930893247671970037760, 110639030605109560753520640, 3031553123982776218213679104, 32290334470701344609454260224,
    3039710798142936831712296960, 102469860286324143684583424, 81680167991183372141461504, 3031553123982776218213679104, 3031561288770772810625712128, 81678683484274900793819136,
    110639328585778905722388480, 3031561288770772810625712128, 32290421437257598114325331968, 3039718984901744206251294720, 102470136265220459088314368, 870009475734778479980314624,
    32290334470701344609454260224, 32290421437257598114325331968, 869993663633641479094665216, 2980930893247671970037760, 81678683484274900793819136, 869993663633641479094665216,
    81898474481973212102000640, 2760830156262863605334016, 81899962983574552927272960, 3039710798142936831712296960, 3039718984901744206251294720, 81898474481973212102000640,
    2760880334244011860557824, 102469860286324143684583424, 102470136265220459088314368, 2760830156262863605334016, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    30, 38, 41, 38, 33, 30,
    29, 34, 30, 29, 37, 40,
    37, 32, 38, 37, 42, 38,
    34, 42, 45, 42, 37, 41,
    40, 45, 41, 30, 38, 41,
    38, 33, 38, 37, 42, 38,
    33, 32, 37, 33, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 17747714405707408, 16961641865305266, 21961645750865787, 17747688185019210, 12554349022063343,
    20330473799865652, 23743447175542703, 20334350766273187, 15443688229645390
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    30302063427784117, 38078188205586330, 41491161581275663, 38082065171993866, 33191402635366070, 30302063427784117,
    29515990888151161, 34515994773711733, 30302037207095911, 29515990888151161, 37292115665952917, 40705089041723604,
    37295992632360452, 32405330095732665, 38078188205586330, 37292115665952917, 42292119551513488, 38078161984898125,
    34515994773711733, 42292119551513488, 45705092927284183, 42295996517921024, 37405333981293237, 41491161581275663,
    40705089041723604, 45705092927284183, 41491135360587457, 30302037207095911, 38078161984898125, 41491135360587457,
    38082038951305660, 33191376414677865, 38082065171993866, 37295992632360452, 42295996517921024, 38082038951305660,
    33191402635366070, 32405330095732665, 37405333981293237, 33191376414677865, 0, 0
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
noncomputable def positiveFloor : ℝ := 81194163 / 1000000000000
noncomputable def negativeCeiling : ℝ := 20298541 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2980985071551189237104640, coefficient := (-2980985071551189237104640) }, { argument := 81680167991183372141461504, coefficient := (-81680167991183372141461504) }, { argument := 870009475734778479980314624, coefficient := (-870009475734778479980314624) }, { argument := 81899962983574552927272960, coefficient := (-81899962983574552927272960) }, { argument := 2760880334244011860557824, coefficient := (-2760880334244011860557824) }, { argument := 2980985071551189237104640, coefficient := (-2980985071551189237104640) }, { argument := 110639030605109560753520640, coefficient := (-110639030605109560753520640) }, { argument := 110639328585778905722388480, coefficient := (-110639328585778905722388480) }, { argument := 2980930893247671970037760, coefficient := (-2980930893247671970037760) }, { argument := 110639030605109560753520640, coefficient := (-110639030605109560753520640) }, { argument := 3031553123982776218213679104, coefficient := (-3031553123982776218213679104) }, { argument := 32290334470701344609454260224, coefficient := (-32290334470701344609454260224) }, { argument := 3039710798142936831712296960, coefficient := (-3039710798142936831712296960) }, { argument := 102469860286324143684583424, coefficient := (-102469860286324143684583424) }, { argument := 81680167991183372141461504, coefficient := (-81680167991183372141461504) }, { argument := 3031553123982776218213679104, coefficient := (-3031553123982776218213679104) }, { argument := 3031561288770772810625712128, coefficient := (-3031561288770772810625712128) }, { argument := 81678683484274900793819136, coefficient := (-81678683484274900793819136) }, { argument := 110639328585778905722388480, coefficient := (-110639328585778905722388480) }, { argument := 3031561288770772810625712128, coefficient := (-3031561288770772810625712128) }, { argument := 32290421437257598114325331968, coefficient := (-32290421437257598114325331968) }, { argument := 3039718984901744206251294720, coefficient := (-3039718984901744206251294720) }, { argument := 102470136265220459088314368, coefficient := (-102470136265220459088314368) }, { argument := 870009475734778479980314624, coefficient := (-870009475734778479980314624) }, { argument := 32290334470701344609454260224, coefficient := (-32290334470701344609454260224) }, { argument := 32290421437257598114325331968, coefficient := (-32290421437257598114325331968) }, { argument := 869993663633641479094665216, coefficient := (-869993663633641479094665216) }, { argument := 2980930893247671970037760, coefficient := (-2980930893247671970037760) }, { argument := 81678683484274900793819136, coefficient := (-81678683484274900793819136) }, { argument := 869993663633641479094665216, coefficient := (-869993663633641479094665216) }, { argument := 81898474481973212102000640, coefficient := (-81898474481973212102000640) }, { argument := 2760830156262863605334016, coefficient := (-2760830156262863605334016) }, { argument := 81899962983574552927272960, coefficient := (-81899962983574552927272960) }, { argument := 3039710798142936831712296960, coefficient := (-3039710798142936831712296960) }, { argument := 3039718984901744206251294720, coefficient := (-3039718984901744206251294720) }, { argument := 81898474481973212102000640, coefficient := (-81898474481973212102000640) }, { argument := 2760880334244011860557824, coefficient := (-2760880334244011860557824) }, { argument := 102469860286324143684583424, coefficient := (-102469860286324143684583424) }, { argument := 102470136265220459088314368, coefficient := (-102470136265220459088314368) }, { argument := 2760830156262863605334016, coefficient := (-2760830156262863605334016) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 2078662944230663212293423104, coefficient := 2078662944230663212293423104 }, { argument := 77149414567436982727636680704, coefficient := 77149414567436982727636680704 }, { argument := 77149622351562228992026083328, coefficient := 77149622351562228992026083328 }, { argument := 2078625165298800255131713536, coefficient := 2078625165298800255131713536 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 454480550311374655366103040, coefficient := 454480550311374655366103040 }, { argument := 12452946528458014603549343744, coefficient := 12452946528458014603549343744 }, { argument := 132641518094654725365709144064, coefficient := 132641518094654725365709144064 }, { argument := 12486456441020457605985730560, coefficient := 12486456441020457605985730560 }, { argument := 420923414084102956477579264, coefficient := 420923414084102956477579264 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk7
