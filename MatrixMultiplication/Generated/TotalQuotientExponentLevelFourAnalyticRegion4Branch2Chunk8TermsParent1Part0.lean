import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
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

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-13135810568657003783447216390144)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    6776228443, 137459054979, 3888665, 1280946726893, 6633605, 3888665,
    30880575, 30880575, 6633605, 560653995, 6633605, 137461549527,
    30880575, 3888665, 6633605, 3888665, 30880575, 30880575,
    3388158767, 6776228443, 546479977233, 136619883831, 13551747933, 546479977233,
    12009788859529, 138717705, 117966504058823, 236636085, 138717705, 1101581775,
    1101581775, 236636085, 19999829115, 236636085, 12010018751877, 1101581775,
    138717705, 236636085, 138717705, 1101581775, 1101581775, 273244093837,
    137459054979, 12009788859529, 3002443353983, 274896808565, 3888665, 138717705,
    138717705, 3888597, 136619883831, 3002443353983, 138717705, 29491579431601,
    236636085, 138717705, 1101581775, 1101581775, 236636085, 19999829115,
    236636085, 3002500826979, 1101581775, 138717705
  ]
def negativeCoefficients : Array ℕ := #[
    7629354972718039073554432, 154765137195531230716624896, 35866604021695876767416320, 1442217800479192826859487232, 30592103430270012536913920, 4483325502711984595927040,
    35602878992124583555891200, 35602878992124583555891200, 30592103430270012536913920, 646390047479239661448069120, 30592103430270012536913920, 154767945806892045170638848,
    35602878992124583555891200, 4483325502711984595927040, 30592103430270012536913920, 4483325502711984595927040, 35602878992124583555891200, 35602878992124583555891200,
    7629455280266639589769216, 7629354972718039073554432, 307640877728996992216989696, 307640628956346025758425088, 7628955867659711174148096, 307640877728996992216989696,
    6760910079071642316122882048, 1279445001313669918375280640, 66409237965189420843349835776, 1091291324649894930378915840, 159930625164208739796910080, 1270037317480481168975462400,
    1270037317480481168975462400, 1091291324649894930378915840, 23058233075145624778954506240, 1091291324649894930378915840, 6761039496958240832171802624, 1270037317480481168975462400,
    159930625164208739796910080, 1091291324649894930378915840, 159930625164208739796910080, 1270037317480481168975462400, 1270037317480481168975462400, 307645499796375510647308288,
    154765137195531230716624896, 6760910079071642316122882048, 6760901385099430508609142784, 154753145577334071655137280, 35866604021695876767416320, 1279445001313669918375280640,
    1279445001313669918375280640, 35865976832397370642661376, 307640628956346025758425088, 6760901385099430508609142784, 1279445001313669918375280640, 66409133069362823912958722048,
    1091291324649894930378915840, 159930625164208739796910080, 1270037317480481168975462400, 1270037317480481168975462400, 1091291324649894930378915840, 23058233075145624778954506240,
    1091291324649894930378915840, 6761030802781115241612705792, 1270037317480481168975462400, 159930625164208739796910080
  ]
def negativeScales : Array ℕ := #[
    32, 37, 21, 40, 22, 21,
    24, 24, 22, 29, 22, 37,
    24, 21, 22, 21, 24, 24,
    31, 32, 38, 36, 33, 38,
    43, 27, 46, 27, 27, 30,
    30, 27, 34, 27, 43, 30,
    27, 27, 27, 30, 30, 37,
    37, 43, 41, 38, 21, 27,
    27, 21, 36, 41, 27, 44,
    27, 27, 30, 30, 27, 34,
    27, 41, 30, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32657835366230724, 37000210989848042, 21890843528124315, 40220347615541450, 22661361678326961, 21890843528124315,
    24880196283270827, 24880196283270827, 22661361678326961, 29062535452037856, 22661361678326961, 37000237171021588,
    24880196283270827, 21890843528124315, 22661361678326961, 21890843528124315, 24880196283270827, 24880196283270827,
    31657854334053330, 32657835366230724, 38991377701586432, 36991376534955596, 33657759894326268, 38991377701586432,
    43449276021216434, 27047576694457359, 46745370601024340, 27818094849264711, 27047576694457359, 30036929450257850,
    30036929450257850, 27818094849264711, 34219268622073859, 27818094849264711, 43449303637137075, 30036929450257850,
    27047576694457359, 27818094849264711, 27047576694457359, 30036929450257850, 30036929450257850, 37991399376813264,
    37000210989848042, 43449276021216434, 41449274166028520, 38000099201633408, 21890843528124315, 27047576694457359,
    27047576694457359, 21890818299896343, 36991376534955596, 41449274166028520, 27047576694457359, 44745368322232809,
    27818094849264711, 27047576694457359, 30036929450257850, 30036929450257850, 27818094849264711, 34219268622073859,
    27818094849264711, 41449301781940948, 30036929450257850, 27047576694457359
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 123052011 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7629354972718039073554432, coefficient := (-7629354972718039073554432) }, { argument := 154765137195531230716624896, coefficient := (-154765137195531230716624896) }, { argument := 35866604021695876767416320, coefficient := (-35866604021695876767416320) }, { argument := 1442217800479192826859487232, coefficient := (-1442217800479192826859487232) }, { argument := 30592103430270012536913920, coefficient := (-30592103430270012536913920) }, { argument := 4483325502711984595927040, coefficient := (-4483325502711984595927040) }, { argument := 35602878992124583555891200, coefficient := (-35602878992124583555891200) }, { argument := 35602878992124583555891200, coefficient := (-35602878992124583555891200) }, { argument := 30592103430270012536913920, coefficient := (-30592103430270012536913920) }, { argument := 646390047479239661448069120, coefficient := (-646390047479239661448069120) }, { argument := 30592103430270012536913920, coefficient := (-30592103430270012536913920) }, { argument := 154767945806892045170638848, coefficient := (-154767945806892045170638848) }, { argument := 35602878992124583555891200, coefficient := (-35602878992124583555891200) }, { argument := 4483325502711984595927040, coefficient := (-4483325502711984595927040) }, { argument := 30592103430270012536913920, coefficient := (-30592103430270012536913920) }, { argument := 4483325502711984595927040, coefficient := (-4483325502711984595927040) }, { argument := 35602878992124583555891200, coefficient := (-35602878992124583555891200) }, { argument := 35602878992124583555891200, coefficient := (-35602878992124583555891200) }, { argument := 7629455280266639589769216, coefficient := (-7629455280266639589769216) }, { argument := 7629354972718039073554432, coefficient := (-7629354972718039073554432) }, { argument := 307640877728996992216989696, coefficient := (-307640877728996992216989696) }, { argument := 307640628956346025758425088, coefficient := (-307640628956346025758425088) }, { argument := 7628955867659711174148096, coefficient := (-7628955867659711174148096) }, { argument := 307640877728996992216989696, coefficient := (-307640877728996992216989696) }, { argument := 6760910079071642316122882048, coefficient := (-6760910079071642316122882048) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 66409237965189420843349835776, coefficient := (-66409237965189420843349835776) }, { argument := 1091291324649894930378915840, coefficient := (-1091291324649894930378915840) }, { argument := 159930625164208739796910080, coefficient := (-159930625164208739796910080) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 1091291324649894930378915840, coefficient := (-1091291324649894930378915840) }, { argument := 23058233075145624778954506240, coefficient := (-23058233075145624778954506240) }, { argument := 1091291324649894930378915840, coefficient := (-1091291324649894930378915840) }, { argument := 6761039496958240832171802624, coefficient := (-6761039496958240832171802624) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 159930625164208739796910080, coefficient := (-159930625164208739796910080) }, { argument := 1091291324649894930378915840, coefficient := (-1091291324649894930378915840) }, { argument := 159930625164208739796910080, coefficient := (-159930625164208739796910080) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 307645499796375510647308288, coefficient := (-307645499796375510647308288) }, { argument := 154765137195531230716624896, coefficient := (-154765137195531230716624896) }, { argument := 6760910079071642316122882048, coefficient := (-6760910079071642316122882048) }, { argument := 6760901385099430508609142784, coefficient := (-6760901385099430508609142784) }, { argument := 154753145577334071655137280, coefficient := (-154753145577334071655137280) }, { argument := 35866604021695876767416320, coefficient := (-35866604021695876767416320) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 35865976832397370642661376, coefficient := (-35865976832397370642661376) }, { argument := 307640628956346025758425088, coefficient := (-307640628956346025758425088) }, { argument := 6760901385099430508609142784, coefficient := (-6760901385099430508609142784) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 66409133069362823912958722048, coefficient := (-66409133069362823912958722048) }, { argument := 1091291324649894930378915840, coefficient := (-1091291324649894930378915840) }, { argument := 159930625164208739796910080, coefficient := (-159930625164208739796910080) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 1091291324649894930378915840, coefficient := (-1091291324649894930378915840) }, { argument := 23058233075145624778954506240, coefficient := (-23058233075145624778954506240) }, { argument := 1091291324649894930378915840, coefficient := (-1091291324649894930378915840) }, { argument := 6761030802781115241612705792, coefficient := (-6761030802781115241612705792) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 159930625164208739796910080, coefficient := (-159930625164208739796910080) }] }

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

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-11619128636337379712790188523520)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    236636085, 138717705, 1101581775, 1101581775, 68310968219, 1280946726893,
    117966504058823, 29491579431601, 2561649649051, 6633605, 236636085, 236636085,
    6633489, 3888665, 138717705, 138717705, 3888597, 30880575,
    1101581775, 1101581775, 30880035, 30880575, 1101581775, 1101581775,
    30880035, 6633605, 236636085, 236636085, 6633489, 560653995,
    19999829115, 19999829115, 560644191, 6633605, 236636085, 236636085,
    6633489, 13551747933, 274896808565, 3888597, 2561649649051, 6633489,
    3888597, 30880035, 30880035, 6633489, 560644191, 6633489,
    274901797185, 30880035, 3888597, 6633489, 3888597, 30880035,
    30880035, 6775963049, 137461549527, 12010018751877, 3002500826979, 274901797185,
    30880575, 1101581775, 1101581775, 30880035
  ]
def negativeCoefficients : Array ℕ := #[
    1091291324649894930378915840, 159930625164208739796910080, 1270037317480481168975462400, 1270037317480481168975462400, 307645251016406194794266624, 1442217800479192826859487232,
    66409237965189420843349835776, 66409133069362823912958722048, 1442080550614980681543974912, 30592103430270012536913920, 1091291324649894930378915840, 1091291324649894930378915840,
    30591568474691874959917056, 4483325502711984595927040, 159930625164208739796910080, 159930625164208739796910080, 4483247104049671330332672, 35602878992124583555891200,
    1270037317480481168975462400, 1270037317480481168975462400, 35602256414512095858524160, 35602878992124583555891200, 1270037317480481168975462400, 1270037317480481168975462400,
    35602256414512095858524160, 30592103430270012536913920, 1091291324649894930378915840, 1091291324649894930378915840, 30591568474691874959917056, 646390047479239661448069120,
    23058233075145624778954506240, 23058233075145624778954506240, 646378744236808495920316416, 30592103430270012536913920, 1091291324649894930378915840, 1091291324649894930378915840,
    30591568474691874959917056, 7628955867659711174148096, 154753145577334071655137280, 35865976832397370642661376, 1442080550614980681543974912, 30591568474691874959917056,
    4483247104049671330332672, 35602256414512095858524160, 35602256414512095858524160, 30591568474691874959917056, 646378744236808495920316416, 30591568474691874959917056,
    154755953920730708280606720, 35602256414512095858524160, 4483247104049671330332672, 30591568474691874959917056, 4483247104049671330332672, 35602256414512095858524160,
    35602256414512095858524160, 7629056165638162482200576, 154767945806892045170638848, 6761039496958240832171802624, 6761030802781115241612705792, 154755953920730708280606720,
    35602878992124583555891200, 1270037317480481168975462400, 1270037317480481168975462400, 35602256414512095858524160
  ]
def negativeScales : Array ℕ := #[
    27, 27, 30, 30, 35, 40,
    46, 44, 41, 22, 27, 27,
    22, 21, 27, 27, 21, 24,
    30, 30, 24, 24, 30, 30,
    24, 22, 27, 27, 22, 29,
    34, 34, 29, 22, 27, 27,
    22, 33, 38, 21, 41, 22,
    21, 24, 24, 22, 29, 22,
    38, 24, 21, 22, 21, 24,
    24, 32, 37, 43, 41, 38,
    24, 30, 30, 24
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    27818094849264711, 27047576694457359, 30036929450257850, 30036929450257850, 35991398210165637, 40220347615541450,
    46745370601024340, 44745368322232809, 41220210313726930, 22661361678326961, 27818094849264711, 27818094849264711,
    22661336450100665, 21890843528124315, 27047576694457359, 27047576694457359, 21890818299896343, 24880196283270827,
    30036929450257850, 30036929450257850, 24880171055043135, 24880196283270827, 30036929450257850, 30036929450257850,
    24880171055043135, 22661361678326961, 27818094849264711, 27818094849264711, 22661336450100665, 29062535452037856,
    34219268622073859, 34219268622073859, 29062510223811577, 22661361678326961, 27818094849264711, 27818094849264711,
    22661336450100665, 33657759894326268, 38000099201633408, 21890818299896343, 41220210313726930, 22661336450100665,
    21890818299896343, 24880171055043135, 24880171055043135, 22661336450100665, 29062510223811577, 22661336450100665,
    38000125382337614, 24880171055043135, 21890818299896343, 22661336450100665, 21890818299896343, 24880171055043135,
    24880171055043135, 32657778861331394, 37000237171021588, 43449303637137075, 41449301781940948, 38000125382337614,
    24880196283270827, 30036929450257850, 30036929450257850, 24880171055043135
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 13608971 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1091291324649894930378915840, coefficient := (-1091291324649894930378915840) }, { argument := 159930625164208739796910080, coefficient := (-159930625164208739796910080) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 307645251016406194794266624, coefficient := (-307645251016406194794266624) }, { argument := 1442217800479192826859487232, coefficient := (-1442217800479192826859487232) }, { argument := 66409237965189420843349835776, coefficient := (-66409237965189420843349835776) }, { argument := 66409133069362823912958722048, coefficient := (-66409133069362823912958722048) }, { argument := 1442080550614980681543974912, coefficient := (-1442080550614980681543974912) }, { argument := 30592103430270012536913920, coefficient := (-30592103430270012536913920) }, { argument := 1091291324649894930378915840, coefficient := (-1091291324649894930378915840) }, { argument := 1091291324649894930378915840, coefficient := (-1091291324649894930378915840) }, { argument := 30591568474691874959917056, coefficient := (-30591568474691874959917056) }, { argument := 4483325502711984595927040, coefficient := (-4483325502711984595927040) }, { argument := 159930625164208739796910080, coefficient := (-159930625164208739796910080) }, { argument := 159930625164208739796910080, coefficient := (-159930625164208739796910080) }, { argument := 4483247104049671330332672, coefficient := (-4483247104049671330332672) }, { argument := 35602878992124583555891200, coefficient := (-35602878992124583555891200) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 35602256414512095858524160, coefficient := (-35602256414512095858524160) }, { argument := 35602878992124583555891200, coefficient := (-35602878992124583555891200) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 35602256414512095858524160, coefficient := (-35602256414512095858524160) }, { argument := 30592103430270012536913920, coefficient := (-30592103430270012536913920) }, { argument := 1091291324649894930378915840, coefficient := (-1091291324649894930378915840) }, { argument := 1091291324649894930378915840, coefficient := (-1091291324649894930378915840) }, { argument := 30591568474691874959917056, coefficient := (-30591568474691874959917056) }, { argument := 646390047479239661448069120, coefficient := (-646390047479239661448069120) }, { argument := 23058233075145624778954506240, coefficient := (-23058233075145624778954506240) }, { argument := 23058233075145624778954506240, coefficient := (-23058233075145624778954506240) }, { argument := 646378744236808495920316416, coefficient := (-646378744236808495920316416) }, { argument := 30592103430270012536913920, coefficient := (-30592103430270012536913920) }, { argument := 1091291324649894930378915840, coefficient := (-1091291324649894930378915840) }, { argument := 1091291324649894930378915840, coefficient := (-1091291324649894930378915840) }, { argument := 30591568474691874959917056, coefficient := (-30591568474691874959917056) }, { argument := 7628955867659711174148096, coefficient := (-7628955867659711174148096) }, { argument := 154753145577334071655137280, coefficient := (-154753145577334071655137280) }, { argument := 35865976832397370642661376, coefficient := (-35865976832397370642661376) }, { argument := 1442080550614980681543974912, coefficient := (-1442080550614980681543974912) }, { argument := 30591568474691874959917056, coefficient := (-30591568474691874959917056) }, { argument := 4483247104049671330332672, coefficient := (-4483247104049671330332672) }, { argument := 35602256414512095858524160, coefficient := (-35602256414512095858524160) }, { argument := 35602256414512095858524160, coefficient := (-35602256414512095858524160) }, { argument := 30591568474691874959917056, coefficient := (-30591568474691874959917056) }, { argument := 646378744236808495920316416, coefficient := (-646378744236808495920316416) }, { argument := 30591568474691874959917056, coefficient := (-30591568474691874959917056) }, { argument := 154755953920730708280606720, coefficient := (-154755953920730708280606720) }, { argument := 35602256414512095858524160, coefficient := (-35602256414512095858524160) }, { argument := 4483247104049671330332672, coefficient := (-4483247104049671330332672) }, { argument := 30591568474691874959917056, coefficient := (-30591568474691874959917056) }, { argument := 4483247104049671330332672, coefficient := (-4483247104049671330332672) }, { argument := 35602256414512095858524160, coefficient := (-35602256414512095858524160) }, { argument := 35602256414512095858524160, coefficient := (-35602256414512095858524160) }, { argument := 7629056165638162482200576, coefficient := (-7629056165638162482200576) }, { argument := 154767945806892045170638848, coefficient := (-154767945806892045170638848) }, { argument := 6761039496958240832171802624, coefficient := (-6761039496958240832171802624) }, { argument := 6761030802781115241612705792, coefficient := (-6761030802781115241612705792) }, { argument := 154755953920730708280606720, coefficient := (-154755953920730708280606720) }, { argument := 35602878992124583555891200, coefficient := (-35602878992124583555891200) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 1270037317480481168975462400, coefficient := (-1270037317480481168975462400) }, { argument := 35602256414512095858524160, coefficient := (-35602256414512095858524160) }] }

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

end TermShard1


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk8
