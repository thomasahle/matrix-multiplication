import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 20, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3090836690221447999556827270348800)
def positiveArguments : Array ℕ := #[
    3895, 3515, 1805, 1805, 3515, 108965,
    3515, 285, 4655, 4641, 69615, 122213,
    4641, 38675, 4641, 122213, 242879, 38675,
    3748381, 239785, 69615, 122213, 4641, 239785,
    4641, 122213, 122213, 4641, 15201, 69249,
    1689, 724581, 32091, 1689, 32091, 62493,
    1180611, 62493, 724581, 1180611, 15201, 62493,
    62493, 69249, 707, 3535, 2929, 52621,
    19695, 707, 78881, 78881, 56459, 2929,
    61, 67, 61, 67, 939524001
  ]
def positiveCoefficients : Array ℕ := #[
    1205444113254139042683022213120, 67989988095126744785475338240, 69827555340940981131028725760, 69827555340940981131028725760, 67989988095126744785475338240, 2107689630948929088349735485440,
    67989988095126744785475338240, 88203227799083344586562600960, 90040795044897580932115988480, 179539991322607807993963610112, 2693099869839117119909454151680, 4727886438162005610507708399616,
    179539991322607807993963610112, 2992333188710130133232726835200, 179539991322607807993963610112, 4727886438162005610507708399616, 4697963106274904309175381131264, 2992333188710130133232726835200,
    72504233162446453128228971216896, 4638116442500701706510726594560, 2693099869839117119909454151680, 4727886438162005610507708399616, 179539991322607807993963610112, 4638116442500701706510726594560,
    179539991322607807993963610112, 4727886438162005610507708399616, 4727886438162005610507708399616, 179539991322607807993963610112, 1176120408573566597421349208064, 1339470465319895291507647709184,
    1045440363176503642152310407168, 14015434868835001952604411396096, 1241460431272098075055868608512, 1045440363176503642152310407168, 1241460431272098075055868608512, 1208790419922832336238608908288,
    45672675866273502866529060913152, 1208790419922832336238608908288, 14015434868835001952604411396096, 45672675866273502866529060913152, 1176120408573566597421349208064, 1208790419922832336238608908288,
    1208790419922832336238608908288, 1339470465319895291507647709184, 54701475485922740897105051648, 1094029509718454817942101032960, 56655099610419981643430232064, 1017838168863062428835418996736,
    1523826817107847782133640724480, 54701475485922740897105051648, 1525780441232345022879965904896, 1525780441232345022879965904896, 1092075885593957577195775852544, 56655099610419981643430232064,
    37757171198204098384423288832, 41470991316060239209120661504, 37757171198204098384423288832, 41470991316060239209120661504, 4436776652173987032622165917696
  ]
def positiveScales : Array ℕ := #[
    11, 11, 10, 10, 11, 16,
    11, 8, 12, 12, 16, 16,
    12, 15, 12, 16, 17, 15,
    21, 17, 16, 16, 12, 17,
    12, 16, 16, 12, 13, 16,
    10, 19, 14, 10, 14, 15,
    20, 15, 19, 20, 13, 15,
    15, 16, 9, 11, 11, 15,
    14, 9, 16, 16, 15, 11,
    5, 6, 5, 6, 29
  ]
def negativeArguments : Array ℕ := #[
    95, 1547, 1689, 101, 1
  ]
def negativeCoefficients : Array ℕ := #[
    7526675438855112071386675281920, 122565967409566930257212491169792, 133816366486592466195495732117504, 8002044413940698096947938983936, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    6, 10, 10, 6, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11927407612511617, 11779308973933791, 10817783121717284, 10817783121717284, 11779308973933791, 16733505284337084,
    11779308973933791, 8154818109052103, 12184565452446155, 12180219982170191, 16087110577778710, 16899038229360781,
    12180219982170191, 15239113671223760, 12180219982170191, 16899038229360781, 17889878230115694, 15239113671223760,
    21837836170815528, 17871381886563018, 16087110577778710, 16899038229360781, 12180219982170191, 17871381886563018,
    12180219982170191, 16899038229360781, 16899038229360781, 12180219982170191, 13891878614010432, 16079505617419469,
    10721953612793919, 19466787450300925, 14969881125348714, 10721953612793919, 14969881125348714, 15931406977961630,
    20171102258176822, 15931406977961630, 19466787450300925, 20171102258176822, 13891878614010432, 15931406977961630,
    15931406977961630, 16079505617419469, 9465566404809393, 11787494499665800, 11516192477879337, 15683351045027278,
    14265541796501405, 9465566404809393, 16267390220893773, 16267390220893773, 15784915955565637, 11516192477879337,
    5930737337099561, 6066089190457772, 5930737337099561, 6066089190457772, 29807354776132995
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6569855608333349, 10595257481453993, 10721953612921693, 6658211482778016, 0
  ]

abbrev PositiveTerm := Fin 59
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 64188676877 / 1000000000000
noncomputable def negativeCeiling : ℝ := 34138544673 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1205444113254139042683022213120, coefficient := 1205444113254139042683022213120 }, { argument := 67989988095126744785475338240, coefficient := 67989988095126744785475338240 }, { argument := 69827555340940981131028725760, coefficient := 69827555340940981131028725760 }, { argument := 69827555340940981131028725760, coefficient := 69827555340940981131028725760 }, { argument := 67989988095126744785475338240, coefficient := 67989988095126744785475338240 }, { argument := 2107689630948929088349735485440, coefficient := 2107689630948929088349735485440 }, { argument := 67989988095126744785475338240, coefficient := 67989988095126744785475338240 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 90040795044897580932115988480, coefficient := 90040795044897580932115988480 }, { argument := 7526675438855112071386675281920, coefficient := (-7526675438855112071386675281920) }, { argument := 179539991322607807993963610112, coefficient := 179539991322607807993963610112 }, { argument := 2693099869839117119909454151680, coefficient := 2693099869839117119909454151680 }, { argument := 4727886438162005610507708399616, coefficient := 4727886438162005610507708399616 }, { argument := 179539991322607807993963610112, coefficient := 179539991322607807993963610112 }, { argument := 2992333188710130133232726835200, coefficient := 2992333188710130133232726835200 }, { argument := 179539991322607807993963610112, coefficient := 179539991322607807993963610112 }, { argument := 4727886438162005610507708399616, coefficient := 4727886438162005610507708399616 }, { argument := 4697963106274904309175381131264, coefficient := 4697963106274904309175381131264 }, { argument := 2992333188710130133232726835200, coefficient := 2992333188710130133232726835200 }, { argument := 72504233162446453128228971216896, coefficient := 72504233162446453128228971216896 }, { argument := 4638116442500701706510726594560, coefficient := 4638116442500701706510726594560 }, { argument := 2693099869839117119909454151680, coefficient := 2693099869839117119909454151680 }, { argument := 4727886438162005610507708399616, coefficient := 4727886438162005610507708399616 }, { argument := 179539991322607807993963610112, coefficient := 179539991322607807993963610112 }, { argument := 4638116442500701706510726594560, coefficient := 4638116442500701706510726594560 }, { argument := 179539991322607807993963610112, coefficient := 179539991322607807993963610112 }, { argument := 4727886438162005610507708399616, coefficient := 4727886438162005610507708399616 }, { argument := 4727886438162005610507708399616, coefficient := 4727886438162005610507708399616 }, { argument := 179539991322607807993963610112, coefficient := 179539991322607807993963610112 }, { argument := 122565967409566930257212491169792, coefficient := (-122565967409566930257212491169792) }, { argument := 1176120408573566597421349208064, coefficient := 1176120408573566597421349208064 }, { argument := 1339470465319895291507647709184, coefficient := 1339470465319895291507647709184 }, { argument := 1045440363176503642152310407168, coefficient := 1045440363176503642152310407168 }, { argument := 14015434868835001952604411396096, coefficient := 14015434868835001952604411396096 }, { argument := 1241460431272098075055868608512, coefficient := 1241460431272098075055868608512 }, { argument := 1045440363176503642152310407168, coefficient := 1045440363176503642152310407168 }, { argument := 1241460431272098075055868608512, coefficient := 1241460431272098075055868608512 }, { argument := 1208790419922832336238608908288, coefficient := 1208790419922832336238608908288 }, { argument := 45672675866273502866529060913152, coefficient := 45672675866273502866529060913152 }, { argument := 1208790419922832336238608908288, coefficient := 1208790419922832336238608908288 }, { argument := 14015434868835001952604411396096, coefficient := 14015434868835001952604411396096 }, { argument := 45672675866273502866529060913152, coefficient := 45672675866273502866529060913152 }, { argument := 1176120408573566597421349208064, coefficient := 1176120408573566597421349208064 }, { argument := 1208790419922832336238608908288, coefficient := 1208790419922832336238608908288 }, { argument := 1208790419922832336238608908288, coefficient := 1208790419922832336238608908288 }, { argument := 1339470465319895291507647709184, coefficient := 1339470465319895291507647709184 }, { argument := 133816366486592466195495732117504, coefficient := (-133816366486592466195495732117504) }, { argument := 54701475485922740897105051648, coefficient := 54701475485922740897105051648 }, { argument := 1094029509718454817942101032960, coefficient := 1094029509718454817942101032960 }, { argument := 56655099610419981643430232064, coefficient := 56655099610419981643430232064 }, { argument := 1017838168863062428835418996736, coefficient := 1017838168863062428835418996736 }, { argument := 1523826817107847782133640724480, coefficient := 1523826817107847782133640724480 }, { argument := 54701475485922740897105051648, coefficient := 54701475485922740897105051648 }, { argument := 1525780441232345022879965904896, coefficient := 1525780441232345022879965904896 }, { argument := 1525780441232345022879965904896, coefficient := 1525780441232345022879965904896 }, { argument := 1092075885593957577195775852544, coefficient := 1092075885593957577195775852544 }, { argument := 56655099610419981643430232064, coefficient := 56655099610419981643430232064 }, { argument := 8002044413940698096947938983936, coefficient := (-8002044413940698096947938983936) }, { argument := 37757171198204098384423288832, coefficient := 37757171198204098384423288832 }, { argument := 41470991316060239209120661504, coefficient := 41470991316060239209120661504 }, { argument := 37757171198204098384423288832, coefficient := 37757171198204098384423288832 }, { argument := 41470991316060239209120661504, coefficient := 41470991316060239209120661504 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 4436776652173987032622165917696, coefficient := 4436776652173987032622165917696 }] }

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


end Parent0

namespace Parent0

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-20398375629982060380058103511515136)
def positiveArguments : Array ℕ := #[
    939524191, 7946641531, 14383832749, 7946641963, 354452119, 27673953469,
    6918486463, 708906777, 1771345, 109984455, 16853249057, 1759752799,
    1771345, 892635, 158490917, 79245467, 446309
  ]
def positiveCoefficients : Array ℕ := #[
    4436777549423618777854756519936, 37526953617374322714392003608576, 135851459338160700645543256260608, 37526955657436643314078735925248, 6695411226190891787091020087296, 261373100620999494472723331022848,
    261373028680468494436548145577984, 6695435206367891799149415235584, 66919522060789853608434728960, 8310190462858956237947409530880, 79587218474231254851646675484672, 8310197636133643716938489135104,
    66919522060789853608434728960, 4215349605436345755327528960, 748452194280074861383339999232, 748452274560305070167308632064, 4215269325206136971358896128
  ]
def positiveScales : Array ℕ := #[
    29, 32, 33, 32, 28, 34,
    32, 29, 20, 26, 33, 30,
    20, 19, 27, 26, 18
  ]
def negativeArguments : Array ℕ := #[
    7, 1331, 6767, 19, 19
  ]
def negativeCoefficients : Array ℕ := #[
    8873554201597605810476922437632, 210905368612971666674013995794432, 536136975734026772495511911923712, 96341445617345434513749443608576, 1505335087771022414277335056384
  ]
def negativeScales : Array ℕ := #[
    2, 10, 12, 4, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    29807355067889277, 32887698120419314, 33743729099688039, 32887698198847948, 28401015513935463, 34687809709286963,
    32687809312198429, 29401020681059530, 20756413798515542, 26712724389395427, 33972307696413989, 30712725634715062,
    20756413798515542, 19767710849834828, 27239824922021690, 26239825076767558, 18767683373823658
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2807354922807594, 10378294855911895, 12724300673336465, 4247927513443586, 4247927513443586
  ]

abbrev PositiveTerm := Fin 17
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 341923108423 / 1000000000000
noncomputable def negativeCeiling : ℝ := 2275332981 / 20000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4436777549423618777854756519936, coefficient := 4436777549423618777854756519936 }, { argument := 8873554201597605810476922437632, coefficient := (-8873554201597605810476922437632) }, { argument := 37526953617374322714392003608576, coefficient := 37526953617374322714392003608576 }, { argument := 135851459338160700645543256260608, coefficient := 135851459338160700645543256260608 }, { argument := 37526955657436643314078735925248, coefficient := 37526955657436643314078735925248 }, { argument := 210905368612971666674013995794432, coefficient := (-210905368612971666674013995794432) }, { argument := 6695411226190891787091020087296, coefficient := 6695411226190891787091020087296 }, { argument := 261373100620999494472723331022848, coefficient := 261373100620999494472723331022848 }, { argument := 261373028680468494436548145577984, coefficient := 261373028680468494436548145577984 }, { argument := 6695435206367891799149415235584, coefficient := 6695435206367891799149415235584 }, { argument := 536136975734026772495511911923712, coefficient := (-536136975734026772495511911923712) }, { argument := 66919522060789853608434728960, coefficient := 66919522060789853608434728960 }, { argument := 8310190462858956237947409530880, coefficient := 8310190462858956237947409530880 }, { argument := 79587218474231254851646675484672, coefficient := 79587218474231254851646675484672 }, { argument := 8310197636133643716938489135104, coefficient := 8310197636133643716938489135104 }, { argument := 66919522060789853608434728960, coefficient := 66919522060789853608434728960 }, { argument := 96341445617345434513749443608576, coefficient := (-96341445617345434513749443608576) }, { argument := 4215349605436345755327528960, coefficient := 4215349605436345755327528960 }, { argument := 748452194280074861383339999232, coefficient := 748452194280074861383339999232 }, { argument := 748452274560305070167308632064, coefficient := 748452274560305070167308632064 }, { argument := 4215269325206136971358896128, coefficient := 4215269325206136971358896128 }, { argument := 1505335087771022414277335056384, coefficient := (-1505335087771022414277335056384) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20
