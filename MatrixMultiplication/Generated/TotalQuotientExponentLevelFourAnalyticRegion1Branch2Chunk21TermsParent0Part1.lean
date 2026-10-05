import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 21, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk21

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 26940559905719400007925668228628480
def positiveArguments : Array ℕ := #[
    3751, 35, 147, 637, 21, 21,
    49, 637, 637, 21, 7861, 315,
    147, 637, 49, 315, 49, 637,
    637, 21, 57, 1083
  ]
def positiveCoefficients : Array ℕ := #[
    297184837591005530313383357710336, 10831975343747077405367336960, 181977185774950900410171260928, 394283902512393617555371065344, 12998370412496492886440804352, 207973926599943886183052869632,
    15164765481245908367514271744, 394283902512393617555371065344, 394283902512393617555371065344, 207973926599943886183052869632, 4865723324411187170491007762432, 389951112374894786593224130560,
    181977185774950900410171260928, 394283902512393617555371065344, 15164765481245908367514271744, 389951112374894786593224130560, 15164765481245908367514271744, 394283902512393617555371065344,
    394283902512393617555371065344, 12998370412496492886440804352, 282250328957066702677000323072, 335172265636516709428937883648
  ]
def positiveScales : Array ℕ := #[
    11, 5, 7, 9, 4, 4,
    5, 9, 9, 4, 12, 8,
    7, 9, 5, 8, 5, 9,
    9, 4, 5, 10
  ]
def negativeArguments : Array ℕ := #[
    8719955937, 12835384765, 22030815811, 12835384765, 747009914805, 747009558603,
    637, 8719960095, 8719955937, 637, 4225706205, 7253055267,
    4225706205, 289696452045, 289696313907, 21, 747009914805, 747009558603,
    7861, 315, 44737703013, 365585619, 44737699317, 365585619,
    38658087, 637, 237399225, 407475015, 237399225, 8719960095,
    8719955937, 49, 8719960095, 8719955937, 315, 49,
    18408804645, 18408795867, 637, 637, 1758861, 7
  ]
def negativeCoefficients : Array ℕ := #[
    80427397751931585113773572096, 236771057847545615846987530240, 812793642001101878326986801152, 236771057847545615846987530240, 3444975179732852698245727518720, 3444973537041069562373301338112,
    197141951256196808777685532672, 80427436102712514355931381760, 80427397751931585113773572096, 197141951256196808777685532672, 155901041788642859262997954560, 535181017051280398306548645888,
    155901041788642859262997954560, 667994538741973383122874531840, 667994220217431776361619390464, 103986963299971943091526434816, 3444975179732852698245727518720, 3444973537041069562373301338112,
    2432861662205593585245503881216, 194975556187447393296612065280, 412632478963217850709001109504, 3371932175360844026873905152, 412632444873634802493749723136, 3371932175360844026873905152,
    365115308681317508660387119104, 197141951256196808777685532672, 8758485493743980857471795200, 30066349272543842601491496960, 8758485493743980857471795200, 80427436102712514355931381760,
    80427397751931585113773572096, 7582382740622954183757135872, 80427436102712514355931381760, 80427397751931585113773572096, 194975556187447393296612065280, 7582382740622954183757135872,
    84895626997307654042372014080, 84895586515927784286760992768, 197141951256196808777685532672, 197141951256196808777685532672, 8305986234426587050206560256, 8873554201597605810476922437632
  ]
def negativeScales : Array ℕ := #[
    33, 33, 34, 33, 39, 39,
    9, 33, 33, 9, 31, 32,
    31, 38, 38, 4, 39, 39,
    12, 8, 35, 28, 35, 28,
    25, 9, 27, 28, 27, 33,
    33, 5, 33, 33, 8, 5,
    34, 34, 9, 9, 20, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11873059547496154, 5129283016944966, 7199672344836364, 9315149562256300, 4392317422778759, 4392317422778759,
    5614709844114682, 9315149562256300, 9315149562256300, 4392317422778759, 12940497133910467, 8299208018387278,
    7199672344836364, 9315149562256300, 5614709844114682, 8299208018387278, 5614709844114682, 9315149562256300,
    9315149562256300, 4392317422778759, 5832890014087662, 10080817527608327
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    33021673698893028, 33579407492958196, 34358803868546644, 33579407492958196, 39442336435296388, 39442335747365785,
    9315149562256301, 33021674386823631, 33021673698893028, 9315149562256301, 31976545336633367, 32755941696272846,
    31976545336633367, 38075751059579424, 38075750371648820, 4392317422778766, 39442336435296388, 39442335747365785,
    12940497143328889, 8299208018387279, 35380772134264296, 28445634079480024, 35380772015076212, 28445634079480024,
    25204266911592593, 9315149562256301, 27822739985366182, 28602136359943887, 27822739985366182, 33021674386823631,
    33021673698893028, 5614709844123661, 33021674386823631, 33021673698893028, 8299208018387279, 5614709844123661,
    34099676898824904, 34099676210894301, 9315149562256301, 9315149562256301, 20746210042941097, 2807354922807594
  ]

abbrev PositiveTerm := Fin 22
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
noncomputable def positiveFloor : ℝ := 21846456871 / 500000000000
noncomputable def negativeCeiling : ℝ := 9624302801 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 80427397751931585113773572096, coefficient := (-80427397751931585113773572096) }, { argument := 236771057847545615846987530240, coefficient := (-236771057847545615846987530240) }, { argument := 812793642001101878326986801152, coefficient := (-812793642001101878326986801152) }, { argument := 236771057847545615846987530240, coefficient := (-236771057847545615846987530240) }, { argument := 3444975179732852698245727518720, coefficient := (-3444975179732852698245727518720) }, { argument := 3444973537041069562373301338112, coefficient := (-3444973537041069562373301338112) }, { argument := 197141951256196808777685532672, coefficient := (-197141951256196808777685532672) }, { argument := 80427436102712514355931381760, coefficient := (-80427436102712514355931381760) }, { argument := 80427397751931585113773572096, coefficient := (-80427397751931585113773572096) }, { argument := 197141951256196808777685532672, coefficient := (-197141951256196808777685532672) }, { argument := 155901041788642859262997954560, coefficient := (-155901041788642859262997954560) }, { argument := 535181017051280398306548645888, coefficient := (-535181017051280398306548645888) }, { argument := 155901041788642859262997954560, coefficient := (-155901041788642859262997954560) }, { argument := 667994538741973383122874531840, coefficient := (-667994538741973383122874531840) }, { argument := 667994220217431776361619390464, coefficient := (-667994220217431776361619390464) }, { argument := 103986963299971943091526434816, coefficient := (-103986963299971943091526434816) }, { argument := 3444975179732852698245727518720, coefficient := (-3444975179732852698245727518720) }, { argument := 3444973537041069562373301338112, coefficient := (-3444973537041069562373301338112) }, { argument := 2432861662205593585245503881216, coefficient := (-2432861662205593585245503881216) }, { argument := 194975556187447393296612065280, coefficient := (-194975556187447393296612065280) }, { argument := 412632478963217850709001109504, coefficient := (-412632478963217850709001109504) }, { argument := 3371932175360844026873905152, coefficient := (-3371932175360844026873905152) }, { argument := 412632444873634802493749723136, coefficient := (-412632444873634802493749723136) }, { argument := 3371932175360844026873905152, coefficient := (-3371932175360844026873905152) }, { argument := 365115308681317508660387119104, coefficient := (-365115308681317508660387119104) }, { argument := 197141951256196808777685532672, coefficient := (-197141951256196808777685532672) }, { argument := 8758485493743980857471795200, coefficient := (-8758485493743980857471795200) }, { argument := 30066349272543842601491496960, coefficient := (-30066349272543842601491496960) }, { argument := 8758485493743980857471795200, coefficient := (-8758485493743980857471795200) }, { argument := 80427436102712514355931381760, coefficient := (-80427436102712514355931381760) }, { argument := 80427397751931585113773572096, coefficient := (-80427397751931585113773572096) }, { argument := 7582382740622954183757135872, coefficient := (-7582382740622954183757135872) }, { argument := 80427436102712514355931381760, coefficient := (-80427436102712514355931381760) }, { argument := 80427397751931585113773572096, coefficient := (-80427397751931585113773572096) }, { argument := 194975556187447393296612065280, coefficient := (-194975556187447393296612065280) }, { argument := 7582382740622954183757135872, coefficient := (-7582382740622954183757135872) }, { argument := 84895626997307654042372014080, coefficient := (-84895626997307654042372014080) }, { argument := 84895586515927784286760992768, coefficient := (-84895586515927784286760992768) }, { argument := 197141951256196808777685532672, coefficient := (-197141951256196808777685532672) }, { argument := 197141951256196808777685532672, coefficient := (-197141951256196808777685532672) }, { argument := 8305986234426587050206560256, coefficient := (-8305986234426587050206560256) }, { argument := 297184837591005530313383357710336, coefficient := 297184837591005530313383357710336 }, { argument := 10831975343747077405367336960, coefficient := 10831975343747077405367336960 }, { argument := 181977185774950900410171260928, coefficient := 181977185774950900410171260928 }, { argument := 394283902512393617555371065344, coefficient := 394283902512393617555371065344 }, { argument := 12998370412496492886440804352, coefficient := 12998370412496492886440804352 }, { argument := 207973926599943886183052869632, coefficient := 207973926599943886183052869632 }, { argument := 15164765481245908367514271744, coefficient := 15164765481245908367514271744 }, { argument := 394283902512393617555371065344, coefficient := 394283902512393617555371065344 }, { argument := 394283902512393617555371065344, coefficient := 394283902512393617555371065344 }, { argument := 207973926599943886183052869632, coefficient := 207973926599943886183052869632 }, { argument := 4865723324411187170491007762432, coefficient := 4865723324411187170491007762432 }, { argument := 389951112374894786593224130560, coefficient := 389951112374894786593224130560 }, { argument := 181977185774950900410171260928, coefficient := 181977185774950900410171260928 }, { argument := 394283902512393617555371065344, coefficient := 394283902512393617555371065344 }, { argument := 15164765481245908367514271744, coefficient := 15164765481245908367514271744 }, { argument := 389951112374894786593224130560, coefficient := 389951112374894786593224130560 }, { argument := 15164765481245908367514271744, coefficient := 15164765481245908367514271744 }, { argument := 394283902512393617555371065344, coefficient := 394283902512393617555371065344 }, { argument := 394283902512393617555371065344, coefficient := 394283902512393617555371065344 }, { argument := 12998370412496492886440804352, coefficient := 12998370412496492886440804352 }, { argument := 8873554201597605810476922437632, coefficient := (-8873554201597605810476922437632) }, { argument := 282250328957066702677000323072, coefficient := 282250328957066702677000323072 }, { argument := 335172265636516709428937883648, coefficient := 335172265636516709428937883648 }] }

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


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-13304516102097569345312174372814848)
def positiveArguments : Array ℕ := #[
    1653, 17043, 513, 1653, 513, 513,
    43947, 513, 17043, 43947, 57, 513,
    513, 1083, 1215, 21627, 1215, 38475,
    65691, 1215, 65691, 65691, 21627, 1215,
    1449, 1623, 1449, 1623, 3, 95,
    916455481, 916455367, 5100336683, 36708298153, 10200671745, 72594047,
    2687257985, 2687224863, 72627169, 382635, 58048587, 587780655,
    29024295, 382605
  ]
def positiveCoefficients : Array ℕ := #[
    255789360617341699301031542784, 2637276511192592003138221768704, 317531620076700040511625363456, 255789360617341699301031542784, 317531620076700040511625363456, 317531620076700040511625363456,
    13600937726618651735247953068032, 317531620076700040511625363456, 2637276511192592003138221768704, 13600937726618651735247953068032, 282250328957066702677000323072, 317531620076700040511625363456,
    317531620076700040511625363456, 335172265636516709428937883648, 94006071733233564625152245760, 1673308076851557450327709974528, 94006071733233564625152245760, 1488429469109531439898243891200,
    2541297472521747363699949043712, 94006071733233564625152245760, 2541297472521747363699949043712, 2541297472521747363699949043712, 1673308076851557450327709974528, 94006071733233564625152245760,
    448443779231129004582207750144, 502294170940043046540319653888, 448443779231129004582207750144, 502294170940043046540319653888, 475368975085586025561263702016, 15053350877710224142773350563840,
    69245418344265263433873847484416, 69245409730668798679640977702912, 48171318006299485181218165620736, 173350036840912903537682167103488, 48171310351343416449523274219520, 1371262777634654878065489870848,
    50760868156751279258486429450240, 50760242499860696824931357294592, 1371888434525237311620562026496, 3613885398345653392685137920, 548253403253485219692731695104, 5551431328902332686647699701760,
    548253431587684116910602977280, 3613602056356681213972316160
  ]
def positiveScales : Array ℕ := #[
    10, 14, 9, 10, 9, 9,
    15, 9, 14, 15, 5, 9,
    9, 10, 10, 14, 10, 15,
    16, 10, 16, 16, 14, 10,
    10, 10, 10, 10, 1, 6,
    29, 29, 32, 35, 33, 26,
    31, 31, 26, 18, 25, 29,
    24, 18
  ]
def negativeArguments : Array ℕ := #[
    57, 81, 3, 3, 95, 437,
    851, 329, 21
  ]
def negativeCoefficients : Array ℕ := #[
    36128042106504537942656041353216, 12834962327310822690154119954432, 1901475900342344102245054808064, 475368975085586025561263702016, 15053350877710224142773350563840, 138490828074934062113514825187328,
    269692665198555805168423606943744, 104264261868771868273103838642176, 6655165651198204357857691828224
  ]
def negativeScales : Array ℕ := #[
    5, 6, 1, 1, 6, 8,
    9, 8, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10690871009288692, 14056891688362846, 9002815015607054, 10690871009288692, 9002815015607054, 9002815015607054,
    15423477064079774, 9002815015607054, 14056891688362846, 15423477064079774, 5832890014087662, 9002815015607054,
    9002815015607054, 10080817527608327, 10246740598493143, 14400545934572177, 10246740598493143, 15231633706102934,
    16003408107101897, 10246740598493143, 16003408107101897, 16003408107101897, 14400545934572177, 10246740598493143,
    10500841879556911, 10664447284546067, 10500841879556911, 10664447284546067, 1584962500720924, 6569855608330797,
    29771489559208532, 29771489379748375, 32247945339278646, 35095387179542610, 33247945110018403, 26113347910563295,
    31323487685130300, 31323469902974697, 26114006009252855, 18545609318891746, 25790757614078850, 29130702636980914,
    24790757688638546, 18545496201827168
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    5832890015409720, 6339850002884626, 1584962500724866, 1584962500724866, 6569855608333349, 8771489469857739,
    9733015321840403, 8361943773735243, 4392317422778766
  ]

abbrev PositiveTerm := Fin 44
abbrev NegativeTerm := Fin 9
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
noncomputable def positiveFloor : ℝ := 212345155503 / 1000000000000
noncomputable def negativeCeiling : ℝ := 61816878707 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 255789360617341699301031542784, coefficient := 255789360617341699301031542784 }, { argument := 2637276511192592003138221768704, coefficient := 2637276511192592003138221768704 }, { argument := 317531620076700040511625363456, coefficient := 317531620076700040511625363456 }, { argument := 255789360617341699301031542784, coefficient := 255789360617341699301031542784 }, { argument := 317531620076700040511625363456, coefficient := 317531620076700040511625363456 }, { argument := 317531620076700040511625363456, coefficient := 317531620076700040511625363456 }, { argument := 13600937726618651735247953068032, coefficient := 13600937726618651735247953068032 }, { argument := 317531620076700040511625363456, coefficient := 317531620076700040511625363456 }, { argument := 2637276511192592003138221768704, coefficient := 2637276511192592003138221768704 }, { argument := 13600937726618651735247953068032, coefficient := 13600937726618651735247953068032 }, { argument := 282250328957066702677000323072, coefficient := 282250328957066702677000323072 }, { argument := 317531620076700040511625363456, coefficient := 317531620076700040511625363456 }, { argument := 317531620076700040511625363456, coefficient := 317531620076700040511625363456 }, { argument := 335172265636516709428937883648, coefficient := 335172265636516709428937883648 }, { argument := 36128042106504537942656041353216, coefficient := (-36128042106504537942656041353216) }, { argument := 94006071733233564625152245760, coefficient := 94006071733233564625152245760 }, { argument := 1673308076851557450327709974528, coefficient := 1673308076851557450327709974528 }, { argument := 94006071733233564625152245760, coefficient := 94006071733233564625152245760 }, { argument := 1488429469109531439898243891200, coefficient := 1488429469109531439898243891200 }, { argument := 2541297472521747363699949043712, coefficient := 2541297472521747363699949043712 }, { argument := 94006071733233564625152245760, coefficient := 94006071733233564625152245760 }, { argument := 2541297472521747363699949043712, coefficient := 2541297472521747363699949043712 }, { argument := 2541297472521747363699949043712, coefficient := 2541297472521747363699949043712 }, { argument := 1673308076851557450327709974528, coefficient := 1673308076851557450327709974528 }, { argument := 94006071733233564625152245760, coefficient := 94006071733233564625152245760 }, { argument := 12834962327310822690154119954432, coefficient := (-12834962327310822690154119954432) }, { argument := 448443779231129004582207750144, coefficient := 448443779231129004582207750144 }, { argument := 502294170940043046540319653888, coefficient := 502294170940043046540319653888 }, { argument := 448443779231129004582207750144, coefficient := 448443779231129004582207750144 }, { argument := 502294170940043046540319653888, coefficient := 502294170940043046540319653888 }, { argument := 1901475900342344102245054808064, coefficient := (-1901475900342344102245054808064) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 15053350877710224142773350563840, coefficient := 15053350877710224142773350563840 }, { argument := 15053350877710224142773350563840, coefficient := (-15053350877710224142773350563840) }, { argument := 69245418344265263433873847484416, coefficient := 69245418344265263433873847484416 }, { argument := 69245409730668798679640977702912, coefficient := 69245409730668798679640977702912 }, { argument := 138490828074934062113514825187328, coefficient := (-138490828074934062113514825187328) }, { argument := 48171318006299485181218165620736, coefficient := 48171318006299485181218165620736 }, { argument := 173350036840912903537682167103488, coefficient := 173350036840912903537682167103488 }, { argument := 48171310351343416449523274219520, coefficient := 48171310351343416449523274219520 }, { argument := 269692665198555805168423606943744, coefficient := (-269692665198555805168423606943744) }, { argument := 1371262777634654878065489870848, coefficient := 1371262777634654878065489870848 }, { argument := 50760868156751279258486429450240, coefficient := 50760868156751279258486429450240 }, { argument := 50760242499860696824931357294592, coefficient := 50760242499860696824931357294592 }, { argument := 1371888434525237311620562026496, coefficient := 1371888434525237311620562026496 }, { argument := 104264261868771868273103838642176, coefficient := (-104264261868771868273103838642176) }, { argument := 3613885398345653392685137920, coefficient := 3613885398345653392685137920 }, { argument := 548253403253485219692731695104, coefficient := 548253403253485219692731695104 }, { argument := 5551431328902332686647699701760, coefficient := 5551431328902332686647699701760 }, { argument := 548253431587684116910602977280, coefficient := 548253431587684116910602977280 }, { argument := 3613602056356681213972316160, coefficient := 3613602056356681213972316160 }, { argument := 6655165651198204357857691828224, coefficient := (-6655165651198204357857691828224) }] }

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

end TermShard3


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk21
