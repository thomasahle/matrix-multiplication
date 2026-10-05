import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 2, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2

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
def constantNumerator : ℤ := (-56338114553751876804516912300032)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    614103, 8490043, 33897787, 16876111, 33897787, 6137931,
    230360839, 918887431, 456461803, 918887431, 77, 77,
    77, 77, 57942081, 11993655, 2406994569, 79158123,
    3913719, 39515937, 80420613, 29104779, 11993655, 3913719,
    12275859, 4509816745, 17986638505, 8931919365, 17986638505, 3,
    3, 3, 3, 1589773065, 2378759625, 29831251965,
    15699813525, 776226825, 7837386975, 15950209275, 794986125, 2378759625,
    776226825, 5, 5, 5, 5, 39451953,
    1783156503, 4957815, 57942081, 1589773065, 39451953, 3198807,
    685610967, 1240070847, 1589773065, 685610967, 20259111, 20259111,
    39451953, 39451953, 1240070847, 39451953
  ]
def negativeCoefficients : Array ℕ := #[
    2900019424229697734666354688, 78306825197894631365279744, 78162975181764835068084224, 77827325144128643707961344, 78162975181764835068084224, 115942238514266257264585211904,
    8498814883276020305151131648, 8475240636102722262294069248, 8420234059365026828960923648, 8475240636102722262294069248, 744698304882611571619004416, 744698304882611571619004416,
    744698304882611571619004416, 744698304882611571619004416, 66802671206571800637997056, 221243884293366932286996480, 2775075800071989151446073344, 182526204542027719136772096,
    9024421596176809080127488, 182235094167957499489026048, 185437308282729915614232576, 67111051191859526246596608, 221243884293366932286996480, 9024421596176809080127488,
    115942210180067360046713929728, 83191435314344850144278609920, 82948729312016194820657643520, 82382415306582665732208721920, 82948729312016194820657643520, 464227514732017603087171584,
    464227514732017603087171584, 464227514732017603087171584, 464227514732017603087171584, 1832883554083238737021501440, 43880370015248305360994304000, 34393091899793760405254307840,
    36201305262579851922820300800, 1789857197990391402882662400, 36143567933612419942082150400, 36778678552254171730201804800, 1833113198753133851836416000, 43880370015248305360994304000,
    1789857197990391402882662400, 24178516392292583494123520, 24178516392292583494123520, 24178516392292583494123520, 24178516392292583494123520, 45485005012438610375344128,
    2055839478388243643580284928, 45727772234899160322539520, 66802671206571800637997056, 1832883554083238737021501440, 45485005012438610375344128, 59007574070190629676122112,
    790455627648595310036385792, 1429704346742327131527708672, 1832883554083238737021501440, 790455627648595310036385792, 46714329472234248493596672, 46714329472234248493596672,
    45485005012438610375344128, 45485005012438610375344128, 1429704346742327131527708672, 45485005012438610375344128
  ]
def negativeScales : Array ℕ := #[
    19, 23, 25, 24, 25, 22,
    27, 29, 28, 29, 6, 6,
    6, 6, 25, 23, 31, 26,
    21, 25, 26, 24, 23, 21,
    23, 32, 34, 33, 34, 1,
    1, 1, 1, 30, 31, 34,
    33, 29, 32, 33, 29, 31,
    29, 2, 2, 2, 2, 25,
    30, 22, 25, 30, 25, 21,
    29, 30, 30, 29, 24, 24,
    25, 25, 30, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19228121125352790, 23017340430019998, 25014687755026265, 24008479146015291, 25014687755026265, 22549320997059275,
    27779320241133459, 29775312893377694, 28765918899082144, 29775312893377694, 6266786540694902, 6266786540694902,
    6266786540694902, 6266786540694902, 25788108164901681, 23515768043299938, 31164585740590692, 26238234067770574,
    21900108749731547, 25235931281901154, 26261061997224836, 24794752727668323, 23515768043299938, 21900108749731547,
    23549320644490498, 32070421665193932, 34066206537613853, 33056323080937095, 34066206537613853, 1584962500724866,
    1584962500724866, 1584962500724866, 1584962500724866, 30566173694110941, 31147562347968134, 34796105475778772,
    33870028374965651, 29531903050024823, 32867725588990109, 33892856305733903, 29566354440166770, 31147562347968134,
    29531903050024823, 2321928094887363, 2321928094887363, 2321928094887363, 2321928094887363, 25233593384315263,
    30731786184240952, 22241273007839948, 25788108164901681, 30566173694110941, 25233593384315263, 21609102519414729,
    29352814946014261, 30207775400159531, 30566173694110941, 29352814946014261, 24272067532129899, 24272067532129899,
    25233593384315263, 25233593384315263, 30207775400159531, 25233593384315263
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
noncomputable def negativeCeiling : ℝ := 38665329 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2900019424229697734666354688, coefficient := (-2900019424229697734666354688) }, { argument := 78306825197894631365279744, coefficient := (-78306825197894631365279744) }, { argument := 78162975181764835068084224, coefficient := (-78162975181764835068084224) }, { argument := 77827325144128643707961344, coefficient := (-77827325144128643707961344) }, { argument := 78162975181764835068084224, coefficient := (-78162975181764835068084224) }, { argument := 115942238514266257264585211904, coefficient := (-115942238514266257264585211904) }, { argument := 8498814883276020305151131648, coefficient := (-8498814883276020305151131648) }, { argument := 8475240636102722262294069248, coefficient := (-8475240636102722262294069248) }, { argument := 8420234059365026828960923648, coefficient := (-8420234059365026828960923648) }, { argument := 8475240636102722262294069248, coefficient := (-8475240636102722262294069248) }, { argument := 744698304882611571619004416, coefficient := (-744698304882611571619004416) }, { argument := 744698304882611571619004416, coefficient := (-744698304882611571619004416) }, { argument := 744698304882611571619004416, coefficient := (-744698304882611571619004416) }, { argument := 744698304882611571619004416, coefficient := (-744698304882611571619004416) }, { argument := 66802671206571800637997056, coefficient := (-66802671206571800637997056) }, { argument := 221243884293366932286996480, coefficient := (-221243884293366932286996480) }, { argument := 2775075800071989151446073344, coefficient := (-2775075800071989151446073344) }, { argument := 182526204542027719136772096, coefficient := (-182526204542027719136772096) }, { argument := 9024421596176809080127488, coefficient := (-9024421596176809080127488) }, { argument := 182235094167957499489026048, coefficient := (-182235094167957499489026048) }, { argument := 185437308282729915614232576, coefficient := (-185437308282729915614232576) }, { argument := 67111051191859526246596608, coefficient := (-67111051191859526246596608) }, { argument := 221243884293366932286996480, coefficient := (-221243884293366932286996480) }, { argument := 9024421596176809080127488, coefficient := (-9024421596176809080127488) }, { argument := 115942210180067360046713929728, coefficient := (-115942210180067360046713929728) }, { argument := 83191435314344850144278609920, coefficient := (-83191435314344850144278609920) }, { argument := 82948729312016194820657643520, coefficient := (-82948729312016194820657643520) }, { argument := 82382415306582665732208721920, coefficient := (-82382415306582665732208721920) }, { argument := 82948729312016194820657643520, coefficient := (-82948729312016194820657643520) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 1832883554083238737021501440, coefficient := (-1832883554083238737021501440) }, { argument := 43880370015248305360994304000, coefficient := (-43880370015248305360994304000) }, { argument := 34393091899793760405254307840, coefficient := (-34393091899793760405254307840) }, { argument := 36201305262579851922820300800, coefficient := (-36201305262579851922820300800) }, { argument := 1789857197990391402882662400, coefficient := (-1789857197990391402882662400) }, { argument := 36143567933612419942082150400, coefficient := (-36143567933612419942082150400) }, { argument := 36778678552254171730201804800, coefficient := (-36778678552254171730201804800) }, { argument := 1833113198753133851836416000, coefficient := (-1833113198753133851836416000) }, { argument := 43880370015248305360994304000, coefficient := (-43880370015248305360994304000) }, { argument := 1789857197990391402882662400, coefficient := (-1789857197990391402882662400) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 66802671206571800637997056, coefficient := (-66802671206571800637997056) }, { argument := 1832883554083238737021501440, coefficient := (-1832883554083238737021501440) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 59007574070190629676122112, coefficient := (-59007574070190629676122112) }, { argument := 790455627648595310036385792, coefficient := (-790455627648595310036385792) }, { argument := 1429704346742327131527708672, coefficient := (-1429704346742327131527708672) }, { argument := 1832883554083238737021501440, coefficient := (-1832883554083238737021501440) }, { argument := 790455627648595310036385792, coefficient := (-790455627648595310036385792) }, { argument := 46714329472234248493596672, coefficient := (-46714329472234248493596672) }, { argument := 46714329472234248493596672, coefficient := (-46714329472234248493596672) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 1429704346742327131527708672, coefficient := (-1429704346742327131527708672) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }] }

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
def constantNumerator : ℤ := (-47209397086092655778117638422528)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    57942081, 3198807, 153, 153, 153, 153,
    5, 5, 5, 5, 3198807, 144580257,
    401985, 3, 3, 3, 3, 2451,
    2451, 2451, 2451, 685610967, 30988368417, 86158785,
    157, 157, 157, 157, 1240070847, 56048946297,
    155836185, 11993655, 2378759625, 2378759625, 11993655, 614103,
    230360839, 918887431, 456461803, 918887431, 1589773065, 2378759625,
    29831251965, 15699813525, 776226825, 7837386975, 15950209275, 794986125,
    2378759625, 776226825, 153, 153, 153, 153,
    685610967, 30988368417, 86158785, 2406994569, 29831251965, 1783156503,
    144580257, 30988368417, 56048946297, 29831251965
  ]
def negativeCoefficients : Array ℕ := #[
    66802671206571800637997056, 59007574070190629676122112, 739862601604153054920179712, 739862601604153054920179712, 739862601604153054920179712, 739862601604153054920179712,
    773712524553362671811952640, 773712524553362671811952640, 773712524553362671811952640, 773712524553362671811952640, 59007574070190629676122112, 2667034998990153915996045312,
    59322515331761072850862080, 464227514732017603087171584, 464227514732017603087171584, 464227514732017603087171584, 464227514732017603087171584, 11852308735501824428819349504,
    11852308735501824428819349504, 11852308735501824428819349504, 11852308735501824428819349504, 790455627648595310036385792, 35727156340638936833030356992, 794674528298382705064673280,
    759205414717987121715478528, 759205414717987121715478528, 759205414717987121715478528, 759205414717987121715478528, 1429704346742327131527708672, 64620035496365604256320847872,
    1437335111059127660949012480, 221243884293366932286996480, 43880370015248305360994304000, 43880370015248305360994304000, 221243884293366932286996480, 2900019424229697734666354688,
    8498814883276020305151131648, 8475240636102722262294069248, 8420234059365026828960923648, 8475240636102722262294069248, 1832883554083238737021501440, 43880370015248305360994304000,
    34393091899793760405254307840, 36201305262579851922820300800, 1789857197990391402882662400, 36143567933612419942082150400, 36778678552254171730201804800, 1833113198753133851836416000,
    43880370015248305360994304000, 1789857197990391402882662400, 739862601604153054920179712, 739862601604153054920179712, 739862601604153054920179712, 739862601604153054920179712,
    790455627648595310036385792, 35727156340638936833030356992, 794674528298382705064673280, 2775075800071989151446073344, 34393091899793760405254307840, 2055839478388243643580284928,
    2667034998990153915996045312, 35727156340638936833030356992, 64620035496365604256320847872, 34393091899793760405254307840
  ]
def negativeScales : Array ℕ := #[
    25, 21, 7, 7, 7, 7,
    2, 2, 2, 2, 21, 27,
    18, 1, 1, 1, 1, 11,
    11, 11, 11, 29, 34, 26,
    7, 7, 7, 7, 30, 35,
    27, 23, 31, 31, 23, 19,
    27, 29, 28, 29, 30, 31,
    34, 33, 29, 32, 33, 29,
    31, 29, 7, 7, 7, 7,
    29, 34, 26, 31, 34, 30,
    27, 34, 35, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    25788108164901681, 21609102519414729, 7257387842692652, 7257387842692652, 7257387842692652, 7257387842692652,
    2321928094887363, 2321928094887363, 2321928094887363, 2321928094887363, 21609102519414729, 27107295319182916,
    18616782142941091, 1584962500724866, 1584962500724866, 1584962500724866, 1584962500724866, 11259154768866840,
    11259154768866840, 11259154768866840, 11259154768866840, 29352814946014261, 34851007747555450, 26360494569538946,
    7294620748891628, 7294620748891628, 7294620748891628, 7294620748891628, 30207775400159531, 35705968200018224,
    27215455023684216, 23515768043299938, 31147562347968134, 31147562347968134, 23515768043299938, 19228121125352790,
    27779320241133459, 29775312893377694, 28765918899082144, 29775312893377694, 30566173694110941, 31147562347968134,
    34796105475778772, 33870028374965651, 29531903050024823, 32867725588990109, 33892856305733903, 29566354440166770,
    31147562347968134, 29531903050024823, 7257387842692652, 7257387842692652, 7257387842692652, 7257387842692652,
    29352814946014261, 34851007747555450, 26360494569538946, 31164585740590692, 34796105475778772, 30731786184240952,
    27107295319182916, 34851007747555450, 35705968200018224, 34796105475778772
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
noncomputable def negativeCeiling : ℝ := 1100843 / 3906250000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 66802671206571800637997056, coefficient := (-66802671206571800637997056) }, { argument := 59007574070190629676122112, coefficient := (-59007574070190629676122112) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 59007574070190629676122112, coefficient := (-59007574070190629676122112) }, { argument := 2667034998990153915996045312, coefficient := (-2667034998990153915996045312) }, { argument := 59322515331761072850862080, coefficient := (-59322515331761072850862080) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 11852308735501824428819349504, coefficient := (-11852308735501824428819349504) }, { argument := 11852308735501824428819349504, coefficient := (-11852308735501824428819349504) }, { argument := 11852308735501824428819349504, coefficient := (-11852308735501824428819349504) }, { argument := 11852308735501824428819349504, coefficient := (-11852308735501824428819349504) }, { argument := 790455627648595310036385792, coefficient := (-790455627648595310036385792) }, { argument := 35727156340638936833030356992, coefficient := (-35727156340638936833030356992) }, { argument := 794674528298382705064673280, coefficient := (-794674528298382705064673280) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 1429704346742327131527708672, coefficient := (-1429704346742327131527708672) }, { argument := 64620035496365604256320847872, coefficient := (-64620035496365604256320847872) }, { argument := 1437335111059127660949012480, coefficient := (-1437335111059127660949012480) }, { argument := 221243884293366932286996480, coefficient := (-221243884293366932286996480) }, { argument := 43880370015248305360994304000, coefficient := (-43880370015248305360994304000) }, { argument := 43880370015248305360994304000, coefficient := (-43880370015248305360994304000) }, { argument := 221243884293366932286996480, coefficient := (-221243884293366932286996480) }, { argument := 2900019424229697734666354688, coefficient := (-2900019424229697734666354688) }, { argument := 8498814883276020305151131648, coefficient := (-8498814883276020305151131648) }, { argument := 8475240636102722262294069248, coefficient := (-8475240636102722262294069248) }, { argument := 8420234059365026828960923648, coefficient := (-8420234059365026828960923648) }, { argument := 8475240636102722262294069248, coefficient := (-8475240636102722262294069248) }, { argument := 1832883554083238737021501440, coefficient := (-1832883554083238737021501440) }, { argument := 43880370015248305360994304000, coefficient := (-43880370015248305360994304000) }, { argument := 34393091899793760405254307840, coefficient := (-34393091899793760405254307840) }, { argument := 36201305262579851922820300800, coefficient := (-36201305262579851922820300800) }, { argument := 1789857197990391402882662400, coefficient := (-1789857197990391402882662400) }, { argument := 36143567933612419942082150400, coefficient := (-36143567933612419942082150400) }, { argument := 36778678552254171730201804800, coefficient := (-36778678552254171730201804800) }, { argument := 1833113198753133851836416000, coefficient := (-1833113198753133851836416000) }, { argument := 43880370015248305360994304000, coefficient := (-43880370015248305360994304000) }, { argument := 1789857197990391402882662400, coefficient := (-1789857197990391402882662400) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 790455627648595310036385792, coefficient := (-790455627648595310036385792) }, { argument := 35727156340638936833030356992, coefficient := (-35727156340638936833030356992) }, { argument := 794674528298382705064673280, coefficient := (-794674528298382705064673280) }, { argument := 2775075800071989151446073344, coefficient := (-2775075800071989151446073344) }, { argument := 34393091899793760405254307840, coefficient := (-34393091899793760405254307840) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 2667034998990153915996045312, coefficient := (-2667034998990153915996045312) }, { argument := 35727156340638936833030356992, coefficient := (-35727156340638936833030356992) }, { argument := 64620035496365604256320847872, coefficient := (-64620035496365604256320847872) }, { argument := 34393091899793760405254307840, coefficient := (-34393091899793760405254307840) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2
