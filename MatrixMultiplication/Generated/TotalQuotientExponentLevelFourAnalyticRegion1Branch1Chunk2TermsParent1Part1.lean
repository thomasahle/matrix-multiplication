import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-20679266311730949487189995552768)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    30988368417, 915674961, 915674961, 1783156503, 1783156503, 56048946297,
    1783156503, 2406994569, 144580257, 20259111, 915674961, 2545905,
    79158123, 15699813525, 15699813525, 79158123, 8490043, 230360839,
    77, 4509816745, 3, 5, 153, 5,
    3, 2451, 157, 230360839, 153, 5,
    157, 5, 153, 5, 8490043, 5,
    5, 5, 5, 157, 157, 157,
    157, 20259111, 915674961, 2545905, 5, 5,
    5, 5, 39451953, 1783156503, 4957815, 3913719,
    776226825, 776226825, 3913719, 153, 153, 153,
    153, 39451953, 1783156503, 4957815
  ]
def negativeCoefficients : Array ℕ := #[
    35727156340638936833030356992, 2111402707533871850163535872, 2111402707533871850163535872, 2055839478388243643580284928, 2055839478388243643580284928, 64620035496365604256320847872,
    2055839478388243643580284928, 2775075800071989151446073344, 2667034998990153915996045312, 46714329472234248493596672, 2111402707533871850163535872, 46963657970977516006932480,
    182526204542027719136772096, 36201305262579851922820300800, 36201305262579851922820300800, 182526204542027719136772096, 78306825197894631365279744, 8498814883276020305151131648,
    744698304882611571619004416, 83191435314344850144278609920, 464227514732017603087171584, 24178516392292583494123520, 739862601604153054920179712, 773712524553362671811952640,
    464227514732017603087171584, 11852308735501824428819349504, 759205414717987121715478528, 8498814883276020305151131648, 739862601604153054920179712, 24178516392292583494123520,
    759205414717987121715478528, 24178516392292583494123520, 739862601604153054920179712, 773712524553362671811952640, 78306825197894631365279744, 24178516392292583494123520,
    24178516392292583494123520, 24178516392292583494123520, 24178516392292583494123520, 759205414717987121715478528, 759205414717987121715478528, 759205414717987121715478528,
    759205414717987121715478528, 46714329472234248493596672, 2111402707533871850163535872, 46963657970977516006932480, 24178516392292583494123520, 24178516392292583494123520,
    24178516392292583494123520, 24178516392292583494123520, 45485005012438610375344128, 2055839478388243643580284928, 45727772234899160322539520, 9024421596176809080127488,
    1789857197990391402882662400, 1789857197990391402882662400, 9024421596176809080127488, 739862601604153054920179712, 739862601604153054920179712, 739862601604153054920179712,
    739862601604153054920179712, 45485005012438610375344128, 2055839478388243643580284928, 45727772234899160322539520
  ]
def negativeScales : Array ℕ := #[
    34, 29, 29, 30, 30, 35,
    30, 31, 27, 24, 29, 21,
    26, 33, 33, 26, 23, 27,
    6, 32, 1, 2, 7, 2,
    1, 11, 7, 27, 7, 2,
    7, 2, 7, 2, 23, 2,
    2, 2, 2, 7, 7, 7,
    7, 24, 29, 21, 2, 2,
    2, 2, 25, 30, 22, 21,
    29, 29, 21, 7, 7, 7,
    7, 25, 30, 22
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34851007747555450, 29770260332253290, 29770260332253290, 30731786184240952, 30731786184240952, 35705968200018224,
    30731786184240952, 31164585740590692, 27107295319182916, 24272067532129899, 29770260332253290, 21279747155654583,
    26238234067770574, 33870028374965651, 33870028374965651, 26238234067770574, 23017340430019998, 27779320241133459,
    6266786540694902, 32070421665193932, 1584962500724866, 2321928094887363, 7257387842692652, 2321928094887363,
    1584962500724866, 11259154768866840, 7294620748891628, 27779320241133459, 7257387842692652, 2321928094887363,
    7294620748891628, 2321928094887363, 7257387842692652, 2321928094887363, 23017340430019998, 2321928094887363,
    2321928094887363, 2321928094887363, 2321928094887363, 7294620748891628, 7294620748891628, 7294620748891628,
    7294620748891628, 24272067532129899, 29770260332253290, 21279747155654583, 2321928094887363, 2321928094887363,
    2321928094887363, 2321928094887363, 25233593384315263, 30731786184240952, 22241273007839948, 21900108749731547,
    29531903050024823, 29531903050024823, 21900108749731547, 7257387842692652, 7257387842692652, 7257387842692652,
    7257387842692652, 25233593384315263, 30731786184240952, 22241273007839948
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
noncomputable def negativeCeiling : ℝ := 122940551 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 35727156340638936833030356992, coefficient := (-35727156340638936833030356992) }, { argument := 2111402707533871850163535872, coefficient := (-2111402707533871850163535872) }, { argument := 2111402707533871850163535872, coefficient := (-2111402707533871850163535872) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 64620035496365604256320847872, coefficient := (-64620035496365604256320847872) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 2775075800071989151446073344, coefficient := (-2775075800071989151446073344) }, { argument := 2667034998990153915996045312, coefficient := (-2667034998990153915996045312) }, { argument := 46714329472234248493596672, coefficient := (-46714329472234248493596672) }, { argument := 2111402707533871850163535872, coefficient := (-2111402707533871850163535872) }, { argument := 46963657970977516006932480, coefficient := (-46963657970977516006932480) }, { argument := 182526204542027719136772096, coefficient := (-182526204542027719136772096) }, { argument := 36201305262579851922820300800, coefficient := (-36201305262579851922820300800) }, { argument := 36201305262579851922820300800, coefficient := (-36201305262579851922820300800) }, { argument := 182526204542027719136772096, coefficient := (-182526204542027719136772096) }, { argument := 78306825197894631365279744, coefficient := (-78306825197894631365279744) }, { argument := 8498814883276020305151131648, coefficient := (-8498814883276020305151131648) }, { argument := 744698304882611571619004416, coefficient := (-744698304882611571619004416) }, { argument := 83191435314344850144278609920, coefficient := (-83191435314344850144278609920) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 11852308735501824428819349504, coefficient := (-11852308735501824428819349504) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 8498814883276020305151131648, coefficient := (-8498814883276020305151131648) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 78306825197894631365279744, coefficient := (-78306825197894631365279744) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 46714329472234248493596672, coefficient := (-46714329472234248493596672) }, { argument := 2111402707533871850163535872, coefficient := (-2111402707533871850163535872) }, { argument := 46963657970977516006932480, coefficient := (-46963657970977516006932480) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 9024421596176809080127488, coefficient := (-9024421596176809080127488) }, { argument := 1789857197990391402882662400, coefficient := (-1789857197990391402882662400) }, { argument := 1789857197990391402882662400, coefficient := (-1789857197990391402882662400) }, { argument := 9024421596176809080127488, coefficient := (-9024421596176809080127488) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }] }

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

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-22032233397064484938735308242944)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5, 5, 5, 5, 1240070847, 56048946297,
    155836185, 39515937, 7837386975, 7837386975, 39515937, 39451953,
    1783156503, 4957815, 80420613, 15950209275, 15950209275, 80420613,
    33897787, 918887431, 77, 17986638505, 3, 5,
    153, 5, 3, 2451, 157, 918887431,
    153, 5, 157, 5, 153, 5,
    33897787, 8490043, 33897787, 16876111, 33897787, 57942081,
    11993655, 2406994569, 79158123, 3913719, 39515937, 80420613,
    29104779, 11993655, 3913719, 29104779, 794986125, 4957815,
    401985, 86158785, 155836185, 794986125, 86158785, 2545905,
    2545905, 4957815, 4957815, 155836185
  ]
def negativeCoefficients : Array ℕ := #[
    773712524553362671811952640, 773712524553362671811952640, 773712524553362671811952640, 773712524553362671811952640, 1429704346742327131527708672, 64620035496365604256320847872,
    1437335111059127660949012480, 182235094167957499489026048, 36143567933612419942082150400, 36143567933612419942082150400, 182235094167957499489026048, 45485005012438610375344128,
    2055839478388243643580284928, 45727772234899160322539520, 185437308282729915614232576, 36778678552254171730201804800, 36778678552254171730201804800, 185437308282729915614232576,
    78162975181764835068084224, 8475240636102722262294069248, 744698304882611571619004416, 82948729312016194820657643520, 464227514732017603087171584, 24178516392292583494123520,
    739862601604153054920179712, 773712524553362671811952640, 464227514732017603087171584, 11852308735501824428819349504, 759205414717987121715478528, 8475240636102722262294069248,
    739862601604153054920179712, 24178516392292583494123520, 759205414717987121715478528, 24178516392292583494123520, 739862601604153054920179712, 773712524553362671811952640,
    78162975181764835068084224, 78306825197894631365279744, 78162975181764835068084224, 77827325144128643707961344, 78162975181764835068084224, 66802671206571800637997056,
    221243884293366932286996480, 2775075800071989151446073344, 182526204542027719136772096, 9024421596176809080127488, 182235094167957499489026048, 185437308282729915614232576,
    67111051191859526246596608, 221243884293366932286996480, 9024421596176809080127488, 67111051191859526246596608, 1833113198753133851836416000, 45727772234899160322539520,
    59322515331761072850862080, 794674528298382705064673280, 1437335111059127660949012480, 1833113198753133851836416000, 794674528298382705064673280, 46963657970977516006932480,
    46963657970977516006932480, 45727772234899160322539520, 45727772234899160322539520, 1437335111059127660949012480
  ]
def negativeScales : Array ℕ := #[
    2, 2, 2, 2, 30, 35,
    27, 25, 32, 32, 25, 25,
    30, 22, 26, 33, 33, 26,
    25, 29, 6, 34, 1, 2,
    7, 2, 1, 11, 7, 29,
    7, 2, 7, 2, 7, 2,
    25, 23, 25, 24, 25, 25,
    23, 31, 26, 21, 25, 26,
    24, 23, 21, 24, 29, 22,
    18, 26, 27, 29, 26, 21,
    21, 22, 22, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    2321928094887363, 2321928094887363, 2321928094887363, 2321928094887363, 30207775400159531, 35705968200018224,
    27215455023684216, 25235931281901154, 32867725588990109, 32867725588990109, 25235931281901154, 25233593384315263,
    30731786184240952, 22241273007839948, 26261061997224836, 33892856305733903, 33892856305733903, 26261061997224836,
    25014687755026265, 29775312893377694, 6266786540694902, 34066206537613853, 1584962500724866, 2321928094887363,
    7257387842692652, 2321928094887363, 1584962500724866, 11259154768866840, 7294620748891628, 29775312893377694,
    7257387842692652, 2321928094887363, 7294620748891628, 2321928094887363, 7257387842692652, 2321928094887363,
    25014687755026265, 23017340430019998, 25014687755026265, 24008479146015291, 25014687755026265, 25788108164901681,
    23515768043299938, 31164585740590692, 26238234067770574, 21900108749731547, 25235931281901154, 26261061997224836,
    24794752727668323, 23515768043299938, 21900108749731547, 24794752727668323, 29566354440166770, 22241273007839948,
    18616782142941091, 26360494569538946, 27215455023684216, 29566354440166770, 26360494569538946, 21279747155654583,
    21279747155654583, 22241273007839948, 22241273007839948, 27215455023684216
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
noncomputable def negativeCeiling : ℝ := 67490791 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 1429704346742327131527708672, coefficient := (-1429704346742327131527708672) }, { argument := 64620035496365604256320847872, coefficient := (-64620035496365604256320847872) }, { argument := 1437335111059127660949012480, coefficient := (-1437335111059127660949012480) }, { argument := 182235094167957499489026048, coefficient := (-182235094167957499489026048) }, { argument := 36143567933612419942082150400, coefficient := (-36143567933612419942082150400) }, { argument := 36143567933612419942082150400, coefficient := (-36143567933612419942082150400) }, { argument := 182235094167957499489026048, coefficient := (-182235094167957499489026048) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 185437308282729915614232576, coefficient := (-185437308282729915614232576) }, { argument := 36778678552254171730201804800, coefficient := (-36778678552254171730201804800) }, { argument := 36778678552254171730201804800, coefficient := (-36778678552254171730201804800) }, { argument := 185437308282729915614232576, coefficient := (-185437308282729915614232576) }, { argument := 78162975181764835068084224, coefficient := (-78162975181764835068084224) }, { argument := 8475240636102722262294069248, coefficient := (-8475240636102722262294069248) }, { argument := 744698304882611571619004416, coefficient := (-744698304882611571619004416) }, { argument := 82948729312016194820657643520, coefficient := (-82948729312016194820657643520) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 11852308735501824428819349504, coefficient := (-11852308735501824428819349504) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 8475240636102722262294069248, coefficient := (-8475240636102722262294069248) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 78162975181764835068084224, coefficient := (-78162975181764835068084224) }, { argument := 78306825197894631365279744, coefficient := (-78306825197894631365279744) }, { argument := 78162975181764835068084224, coefficient := (-78162975181764835068084224) }, { argument := 77827325144128643707961344, coefficient := (-77827325144128643707961344) }, { argument := 78162975181764835068084224, coefficient := (-78162975181764835068084224) }, { argument := 66802671206571800637997056, coefficient := (-66802671206571800637997056) }, { argument := 221243884293366932286996480, coefficient := (-221243884293366932286996480) }, { argument := 2775075800071989151446073344, coefficient := (-2775075800071989151446073344) }, { argument := 182526204542027719136772096, coefficient := (-182526204542027719136772096) }, { argument := 9024421596176809080127488, coefficient := (-9024421596176809080127488) }, { argument := 182235094167957499489026048, coefficient := (-182235094167957499489026048) }, { argument := 185437308282729915614232576, coefficient := (-185437308282729915614232576) }, { argument := 67111051191859526246596608, coefficient := (-67111051191859526246596608) }, { argument := 221243884293366932286996480, coefficient := (-221243884293366932286996480) }, { argument := 9024421596176809080127488, coefficient := (-9024421596176809080127488) }, { argument := 67111051191859526246596608, coefficient := (-67111051191859526246596608) }, { argument := 1833113198753133851836416000, coefficient := (-1833113198753133851836416000) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 59322515331761072850862080, coefficient := (-59322515331761072850862080) }, { argument := 794674528298382705064673280, coefficient := (-794674528298382705064673280) }, { argument := 1437335111059127660949012480, coefficient := (-1437335111059127660949012480) }, { argument := 1833113198753133851836416000, coefficient := (-1833113198753133851836416000) }, { argument := 794674528298382705064673280, coefficient := (-794674528298382705064673280) }, { argument := 46963657970977516006932480, coefficient := (-46963657970977516006932480) }, { argument := 46963657970977516006932480, coefficient := (-46963657970977516006932480) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 1437335111059127660949012480, coefficient := (-1437335111059127660949012480) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2
