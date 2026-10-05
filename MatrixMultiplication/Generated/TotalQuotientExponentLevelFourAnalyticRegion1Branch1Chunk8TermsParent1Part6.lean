import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 6, for level-four region 1, branch 1,
parent chunk 8, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard12

/-! Directed signed-log shard 12.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-10557522597395752096713639853031424)
def positiveArguments : Array ℕ := #[
    27675, 3, 1, 1, 1, 1,
    1643, 39803, 30157, 16801, 1643, 16801,
    33549, 1643, 39803, 1643, 21, 63,
    133, 343, 287, 8029, 245, 287,
    259, 133, 133, 259, 8029, 259,
    21, 343, 25165821, 25165827, 63667583, 233376337,
    3979139, 78149329, 1533789101, 1533789309, 78149851, 10641829,
    527190553, 679921397, 1054382809, 10641829, 113854147, 21486811453,
    2685851557, 14231643, 30921801, 1397609151, 3885855
  ]
def positiveCoefficients : Array ℕ := #[
    535312352925357798559894732800, 475368975085586025561263702016, 316912650057057350374175801344, 316912650057057350374175801344, 316912650057057350374175801344, 316912650057057350374175801344,
    31780241946029371744675954688, 769901990369937360653278773248, 583321215073893952345826394112, 649957206251052312455630815232, 31780241946029371744675954688, 649957206251052312455630815232,
    648932037156019106915479977984, 31780241946029371744675954688, 769901990369937360653278773248, 31780241946029371744675954688, 103986963299971943091526434816, 77990222474978957318644826112,
    82323012612477788280791760896, 106153358368721358572599902208, 1421155165099616555584194609152, 2484855143855579556791267098624, 75823827406229541837571358720, 1421155165099616555584194609152,
    80156617543728372799718293504, 82323012612477788280791760896, 82323012612477788280791760896, 80156617543728372799718293504, 2484855143855579556791267098624, 80156617543728372799718293504,
    103986963299971943091526434816, 106153358368721358572599902208, 237684459208594115562760568832, 237684515876991909998503133184, 601323320009042429647085633536, 2204177183487382096923909423104,
    601310484616941989951394807808, 369049771928352767918404009984, 14486228484706330065007481454592, 14486230449210786938779890352128, 369052237003656825873205559296, 100509233172060387309642579968,
    19916695980581706296977579311104, 205493633035437167525795062611968, 19916728149342187605000775008256, 100509233172060387309642579968, 537661007728513567997990797312, 101468598229386821083689845260288,
    101468602965920403401943994597376, 537656271194931249743841460224, 292048153264730156477020372992, 13200045221668601781569760264192, 293606902548662803229866721280
  ]
def positiveScales : Array ℕ := #[
    14, 1, 0, 0, 0, 0,
    10, 15, 14, 14, 10, 14,
    15, 10, 15, 10, 4, 5,
    7, 8, 8, 12, 7, 8,
    8, 7, 7, 8, 12, 8,
    4, 8, 24, 24, 25, 27,
    21, 26, 30, 30, 26, 23,
    28, 29, 29, 23, 26, 34,
    31, 23, 24, 30, 21
  ]
def negativeArguments : Array ℕ := #[
    27, 3, 1, 53, 7, 3,
    43, 375, 3099, 2575, 87
  ]
def negativeCoefficients : Array ℕ := #[
    2139160387885137115025686659072, 475368975085586025561263702016, 1267650600228229401496703205376, 4199092613256009892457829367808, 8873554201597605810476922437632, 475368975085586025561263702016,
    3406810988113366516522389864448, 29710560942849126597578981376000, 245528075631705182202392702091264, 204012518474230669303375672115200, 13785700277481994741276647358464
  ]
def negativeScales : Array ℕ := #[
    4, 1, 0, 5, 2, 1,
    5, 8, 11, 11, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14756295696540282, 1584962500720924, 0, 0, 0, 0,
    10682116764947138, 15280589552077470, 14880205296681195, 14036259484702606, 10682116764947138, 14036259484702606,
    15033982143991540, 10682116764947138, 15280589552077470, 10682116764947138, 4392317422778759, 5977279922488012,
    7055282435501189, 8422064766172810, 8164906926675687, 12971004597160441, 7936637938489789, 8164906926675687,
    8016808287686553, 7055282435501189, 7055282435501189, 8016808287686553, 12971004597160441, 8016808287686553,
    4392317422778759, 8422064766172810, 24584962328738263, 24584962672703565, 25924055660310504, 27798083046654869,
    21924024865306525, 26219730150327988, 30514452977075551, 30514453172722102, 26219739786806072, 23343242790845978,
    28973749276323301, 29340792730884057, 29973751606512658, 23343242790845978, 26762611599939159, 34322732358012288,
    31322732425356999, 23762598890437244, 24882121013618560, 30380313813589330, 21889800637113917
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4754887502413606, 1584962500724866, 0, 5727920454700926, 2807354922807594, 1584962500724866,
    5426264754702117, 8550746785384604, 11597587039591505, 11330356716957944, 6442943495848765
  ]

abbrev PositiveTerm := Fin 53
abbrev NegativeTerm := Fin 11
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
noncomputable def positiveFloor : ℝ := 18635064583 / 100000000000
noncomputable def negativeCeiling : ℝ := 3358980533 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 535312352925357798559894732800, coefficient := 535312352925357798559894732800 }, { argument := 2139160387885137115025686659072, coefficient := (-2139160387885137115025686659072) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 31780241946029371744675954688, coefficient := 31780241946029371744675954688 }, { argument := 769901990369937360653278773248, coefficient := 769901990369937360653278773248 }, { argument := 583321215073893952345826394112, coefficient := 583321215073893952345826394112 }, { argument := 649957206251052312455630815232, coefficient := 649957206251052312455630815232 }, { argument := 31780241946029371744675954688, coefficient := 31780241946029371744675954688 }, { argument := 649957206251052312455630815232, coefficient := 649957206251052312455630815232 }, { argument := 648932037156019106915479977984, coefficient := 648932037156019106915479977984 }, { argument := 31780241946029371744675954688, coefficient := 31780241946029371744675954688 }, { argument := 769901990369937360653278773248, coefficient := 769901990369937360653278773248 }, { argument := 31780241946029371744675954688, coefficient := 31780241946029371744675954688 }, { argument := 4199092613256009892457829367808, coefficient := (-4199092613256009892457829367808) }, { argument := 103986963299971943091526434816, coefficient := 103986963299971943091526434816 }, { argument := 77990222474978957318644826112, coefficient := 77990222474978957318644826112 }, { argument := 82323012612477788280791760896, coefficient := 82323012612477788280791760896 }, { argument := 106153358368721358572599902208, coefficient := 106153358368721358572599902208 }, { argument := 1421155165099616555584194609152, coefficient := 1421155165099616555584194609152 }, { argument := 2484855143855579556791267098624, coefficient := 2484855143855579556791267098624 }, { argument := 75823827406229541837571358720, coefficient := 75823827406229541837571358720 }, { argument := 1421155165099616555584194609152, coefficient := 1421155165099616555584194609152 }, { argument := 80156617543728372799718293504, coefficient := 80156617543728372799718293504 }, { argument := 82323012612477788280791760896, coefficient := 82323012612477788280791760896 }, { argument := 82323012612477788280791760896, coefficient := 82323012612477788280791760896 }, { argument := 80156617543728372799718293504, coefficient := 80156617543728372799718293504 }, { argument := 2484855143855579556791267098624, coefficient := 2484855143855579556791267098624 }, { argument := 80156617543728372799718293504, coefficient := 80156617543728372799718293504 }, { argument := 103986963299971943091526434816, coefficient := 103986963299971943091526434816 }, { argument := 106153358368721358572599902208, coefficient := 106153358368721358572599902208 }, { argument := 8873554201597605810476922437632, coefficient := (-8873554201597605810476922437632) }, { argument := 237684459208594115562760568832, coefficient := 237684459208594115562760568832 }, { argument := 237684515876991909998503133184, coefficient := 237684515876991909998503133184 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 601323320009042429647085633536, coefficient := 601323320009042429647085633536 }, { argument := 2204177183487382096923909423104, coefficient := 2204177183487382096923909423104 }, { argument := 601310484616941989951394807808, coefficient := 601310484616941989951394807808 }, { argument := 3406810988113366516522389864448, coefficient := (-3406810988113366516522389864448) }, { argument := 369049771928352767918404009984, coefficient := 369049771928352767918404009984 }, { argument := 14486228484706330065007481454592, coefficient := 14486228484706330065007481454592 }, { argument := 14486230449210786938779890352128, coefficient := 14486230449210786938779890352128 }, { argument := 369052237003656825873205559296, coefficient := 369052237003656825873205559296 }, { argument := 29710560942849126597578981376000, coefficient := (-29710560942849126597578981376000) }, { argument := 100509233172060387309642579968, coefficient := 100509233172060387309642579968 }, { argument := 19916695980581706296977579311104, coefficient := 19916695980581706296977579311104 }, { argument := 205493633035437167525795062611968, coefficient := 205493633035437167525795062611968 }, { argument := 19916728149342187605000775008256, coefficient := 19916728149342187605000775008256 }, { argument := 100509233172060387309642579968, coefficient := 100509233172060387309642579968 }, { argument := 245528075631705182202392702091264, coefficient := (-245528075631705182202392702091264) }, { argument := 537661007728513567997990797312, coefficient := 537661007728513567997990797312 }, { argument := 101468598229386821083689845260288, coefficient := 101468598229386821083689845260288 }, { argument := 101468602965920403401943994597376, coefficient := 101468602965920403401943994597376 }, { argument := 537656271194931249743841460224, coefficient := 537656271194931249743841460224 }, { argument := 204012518474230669303375672115200, coefficient := (-204012518474230669303375672115200) }, { argument := 292048153264730156477020372992, coefficient := 292048153264730156477020372992 }, { argument := 13200045221668601781569760264192, coefficient := 13200045221668601781569760264192 }, { argument := 293606902548662803229866721280, coefficient := 293606902548662803229866721280 }, { argument := 13785700277481994741276647358464, coefficient := (-13785700277481994741276647358464) }] }

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

end TermShard12


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
