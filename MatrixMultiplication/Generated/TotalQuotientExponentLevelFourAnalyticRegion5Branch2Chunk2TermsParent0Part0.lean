import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 2, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk2

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-53880957737261574856568318459904)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    132623764091, 6162797170173, 3081313782485, 66336647407, 17289687803, 434174200187,
    18898005036565, 1735296978287, 17024613545, 17289687803, 2523515252213, 2523517655579,
    17289816833, 476158431385, 22126259600655, 11062825333975, 238168130645, 2523515252213,
    31754100877255, 689941647047881, 31731623113897, 1240305421873, 434174200187, 31754100877255,
    31754129469855, 217088333033, 132623764091, 476158431385, 33110899003, 33110899003,
    1538606267709, 769281962005, 16561632431, 2523517655579, 31754129469855, 689942299756585,
    15865825794945, 1240306673213, 18898005036565, 689941647047881, 689942299756585, 18898118536441,
    6162797170173, 22126259600655, 1538606267709, 17289816833, 217088333033, 18898118536441,
    1735306877755, 532022601, 1735296978287, 31731623113897, 15865825794945, 1735306877755,
    3081313782485, 11062825333975, 769281962005, 17024613545, 1240305421873, 1240306673213,
    532022601, 66336647407, 238168130645, 16561632431
  ]
def negativeCoefficients : Array ℕ := #[
    149321083635175042039414784, 6938692759787767506457853952, 6938501801305509782125281280, 149376850271586589853351936, 19466457886735752413315072, 488836691544014083680370688,
    5319315527544993164705136640, 488442676549405055513526272, 19168010804347174733742080, 19466457886735752413315072, 710306396845639376964681728, 710307073333028254147149824,
    19466603161600732317089792, 536106733538701471897354240, 24911953623153179408172318720, 24911268025877346481130700800, 536306952212174804573224960, 710306396845639376964681728,
    17875969609786344767813058560, 194201309034513946450314919936, 17863315753950943394203172864, 698229879471606079869157376, 488836691544014083680370688, 17875969609786344767813058560,
    17875985705989182962018549760, 488839467876950468863197184, 149321083635175042039414784, 536106733538701471897354240, 149118232411812927518015488, 149118232411812927518015488,
    6929266613924162012304113664, 6929075914857124123860008960, 149173923289797443612311552, 710307073333028254147149824, 17875985705989182962018549760, 194201492755681203692775669760,
    17863331784509876369809735680, 698230583913400794093715456, 5319315527544993164705136640, 194201309034513946450314919936, 194201492755681203692775669760, 5319347474919946927049015296,
    6938692759787767506457853952, 24911953623153179408172318720, 6929266613924162012304113664, 19466603161600732317089792, 488839467876950468863197184, 5319347474919946927049015296,
    488445463001929803397857280, 19168134300930256580640768, 488442676549405055513526272, 17863315753950943394203172864, 17863331784509876369809735680, 488445463001929803397857280,
    6938501801305509782125281280, 24911268025877346481130700800, 6929075914857124123860008960, 19168010804347174733742080, 698229879471606079869157376, 698230583913400794093715456,
    19168134300930256580640768, 149376850271586589853351936, 536306952212174804573224960, 149173923289797443612311552
  ]
def negativeScales : Array ℕ := #[
    36, 42, 41, 35, 34, 38,
    44, 40, 33, 34, 41, 41,
    34, 38, 44, 43, 37, 41,
    44, 49, 44, 40, 38, 44,
    44, 37, 36, 38, 34, 34,
    40, 39, 33, 41, 44, 49,
    43, 40, 44, 49, 49, 44,
    42, 44, 40, 34, 37, 44,
    40, 28, 40, 44, 43, 40,
    41, 43, 39, 33, 40, 40,
    28, 35, 37, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36948548360788997, 42486722448593129, 41486682743902938, 35949087060629209, 34009192767586028, 38659483043421115,
    44103299178259132, 40658319725073266, 33986903017805718, 34009192767586028, 41198571945009499, 41198573319014493,
    34009203534133617, 38792650723193820, 44330824820613483, 43330785115923292, 37793189422947152, 41198571945009499,
    44852008155825963, 49293467677162275, 44850986554176195, 40173832562780701, 38659483043421115, 44852008155825963,
    44852009454882902, 37659491237139911, 36948548360788997, 38792650723193820, 34946587140983861, 34946587140983861,
    40484761229120243, 39484721524430052, 33947125840821240, 41198573319014493, 44852009454882902, 49293469042001127,
    43850987848851752, 40173834018310178, 44103299178259132, 49293467677162275, 49293469042001127, 44103307842941791,
    42486722448593129, 44330824820613483, 40484761229120243, 34009203534133617, 37659491237139911, 44103307842941791,
    40658327955291402, 28986912312843745, 40658319725073266, 44850986554176195, 43850987848851752, 40658327955291402,
    41486682743902938, 43330785115923292, 39484721524430052, 33986903017805718, 40173832562780701, 40173834018310178,
    28986912312843745, 35949087060629209, 37793189422947152, 33947125840821240
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
noncomputable def negativeCeiling : ℝ := 3175373 / 5000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 149321083635175042039414784, coefficient := (-149321083635175042039414784) }, { argument := 6938692759787767506457853952, coefficient := (-6938692759787767506457853952) }, { argument := 6938501801305509782125281280, coefficient := (-6938501801305509782125281280) }, { argument := 149376850271586589853351936, coefficient := (-149376850271586589853351936) }, { argument := 19466457886735752413315072, coefficient := (-19466457886735752413315072) }, { argument := 488836691544014083680370688, coefficient := (-488836691544014083680370688) }, { argument := 5319315527544993164705136640, coefficient := (-5319315527544993164705136640) }, { argument := 488442676549405055513526272, coefficient := (-488442676549405055513526272) }, { argument := 19168010804347174733742080, coefficient := (-19168010804347174733742080) }, { argument := 19466457886735752413315072, coefficient := (-19466457886735752413315072) }, { argument := 710306396845639376964681728, coefficient := (-710306396845639376964681728) }, { argument := 710307073333028254147149824, coefficient := (-710307073333028254147149824) }, { argument := 19466603161600732317089792, coefficient := (-19466603161600732317089792) }, { argument := 536106733538701471897354240, coefficient := (-536106733538701471897354240) }, { argument := 24911953623153179408172318720, coefficient := (-24911953623153179408172318720) }, { argument := 24911268025877346481130700800, coefficient := (-24911268025877346481130700800) }, { argument := 536306952212174804573224960, coefficient := (-536306952212174804573224960) }, { argument := 710306396845639376964681728, coefficient := (-710306396845639376964681728) }, { argument := 17875969609786344767813058560, coefficient := (-17875969609786344767813058560) }, { argument := 194201309034513946450314919936, coefficient := (-194201309034513946450314919936) }, { argument := 17863315753950943394203172864, coefficient := (-17863315753950943394203172864) }, { argument := 698229879471606079869157376, coefficient := (-698229879471606079869157376) }, { argument := 488836691544014083680370688, coefficient := (-488836691544014083680370688) }, { argument := 17875969609786344767813058560, coefficient := (-17875969609786344767813058560) }, { argument := 17875985705989182962018549760, coefficient := (-17875985705989182962018549760) }, { argument := 488839467876950468863197184, coefficient := (-488839467876950468863197184) }, { argument := 149321083635175042039414784, coefficient := (-149321083635175042039414784) }, { argument := 536106733538701471897354240, coefficient := (-536106733538701471897354240) }, { argument := 149118232411812927518015488, coefficient := (-149118232411812927518015488) }, { argument := 149118232411812927518015488, coefficient := (-149118232411812927518015488) }, { argument := 6929266613924162012304113664, coefficient := (-6929266613924162012304113664) }, { argument := 6929075914857124123860008960, coefficient := (-6929075914857124123860008960) }, { argument := 149173923289797443612311552, coefficient := (-149173923289797443612311552) }, { argument := 710307073333028254147149824, coefficient := (-710307073333028254147149824) }, { argument := 17875985705989182962018549760, coefficient := (-17875985705989182962018549760) }, { argument := 194201492755681203692775669760, coefficient := (-194201492755681203692775669760) }, { argument := 17863331784509876369809735680, coefficient := (-17863331784509876369809735680) }, { argument := 698230583913400794093715456, coefficient := (-698230583913400794093715456) }, { argument := 5319315527544993164705136640, coefficient := (-5319315527544993164705136640) }, { argument := 194201309034513946450314919936, coefficient := (-194201309034513946450314919936) }, { argument := 194201492755681203692775669760, coefficient := (-194201492755681203692775669760) }, { argument := 5319347474919946927049015296, coefficient := (-5319347474919946927049015296) }, { argument := 6938692759787767506457853952, coefficient := (-6938692759787767506457853952) }, { argument := 24911953623153179408172318720, coefficient := (-24911953623153179408172318720) }, { argument := 6929266613924162012304113664, coefficient := (-6929266613924162012304113664) }, { argument := 19466603161600732317089792, coefficient := (-19466603161600732317089792) }, { argument := 488839467876950468863197184, coefficient := (-488839467876950468863197184) }, { argument := 5319347474919946927049015296, coefficient := (-5319347474919946927049015296) }, { argument := 488445463001929803397857280, coefficient := (-488445463001929803397857280) }, { argument := 19168134300930256580640768, coefficient := (-19168134300930256580640768) }, { argument := 488442676549405055513526272, coefficient := (-488442676549405055513526272) }, { argument := 17863315753950943394203172864, coefficient := (-17863315753950943394203172864) }, { argument := 17863331784509876369809735680, coefficient := (-17863331784509876369809735680) }, { argument := 488445463001929803397857280, coefficient := (-488445463001929803397857280) }, { argument := 6938501801305509782125281280, coefficient := (-6938501801305509782125281280) }, { argument := 24911268025877346481130700800, coefficient := (-24911268025877346481130700800) }, { argument := 6929075914857124123860008960, coefficient := (-6929075914857124123860008960) }, { argument := 19168010804347174733742080, coefficient := (-19168010804347174733742080) }, { argument := 698229879471606079869157376, coefficient := (-698229879471606079869157376) }, { argument := 698230583913400794093715456, coefficient := (-698230583913400794093715456) }, { argument := 19168134300930256580640768, coefficient := (-19168134300930256580640768) }, { argument := 149376850271586589853351936, coefficient := (-149376850271586589853351936) }, { argument := 536306952212174804573224960, coefficient := (-536306952212174804573224960) }, { argument := 149173923289797443612311552, coefficient := (-149173923289797443612311552) }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 54513048397558156977869110116352
def positiveArguments : Array ℕ := #[
    7, 1500931, 5388785, 374723, 1341537, 12247521,
    24495065, 1341545, 309071, 3888901, 84500317, 1943069,
    151915, 88361, 4105983, 2052935, 44197
  ]
def positiveCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 28351784990000077840951803904, 101791270669562804331547197440, 28313269368965793014588899328, 12670458728658990462092181504, 462698261349136960138329980928,
    462698695806853384145689640960, 12670534286522716376415600640, 2919093062454008231684472832, 73459262950392984564750352384, 798082929585320180469689483264, 73407071356024309245848584192,
    2869593216980568610554511360, 1669092099171378882909569024, 77559825993730217853868572672, 77557691484079960774231982080, 1669715451547117676077776896
  ]
def positiveScales : Array ℕ := #[
    2, 20, 22, 18, 20, 23,
    24, 20, 18, 21, 26, 20,
    17, 16, 21, 20, 15
  ]
def negativeArguments : Array ℕ := #[
    1, 3, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 950737950171172051122527404032, 950737950171172051122527404032, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 1, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 20517426224999651, 22361528597020208, 18515465005526778, 20355455414440976, 23545986429526440,
    24545987784166712, 20355464017652005, 18237578767523428, 21890931077555087, 26332453417836773, 20889905702235588,
    17212904802191202, 16431122125617886, 21969296222705614, 20969256518016003, 15431660825365022
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 1584962500724866, 1584962500724866, 0
  ]

abbrev PositiveTerm := Fin 17
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 684994121 / 1000000000000
noncomputable def negativeCeiling : ℝ := 36276913 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1109194275199700726309615304704, coefficient := 1109194275199700726309615304704 }, { argument := 28351784990000077840951803904, coefficient := 28351784990000077840951803904 }, { argument := 101791270669562804331547197440, coefficient := 101791270669562804331547197440 }, { argument := 28313269368965793014588899328, coefficient := 28313269368965793014588899328 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 12670458728658990462092181504, coefficient := 12670458728658990462092181504 }, { argument := 462698261349136960138329980928, coefficient := 462698261349136960138329980928 }, { argument := 462698695806853384145689640960, coefficient := 462698695806853384145689640960 }, { argument := 12670534286522716376415600640, coefficient := 12670534286522716376415600640 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 2919093062454008231684472832, coefficient := 2919093062454008231684472832 }, { argument := 73459262950392984564750352384, coefficient := 73459262950392984564750352384 }, { argument := 798082929585320180469689483264, coefficient := 798082929585320180469689483264 }, { argument := 73407071356024309245848584192, coefficient := 73407071356024309245848584192 }, { argument := 2869593216980568610554511360, coefficient := 2869593216980568610554511360 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 1669092099171378882909569024, coefficient := 1669092099171378882909569024 }, { argument := 77559825993730217853868572672, coefficient := 77559825993730217853868572672 }, { argument := 77557691484079960774231982080, coefficient := 77557691484079960774231982080 }, { argument := 1669715451547117676077776896, coefficient := 1669715451547117676077776896 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk2
