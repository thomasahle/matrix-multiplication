import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 6, for level-four region 1, branch 1,
parent chunk 11, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11

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
def constantNumerator : ℤ := (-12626080017165121642583683804168192)
def positiveArguments : Array ℕ := #[
    1467, 4401, 9291, 23961, 20049, 560883,
    17115, 20049, 18093, 9291, 9291, 18093,
    560883, 18093, 1467, 23961, 351, 5265,
    9243, 351, 2925, 351, 9243, 18369,
    2925, 283491, 18135, 5265, 9243, 351,
    18135, 351, 9243, 9243, 351, 25165827,
    25165821, 127167991, 467101595, 63575351, 79043523, 3091849935,
    3091850187, 79044003, 11567371, 525606195, 42764864693, 4204856711,
    11567371, 58135279, 10696060177, 21392121883, 116269029, 15994035,
    722901285, 2009925
  ]
def positiveCoefficients : Array ℕ := #[
    454014509407913215819253809152, 340510882055934911864440356864, 359428153281264629190242598912, 463473145020578074482154930176, 6204864961908147282863135391744, 10849055047726592886347585814528,
    331052246443270053201539235840, 6204864961908147282863135391744, 349969517668599770527341477888, 359428153281264629190242598912, 359428153281264629190242598912, 349969517668599770527341477888,
    10849055047726592886347585814528, 349969517668599770527341477888, 454014509407913215819253809152, 463473145020578074482154930176, 13578654805911514890299768832, 203679822088672723354496532480,
    357571243222336558777893912576, 13578654805911514890299768832, 226310913431858581504996147200, 13578654805911514890299768832, 357571243222336558777893912576, 355308134088017972962843951104,
    226310913431858581504996147200, 5483513432453933429866056646656, 350781915819380801332744028160, 203679822088672723354496532480, 357571243222336558777893912576, 13578654805911514890299768832,
    350781915819380801332744028160, 13578654805911514890299768832, 357571243222336558777893912576, 357571243222336558777893912576, 13578654805911514890299768832, 237684515876991909998503133184,
    237684459208594115562760568832, 600533858392268696708486004736, 2205824916322951456401517445120, 600452213398146363412386414592, 373272483703135907450619691008, 14600848503106691167439038709760,
    14600849693143044850589632561152, 373274750439047684880322265088, 109250730210636661650391826432, 19856840627653175214165731573760, 201951363670678679920624510435328, 19856874397295894214998654713856,
    109250730210636661650391826432, 549072186043751090258463162368, 101021432157243129704664881168384, 101021439377741482012352412909568, 549064965545398782570931421184, 302118779239376023941745213440,
    13655219194829588049899751997440, 303731278498616692996413849600
  ]
def positiveScales : Array ℕ := #[
    10, 12, 13, 14, 14, 19,
    14, 14, 14, 13, 13, 14,
    19, 14, 10, 14, 8, 12,
    13, 8, 11, 8, 13, 14,
    11, 18, 14, 12, 13, 8,
    14, 8, 13, 13, 8, 24,
    24, 26, 28, 25, 26, 31,
    31, 26, 23, 28, 35, 31,
    23, 25, 33, 34, 26, 23,
    29, 20
  ]
def negativeArguments : Array ℕ := #[
    489, 117, 3, 43, 189, 3053,
    641, 45
  ]
def negativeCoefficients : Array ℕ := #[
    38742571469475261083242991714304, 9269695014168927498444642189312, 475368975085586025561263702016, 3406810988113366516522389864448, 29948245430391919610359613227008, 241883580156049022673089680375808,
    203141008686573761589846688661504, 14261069252567580766837911060480
  ]
def negativeScales : Array ℕ := #[
    8, 6, 1, 5, 7, 11,
    9, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10518653155673358, 12103615656394545, 13181618168395819, 14548400499067362, 14291242659570317, 19097340330968058,
    14062973671897200, 14291242659570317, 14143144020581183, 13181618168395819, 13181618168395819, 14143144020581183,
    19097340330968058, 14143144020581183, 10518653155673358, 14548400499067362, 8455327220304556, 12362217815913078,
    13174145467760507, 8455327220304556, 11514220909358101, 8455327220304556, 13174145467760507, 14164985468475031,
    11514220909358101, 18112943409034750, 14146489124857641, 12362217815913078, 13174145467760507, 8455327220304556,
    14146489124857641, 8455327220304556, 13174145467760507, 13174145467760507, 8455327220304556, 24584962672703565,
    24584962328738263, 26922160339409283, 28799161130540326, 25921964185881339, 26236143914035952, 31525823152781593,
    31525823270367874, 26236152674924773, 23463557674184719, 28969407038137567, 35315706924225568, 31969409491662519,
    23463557674184719, 25792910583263208, 33316360436172879, 34316360539289382, 26792891611175535, 23931030613829156,
    29429223414070275, 20938710237288230
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    8933690662845865, 6870364722125690, 1584962500724866, 5426264754702117, 7562242424222992, 11576011874209651,
    9324180546618742, 5491853096329881
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
noncomputable def positiveFloor : ℝ := 26289587689 / 125000000000
noncomputable def negativeCeiling : ℝ := 65337248739 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 454014509407913215819253809152, coefficient := 454014509407913215819253809152 }, { argument := 340510882055934911864440356864, coefficient := 340510882055934911864440356864 }, { argument := 359428153281264629190242598912, coefficient := 359428153281264629190242598912 }, { argument := 463473145020578074482154930176, coefficient := 463473145020578074482154930176 }, { argument := 6204864961908147282863135391744, coefficient := 6204864961908147282863135391744 }, { argument := 10849055047726592886347585814528, coefficient := 10849055047726592886347585814528 }, { argument := 331052246443270053201539235840, coefficient := 331052246443270053201539235840 }, { argument := 6204864961908147282863135391744, coefficient := 6204864961908147282863135391744 }, { argument := 349969517668599770527341477888, coefficient := 349969517668599770527341477888 }, { argument := 359428153281264629190242598912, coefficient := 359428153281264629190242598912 }, { argument := 359428153281264629190242598912, coefficient := 359428153281264629190242598912 }, { argument := 349969517668599770527341477888, coefficient := 349969517668599770527341477888 }, { argument := 10849055047726592886347585814528, coefficient := 10849055047726592886347585814528 }, { argument := 349969517668599770527341477888, coefficient := 349969517668599770527341477888 }, { argument := 454014509407913215819253809152, coefficient := 454014509407913215819253809152 }, { argument := 463473145020578074482154930176, coefficient := 463473145020578074482154930176 }, { argument := 38742571469475261083242991714304, coefficient := (-38742571469475261083242991714304) }, { argument := 13578654805911514890299768832, coefficient := 13578654805911514890299768832 }, { argument := 203679822088672723354496532480, coefficient := 203679822088672723354496532480 }, { argument := 357571243222336558777893912576, coefficient := 357571243222336558777893912576 }, { argument := 13578654805911514890299768832, coefficient := 13578654805911514890299768832 }, { argument := 226310913431858581504996147200, coefficient := 226310913431858581504996147200 }, { argument := 13578654805911514890299768832, coefficient := 13578654805911514890299768832 }, { argument := 357571243222336558777893912576, coefficient := 357571243222336558777893912576 }, { argument := 355308134088017972962843951104, coefficient := 355308134088017972962843951104 }, { argument := 226310913431858581504996147200, coefficient := 226310913431858581504996147200 }, { argument := 5483513432453933429866056646656, coefficient := 5483513432453933429866056646656 }, { argument := 350781915819380801332744028160, coefficient := 350781915819380801332744028160 }, { argument := 203679822088672723354496532480, coefficient := 203679822088672723354496532480 }, { argument := 357571243222336558777893912576, coefficient := 357571243222336558777893912576 }, { argument := 13578654805911514890299768832, coefficient := 13578654805911514890299768832 }, { argument := 350781915819380801332744028160, coefficient := 350781915819380801332744028160 }, { argument := 13578654805911514890299768832, coefficient := 13578654805911514890299768832 }, { argument := 357571243222336558777893912576, coefficient := 357571243222336558777893912576 }, { argument := 357571243222336558777893912576, coefficient := 357571243222336558777893912576 }, { argument := 13578654805911514890299768832, coefficient := 13578654805911514890299768832 }, { argument := 9269695014168927498444642189312, coefficient := (-9269695014168927498444642189312) }, { argument := 237684515876991909998503133184, coefficient := 237684515876991909998503133184 }, { argument := 237684459208594115562760568832, coefficient := 237684459208594115562760568832 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 600533858392268696708486004736, coefficient := 600533858392268696708486004736 }, { argument := 2205824916322951456401517445120, coefficient := 2205824916322951456401517445120 }, { argument := 600452213398146363412386414592, coefficient := 600452213398146363412386414592 }, { argument := 3406810988113366516522389864448, coefficient := (-3406810988113366516522389864448) }, { argument := 373272483703135907450619691008, coefficient := 373272483703135907450619691008 }, { argument := 14600848503106691167439038709760, coefficient := 14600848503106691167439038709760 }, { argument := 14600849693143044850589632561152, coefficient := 14600849693143044850589632561152 }, { argument := 373274750439047684880322265088, coefficient := 373274750439047684880322265088 }, { argument := 29948245430391919610359613227008, coefficient := (-29948245430391919610359613227008) }, { argument := 109250730210636661650391826432, coefficient := 109250730210636661650391826432 }, { argument := 19856840627653175214165731573760, coefficient := 19856840627653175214165731573760 }, { argument := 201951363670678679920624510435328, coefficient := 201951363670678679920624510435328 }, { argument := 19856874397295894214998654713856, coefficient := 19856874397295894214998654713856 }, { argument := 109250730210636661650391826432, coefficient := 109250730210636661650391826432 }, { argument := 241883580156049022673089680375808, coefficient := (-241883580156049022673089680375808) }, { argument := 549072186043751090258463162368, coefficient := 549072186043751090258463162368 }, { argument := 101021432157243129704664881168384, coefficient := 101021432157243129704664881168384 }, { argument := 101021439377741482012352412909568, coefficient := 101021439377741482012352412909568 }, { argument := 549064965545398782570931421184, coefficient := 549064965545398782570931421184 }, { argument := 203141008686573761589846688661504, coefficient := (-203141008686573761589846688661504) }, { argument := 302118779239376023941745213440, coefficient := 302118779239376023941745213440 }, { argument := 13655219194829588049899751997440, coefficient := 13655219194829588049899751997440 }, { argument := 303731278498616692996413849600, coefficient := 303731278498616692996413849600 }, { argument := 14261069252567580766837911060480, coefficient := (-14261069252567580766837911060480) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
