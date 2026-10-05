import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 14, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1483529073452603318396407854923776)
def positiveArguments : Array ℕ := #[
    299, 771, 1, 9, 9, 19,
    3008053, 10761111, 752013, 760265, 28075575, 224604545,
    6082175, 983759, 157054363, 6268665457, 157054363, 3934587,
    13654161, 1148168047, 574083885, 6827219, 1435659, 6952949,
    1435659
  ]
def positiveCoefficients : Array ℕ := #[
    46268008968291087774354767872, 238612942572257047986806194176, 4951760157141521099596496896, 5570730176784211237046059008, 5570730176784211237046059008, 5880215186605556305770840064,
    28410257331790969787987787776, 101635819809679701350402752512, 28410247887058004048697360384, 57443999265582253094249431040, 2121330469876687030728209203200, 2121329950416373915067235696640,
    57444518725895368755222937600, 18582682115285437223121453056, 2966673039278570164292096622592, 29602935646459527184941498499072, 2966673039278570164292096622592, 18580561772734628752420503552,
    128959904516211755521369178112, 10844140603709399001184467943424, 10844137987518367491401019555840, 128962520707243265304817565696, 54237663539441215822796685312, 525349973035232269102758232064,
    54237663539441215822796685312
  ]
def positiveScales : Array ℕ := #[
    8, 9, 0, 3, 3, 4,
    21, 23, 19, 19, 24, 27,
    22, 19, 27, 32, 27, 21,
    23, 30, 29, 22, 20, 22,
    20
  ]
def negativeArguments : Array ℕ := #[
    1, 1, 55, 449, 277, 1
  ]
def negativeCoefficients : Array ℕ := #[
    633825300114114700748351602688, 158456325028528675187087900672, 4357548938284538567644917268480, 35573444968904687579501233700864, 21946201016451221513411674243072, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    0, 0, 5, 8, 8, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8224001674198104, 9590587049914763, 0, 3169925001442312, 3169925001442312, 4247927513443585,
    21520398555941934, 23359323696701572, 19520398076330943, 19536142850292803, 24742812234150653, 27742811880870992,
    22536155896380102, 19907945403420348, 27226688780987417, 32545511192787486, 27226688780987417, 21907780777981367,
    23702837332515233, 30096686665713059, 29096686317657236, 22702866599965116, 20453281687963018, 22729193576691355,
    20453281687963018
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0, 5781359713964302, 8810571635541341, 8113742166049189, 0
  ]

abbrev PositiveTerm := Fin 25
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 5741184333 / 250000000000
noncomputable def negativeCeiling : ℝ := 3109659209 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 46268008968291087774354767872, coefficient := 46268008968291087774354767872 }, { argument := 238612942572257047986806194176, coefficient := 238612942572257047986806194176 }, { argument := 4951760157141521099596496896, coefficient := 4951760157141521099596496896 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 5880215186605556305770840064, coefficient := 5880215186605556305770840064 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 28410257331790969787987787776, coefficient := 28410257331790969787987787776 }, { argument := 101635819809679701350402752512, coefficient := 101635819809679701350402752512 }, { argument := 28410247887058004048697360384, coefficient := 28410247887058004048697360384 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 57443999265582253094249431040, coefficient := 57443999265582253094249431040 }, { argument := 2121330469876687030728209203200, coefficient := 2121330469876687030728209203200 }, { argument := 2121329950416373915067235696640, coefficient := 2121329950416373915067235696640 }, { argument := 57444518725895368755222937600, coefficient := 57444518725895368755222937600 }, { argument := 4357548938284538567644917268480, coefficient := (-4357548938284538567644917268480) }, { argument := 18582682115285437223121453056, coefficient := 18582682115285437223121453056 }, { argument := 2966673039278570164292096622592, coefficient := 2966673039278570164292096622592 }, { argument := 29602935646459527184941498499072, coefficient := 29602935646459527184941498499072 }, { argument := 2966673039278570164292096622592, coefficient := 2966673039278570164292096622592 }, { argument := 18580561772734628752420503552, coefficient := 18580561772734628752420503552 }, { argument := 35573444968904687579501233700864, coefficient := (-35573444968904687579501233700864) }, { argument := 128959904516211755521369178112, coefficient := 128959904516211755521369178112 }, { argument := 10844140603709399001184467943424, coefficient := 10844140603709399001184467943424 }, { argument := 10844137987518367491401019555840, coefficient := 10844137987518367491401019555840 }, { argument := 128962520707243265304817565696, coefficient := 128962520707243265304817565696 }, { argument := 21946201016451221513411674243072, coefficient := (-21946201016451221513411674243072) }, { argument := 54237663539441215822796685312, coefficient := 54237663539441215822796685312 }, { argument := 525349973035232269102758232064, coefficient := 525349973035232269102758232064 }, { argument := 54237663539441215822796685312, coefficient := 54237663539441215822796685312 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }] }

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

end TermShard8


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14
