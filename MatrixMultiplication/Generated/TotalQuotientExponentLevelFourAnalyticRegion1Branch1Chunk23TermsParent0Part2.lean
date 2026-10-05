import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 23, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 1113886298588971340904955222425600
def positiveArguments : Array ℕ := #[
    95, 27, 405, 711, 27, 225,
    27, 711, 1413, 225, 21807, 1395,
    405, 711, 27, 1395, 27, 711,
    711, 27, 909, 4141, 101, 43329,
    1919, 101, 1919, 3737, 70599, 3737,
    43329, 70599, 909, 3737, 3737, 4141,
    413, 2065, 1711, 30739, 11505, 413,
    46079, 46079, 32981, 1711, 305, 335,
    305, 335, 1, 9, 9, 9368053,
    1094943525, 299777595, 12371533
  ]
def positiveCoefficients : Array ℕ := #[
    15053350877710224142773350563840, 2089023816294079213892272128, 31335357244411188208384081920, 55010960495744085965829832704, 2089023816294079213892272128, 34817063604901320231537868800,
    2089023816294079213892272128, 55010960495744085965829832704, 54662789859695072763514454016, 34817063604901320231537868800, 843617451146758989210162561024, 53966448587597046358883696640,
    31335357244411188208384081920, 55010960495744085965829832704, 2089023816294079213892272128, 53966448587597046358883696640, 2089023816294079213892272128, 55010960495744085965829832704,
    55010960495744085965829832704, 2089023816294079213892272128, 70330468481900666867706494976, 80098589104386870599332397056, 62515971983911703882405773312, 838104749409316280173502398464,
    74237716730895148360356855808, 62515971983911703882405773312, 74237716730895148360356855808, 72284092606397907614031675392, 2731166526047142563362602221568, 72284092606397907614031675392,
    838104749409316280173502398464, 2731166526047142563362602221568, 70330468481900666867706494976, 72284092606397907614031675392, 72284092606397907614031675392, 80098589104386870599332397056,
    31954327264053878345833644032, 639086545281077566916672880640, 33095553237770088286756274176, 594578732306145379220690305024, 890156259498643753919651512320, 31954327264053878345833644032,
    891297485472359963860574142464, 891297485472359963860574142464, 637945319307361356975750250496, 33095553237770088286756274176, 188785855991020491922116444160, 207354956580301196045603307520,
    188785855991020491922116444160, 207354956580301196045603307520, 158456325028528675187087900672, 713053462628379038341895553024, 713053462628379038341895553024, 1415660143902285710499214524416,
    5170724603095141445783676518400, 1415659666943270940665047941120, 58422912780915750459532115968
  ]
def positiveScales : Array ℕ := #[
    6, 4, 8, 9, 4, 7,
    4, 9, 10, 7, 14, 10,
    8, 9, 4, 10, 4, 9,
    9, 4, 9, 12, 6, 15,
    10, 6, 10, 11, 16, 11,
    15, 16, 9, 11, 11, 12,
    8, 11, 10, 14, 13, 8,
    15, 15, 15, 10, 8, 8,
    8, 8, 0, 3, 3, 23,
    30, 28, 23
  ]
def negativeArguments : Array ℕ := #[
    9, 101, 59, 5, 1, 9,
    101
  ]
def negativeCoefficients : Array ℕ := #[
    1426106925256758076683791106048, 8002044413940698096947938983936, 4674461588341595918019093069824, 792281625142643375935439503360, 158456325028528675187087900672, 1426106925256758076683791106048,
    8002044413940698096947938983936
  ]
def negativeScales : Array ℕ := #[
    3, 6, 5, 2, 0, 3,
    6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6569855608330797, 4754887502147955, 8661778097770205, 9473705749619407, 4754887502147955, 7813781191164178,
    4754887502147955, 9473705749619407, 10464545750333933, 7813781191164178, 14412503690893657, 10446049406716546,
    8661778097770205, 9473705749619407, 4754887502147955, 10446049406716546, 4754887502147955, 9473705749619407,
    9473705749619407, 4754887502147955, 9828136484123869, 12015763487369878, 6658211482750164, 15403045320251339,
    10906138995894173, 6658211482750164, 10906138995894173, 11867664848231192, 16107360128127231, 11867664848231192,
    15403045320251339, 16107360128127231, 9828136484123869, 11867664848231192, 11867664848231192, 12015763487369878,
    8689997971415898, 11011926066306807, 10740624044478062, 14907782611330225, 13489973363111439, 8689997971415898,
    15491821787503807, 15491821787503807, 15009347522205031, 10740624044478062, 8252665432450248, 8388017285345134,
    8252665432450248, 8388017285345134, 0, 3169925001442312, 3169925001442312, 23159317807270568,
    30028209314403040, 28159317321202973, 23560520944999858
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3169925001442313, 6658211482778016, 5882643052550791, 2321928094887363, 0, 3169925001442313,
    6658211482778016
  ]

abbrev PositiveTerm := Fin 57
abbrev NegativeTerm := Fin 7
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
noncomputable def positiveFloor : ℝ := 6575576319 / 1000000000000
noncomputable def negativeCeiling : ℝ := 109039023 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 15053350877710224142773350563840, coefficient := 15053350877710224142773350563840 }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 31335357244411188208384081920, coefficient := 31335357244411188208384081920 }, { argument := 55010960495744085965829832704, coefficient := 55010960495744085965829832704 }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 34817063604901320231537868800, coefficient := 34817063604901320231537868800 }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 55010960495744085965829832704, coefficient := 55010960495744085965829832704 }, { argument := 54662789859695072763514454016, coefficient := 54662789859695072763514454016 }, { argument := 34817063604901320231537868800, coefficient := 34817063604901320231537868800 }, { argument := 843617451146758989210162561024, coefficient := 843617451146758989210162561024 }, { argument := 53966448587597046358883696640, coefficient := 53966448587597046358883696640 }, { argument := 31335357244411188208384081920, coefficient := 31335357244411188208384081920 }, { argument := 55010960495744085965829832704, coefficient := 55010960495744085965829832704 }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 53966448587597046358883696640, coefficient := 53966448587597046358883696640 }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 55010960495744085965829832704, coefficient := 55010960495744085965829832704 }, { argument := 55010960495744085965829832704, coefficient := 55010960495744085965829832704 }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 70330468481900666867706494976, coefficient := 70330468481900666867706494976 }, { argument := 80098589104386870599332397056, coefficient := 80098589104386870599332397056 }, { argument := 62515971983911703882405773312, coefficient := 62515971983911703882405773312 }, { argument := 838104749409316280173502398464, coefficient := 838104749409316280173502398464 }, { argument := 74237716730895148360356855808, coefficient := 74237716730895148360356855808 }, { argument := 62515971983911703882405773312, coefficient := 62515971983911703882405773312 }, { argument := 74237716730895148360356855808, coefficient := 74237716730895148360356855808 }, { argument := 72284092606397907614031675392, coefficient := 72284092606397907614031675392 }, { argument := 2731166526047142563362602221568, coefficient := 2731166526047142563362602221568 }, { argument := 72284092606397907614031675392, coefficient := 72284092606397907614031675392 }, { argument := 838104749409316280173502398464, coefficient := 838104749409316280173502398464 }, { argument := 2731166526047142563362602221568, coefficient := 2731166526047142563362602221568 }, { argument := 70330468481900666867706494976, coefficient := 70330468481900666867706494976 }, { argument := 72284092606397907614031675392, coefficient := 72284092606397907614031675392 }, { argument := 72284092606397907614031675392, coefficient := 72284092606397907614031675392 }, { argument := 80098589104386870599332397056, coefficient := 80098589104386870599332397056 }, { argument := 8002044413940698096947938983936, coefficient := (-8002044413940698096947938983936) }, { argument := 31954327264053878345833644032, coefficient := 31954327264053878345833644032 }, { argument := 639086545281077566916672880640, coefficient := 639086545281077566916672880640 }, { argument := 33095553237770088286756274176, coefficient := 33095553237770088286756274176 }, { argument := 594578732306145379220690305024, coefficient := 594578732306145379220690305024 }, { argument := 890156259498643753919651512320, coefficient := 890156259498643753919651512320 }, { argument := 31954327264053878345833644032, coefficient := 31954327264053878345833644032 }, { argument := 891297485472359963860574142464, coefficient := 891297485472359963860574142464 }, { argument := 891297485472359963860574142464, coefficient := 891297485472359963860574142464 }, { argument := 637945319307361356975750250496, coefficient := 637945319307361356975750250496 }, { argument := 33095553237770088286756274176, coefficient := 33095553237770088286756274176 }, { argument := 4674461588341595918019093069824, coefficient := (-4674461588341595918019093069824) }, { argument := 188785855991020491922116444160, coefficient := 188785855991020491922116444160 }, { argument := 207354956580301196045603307520, coefficient := 207354956580301196045603307520 }, { argument := 188785855991020491922116444160, coefficient := 188785855991020491922116444160 }, { argument := 207354956580301196045603307520, coefficient := 207354956580301196045603307520 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 713053462628379038341895553024, coefficient := 713053462628379038341895553024 }, { argument := 713053462628379038341895553024, coefficient := 713053462628379038341895553024 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 1415660143902285710499214524416, coefficient := 1415660143902285710499214524416 }, { argument := 5170724603095141445783676518400, coefficient := 5170724603095141445783676518400 }, { argument := 1415659666943270940665047941120, coefficient := 1415659666943270940665047941120 }, { argument := 8002044413940698096947938983936, coefficient := (-8002044413940698096947938983936) }, { argument := 58422912780915750459532115968, coefficient := 58422912780915750459532115968 }] }

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

end TermShard4


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-136456336569513756284088813092864)
def positiveArguments : Array ℕ := #[
    241278199, 482556221, 1546449, 3855, 1822545, 69182355,
    7290185, 3855, 47557, 8341051, 2085263, 11889
  ]
def positiveCoefficients : Array ℕ := #[
    2278808160009504697859082027008, 2278807324150637229931879202816, 58423191400538239768599724032, 582551129326799433561538560, 68853803372173260287964610560, 653408868915978427795935068160,
    68853850595838088984416747520, 582551129326799433561538560, 449163165651663434855481344, 78778999348612674158688468992, 78779008793345639897978896384, 449153720918697695565053952
  ]
def positiveScales : Array ℕ := #[
    27, 28, 20, 11, 20, 26,
    22, 11, 15, 22, 20, 13
  ]
def negativeArguments : Array ℕ := #[
    59, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    4674461588341595918019093069824, 792281625142643375935439503360, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    5, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    27846122323887897, 28846121794712302, 20560527825214658, 11912515144465203, 20797523005498334, 26043900788778023,
    22797523994976334, 11912515144465203, 15537370089131860, 22991797747512055, 20991797920475261, 13537339752689083
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    5882643052550791, 2321928094887363, 0
  ]

abbrev PositiveTerm := Fin 12
abbrev NegativeTerm := Fin 3
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
noncomputable def positiveFloor : ℝ := 1852538291 / 1000000000000
noncomputable def negativeCeiling : ℝ := 176570521 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2278808160009504697859082027008, coefficient := 2278808160009504697859082027008 }, { argument := 2278807324150637229931879202816, coefficient := 2278807324150637229931879202816 }, { argument := 58423191400538239768599724032, coefficient := 58423191400538239768599724032 }, { argument := 4674461588341595918019093069824, coefficient := (-4674461588341595918019093069824) }, { argument := 582551129326799433561538560, coefficient := 582551129326799433561538560 }, { argument := 68853803372173260287964610560, coefficient := 68853803372173260287964610560 }, { argument := 653408868915978427795935068160, coefficient := 653408868915978427795935068160 }, { argument := 68853850595838088984416747520, coefficient := 68853850595838088984416747520 }, { argument := 582551129326799433561538560, coefficient := 582551129326799433561538560 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 449163165651663434855481344, coefficient := 449163165651663434855481344 }, { argument := 78778999348612674158688468992, coefficient := 78778999348612674158688468992 }, { argument := 78779008793345639897978896384, coefficient := 78779008793345639897978896384 }, { argument := 449153720918697695565053952, coefficient := 449153720918697695565053952 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end TermShard5


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23
