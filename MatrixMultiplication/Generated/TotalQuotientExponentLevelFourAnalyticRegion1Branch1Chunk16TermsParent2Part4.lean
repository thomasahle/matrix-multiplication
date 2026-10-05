import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 16, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16

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
def constantNumerator : ℤ := (-1436629021074743097124533219360768)
def positiveArguments : Array ℕ := #[
    1287, 2097, 27, 111, 111, 123,
    92753, 10841025, 2968095, 12371533, 241278199, 482556221,
    1546449, 20817, 9841743, 373584717, 39366999, 20817,
    6134853, 1075995579, 268998927, 1533681, 1066269, 48193419,
    133995
  ]
def positiveCoefficients : Array ℕ := #[
    49788400955008887931099152384, 162247516398840152278966468608, 4178047632588158427784544256, 4294104511271162828556337152, 4294104511271162828556337152, 4758332026003180431643508736,
    28032874136678924960380485632, 102390586199903791005617356800, 28032864691945959221090058240, 58422912780915750459532115968, 2278808160009504697859082027008, 2278807324150637229931879202816,
    58423191400538239768599724032, 25166208786917735529858465792, 2974484305677884844440071176192, 28227263137170268080784394944512, 2974486345740205444126803492864, 25166208786917735529858465792,
    57942048369064583096357093376, 10162490915971034966470812499968, 10162492134341587546839277633536, 57940829998512002727891959808, 10070625974645867464724840448, 455173973160986268329991733248,
    10124375949953889766547128320
  ]
def positiveScales : Array ℕ := #[
    10, 11, 4, 6, 6, 6,
    16, 23, 21, 23, 27, 28,
    20, 14, 23, 28, 25, 14,
    22, 30, 28, 20, 20, 25,
    17
  ]
def negativeArguments : Array ℕ := #[
    3, 1, 59, 27, 129, 3
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 158456325028528675187087900672, 4674461588341595918019093069824, 34226566206162193840410986545152, 20440865928680199099134339186688, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    1, 0, 5, 4, 7, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10329796338220701, 11034111146096592, 4754887502147955, 6794415866314396, 6794415866314396, 6942514504772358,
    16501106324518755, 23369997831651245, 21501105838451160, 23560520944999858, 27846122323887897, 28846121794712302,
    20560527825214658, 14345474552078502, 23230482412812495, 28476860196054121, 25230483402290496, 14345474552078502,
    22548597344555091, 30003025004215483, 28003025177178693, 20548567008112314, 20024140018686312, 25522332818461723,
    17031819642210997
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 0, 5882643052550791, 4754887502413606, 7011227255423255, 1584962500724866
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
noncomputable def positiveFloor : ℝ := 1017317727 / 50000000000
noncomputable def negativeCeiling : ℝ := 1008296853 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 49788400955008887931099152384, coefficient := 49788400955008887931099152384 }, { argument := 162247516398840152278966468608, coefficient := 162247516398840152278966468608 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4758332026003180431643508736, coefficient := 4758332026003180431643508736 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 28032874136678924960380485632, coefficient := 28032874136678924960380485632 }, { argument := 102390586199903791005617356800, coefficient := 102390586199903791005617356800 }, { argument := 28032864691945959221090058240, coefficient := 28032864691945959221090058240 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 58422912780915750459532115968, coefficient := 58422912780915750459532115968 }, { argument := 2278808160009504697859082027008, coefficient := 2278808160009504697859082027008 }, { argument := 2278807324150637229931879202816, coefficient := 2278807324150637229931879202816 }, { argument := 58423191400538239768599724032, coefficient := 58423191400538239768599724032 }, { argument := 4674461588341595918019093069824, coefficient := (-4674461588341595918019093069824) }, { argument := 25166208786917735529858465792, coefficient := 25166208786917735529858465792 }, { argument := 2974484305677884844440071176192, coefficient := 2974484305677884844440071176192 }, { argument := 28227263137170268080784394944512, coefficient := 28227263137170268080784394944512 }, { argument := 2974486345740205444126803492864, coefficient := 2974486345740205444126803492864 }, { argument := 25166208786917735529858465792, coefficient := 25166208786917735529858465792 }, { argument := 34226566206162193840410986545152, coefficient := (-34226566206162193840410986545152) }, { argument := 57942048369064583096357093376, coefficient := 57942048369064583096357093376 }, { argument := 10162490915971034966470812499968, coefficient := 10162490915971034966470812499968 }, { argument := 10162492134341587546839277633536, coefficient := 10162492134341587546839277633536 }, { argument := 57940829998512002727891959808, coefficient := 57940829998512002727891959808 }, { argument := 20440865928680199099134339186688, coefficient := (-20440865928680199099134339186688) }, { argument := 10070625974645867464724840448, coefficient := 10070625974645867464724840448 }, { argument := 455173973160986268329991733248, coefficient := 455173973160986268329991733248 }, { argument := 10124375949953889766547128320, coefficient := 10124375949953889766547128320 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16
