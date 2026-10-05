import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 6, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk6

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
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    1, 18885, 1283667, 14134327, 1283687, 37765,
    40019, 8228493, 4115203, 158241
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 356727564115972999442595840, 12123892031931657725059006464, 133494944165438927648728285184, 12124080926590972510867554304, 356680340451144302990458880,
    1511875074223682654455201792, 77715919095454991106762080256, 77733986869618450369349681152, 1494543989231551056520937472
  ]
def positiveScales : Array ℕ := #[
    0, 14, 20, 23, 20, 15,
    15, 22, 21, 17
  ]
def negativeArguments : Array ℕ := #[
    755758815, 155395090305, 77715608655, 2988381285, 51371069673, 10562644923831,
    5282550289401, 203128749747, 755758815, 51371069673, 565641632213, 51371870053,
    1511317535, 565641632213, 116304210779211, 58165624873381, 2236630038807, 155395090305,
    10562644923831, 116304210779211, 10562809493691, 310749038145, 51371870053, 10562809493691,
    5282632593461, 203131914567, 77715608655, 5282550289401, 58165624873381, 5282632593461,
    155410641295, 1511317535, 310749038145, 155410641295, 5975971365, 2988381285,
    203128749747, 2236630038807, 203131914567, 5975971365, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1701817558807983811461120, 87479658849100321951580160, 87499996544882323457310720, 1682309105195870500945920, 57838682559236646950141952, 2973120233938259544046043136,
    2973811439364031175681114112, 57175660104301495852204032, 1701817558807983811461120, 57838682559236646950141952, 636855861014926486679846912, 57839583707004085649539072,
    1701592271866124136611840, 636855861014926486679846912, 32736725020429642739446972416, 32744335813191340647746895872, 629555388083553950490427392, 87479658849100321951580160,
    2973120233938259544046043136, 32736725020429642739446972416, 2973166556235770319964471296, 87468078274722627971973120, 57839583707004085649539072, 2973166556235770319964471296,
    2973857772430774560549240832, 57176550921937289270525952, 87499996544882323457310720, 2973811439364031175681114112, 32744335813191340647746895872, 2973857772430774560549240832,
    87488413278196477240279040, 1701592271866124136611840, 87468078274722627971973120, 87488413278196477240279040, 1682086400786922146365440, 1682309105195870500945920,
    57175660104301495852204032, 629555388083553950490427392, 57176550921937289270525952, 1682086400786922146365440, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    29, 37, 36, 31, 35, 43,
    42, 37, 29, 35, 39, 35,
    30, 39, 46, 45, 41, 37,
    43, 46, 43, 38, 35, 43,
    42, 37, 36, 42, 45, 42,
    37, 30, 38, 37, 32, 31,
    37, 41, 37, 32, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 14204953163327534, 20291839566366545, 23752699855687199, 20291862043906315, 15204762166432983,
    15288397496991357, 22972196802137821, 21972532167897502, 17271763922750127
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    29493350660319110, 37177149966396416, 36177485332161240, 31476717086077786, 35580237063361146, 43264036369435427,
    42264371735200251, 37563603489118672, 29493350660319110, 35580237063361146, 39041097352693352, 35580259540900917,
    30493159663424557, 39041097352693352, 46724896658899498, 45725232024665303, 41024463778452122, 37177149966396416,
    43264036369435427, 46724896658899498, 43264058846975197, 38176958969501864, 35580259540900917, 43264058846975197,
    42264394212740021, 37563625966658443, 36177485332161240, 42264371735200251, 45725232024665303, 42264394212740021,
    37177294335266688, 30493159663424557, 38176958969501864, 37177294335266688, 32476526089183233, 31476717086077786,
    37563603489118672, 41024463778452122, 37563625966658443, 32476526089183233, 0, 0
  ]

abbrev PositiveTerm := Fin 10
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
noncomputable def positiveFloor : ℝ := 43427539 / 500000000000
noncomputable def negativeCeiling : ℝ := 86855079 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1701817558807983811461120, coefficient := (-1701817558807983811461120) }, { argument := 87479658849100321951580160, coefficient := (-87479658849100321951580160) }, { argument := 87499996544882323457310720, coefficient := (-87499996544882323457310720) }, { argument := 1682309105195870500945920, coefficient := (-1682309105195870500945920) }, { argument := 57838682559236646950141952, coefficient := (-57838682559236646950141952) }, { argument := 2973120233938259544046043136, coefficient := (-2973120233938259544046043136) }, { argument := 2973811439364031175681114112, coefficient := (-2973811439364031175681114112) }, { argument := 57175660104301495852204032, coefficient := (-57175660104301495852204032) }, { argument := 1701817558807983811461120, coefficient := (-1701817558807983811461120) }, { argument := 57838682559236646950141952, coefficient := (-57838682559236646950141952) }, { argument := 636855861014926486679846912, coefficient := (-636855861014926486679846912) }, { argument := 57839583707004085649539072, coefficient := (-57839583707004085649539072) }, { argument := 1701592271866124136611840, coefficient := (-1701592271866124136611840) }, { argument := 636855861014926486679846912, coefficient := (-636855861014926486679846912) }, { argument := 32736725020429642739446972416, coefficient := (-32736725020429642739446972416) }, { argument := 32744335813191340647746895872, coefficient := (-32744335813191340647746895872) }, { argument := 629555388083553950490427392, coefficient := (-629555388083553950490427392) }, { argument := 87479658849100321951580160, coefficient := (-87479658849100321951580160) }, { argument := 2973120233938259544046043136, coefficient := (-2973120233938259544046043136) }, { argument := 32736725020429642739446972416, coefficient := (-32736725020429642739446972416) }, { argument := 2973166556235770319964471296, coefficient := (-2973166556235770319964471296) }, { argument := 87468078274722627971973120, coefficient := (-87468078274722627971973120) }, { argument := 57839583707004085649539072, coefficient := (-57839583707004085649539072) }, { argument := 2973166556235770319964471296, coefficient := (-2973166556235770319964471296) }, { argument := 2973857772430774560549240832, coefficient := (-2973857772430774560549240832) }, { argument := 57176550921937289270525952, coefficient := (-57176550921937289270525952) }, { argument := 87499996544882323457310720, coefficient := (-87499996544882323457310720) }, { argument := 2973811439364031175681114112, coefficient := (-2973811439364031175681114112) }, { argument := 32744335813191340647746895872, coefficient := (-32744335813191340647746895872) }, { argument := 2973857772430774560549240832, coefficient := (-2973857772430774560549240832) }, { argument := 87488413278196477240279040, coefficient := (-87488413278196477240279040) }, { argument := 1701592271866124136611840, coefficient := (-1701592271866124136611840) }, { argument := 87468078274722627971973120, coefficient := (-87468078274722627971973120) }, { argument := 87488413278196477240279040, coefficient := (-87488413278196477240279040) }, { argument := 1682086400786922146365440, coefficient := (-1682086400786922146365440) }, { argument := 1682309105195870500945920, coefficient := (-1682309105195870500945920) }, { argument := 57175660104301495852204032, coefficient := (-57175660104301495852204032) }, { argument := 629555388083553950490427392, coefficient := (-629555388083553950490427392) }, { argument := 57176550921937289270525952, coefficient := (-57176550921937289270525952) }, { argument := 1682086400786922146365440, coefficient := (-1682086400786922146365440) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 356727564115972999442595840, coefficient := 356727564115972999442595840 }, { argument := 12123892031931657725059006464, coefficient := 12123892031931657725059006464 }, { argument := 133494944165438927648728285184, coefficient := 133494944165438927648728285184 }, { argument := 12124080926590972510867554304, coefficient := 12124080926590972510867554304 }, { argument := 356680340451144302990458880, coefficient := 356680340451144302990458880 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1511875074223682654455201792, coefficient := 1511875074223682654455201792 }, { argument := 77715919095454991106762080256, coefficient := 77715919095454991106762080256 }, { argument := 77733986869618450369349681152, coefficient := 77733986869618450369349681152 }, { argument := 1494543989231551056520937472, coefficient := 1494543989231551056520937472 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk6
