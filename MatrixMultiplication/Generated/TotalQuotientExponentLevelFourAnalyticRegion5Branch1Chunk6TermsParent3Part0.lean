import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 6, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk6

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1789864382149381839002477264896)
def positiveArguments : Array ℕ := #[
    7, 33554385, 33554479, 18356457, 15990603, 18344427,
    235865, 32610951, 8152741, 943489
  ]
def positiveCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 316912206154607960627525713920, 316913093959506740120825888768, 173371834562075757940932870144, 604107901184598378904503189504, 173258214424497914277091344384,
    8910727763856390946627256320, 308001723953808678902449569792, 308001846735337233513225125888, 8911001661112397386049650688
  ]
def positiveScales : Array ℕ := #[
    2, 24, 25, 24, 23, 24,
    17, 24, 22, 19
  ]
def negativeArguments : Array ℕ := #[
    7914304875809, 273560101410223, 136780105230479, 3957274072585, 14037903024327, 97852136771571,
    28057179221631, 7914304875809, 7914327331551, 7914327331551, 273560867482193, 136780488267633,
    3957285300727, 97852136771571, 85228747171815, 97788475543665, 273560101410223, 273560867482193,
    28057179221631, 97788475543665, 1752409520145, 136780105230479, 136780488267633, 3957274072585,
    3957285300727, 1, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    2227678780599369501406920704, 77000323173407212507431436288, 77000353868460306912350568448, 2227747254837091392573931520, 15805273707355559011232514048, 55085855837731745633667121152,
    15794787735950574325566799872, 2227678780599369501406920704, 2227685101328825971906707456, 2227685101328825971906707456, 77000538803497126943793348608, 77000569499208309844261994496,
    2227753575719107300450893824, 55085855837731745633667121152, 191918077002120124412586885120, 55050017752447319405997588480, 77000323173407212507431436288, 77000538803497126943793348608,
    15794787735950574325566799872, 55050017752447319405997588480, 15784301723851063406981283840, 77000353868460306912350568448, 77000569499208309844261994496, 2227747254837091392573931520,
    2227753575719107300450893824, 633825300114114700748351602688, 950737950171172051122527404032, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    42, 47, 46, 41, 43, 46,
    44, 42, 42, 42, 47, 46,
    41, 46, 46, 46, 47, 47,
    44, 46, 40, 46, 46, 41,
    41, 0, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 24999997977742902, 25000002020794732, 24129784293672231, 23930721007113603, 24128838505992378,
    17847601827321829, 24958853177013190, 22958853752127714, 19847646172088017
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    42847599782356614, 47958851169809799, 46958851744919086, 41847644127137806, 43674392676172347, 46475668588486943,
    44673435205912890, 42847599782356614, 42847603875797946, 42847603875797946, 47958855209897890, 46958855785017897,
    41847648220552115, 46475668588486943, 46276405358905360, 46474729685874117, 47958851169809799, 47958855209897890,
    44673435205912890, 46474729685874117, 40672477096069732, 46958851744919086, 46958855785017897, 41847644127137806,
    41847648220552115, 0, 1584962500724866, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 28
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
noncomputable def positiveFloor : ℝ := 684606143 / 1000000000000
noncomputable def negativeCeiling : ℝ := 321138913 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2227678780599369501406920704, coefficient := (-2227678780599369501406920704) }, { argument := 77000323173407212507431436288, coefficient := (-77000323173407212507431436288) }, { argument := 77000353868460306912350568448, coefficient := (-77000353868460306912350568448) }, { argument := 2227747254837091392573931520, coefficient := (-2227747254837091392573931520) }, { argument := 15805273707355559011232514048, coefficient := (-15805273707355559011232514048) }, { argument := 55085855837731745633667121152, coefficient := (-55085855837731745633667121152) }, { argument := 15794787735950574325566799872, coefficient := (-15794787735950574325566799872) }, { argument := 2227678780599369501406920704, coefficient := (-2227678780599369501406920704) }, { argument := 2227685101328825971906707456, coefficient := (-2227685101328825971906707456) }, { argument := 2227685101328825971906707456, coefficient := (-2227685101328825971906707456) }, { argument := 77000538803497126943793348608, coefficient := (-77000538803497126943793348608) }, { argument := 77000569499208309844261994496, coefficient := (-77000569499208309844261994496) }, { argument := 2227753575719107300450893824, coefficient := (-2227753575719107300450893824) }, { argument := 55085855837731745633667121152, coefficient := (-55085855837731745633667121152) }, { argument := 191918077002120124412586885120, coefficient := (-191918077002120124412586885120) }, { argument := 55050017752447319405997588480, coefficient := (-55050017752447319405997588480) }, { argument := 77000323173407212507431436288, coefficient := (-77000323173407212507431436288) }, { argument := 77000538803497126943793348608, coefficient := (-77000538803497126943793348608) }, { argument := 15794787735950574325566799872, coefficient := (-15794787735950574325566799872) }, { argument := 55050017752447319405997588480, coefficient := (-55050017752447319405997588480) }, { argument := 15784301723851063406981283840, coefficient := (-15784301723851063406981283840) }, { argument := 77000353868460306912350568448, coefficient := (-77000353868460306912350568448) }, { argument := 77000569499208309844261994496, coefficient := (-77000569499208309844261994496) }, { argument := 2227747254837091392573931520, coefficient := (-2227747254837091392573931520) }, { argument := 2227753575719107300450893824, coefficient := (-2227753575719107300450893824) }, { argument := 1109194275199700726309615304704, coefficient := 1109194275199700726309615304704 }, { argument := 316912206154607960627525713920, coefficient := 316912206154607960627525713920 }, { argument := 316913093959506740120825888768, coefficient := 316913093959506740120825888768 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 173371834562075757940932870144, coefficient := 173371834562075757940932870144 }, { argument := 604107901184598378904503189504, coefficient := 604107901184598378904503189504 }, { argument := 173258214424497914277091344384, coefficient := 173258214424497914277091344384 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 8910727763856390946627256320, coefficient := 8910727763856390946627256320 }, { argument := 308001723953808678902449569792, coefficient := 308001723953808678902449569792 }, { argument := 308001846735337233513225125888, coefficient := 308001846735337233513225125888 }, { argument := 8911001661112397386049650688, coefficient := 8911001661112397386049650688 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk6
