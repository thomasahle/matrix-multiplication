import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 11, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk11

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
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    1, 3100025, 10577173, 1550009, 203781, 2046205,
    8186411, 50551
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 29278908312115943807175884800, 99898574517427547747769122816, 29278842198985183632142893056, 1924657128491318342584369152, 77303439272642259075926589440,
    77318465842790750286996570112, 1909762784604347481580371968
  ]
def positiveScales : Array ℕ := #[
    0, 21, 23, 20, 17, 20,
    22, 15
  ]
def negativeArguments : Array ℕ := #[
    631726194525, 6343286655125, 25378078760275, 156709363775, 631726194525, 2155426891113,
    315862384029, 2155426891113, 21643064278465, 86589085396103, 534686672323, 6343286655125,
    21643064278465, 3171636165845, 315862384029, 3171636165845, 12689010727699, 78354504959,
    25378078760275, 86589085396103, 12689010727699, 156709363775, 534686672323, 78354504959,
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    177815115891435716896358400, 7141905854081297492738048000, 7143294128009599317861990400, 176439058075639376091545600, 177815115891435716896358400, 606698733977553341018800128,
    177814714376670113377026048, 606698733977553341018800128, 24367924054912666718867292160, 24372660795265095489780973568, 602003674558458324217495552, 7141905854081297492738048000,
    24367924054912666718867292160, 7141889727327165326357954560, 177814714376670113377026048, 7141889727327165326357954560, 7143277998120680335855321088, 176438659668076040481144832,
    7143294128009599317861990400, 24372660795265095489780973568, 7143277998120680335855321088, 176439058075639376091545600, 602003674558458324217495552, 176438659668076040481144832,
    158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    39, 42, 44, 37, 39, 40,
    38, 40, 44, 46, 38, 42,
    44, 41, 38, 41, 43, 36,
    44, 46, 43, 37, 38, 36,
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 21563848419414074, 23334450748764632, 20563845161738188, 17636660019150534, 20964519257901833,
    22964799667821649, 15625452011355991
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    39200508438565675, 42528367678136978, 44528648088060622, 37189300430770893, 39200508438565675, 40971110782740040,
    38200505180889789, 40971110782740040, 44298970007486730, 46299250417410368, 38959902772430800, 42528367678136978,
    44298970007486730, 41528364420461092, 38200505180889789, 41528364420461092, 43528644830384736, 36189297173095007,
    44528648088060622, 46299250417410368, 43528644830384736, 37189300430770893, 38959902772430800, 36189297173095007,
    0, 0
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 42277459 / 500000000000
noncomputable def negativeCeiling : ℝ := 84554919 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 177815115891435716896358400, coefficient := (-177815115891435716896358400) }, { argument := 7141905854081297492738048000, coefficient := (-7141905854081297492738048000) }, { argument := 7143294128009599317861990400, coefficient := (-7143294128009599317861990400) }, { argument := 176439058075639376091545600, coefficient := (-176439058075639376091545600) }, { argument := 177815115891435716896358400, coefficient := (-177815115891435716896358400) }, { argument := 606698733977553341018800128, coefficient := (-606698733977553341018800128) }, { argument := 177814714376670113377026048, coefficient := (-177814714376670113377026048) }, { argument := 606698733977553341018800128, coefficient := (-606698733977553341018800128) }, { argument := 24367924054912666718867292160, coefficient := (-24367924054912666718867292160) }, { argument := 24372660795265095489780973568, coefficient := (-24372660795265095489780973568) }, { argument := 602003674558458324217495552, coefficient := (-602003674558458324217495552) }, { argument := 7141905854081297492738048000, coefficient := (-7141905854081297492738048000) }, { argument := 24367924054912666718867292160, coefficient := (-24367924054912666718867292160) }, { argument := 7141889727327165326357954560, coefficient := (-7141889727327165326357954560) }, { argument := 177814714376670113377026048, coefficient := (-177814714376670113377026048) }, { argument := 7141889727327165326357954560, coefficient := (-7141889727327165326357954560) }, { argument := 7143277998120680335855321088, coefficient := (-7143277998120680335855321088) }, { argument := 176438659668076040481144832, coefficient := (-176438659668076040481144832) }, { argument := 7143294128009599317861990400, coefficient := (-7143294128009599317861990400) }, { argument := 24372660795265095489780973568, coefficient := (-24372660795265095489780973568) }, { argument := 7143277998120680335855321088, coefficient := (-7143277998120680335855321088) }, { argument := 176439058075639376091545600, coefficient := (-176439058075639376091545600) }, { argument := 602003674558458324217495552, coefficient := (-602003674558458324217495552) }, { argument := 176438659668076040481144832, coefficient := (-176438659668076040481144832) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 29278908312115943807175884800, coefficient := 29278908312115943807175884800 }, { argument := 99898574517427547747769122816, coefficient := 99898574517427547747769122816 }, { argument := 29278842198985183632142893056, coefficient := 29278842198985183632142893056 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1924657128491318342584369152, coefficient := 1924657128491318342584369152 }, { argument := 77303439272642259075926589440, coefficient := 77303439272642259075926589440 }, { argument := 77318465842790750286996570112, coefficient := 77318465842790750286996570112 }, { argument := 1909762784604347481580371968, coefficient := 1909762784604347481580371968 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk11
