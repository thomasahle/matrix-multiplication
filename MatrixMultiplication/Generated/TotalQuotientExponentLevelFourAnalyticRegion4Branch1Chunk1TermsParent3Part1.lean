import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 4, branch 1,
parent chunk 1, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 78914000289354390643692632276992
def positiveArguments : Array ℕ := #[
    5, 17, 17, 137, 19, 61,
    19, 17, 137, 61, 2405, 61,
    17, 17, 19, 61, 19, 137,
    137, 9, 15851765, 26101945, 15830425, 2271305,
    81614815, 81612685, 2273355, 35243, 2584505, 56488935,
    2584503, 140941
  ]
def positiveCoefficients : Array ℕ := #[
    1584563250285286751870879006720, 657655645870358271040159744, 5261245166962866168321277952, 5299930793190534301911875584, 735026898325694538221355008, 4719646399775512298052911104,
    735026898325694538221355008, 5261245166962866168321277952, 5299930793190534301911875584, 4719646399775512298052911104, 93038931077541861285387304960, 4719646399775512298052911104,
    5261245166962866168321277952, 5261245166962866168321277952, 735026898325694538221355008, 4719646399775512298052911104, 735026898325694538221355008, 5299930793190534301911875584,
    5299930793190534301911875584, 696341272098026404630757376, 149715687460652283121767546880, 493051800822827686149624954880, 149514136859163406664047001600, 21451869208748479044187586560,
    770830133723213526462869012480, 770810016441996501774258667520, 21471230911328244589563740160, 1331442895646199250130305024, 48819919147236049612093521920, 533522906594004003899068907520,
    48819881368304186654931812352, 1331150108924261332127055872
  ]
def positiveScales : Array ℕ := #[
    2, 4, 4, 7, 4, 5,
    4, 4, 7, 5, 11, 5,
    4, 4, 4, 5, 4, 7,
    7, 3, 23, 24, 23, 21,
    26, 26, 21, 15, 21, 25,
    21, 17
  ]
def negativeArguments : Array ℕ := #[
    2244733442573, 678012361561, 1, 5, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    631836293469865842613157888, 190843513679919350353494016, 158456325028528675187087900672, 792281625142643375935439503360, 1584563250285286751870879006720, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    41, 39, 0, 2, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 4087462841250339, 4087462841250339, 7098032082960526, 4247927513443585, 5930737337099561,
    4247927513443585, 4087462841250339, 7098032082960526, 5930737337099561, 11231821178657404, 5930737337099561,
    4087462841250339, 4087462841250339, 4247927513443585, 5930737337099561, 4247927513443585, 7098032082960526,
    7098032082960526, 3169925001442312, 23918140148682295, 24637653978182171, 23916196651933429, 21115090019288915,
    26282327723111929, 26282290070872725, 21116391557812991, 15105049115978803, 21301456562657998, 25751464965636901,
    21301455446238723, 17104731829819968
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    41029681276750604, 39302520620662689, 0, 2321928094887363, 2321928094887363, 0
  ]

abbrev PositiveTerm := Fin 32
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
noncomputable def positiveFloor : ℝ := 245798063 / 250000000000
noncomputable def negativeCeiling : ℝ := 66833231 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 631836293469865842613157888, coefficient := (-631836293469865842613157888) }, { argument := 190843513679919350353494016, coefficient := (-190843513679919350353494016) }, { argument := 1584563250285286751870879006720, coefficient := 1584563250285286751870879006720 }, { argument := 657655645870358271040159744, coefficient := 657655645870358271040159744 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 5299930793190534301911875584, coefficient := 5299930793190534301911875584 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 5299930793190534301911875584, coefficient := 5299930793190534301911875584 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 93038931077541861285387304960, coefficient := 93038931077541861285387304960 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 5299930793190534301911875584, coefficient := 5299930793190534301911875584 }, { argument := 5299930793190534301911875584, coefficient := 5299930793190534301911875584 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 149715687460652283121767546880, coefficient := 149715687460652283121767546880 }, { argument := 493051800822827686149624954880, coefficient := 493051800822827686149624954880 }, { argument := 149514136859163406664047001600, coefficient := 149514136859163406664047001600 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 21451869208748479044187586560, coefficient := 21451869208748479044187586560 }, { argument := 770830133723213526462869012480, coefficient := 770830133723213526462869012480 }, { argument := 770810016441996501774258667520, coefficient := 770810016441996501774258667520 }, { argument := 21471230911328244589563740160, coefficient := 21471230911328244589563740160 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 1331442895646199250130305024, coefficient := 1331442895646199250130305024 }, { argument := 48819919147236049612093521920, coefficient := 48819919147236049612093521920 }, { argument := 533522906594004003899068907520, coefficient := 533522906594004003899068907520 }, { argument := 48819881368304186654931812352, coefficient := 48819881368304186654931812352 }, { argument := 1331150108924261332127055872, coefficient := 1331150108924261332127055872 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk1
