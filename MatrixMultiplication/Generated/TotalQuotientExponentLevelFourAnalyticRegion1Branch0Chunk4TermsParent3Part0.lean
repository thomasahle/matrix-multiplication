import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 4, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk4

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    129, 173, 367, 1033, 1163, 2077,
    4647, 6851, 8237, 16825, 23523, 33639,
    57717
  ]
def positiveCoefficients : Array ℕ := #[
    140075391325219348865385704194048, 263275184034900393823346546966528, 158456325028528675187087900672, 7764359926397905084167307132928, 4832917913370124593206180970496, 90557789753804137869420735234048,
    4674461588341595918019093069824, 1085584282770449953706739207503872, 89765508128661494493485295730688, 125893550235166032436141337083904, 354546027251332910731109177753600, 125735093910137503760954249183232,
    281656117738209720145048743444480
  ]
def positiveScales : Array ℕ := #[
    7, 7, 8, 10, 10, 11,
    12, 12, 13, 14, 14, 15,
    15
  ]
def negativeArguments : Array ℕ := #[
    13, 25, 41, 55, 133, 221,
    241, 293, 301, 481, 609, 1067,
    3323, 339036971423
  ]
def negativeCoefficients : Array ℕ := #[
    4119864450741745554864285417472, 3961408125713216879677197516800, 6496709326169675682670603927552, 139441566025105234164637352591360, 84298764915177255199530763157504, 140075391325219348865385704194048,
    38187974331875410720088184061952, 185710812933435607319267019587584, 47695353833587131231313458102272, 38108746169361146382494640111616, 48249950971186981594468265754624, 84536449402720048212311395008512,
    263275184034900393823346546966528, 542792141385224976853369603751936
  ]
def negativeScales : Array ℕ := #[
    3, 4, 5, 5, 7, 7,
    7, 8, 8, 8, 9, 10,
    11, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7011227255423254, 7434628227636722, 8519636252843180, 10012624538865059, 10183635381473218, 11020285500844647,
    12182083929510724, 12742098869766579, 13007903273382046, 14038318884385041, 14521784445213500, 15037847198207772,
    15816708693224067
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3700439718214233, 4643856189792934, 5357552004618085, 5781359713964302, 7055282435501190, 7787902559895231,
    7912889341723050, 8194756854422248, 8233619676759703, 8909893088979699, 9250298417906333, 10059344460824425,
    11698270577761530, 38302651649217809
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 14
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
noncomputable def positiveFloor : ℝ := 6090865389 / 15625000000
noncomputable def negativeCeiling : ℝ := 72904844757 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 13, coefficient := (-4119864450741745554864285417472) }, { argument := 25, coefficient := (-3961408125713216879677197516800) }, { argument := 41, coefficient := (-6496709326169675682670603927552) }, { argument := 55, coefficient := (-139441566025105234164637352591360) }, { argument := 129, coefficient := 140075391325219348865385704194048 }, { argument := 133, coefficient := (-84298764915177255199530763157504) }, { argument := 173, coefficient := 263275184034900393823346546966528 }, { argument := 221, coefficient := (-140075391325219348865385704194048) }, { argument := 241, coefficient := (-38187974331875410720088184061952) }, { argument := 293, coefficient := (-185710812933435607319267019587584) }, { argument := 301, coefficient := (-47695353833587131231313458102272) }, { argument := 367, coefficient := 158456325028528675187087900672 }, { argument := 481, coefficient := (-38108746169361146382494640111616) }, { argument := 609, coefficient := (-48249950971186981594468265754624) }, { argument := 1033, coefficient := 7764359926397905084167307132928 }, { argument := 1067, coefficient := (-84536449402720048212311395008512) }, { argument := 1163, coefficient := 4832917913370124593206180970496 }, { argument := 2077, coefficient := 90557789753804137869420735234048 }, { argument := 3323, coefficient := (-263275184034900393823346546966528) }, { argument := 4647, coefficient := 4674461588341595918019093069824 }, { argument := 6851, coefficient := 1085584282770449953706739207503872 }, { argument := 8237, coefficient := 89765508128661494493485295730688 }, { argument := 16825, coefficient := 125893550235166032436141337083904 }, { argument := 23523, coefficient := 354546027251332910731109177753600 }, { argument := 33639, coefficient := 125735093910137503760954249183232 }, { argument := 57717, coefficient := 281656117738209720145048743444480 }, { argument := 339036971423, coefficient := (-542792141385224976853369603751936) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  rfl

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk4
