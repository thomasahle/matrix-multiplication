import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 10, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk10

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    47, 125, 129, 249, 257, 267,
    499, 987, 1327, 1701, 2135, 12213,
    17027, 18353, 18363
  ]
def positiveCoefficients : Array ℕ := #[
    1426106925256758076683791106048, 328559189946654208000426762043392, 34701935181247779865972250247168, 328400733621625679325239674142720, 39693309419646433134365519118336, 14736438227653166792399174762496,
    304156915892260792021615225339904, 302096983666889919244183082631168, 613067521535377444298843087699968, 673677065858789662557904209707008, 14815666390167431129992718712832, 819536113047550308067618622275584,
    2698035846260757752410545684742144, 249489483757418399082069899608064, 248855658457304284381321548005376
  ]
def positiveScales : Array ℕ := #[
    5, 6, 7, 7, 8, 8,
    8, 9, 10, 10, 11, 13,
    14, 14, 14
  ]
def negativeArguments : Array ℕ := #[
    3, 5, 31, 39, 41, 49,
    75, 97, 121, 141, 233, 291,
    501, 557, 747, 1153, 1497, 2317,
    3869, 4145, 4147, 5415, 350905531907
  ]
def negativeCoefficients : Array ℕ := #[
    3802951800684688204490109616128, 3961408125713216879677197516800, 39297168607075111446397799366656, 12359593352225236664592856252416, 3248354663084837841335301963776, 11646539889596857626250960699392,
    11884224377139650639031592550400, 7685131763883640746573763182592, 19173215328451969697637635981312, 89369367316090172805517575979008, 18460161865823590659295740428288, 46110790583301844479442579095552,
    39693309419646433134365519118336, 88260173040890472079207960674304, 118366874796310920364754661801984, 182700142757893562490712349474816, 118604559283853713377535293652992, 183571652545550470204241332928512,
    613067521535377444298843087699968, 328400733621625679325239674142720, 328559189946654208000426762043392, 429020500014741388069040491069440, 1349017923130378876205272842371072
  ]
def negativeScales : Array ℕ := #[
    1, 2, 4, 5, 5, 5,
    6, 6, 6, 7, 7, 8,
    8, 9, 9, 10, 10, 11,
    11, 12, 12, 12, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5554588851677541, 6965784283824454, 7011227255423254, 7960001931307143, 8005624549193878, 8060695931687553,
    8962896004538793, 9946906273845666, 10373952655370192, 10732167425653982, 11060020354507852, 13576130006860986,
    14055536647426470, 14163728286289152, 14164514153527719
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2321928094887363, 4954196321574415, 5285402218862249, 5357552004618085, 5614709844123661,
    6228818690495881, 6599912842192769, 6918863243376152, 7139551352398794, 7864186146919547, 8184875342908284,
    8968666807433246, 9121533517340032, 9544964432790378, 10171176797651772, 10547858506059663, 11178042328864822,
    11917745019426307, 12017156386383113, 12017852331905962, 12402745622495697, 38352291735279601
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 23
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
noncomputable def positiveFloor : ℝ := 488599289169 / 500000000000
noncomputable def negativeCeiling : ℝ := 980883133563 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-3802951800684688204490109616128) }, { argument := 5, coefficient := (-3961408125713216879677197516800) }, { argument := 31, coefficient := (-39297168607075111446397799366656) }, { argument := 39, coefficient := (-12359593352225236664592856252416) }, { argument := 41, coefficient := (-3248354663084837841335301963776) }, { argument := 47, coefficient := 1426106925256758076683791106048 }, { argument := 49, coefficient := (-11646539889596857626250960699392) }, { argument := 75, coefficient := (-11884224377139650639031592550400) }, { argument := 97, coefficient := (-7685131763883640746573763182592) }, { argument := 121, coefficient := (-19173215328451969697637635981312) }, { argument := 125, coefficient := 328559189946654208000426762043392 }, { argument := 129, coefficient := 34701935181247779865972250247168 }, { argument := 141, coefficient := (-89369367316090172805517575979008) }, { argument := 233, coefficient := (-18460161865823590659295740428288) }, { argument := 249, coefficient := 328400733621625679325239674142720 }, { argument := 257, coefficient := 39693309419646433134365519118336 }, { argument := 267, coefficient := 14736438227653166792399174762496 }, { argument := 291, coefficient := (-46110790583301844479442579095552) }, { argument := 499, coefficient := 304156915892260792021615225339904 }, { argument := 501, coefficient := (-39693309419646433134365519118336) }, { argument := 557, coefficient := (-88260173040890472079207960674304) }, { argument := 747, coefficient := (-118366874796310920364754661801984) }, { argument := 987, coefficient := 302096983666889919244183082631168 }, { argument := 1153, coefficient := (-182700142757893562490712349474816) }, { argument := 1327, coefficient := 613067521535377444298843087699968 }, { argument := 1497, coefficient := (-118604559283853713377535293652992) }, { argument := 1701, coefficient := 673677065858789662557904209707008 }, { argument := 2135, coefficient := 14815666390167431129992718712832 }, { argument := 2317, coefficient := (-183571652545550470204241332928512) }, { argument := 3869, coefficient := (-613067521535377444298843087699968) }, { argument := 4145, coefficient := (-328400733621625679325239674142720) }, { argument := 4147, coefficient := (-328559189946654208000426762043392) }, { argument := 5415, coefficient := (-429020500014741388069040491069440) }, { argument := 12213, coefficient := 819536113047550308067618622275584 }, { argument := 17027, coefficient := 2698035846260757752410545684742144 }, { argument := 18353, coefficient := 249489483757418399082069899608064 }, { argument := 18363, coefficient := 248855658457304284381321548005376 }, { argument := 350905531907, coefficient := (-1349017923130378876205272842371072) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk10
