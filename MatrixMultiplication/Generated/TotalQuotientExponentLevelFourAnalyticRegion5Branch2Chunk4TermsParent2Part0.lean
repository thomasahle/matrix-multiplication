import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 4, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    1, 51985, 164479, 3510773, 1317071, 12309
  ]
def positiveCoefficients : Array ℕ := #[
    79228162514264337593543950336, 490984443223957012867973120, 12427681867774662001656070144, 132633253953309703486585176064, 12439383891919212982495608832, 465020872301139703483072512
  ]
def positiveScales : Array ℕ := #[
    0, 15, 17, 21, 20, 13
  ]
def negativeArguments : Array ℕ := #[
    2702440225, 8550440815, 182507534405, 68467935935, 639883365, 8550440815,
    27053341441, 577448432267, 216630521009, 2024572011, 182507534405, 577448432267,
    12325527057529, 4623937305883, 43214104857, 68467935935, 216630521009, 4623937305883,
    1734676019041, 16211826939, 639883365, 2024572011, 43214104857, 16211826939,
    151511481, 1
  ]
def negativeCoefficients : Array ℕ := #[
    760669299393814960537600, 19253881034143740062597120, 205485215984666494600478720, 19272010672730812039823360, 720444621043644770549760, 19253881034143740062597120,
    487349673731257589190098944, 5201193088766676597540388864, 487808566846604402577375232, 18235723508648671457574912, 205485215984666494600478720, 5201193088766676597540388864,
    55509239063432570414389264384, 5206090581939803495430356992, 194619026531134741332099072, 19272010672730812039823360, 487808566846604402577375232, 5206090581939803495430356992,
    488267892060098939003600896, 18252894440368842196647936, 720444621043644770549760, 18235723508648671457574912, 194619026531134741332099072, 18252894440368842196647936,
    682347049373951984664576, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    31, 32, 37, 35, 29, 32,
    34, 39, 37, 30, 37, 39,
    43, 42, 35, 35, 37, 42,
    40, 33, 29, 30, 35, 33,
    27, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 15665807780735268, 17327543872805543, 21743357286589869, 20328901689092439, 13587425939613443
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    31331615561474477, 32993351674829412, 37409165067339174, 35994709491585348, 29253233720350930, 32993351674829412,
    34655087745635326, 39070901159407471, 37656445561923066, 30914969818117506, 37409165067339174, 39070901159407471,
    43486714573204026, 42072258975694366, 35330783226215618, 35994709491585348, 37656445561923066, 42072258975694366,
    40657803378210832, 33916327634542138, 29253233720350930, 30914969818117506, 35330783226215618, 33916327634542138,
    27174851879227383, 0
  ]

abbrev PositiveTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 20259113 / 500000000000
noncomputable def negativeCeiling : ℝ := 40518227 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 760669299393814960537600, coefficient := (-760669299393814960537600) }, { argument := 19253881034143740062597120, coefficient := (-19253881034143740062597120) }, { argument := 205485215984666494600478720, coefficient := (-205485215984666494600478720) }, { argument := 19272010672730812039823360, coefficient := (-19272010672730812039823360) }, { argument := 720444621043644770549760, coefficient := (-720444621043644770549760) }, { argument := 19253881034143740062597120, coefficient := (-19253881034143740062597120) }, { argument := 487349673731257589190098944, coefficient := (-487349673731257589190098944) }, { argument := 5201193088766676597540388864, coefficient := (-5201193088766676597540388864) }, { argument := 487808566846604402577375232, coefficient := (-487808566846604402577375232) }, { argument := 18235723508648671457574912, coefficient := (-18235723508648671457574912) }, { argument := 205485215984666494600478720, coefficient := (-205485215984666494600478720) }, { argument := 5201193088766676597540388864, coefficient := (-5201193088766676597540388864) }, { argument := 55509239063432570414389264384, coefficient := (-55509239063432570414389264384) }, { argument := 5206090581939803495430356992, coefficient := (-5206090581939803495430356992) }, { argument := 194619026531134741332099072, coefficient := (-194619026531134741332099072) }, { argument := 19272010672730812039823360, coefficient := (-19272010672730812039823360) }, { argument := 487808566846604402577375232, coefficient := (-487808566846604402577375232) }, { argument := 5206090581939803495430356992, coefficient := (-5206090581939803495430356992) }, { argument := 488267892060098939003600896, coefficient := (-488267892060098939003600896) }, { argument := 18252894440368842196647936, coefficient := (-18252894440368842196647936) }, { argument := 720444621043644770549760, coefficient := (-720444621043644770549760) }, { argument := 18235723508648671457574912, coefficient := (-18235723508648671457574912) }, { argument := 194619026531134741332099072, coefficient := (-194619026531134741332099072) }, { argument := 18252894440368842196647936, coefficient := (-18252894440368842196647936) }, { argument := 682347049373951984664576, coefficient := (-682347049373951984664576) }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 490984443223957012867973120, coefficient := 490984443223957012867973120 }, { argument := 12427681867774662001656070144, coefficient := 12427681867774662001656070144 }, { argument := 132633253953309703486585176064, coefficient := 132633253953309703486585176064 }, { argument := 12439383891919212982495608832, coefficient := 12439383891919212982495608832 }, { argument := 465020872301139703483072512, coefficient := 465020872301139703483072512 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk4
