import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 4, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-24809789127660535042472609778237440)
def positiveArguments : Array ℕ := #[
    23009, 44807, 44807, 1408393, 44807, 56917,
    3633, 1271, 3895, 11521, 25707, 1271,
    12833, 26117, 1271, 3895, 1271, 257,
    1025, 509, 1025, 8388605, 8388611, 146955851,
    528136073, 36747915, 450230907, 17786600215, 8893300961, 112558635,
    5971813, 2304657355, 23967754883, 1152329743, 5971813, 45376743,
    8888490777, 8888490879, 45376641, 355423, 16064473, 44665
  ]
def positiveCoefficients : Array ℕ := #[
    890117573872416085786060914688, 866693427191563030896954048512, 866693427191563030896954048512, 27242282589832102836031285362688, 866693427191563030896954048512, 1100934894000093579788022710272,
    1124359040680946634677129576448, 49169430935366197793649590272, 1205444113254139042683022213120, 891394199537929134194550636544, 994491393434664710213493325824, 49169430935366197793649590272,
    992905282759330316736278822912, 1010352500188008644985638354944, 49169430935366197793649590272, 1205444113254139042683022213120, 49169430935366197793649590272, 39768823762042841331134365696,
    39652766883359836930362572800, 39381967499766159995228389376, 39652766883359836930362572800, 79228134180065440375672668160, 79228190848463234811415232512, 1387958770447971268893545070592,
    4988104179059192388129302511616, 1388296976890741427144459550720, 2126155344768800327330558902272, 83994844699518025374898994544640, 83994852760597611633383374323712, 2126172501126232592751620259840,
    225608716425321796740300406784, 43533746591004037391940132536320, 452738089316457899692159529910272, 43533786844455937372795934081024, 225608716425321796740300406784, 214285610244989793363063472128,
    41974710928600769975199090081792, 41974711410282151227902901878784, 214285128563608540659251675136, 26855002599055646572599574528, 1213797261762630048879977955328, 26998335866543706044125675520
  ]
def positiveScales : Array ℕ := #[
    14, 15, 15, 20, 15, 15,
    11, 10, 11, 13, 14, 10,
    13, 14, 10, 11, 10, 8,
    10, 8, 10, 22, 23, 27,
    28, 25, 28, 34, 33, 26,
    22, 31, 34, 30, 22, 25,
    33, 33, 25, 18, 23, 15
  ]
def negativeArguments : Array ℕ := #[
    1211, 41, 1, 1, 49, 1087,
    6819, 1065, 1
  ]
def negativeCoefficients : Array ℕ := #[
    95945304804774112825781723856896, 6496709326169675682670603927552, 158456325028528675187087900672, 158456325028528675187087900672, 7764359926397905084167307132928, 172242025306010669928364548030464,
    540256840184768518050376197341184, 84377993077691519537124307107840, 1267650600228229401496703205376
  ]
def negativeScales : Array ℕ := #[
    10, 5, 0, 0, 5, 10,
    12, 10, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14489910663137901, 15451436515323275, 15451436515323275, 20425618531167545, 15451436515323275, 15796572001334644,
    11826945650346870, 10311748315004958, 11927407612511617, 13491978324838996, 14649873637418802, 10311748315004958,
    13647570851549456, 14672701566872049, 10311748315004958, 11927407612511617, 10311748315004958, 8005624549193878,
    10001408194392808, 8991521844801183, 10001408194392808, 22999999482592385, 23000000515947860, 27130807559671267,
    28976334442516707, 25131159060977055, 28746089855960638, 34050071724701068, 33050071863158125, 26746101497298125,
    22509737559278088, 31101905127856538, 34480375723490167, 30101906461843000, 22509737559278088, 25435449724822076,
    33049291331153917, 33049291347709584, 25435446481859936, 18439177517965153, 23937370317221351, 15446857141489837
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    10241983149694329, 5357552004618085, 0, 0, 5614709844123661, 10086136225027310,
    12735344469701700, 10056637715113201, 0
  ]

abbrev PositiveTerm := Fin 42
abbrev NegativeTerm := Fin 9
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
noncomputable def positiveFloor : ℝ := 83665729769 / 250000000000
noncomputable def negativeCeiling : ℝ := 126717086489 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 890117573872416085786060914688, coefficient := 890117573872416085786060914688 }, { argument := 866693427191563030896954048512, coefficient := 866693427191563030896954048512 }, { argument := 866693427191563030896954048512, coefficient := 866693427191563030896954048512 }, { argument := 27242282589832102836031285362688, coefficient := 27242282589832102836031285362688 }, { argument := 866693427191563030896954048512, coefficient := 866693427191563030896954048512 }, { argument := 1100934894000093579788022710272, coefficient := 1100934894000093579788022710272 }, { argument := 1124359040680946634677129576448, coefficient := 1124359040680946634677129576448 }, { argument := 95945304804774112825781723856896, coefficient := (-95945304804774112825781723856896) }, { argument := 49169430935366197793649590272, coefficient := 49169430935366197793649590272 }, { argument := 1205444113254139042683022213120, coefficient := 1205444113254139042683022213120 }, { argument := 891394199537929134194550636544, coefficient := 891394199537929134194550636544 }, { argument := 994491393434664710213493325824, coefficient := 994491393434664710213493325824 }, { argument := 49169430935366197793649590272, coefficient := 49169430935366197793649590272 }, { argument := 992905282759330316736278822912, coefficient := 992905282759330316736278822912 }, { argument := 1010352500188008644985638354944, coefficient := 1010352500188008644985638354944 }, { argument := 49169430935366197793649590272, coefficient := 49169430935366197793649590272 }, { argument := 1205444113254139042683022213120, coefficient := 1205444113254139042683022213120 }, { argument := 49169430935366197793649590272, coefficient := 49169430935366197793649590272 }, { argument := 6496709326169675682670603927552, coefficient := (-6496709326169675682670603927552) }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 79228134180065440375672668160, coefficient := 79228134180065440375672668160 }, { argument := 79228190848463234811415232512, coefficient := 79228190848463234811415232512 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1387958770447971268893545070592, coefficient := 1387958770447971268893545070592 }, { argument := 4988104179059192388129302511616, coefficient := 4988104179059192388129302511616 }, { argument := 1388296976890741427144459550720, coefficient := 1388296976890741427144459550720 }, { argument := 7764359926397905084167307132928, coefficient := (-7764359926397905084167307132928) }, { argument := 2126155344768800327330558902272, coefficient := 2126155344768800327330558902272 }, { argument := 83994844699518025374898994544640, coefficient := 83994844699518025374898994544640 }, { argument := 83994852760597611633383374323712, coefficient := 83994852760597611633383374323712 }, { argument := 2126172501126232592751620259840, coefficient := 2126172501126232592751620259840 }, { argument := 172242025306010669928364548030464, coefficient := (-172242025306010669928364548030464) }, { argument := 225608716425321796740300406784, coefficient := 225608716425321796740300406784 }, { argument := 43533746591004037391940132536320, coefficient := 43533746591004037391940132536320 }, { argument := 452738089316457899692159529910272, coefficient := 452738089316457899692159529910272 }, { argument := 43533786844455937372795934081024, coefficient := 43533786844455937372795934081024 }, { argument := 225608716425321796740300406784, coefficient := 225608716425321796740300406784 }, { argument := 540256840184768518050376197341184, coefficient := (-540256840184768518050376197341184) }, { argument := 214285610244989793363063472128, coefficient := 214285610244989793363063472128 }, { argument := 41974710928600769975199090081792, coefficient := 41974710928600769975199090081792 }, { argument := 41974711410282151227902901878784, coefficient := 41974711410282151227902901878784 }, { argument := 214285128563608540659251675136, coefficient := 214285128563608540659251675136 }, { argument := 84377993077691519537124307107840, coefficient := (-84377993077691519537124307107840) }, { argument := 26855002599055646572599574528, coefficient := 26855002599055646572599574528 }, { argument := 1213797261762630048879977955328, coefficient := 1213797261762630048879977955328 }, { argument := 26998335866543706044125675520, coefficient := 26998335866543706044125675520 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4
