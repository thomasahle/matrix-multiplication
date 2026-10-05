import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 11, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk11

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
def constantNumerator : ℤ := (-299412123835437295436728425775104)
def positiveArguments : Array ℕ := #[
    107, 119, 786476391, 2545, 786408089, 1285,
    347627501, 665, 217, 150479371, 2191, 347627451,
    4389, 1967, 665, 217
  ]
def positiveCoefficients : Array ℕ := #[
    33909653556105136490036810743808, 18856302678394912347263460179968, 14856118993706727564472215404544, 196909837498830799976141946880, 14854828805404675714442671947776, 198844118810214206655671828480,
    3283248918492268148787502907392, 205807531531194470701979402240, 8394780891403984989159686144, 11369899807579303788002154643456, 169520414129641761393998823424, 3283248446255619861822981537792,
    169791213513235438329133006848, 152189253579646437545411084288, 205807531531194470701979402240, 8394780891403984989159686144
  ]
def positiveScales : Array ℕ := #[
    6, 6, 29, 11, 29, 10,
    28, 9, 7, 27, 11, 28,
    12, 10, 9, 7
  ]
def negativeArguments : Array ℕ := #[
    347627501, 665, 217, 150479371, 2191, 347627451,
    4389, 1967, 665, 217, 794659857413, 10674506225,
    189445, 5389681925, 347627501, 10674506225, 10674501135, 665,
    217, 189445, 10674501135, 794519985147, 5389679355, 150479371,
    2191, 347627451, 5389681925, 5389679355, 4389, 1967,
    665, 217, 119, 95, 119
  ]
def negativeCoefficients : Array ℕ := #[
    1641624459246134074393751453696, 102903765765597235350989701120, 4197390445701992494579843072, 5684949903789651894001077321728, 84760207064820880696999411712, 1641624223127809930911490768896,
    84895606756617719164566503424, 76094626789823218772705542144, 102903765765597235350989701120, 4197390445701992494579843072, 3664721753837033762286680932352, 49227471111448616891737702400,
    3664399230350294784035384197120, 49711041554586619022304870400, 1641624459246134074393751453696, 49227471111448616891737702400, 49227447637966783096333271040, 102903765765597235350989701120,
    4197390445701992494579843072, 3664399230350294784035384197120, 49227447637966783096333271040, 3664076706863555805784087461888, 49711017850520484305531043840, 5684949903789651894001077321728,
    84760207064820880696999411712, 1641624223127809930911490768896, 49711041554586619022304870400, 49711017850520484305531043840, 84895606756617719164566503424, 76094626789823218772705542144,
    102903765765597235350989701120, 4197390445701992494579843072, 18856302678394912347263460179968, 30106701755420448285546701127680, 18856302678394912347263460179968
  ]
def negativeScales : Array ℕ := #[
    28, 9, 7, 27, 11, 28,
    12, 10, 9, 7, 39, 33,
    17, 32, 28, 33, 33, 9,
    7, 17, 33, 39, 32, 27,
    11, 28, 32, 32, 12, 10,
    9, 7, 6, 6, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6741466986389582, 6894817763061968, 29550828217558030, 11313449940963057, 29550702920426553, 10327552644081240,
    28372966978152536, 9377210530388551, 7761551232426566, 27164990482656128, 11097373768990222, 28372966770646637,
    12099676554859642, 10941781241718677, 9377210530388551, 7761551232426566
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    28372966978152540, 9377210530388555, 7761551232733342, 27164990482656129, 11097373768990223, 28372966770646641,
    12099676554859644, 10941781251345720, 9377210530388555, 7761551232733342, 39531546511666042, 33313450284928319,
    17531419537903102, 32327552988046502, 28372966978152540, 33313450284928319, 33313449596997716, 9377210530388555,
    7761551232733342, 17531419537903102, 33313449596997716, 39531292552964027, 32327552300115899, 27164990482656129,
    11097373768990223, 28372966770646641, 32327552988046502, 32327552300115899, 12099676554859644, 10941781251345720,
    9377210530388555, 7761551232733342, 6894817767286876, 6569855608333349, 6894817767286876
  ]

abbrev PositiveTerm := Fin 16
abbrev NegativeTerm := Fin 35
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
noncomputable def positiveFloor : ℝ := 5129973 / 244140625
noncomputable def negativeCeiling : ℝ := 16776936801 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1641624459246134074393751453696, coefficient := (-1641624459246134074393751453696) }, { argument := 102903765765597235350989701120, coefficient := (-102903765765597235350989701120) }, { argument := 4197390445701992494579843072, coefficient := (-4197390445701992494579843072) }, { argument := 5684949903789651894001077321728, coefficient := (-5684949903789651894001077321728) }, { argument := 84760207064820880696999411712, coefficient := (-84760207064820880696999411712) }, { argument := 1641624223127809930911490768896, coefficient := (-1641624223127809930911490768896) }, { argument := 84895606756617719164566503424, coefficient := (-84895606756617719164566503424) }, { argument := 76094626789823218772705542144, coefficient := (-76094626789823218772705542144) }, { argument := 102903765765597235350989701120, coefficient := (-102903765765597235350989701120) }, { argument := 4197390445701992494579843072, coefficient := (-4197390445701992494579843072) }, { argument := 3664721753837033762286680932352, coefficient := (-3664721753837033762286680932352) }, { argument := 49227471111448616891737702400, coefficient := (-49227471111448616891737702400) }, { argument := 3664399230350294784035384197120, coefficient := (-3664399230350294784035384197120) }, { argument := 49711041554586619022304870400, coefficient := (-49711041554586619022304870400) }, { argument := 1641624459246134074393751453696, coefficient := (-1641624459246134074393751453696) }, { argument := 49227471111448616891737702400, coefficient := (-49227471111448616891737702400) }, { argument := 49227447637966783096333271040, coefficient := (-49227447637966783096333271040) }, { argument := 102903765765597235350989701120, coefficient := (-102903765765597235350989701120) }, { argument := 4197390445701992494579843072, coefficient := (-4197390445701992494579843072) }, { argument := 3664399230350294784035384197120, coefficient := (-3664399230350294784035384197120) }, { argument := 49227447637966783096333271040, coefficient := (-49227447637966783096333271040) }, { argument := 3664076706863555805784087461888, coefficient := (-3664076706863555805784087461888) }, { argument := 49711017850520484305531043840, coefficient := (-49711017850520484305531043840) }, { argument := 5684949903789651894001077321728, coefficient := (-5684949903789651894001077321728) }, { argument := 84760207064820880696999411712, coefficient := (-84760207064820880696999411712) }, { argument := 1641624223127809930911490768896, coefficient := (-1641624223127809930911490768896) }, { argument := 49711041554586619022304870400, coefficient := (-49711041554586619022304870400) }, { argument := 49711017850520484305531043840, coefficient := (-49711017850520484305531043840) }, { argument := 84895606756617719164566503424, coefficient := (-84895606756617719164566503424) }, { argument := 76094626789823218772705542144, coefficient := (-76094626789823218772705542144) }, { argument := 102903765765597235350989701120, coefficient := (-102903765765597235350989701120) }, { argument := 4197390445701992494579843072, coefficient := (-4197390445701992494579843072) }, { argument := 33909653556105136490036810743808, coefficient := 33909653556105136490036810743808 }, { argument := 18856302678394912347263460179968, coefficient := 18856302678394912347263460179968 }, { argument := 18856302678394912347263460179968, coefficient := (-18856302678394912347263460179968) }, { argument := 14856118993706727564472215404544, coefficient := 14856118993706727564472215404544 }, { argument := 196909837498830799976141946880, coefficient := 196909837498830799976141946880 }, { argument := 14854828805404675714442671947776, coefficient := 14854828805404675714442671947776 }, { argument := 198844118810214206655671828480, coefficient := 198844118810214206655671828480 }, { argument := 30106701755420448285546701127680, coefficient := (-30106701755420448285546701127680) }, { argument := 3283248918492268148787502907392, coefficient := 3283248918492268148787502907392 }, { argument := 205807531531194470701979402240, coefficient := 205807531531194470701979402240 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 11369899807579303788002154643456, coefficient := 11369899807579303788002154643456 }, { argument := 169520414129641761393998823424, coefficient := 169520414129641761393998823424 }, { argument := 3283248446255619861822981537792, coefficient := 3283248446255619861822981537792 }, { argument := 169791213513235438329133006848, coefficient := 169791213513235438329133006848 }, { argument := 152189253579646437545411084288, coefficient := 152189253579646437545411084288 }, { argument := 205807531531194470701979402240, coefficient := 205807531531194470701979402240 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 18856302678394912347263460179968, coefficient := (-18856302678394912347263460179968) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk11
