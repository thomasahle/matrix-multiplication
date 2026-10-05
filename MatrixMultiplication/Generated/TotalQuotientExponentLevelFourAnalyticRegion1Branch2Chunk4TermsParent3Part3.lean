import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 4, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-27390556843332060030801252771168256)
def positiveArguments : Array ℕ := #[
    1271, 32893034027, 12833, 9625222921, 25707, 11521,
    3895, 1271, 200417001, 56917, 6037834957, 1408393,
    44807, 48302702041, 23009, 23009, 778673, 42385,
    1408393, 778673, 1603322999, 44807, 42385, 56917,
    65160833, 2769606839, 326043, 14804184525, 334567, 10655,
    326043, 185397, 334567, 5223081, 6393, 1384803901,
    326043, 10655, 6393, 10655, 164087, 185397,
    65160833, 4100993, 41063551, 1785, 1581, 74001,
    20145, 20531781, 74001, 1785, 1785, 765,
    1785, 20145, 765, 2050491, 1581
  ]
def positiveCoefficients : Array ℕ := #[
    49169430935366197793649590272, 155332961408995552619520214433792, 992905282759330316736278822912, 45453830112279062966004682326016, 994491393434664710213493325824, 891394199537929134194550636544,
    1205444113254139042683022213120, 49169430935366197793649590272, 7571540224957217341303651565568, 1100934894000093579788022710272, 228102955440283884363531551768576, 27242282589832102836031285362688,
    866693427191563030896954048512, 228103061150457603400539660353536, 890117573872416085786060914688, 890117573872416085786060914688, 15061726315788514293695714951168, 819845133829856921118740316160,
    27242282589832102836031285362688, 15061726315788514293695714951168, 7571478791691641690089066594304, 866693427191563030896954048512, 819845133829856921118740316160, 1100934894000093579788022710272,
    307713333755066312538894368768, 13079098507220145729356058066944, 6306588816073800640139611865088, 69910784807077479264838641254400, 6471466955056122225502738972672, 206097673727901981703908884480,
    6306588816073800640139611865088, 3586099522865494481648014589952, 6471466955056122225502738972672, 101029079661417551431256135172096, 3957075335575718048715050582016, 13079103054859068732824398856192,
    6306588816073800640139611865088, 206097673727901981703908884480, 3957075335575718048715050582016, 206097673727901981703908884480, 6347808350819381036480393641984, 3586099522865494481648014589952,
    307713333755066312538894368768, 77465567558732139735403200512, 775668547640033210338046377984, 69053842816387618459216773120, 61161975065943319206734856192, 2862775026473669553837815365632,
    779321940356374551182589296640, 775668755424158456602435780608, 2862775026473669553837815365632, 69053842816387618459216773120, 69053842816387618459216773120, 59189008128332244393614376960,
    69053842816387618459216773120, 779321940356374551182589296640, 59189008128332244393614376960, 77465359774606893471013797888, 61161975065943319206734856192
  ]
def positiveScales : Array ℕ := #[
    10, 34, 13, 33, 14, 13,
    11, 10, 27, 15, 32, 20,
    15, 35, 14, 14, 19, 15,
    20, 19, 30, 15, 15, 15,
    25, 31, 18, 33, 18, 13,
    18, 17, 18, 22, 12, 30,
    18, 13, 12, 13, 17, 17,
    25, 21, 25, 10, 10, 16,
    14, 24, 16, 10, 10, 9,
    10, 14, 9, 20, 10
  ]
def negativeArguments : Array ℕ := #[
    397, 3555, 397, 15
  ]
def negativeCoefficients : Array ℕ := #[
    251628644145303536197095586267136, 563312235476419440290097486888960, 251628644145303536197095586267136, 9507379501711720511225274040320
  ]
def negativeScales : Array ℕ := #[
    8, 11, 8, 3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10311748315004958, 34937063035698153, 13647570851549456, 33164172808010716, 14649873637418802, 13491978324838996,
    11927407612511617, 10311748315004958, 27578429653949492, 15796572001334644, 32491384175598981, 20425618531167545,
    15451436515323275, 35491384844189652, 14489910663137901, 14489910663137901, 19570658077022122, 15371266166639294,
    20425618531167545, 19570658077022122, 30578417948295884, 15451436515323275, 15371266166639294, 15796572001334644,
    25957501710520193, 31367034046259834, 18314702720475354, 33785285972007906, 18351935626674330, 13379242972670065,
    18314702720475354, 17500258373631414, 18351935626674330, 22316469646649542, 12642277378502772, 30367034547888825,
    18314702720475354, 13379242972670065, 12642277378502772, 13379242972670065, 17324101418477604, 17500258373631414,
    25957501710520193, 21967541849587614, 25291355055140170, 10801708358875019, 10626621652357647, 16175257146038239,
    14298134185035960, 24291355441605611, 16175257146038239, 10801708358875019, 10801708358875019, 9579315937579817,
    10801708358875019, 14298134185035960, 9579315937579817, 20967537979874472, 10626621652357647
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    8632995197156697, 11795633845097634, 8632995197156697, 3906890600547867
  ]

abbrev PositiveTerm := Fin 59
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 94136339131 / 250000000000
noncomputable def negativeCeiling : ℝ := 132725304607 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 49169430935366197793649590272, coefficient := 49169430935366197793649590272 }, { argument := 155332961408995552619520214433792, coefficient := 155332961408995552619520214433792 }, { argument := 992905282759330316736278822912, coefficient := 992905282759330316736278822912 }, { argument := 45453830112279062966004682326016, coefficient := 45453830112279062966004682326016 }, { argument := 994491393434664710213493325824, coefficient := 994491393434664710213493325824 }, { argument := 891394199537929134194550636544, coefficient := 891394199537929134194550636544 }, { argument := 1205444113254139042683022213120, coefficient := 1205444113254139042683022213120 }, { argument := 49169430935366197793649590272, coefficient := 49169430935366197793649590272 }, { argument := 251628644145303536197095586267136, coefficient := (-251628644145303536197095586267136) }, { argument := 7571540224957217341303651565568, coefficient := 7571540224957217341303651565568 }, { argument := 1100934894000093579788022710272, coefficient := 1100934894000093579788022710272 }, { argument := 228102955440283884363531551768576, coefficient := 228102955440283884363531551768576 }, { argument := 27242282589832102836031285362688, coefficient := 27242282589832102836031285362688 }, { argument := 866693427191563030896954048512, coefficient := 866693427191563030896954048512 }, { argument := 228103061150457603400539660353536, coefficient := 228103061150457603400539660353536 }, { argument := 890117573872416085786060914688, coefficient := 890117573872416085786060914688 }, { argument := 890117573872416085786060914688, coefficient := 890117573872416085786060914688 }, { argument := 15061726315788514293695714951168, coefficient := 15061726315788514293695714951168 }, { argument := 819845133829856921118740316160, coefficient := 819845133829856921118740316160 }, { argument := 27242282589832102836031285362688, coefficient := 27242282589832102836031285362688 }, { argument := 15061726315788514293695714951168, coefficient := 15061726315788514293695714951168 }, { argument := 7571478791691641690089066594304, coefficient := 7571478791691641690089066594304 }, { argument := 866693427191563030896954048512, coefficient := 866693427191563030896954048512 }, { argument := 819845133829856921118740316160, coefficient := 819845133829856921118740316160 }, { argument := 1100934894000093579788022710272, coefficient := 1100934894000093579788022710272 }, { argument := 563312235476419440290097486888960, coefficient := (-563312235476419440290097486888960) }, { argument := 307713333755066312538894368768, coefficient := 307713333755066312538894368768 }, { argument := 13079098507220145729356058066944, coefficient := 13079098507220145729356058066944 }, { argument := 6306588816073800640139611865088, coefficient := 6306588816073800640139611865088 }, { argument := 69910784807077479264838641254400, coefficient := 69910784807077479264838641254400 }, { argument := 6471466955056122225502738972672, coefficient := 6471466955056122225502738972672 }, { argument := 206097673727901981703908884480, coefficient := 206097673727901981703908884480 }, { argument := 6306588816073800640139611865088, coefficient := 6306588816073800640139611865088 }, { argument := 3586099522865494481648014589952, coefficient := 3586099522865494481648014589952 }, { argument := 6471466955056122225502738972672, coefficient := 6471466955056122225502738972672 }, { argument := 101029079661417551431256135172096, coefficient := 101029079661417551431256135172096 }, { argument := 3957075335575718048715050582016, coefficient := 3957075335575718048715050582016 }, { argument := 13079103054859068732824398856192, coefficient := 13079103054859068732824398856192 }, { argument := 6306588816073800640139611865088, coefficient := 6306588816073800640139611865088 }, { argument := 206097673727901981703908884480, coefficient := 206097673727901981703908884480 }, { argument := 3957075335575718048715050582016, coefficient := 3957075335575718048715050582016 }, { argument := 206097673727901981703908884480, coefficient := 206097673727901981703908884480 }, { argument := 6347808350819381036480393641984, coefficient := 6347808350819381036480393641984 }, { argument := 3586099522865494481648014589952, coefficient := 3586099522865494481648014589952 }, { argument := 307713333755066312538894368768, coefficient := 307713333755066312538894368768 }, { argument := 251628644145303536197095586267136, coefficient := (-251628644145303536197095586267136) }, { argument := 77465567558732139735403200512, coefficient := 77465567558732139735403200512 }, { argument := 775668547640033210338046377984, coefficient := 775668547640033210338046377984 }, { argument := 69053842816387618459216773120, coefficient := 69053842816387618459216773120 }, { argument := 61161975065943319206734856192, coefficient := 61161975065943319206734856192 }, { argument := 2862775026473669553837815365632, coefficient := 2862775026473669553837815365632 }, { argument := 779321940356374551182589296640, coefficient := 779321940356374551182589296640 }, { argument := 775668755424158456602435780608, coefficient := 775668755424158456602435780608 }, { argument := 2862775026473669553837815365632, coefficient := 2862775026473669553837815365632 }, { argument := 69053842816387618459216773120, coefficient := 69053842816387618459216773120 }, { argument := 69053842816387618459216773120, coefficient := 69053842816387618459216773120 }, { argument := 59189008128332244393614376960, coefficient := 59189008128332244393614376960 }, { argument := 69053842816387618459216773120, coefficient := 69053842816387618459216773120 }, { argument := 779321940356374551182589296640, coefficient := 779321940356374551182589296640 }, { argument := 59189008128332244393614376960, coefficient := 59189008128332244393614376960 }, { argument := 77465359774606893471013797888, coefficient := 77465359774606893471013797888 }, { argument := 61161975065943319206734856192, coefficient := 61161975065943319206734856192 }, { argument := 9507379501711720511225274040320, coefficient := (-9507379501711720511225274040320) }] }

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

end TermShard6


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
