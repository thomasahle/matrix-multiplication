import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 6, for level-four region 1, branch 2,
parent chunk 12, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard12

/-! Directed signed-log shard 12.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-12688608971671183926448446681120768)
def positiveArguments : Array ℕ := #[
    29295, 22785, 3255, 30597, 361305, 25389,
    22785, 361305, 3255, 25389, 25389, 25389,
    25389, 25389, 29295, 30597, 825, 3465,
    15015, 495, 495, 1155, 15015, 15015,
    495, 185295, 7425, 3465, 15015, 1155,
    7425, 1155, 15015, 15015, 495, 137,
    2603, 3973, 40963, 1233, 3973, 1233,
    1233, 105627, 1233, 40963, 105627, 137,
    1233, 1233, 2603, 1, 295698469, 295698395,
    15070504713, 26469882159, 15070504601
  ]
def positiveCoefficients : Array ℕ := #[
    566647710169768986768278814720, 440725996798709211930883522560, 503686853484239099349581168640, 591832052843980941735757873152, 6988655092093817503475438714880, 15715029828708259899706932461568,
    440725996798709211930883522560, 6988655092093817503475438714880, 503686853484239099349581168640, 491094682147133121865841639424, 491094682147133121865841639424, 491094682147133121865841639424,
    15715029828708259899706932461568, 491094682147133121865841639424, 566647710169768986768278814720, 591832052843980941735757873152, 127662566551304840848972185600, 2144731118061921326262732718080,
    4646917422467496206902587555840, 153195079861565809018766622720, 2451121277785052944300265963520, 178727593171826777188561059840, 4646917422467496206902587555840, 4646917422467496206902587555840,
    2451121277785052944300265963520, 57346024894846134509358305771520, 4595852395846974270562998681600, 2144731118061921326262732718080, 4646917422467496206902587555840, 178727593171826777188561059840,
    4595852395846974270562998681600, 178727593171826777188561059840, 4646917422467496206902587555840, 4646917422467496206902587555840, 153195079861565809018766622720, 84798892691048548830590009344,
    100698685070620151736325636096, 76848996501262747377722195968, 792339653581984878135825399808, 95398754277429617434413760512, 76848996501262747377722195968, 95398754277429617434413760512,
    95398754277429617434413760512, 4086246641549901946774056075264, 95398754277429617434413760512, 792339653581984878135825399808, 4086246641549901946774056075264, 84798892691048548830590009344,
    95398754277429617434413760512, 95398754277429617434413760512, 100698685070620151736325636096, 316912650057057350374175801344, 5585586156165875265052340125696, 5585584758345396335637356871680,
    71168446336600221957643460149248, 250000968626341601929342985699328, 71168445807695175876243196215296
  ]
def positiveScales : Array ℕ := #[
    14, 14, 11, 14, 18, 14,
    14, 18, 11, 14, 14, 14,
    14, 14, 14, 14, 9, 11,
    13, 8, 8, 10, 13, 13,
    8, 17, 12, 11, 13, 10,
    12, 10, 13, 13, 8, 7,
    11, 11, 15, 10, 11, 10,
    10, 16, 10, 15, 16, 7,
    10, 10, 11, 0, 28, 28,
    33, 34, 33
  ]
def negativeArguments : Array ℕ := #[
    53, 651, 165, 137, 1, 141,
    619
  ]
def negativeCoefficients : Array ℕ := #[
    4199092613256009892457829367808, 51577533796786083773397111668736, 104581174518828925623478014443520, 10854258264454214250315521196032, 316912650057057350374175801344, 11171170914511271600689696997376,
    392337860770636999763229642063872
  ]
def negativeScales : Array ℕ := #[
    5, 9, 7, 7, 0, 7,
    9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14838366829409580, 14475796750110594, 11668441828050895, 14901102584567926, 18462857694403098, 14631915952027052,
    14475796750110594, 18462857694403098, 11668441828050895, 14631915952027052, 14631915952027052, 14631915952027052,
    14631915952027052, 14631915952027052, 14838366829409580, 14901102584567926, 9688250309129776, 11758639637007751,
    13874116854275931, 8951284714309401, 8951284714309401, 10173677136303419, 13874116854275931, 13874116854275931,
    8951284714309401, 17499464426646399, 12858175310450317, 11758639637007751, 13874116854275931, 10173677136303419,
    12858175310450317, 10173677136303419, 13874116854275931, 13874116854275931, 8951284714309401, 7098032082960526,
    11345959596404111, 11956013077376204, 15322033757158631, 10267957084402838, 11956013077376204, 10267957084402838,
    10267957084402838, 16688619132872129, 10267957084402838, 15322033757158631, 16688619132872129, 7098032082960526,
    10267957084402838, 10267957084402838, 11345959596404111, 0, 28139551532919578, 28139551171877985,
    33811008682597390, 34623632721001138, 33811008671875663
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    5727920454700926, 9346513733165637, 7366322214245818, 7098032082960527, 0, 7139551352398794,
    9273795599214265
  ]

abbrev PositiveTerm := Fin 57
abbrev NegativeTerm := Fin 7
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
noncomputable def positiveFloor : ℝ := 197078868303 / 1000000000000
noncomputable def negativeCeiling : ℝ := 3052456307 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4199092613256009892457829367808, coefficient := (-4199092613256009892457829367808) }, { argument := 566647710169768986768278814720, coefficient := 566647710169768986768278814720 }, { argument := 440725996798709211930883522560, coefficient := 440725996798709211930883522560 }, { argument := 503686853484239099349581168640, coefficient := 503686853484239099349581168640 }, { argument := 591832052843980941735757873152, coefficient := 591832052843980941735757873152 }, { argument := 6988655092093817503475438714880, coefficient := 6988655092093817503475438714880 }, { argument := 15715029828708259899706932461568, coefficient := 15715029828708259899706932461568 }, { argument := 440725996798709211930883522560, coefficient := 440725996798709211930883522560 }, { argument := 6988655092093817503475438714880, coefficient := 6988655092093817503475438714880 }, { argument := 503686853484239099349581168640, coefficient := 503686853484239099349581168640 }, { argument := 491094682147133121865841639424, coefficient := 491094682147133121865841639424 }, { argument := 491094682147133121865841639424, coefficient := 491094682147133121865841639424 }, { argument := 491094682147133121865841639424, coefficient := 491094682147133121865841639424 }, { argument := 15715029828708259899706932461568, coefficient := 15715029828708259899706932461568 }, { argument := 491094682147133121865841639424, coefficient := 491094682147133121865841639424 }, { argument := 566647710169768986768278814720, coefficient := 566647710169768986768278814720 }, { argument := 591832052843980941735757873152, coefficient := 591832052843980941735757873152 }, { argument := 51577533796786083773397111668736, coefficient := (-51577533796786083773397111668736) }, { argument := 127662566551304840848972185600, coefficient := 127662566551304840848972185600 }, { argument := 2144731118061921326262732718080, coefficient := 2144731118061921326262732718080 }, { argument := 4646917422467496206902587555840, coefficient := 4646917422467496206902587555840 }, { argument := 153195079861565809018766622720, coefficient := 153195079861565809018766622720 }, { argument := 2451121277785052944300265963520, coefficient := 2451121277785052944300265963520 }, { argument := 178727593171826777188561059840, coefficient := 178727593171826777188561059840 }, { argument := 4646917422467496206902587555840, coefficient := 4646917422467496206902587555840 }, { argument := 4646917422467496206902587555840, coefficient := 4646917422467496206902587555840 }, { argument := 2451121277785052944300265963520, coefficient := 2451121277785052944300265963520 }, { argument := 57346024894846134509358305771520, coefficient := 57346024894846134509358305771520 }, { argument := 4595852395846974270562998681600, coefficient := 4595852395846974270562998681600 }, { argument := 2144731118061921326262732718080, coefficient := 2144731118061921326262732718080 }, { argument := 4646917422467496206902587555840, coefficient := 4646917422467496206902587555840 }, { argument := 178727593171826777188561059840, coefficient := 178727593171826777188561059840 }, { argument := 4595852395846974270562998681600, coefficient := 4595852395846974270562998681600 }, { argument := 178727593171826777188561059840, coefficient := 178727593171826777188561059840 }, { argument := 4646917422467496206902587555840, coefficient := 4646917422467496206902587555840 }, { argument := 4646917422467496206902587555840, coefficient := 4646917422467496206902587555840 }, { argument := 153195079861565809018766622720, coefficient := 153195079861565809018766622720 }, { argument := 104581174518828925623478014443520, coefficient := (-104581174518828925623478014443520) }, { argument := 84798892691048548830590009344, coefficient := 84798892691048548830590009344 }, { argument := 100698685070620151736325636096, coefficient := 100698685070620151736325636096 }, { argument := 76848996501262747377722195968, coefficient := 76848996501262747377722195968 }, { argument := 792339653581984878135825399808, coefficient := 792339653581984878135825399808 }, { argument := 95398754277429617434413760512, coefficient := 95398754277429617434413760512 }, { argument := 76848996501262747377722195968, coefficient := 76848996501262747377722195968 }, { argument := 95398754277429617434413760512, coefficient := 95398754277429617434413760512 }, { argument := 95398754277429617434413760512, coefficient := 95398754277429617434413760512 }, { argument := 4086246641549901946774056075264, coefficient := 4086246641549901946774056075264 }, { argument := 95398754277429617434413760512, coefficient := 95398754277429617434413760512 }, { argument := 792339653581984878135825399808, coefficient := 792339653581984878135825399808 }, { argument := 4086246641549901946774056075264, coefficient := 4086246641549901946774056075264 }, { argument := 84798892691048548830590009344, coefficient := 84798892691048548830590009344 }, { argument := 95398754277429617434413760512, coefficient := 95398754277429617434413760512 }, { argument := 95398754277429617434413760512, coefficient := 95398754277429617434413760512 }, { argument := 100698685070620151736325636096, coefficient := 100698685070620151736325636096 }, { argument := 10854258264454214250315521196032, coefficient := (-10854258264454214250315521196032) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 5585586156165875265052340125696, coefficient := 5585586156165875265052340125696 }, { argument := 5585584758345396335637356871680, coefficient := 5585584758345396335637356871680 }, { argument := 11171170914511271600689696997376, coefficient := (-11171170914511271600689696997376) }, { argument := 71168446336600221957643460149248, coefficient := 71168446336600221957643460149248 }, { argument := 250000968626341601929342985699328, coefficient := 250000968626341601929342985699328 }, { argument := 71168445807695175876243196215296, coefficient := 71168445807695175876243196215296 }, { argument := 392337860770636999763229642063872, coefficient := (-392337860770636999763229642063872) }] }

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

end TermShard12


end Parent3

namespace Parent3

namespace TermShard13

/-! Directed signed-log shard 13.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-138021626150640222582901422468104192)
def positiveArguments : Array ℕ := #[
    491669073, 36384764601, 145533165207, 3939247101, 331617957, 46664852843,
    20961, 481939892377, 21509, 685, 20961, 11919,
    21509, 335787, 411, 23332429153, 20961, 685,
    411, 685, 10549, 11919, 331608213, 429889929,
    34742560375, 245, 217, 10157, 2765, 17371281111,
    10157, 245, 245, 105, 245, 2765,
    105, 214944041, 217, 53836183, 3507, 269315689,
    5649, 175, 5649, 3773, 53864855, 3507,
    21, 535, 489, 535, 489
  ]
def positiveCoefficients : Array ℕ := #[
    37149464815980621472908787580928, 1374577542710914720549722409402368, 1374521883038935224660593574150144, 37205136955007632137900986990592, 1566021525254507243080695939072, 220368536993827474248743128137728,
    405444705679075874096258482176, 2275896794518948828408823406395392, 416044567265456942700082233344, 13249826982976335754779688960, 405444705679075874096258482176, 230546989503788242133166587904,
    416044567265456942700082233344, 6495065187054999786993003528192, 254396678073145646491770028032, 220368562792115570165614930558976, 405444705679075874096258482176, 13249826982976335754779688960,
    254396678073145646491770028032, 13249826982976335754779688960, 408094671075671141247214419968, 230546989503788242133166587904, 1565975510515498161257733685248, 2030097792032811497170963267584,
    164067102643975052091663056896000, 75823827406229541837571358720, 67158247131231879913277489152, 3143439244755401863037601185792, 855726052156019115024019619840, 164067111366185945951897766592512,
    3143439244755401863037601185792, 75823827406229541837571358720, 75823827406229541837571358720, 64991852062482464432204021760, 75823827406229541837571358720, 855726052156019115024019619840,
    64991852062482464432204021760, 2030089069821917636936253571072, 67158247131231879913277489152, 508468372329673169739223924736, 135670491180432144502225895424, 5087229532178180791648361906176,
    218535102560097286653286023168, 6769984589841923378354585600, 218535102560097286653286023168, 145960867756991868037324865536, 508739171713266846674358108160, 135670491180432144502225895424,
    6499185206248246443220402176, 41393620063604902941939466240, 37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096
  ]
def positiveScales : Array ℕ := #[
    28, 35, 37, 31, 28, 35,
    14, 38, 14, 9, 14, 13,
    14, 18, 8, 34, 14, 9,
    8, 9, 13, 13, 28, 28,
    35, 7, 7, 13, 11, 34,
    13, 7, 7, 6, 7, 11,
    6, 27, 7, 25, 11, 28,
    12, 7, 12, 11, 25, 11,
    4, 9, 8, 9, 8
  ]
def negativeArguments : Array ℕ := #[
    35637, 17227, 4301, 11, 1
  ]
def negativeCoefficients : Array ℕ := #[
    2823454027520838198821125758124032, 2729727111266463487447963264876544, 340760326973850915989832530395136, 6972078301255261708231867629568, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    15, 14, 12, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    28873112368448692, 35082615425786798, 37082557006704533, 31875272770945249, 28304946889495357, 35441617294954399,
    14355419925653178, 38810062268223022, 14392652831852153, 9419960177847887, 14355419925653178, 13540975578809191,
    14392652831852153, 18357186851827365, 8682994583678684, 34441617463849018, 14355419925653178, 9419960177847887,
    8682994583678684, 9419960177847887, 13364818623655427, 13540975578809191, 28304904497861507, 28679392071901792,
    35015985027164934, 7936637938489789, 7761551232426566, 13310186726124348, 11433063765122067, 34015985103862151,
    13310186726124348, 7936637938489789, 7936637938489789, 6714245517659862, 7936637938489789, 11433063765122067,
    6714245517659862, 27679385873423333, 7761551232426566, 25682072790312441, 11776021715228447, 28004723035664062,
    12463779785335379, 7451211111832325, 12463779785335379, 11881496384617007, 25682840934314667, 11776021715228447,
    4392317422778759, 9063395081288509, 8933690654464738, 9063395081288509, 8933690654464738
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    15121088272321424, 14072383864515764, 12070456415944650, 3459431618637364, 0
  ]

abbrev PositiveTerm := Fin 53
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 2614004648401 / 1000000000000
noncomputable def negativeCeiling : ℝ := 513047981003 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 37149464815980621472908787580928, coefficient := 37149464815980621472908787580928 }, { argument := 1374577542710914720549722409402368, coefficient := 1374577542710914720549722409402368 }, { argument := 1374521883038935224660593574150144, coefficient := 1374521883038935224660593574150144 }, { argument := 37205136955007632137900986990592, coefficient := 37205136955007632137900986990592 }, { argument := 2823454027520838198821125758124032, coefficient := (-2823454027520838198821125758124032) }, { argument := 1566021525254507243080695939072, coefficient := 1566021525254507243080695939072 }, { argument := 220368536993827474248743128137728, coefficient := 220368536993827474248743128137728 }, { argument := 405444705679075874096258482176, coefficient := 405444705679075874096258482176 }, { argument := 2275896794518948828408823406395392, coefficient := 2275896794518948828408823406395392 }, { argument := 416044567265456942700082233344, coefficient := 416044567265456942700082233344 }, { argument := 13249826982976335754779688960, coefficient := 13249826982976335754779688960 }, { argument := 405444705679075874096258482176, coefficient := 405444705679075874096258482176 }, { argument := 230546989503788242133166587904, coefficient := 230546989503788242133166587904 }, { argument := 416044567265456942700082233344, coefficient := 416044567265456942700082233344 }, { argument := 6495065187054999786993003528192, coefficient := 6495065187054999786993003528192 }, { argument := 254396678073145646491770028032, coefficient := 254396678073145646491770028032 }, { argument := 220368562792115570165614930558976, coefficient := 220368562792115570165614930558976 }, { argument := 405444705679075874096258482176, coefficient := 405444705679075874096258482176 }, { argument := 13249826982976335754779688960, coefficient := 13249826982976335754779688960 }, { argument := 254396678073145646491770028032, coefficient := 254396678073145646491770028032 }, { argument := 13249826982976335754779688960, coefficient := 13249826982976335754779688960 }, { argument := 408094671075671141247214419968, coefficient := 408094671075671141247214419968 }, { argument := 230546989503788242133166587904, coefficient := 230546989503788242133166587904 }, { argument := 1565975510515498161257733685248, coefficient := 1565975510515498161257733685248 }, { argument := 2729727111266463487447963264876544, coefficient := (-2729727111266463487447963264876544) }, { argument := 2030097792032811497170963267584, coefficient := 2030097792032811497170963267584 }, { argument := 164067102643975052091663056896000, coefficient := 164067102643975052091663056896000 }, { argument := 75823827406229541837571358720, coefficient := 75823827406229541837571358720 }, { argument := 67158247131231879913277489152, coefficient := 67158247131231879913277489152 }, { argument := 3143439244755401863037601185792, coefficient := 3143439244755401863037601185792 }, { argument := 855726052156019115024019619840, coefficient := 855726052156019115024019619840 }, { argument := 164067111366185945951897766592512, coefficient := 164067111366185945951897766592512 }, { argument := 3143439244755401863037601185792, coefficient := 3143439244755401863037601185792 }, { argument := 75823827406229541837571358720, coefficient := 75823827406229541837571358720 }, { argument := 75823827406229541837571358720, coefficient := 75823827406229541837571358720 }, { argument := 64991852062482464432204021760, coefficient := 64991852062482464432204021760 }, { argument := 75823827406229541837571358720, coefficient := 75823827406229541837571358720 }, { argument := 855726052156019115024019619840, coefficient := 855726052156019115024019619840 }, { argument := 64991852062482464432204021760, coefficient := 64991852062482464432204021760 }, { argument := 2030089069821917636936253571072, coefficient := 2030089069821917636936253571072 }, { argument := 67158247131231879913277489152, coefficient := 67158247131231879913277489152 }, { argument := 340760326973850915989832530395136, coefficient := (-340760326973850915989832530395136) }, { argument := 508468372329673169739223924736, coefficient := 508468372329673169739223924736 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 5087229532178180791648361906176, coefficient := 5087229532178180791648361906176 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 6769984589841923378354585600, coefficient := 6769984589841923378354585600 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 145960867756991868037324865536, coefficient := 145960867756991868037324865536 }, { argument := 508739171713266846674358108160, coefficient := 508739171713266846674358108160 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 6499185206248246443220402176, coefficient := 6499185206248246443220402176 }, { argument := 6972078301255261708231867629568, coefficient := (-6972078301255261708231867629568) }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end TermShard13


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
