import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
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

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-40594857617600243537005877657600)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    166549205605, 4551519099587, 424937969, 90147285901205, 189205957, 58933003,
    52729529, 424937969, 189205957, 7459677485, 189205957, 4551515842663,
    52729529, 58933003, 189205957, 58933003, 424937969, 424937969,
    339401188685, 64452131835, 1158592444865, 18537006770645, 516071643715, 166549205605,
    2201745370663, 665406605381, 2201745370663, 14920740268673, 1448601969, 294372388919829,
    644997957, 200901003, 179753529, 1448601969, 644997957, 25429837485,
    644997957, 29841459993807, 179753529, 200901003, 644997957, 200901003,
    1448601969, 1448601969, 2244733442573, 1158592444865, 83262192196865, 666080142187435,
    18554221174845, 4551519099587, 14920740268673, 1136150539951, 424937969, 1448601969,
    212469327, 665406605381, 1136150539951, 212469327, 44998346130219, 94603131,
    29466549, 26364807, 212469327, 94603131
  ]
def negativeCoefficients : Array ℕ := #[
    187517735075382530953707520, 5124554930217427168592396288, 489920122584057697475231744, 50748410399141050710973480960, 436279233250036781693272064, 67945126489759826657148928,
    486344063295122969756434432, 489920122584057697475231744, 436279233250036781693272064, 8600422589888020163707535360, 436279233250036781693272064, 5124551263246998975086067712,
    486344063295122969756434432, 67945126489759826657148928, 436279233250036781693272064, 67945126489759826657148928, 489920122584057697475231744, 489920122584057697475231744,
    191065883361358675412254720, 145133298457670041290670080, 5217836502968285931807703040, 5217703549052573963119493120, 145261253895709585875927040, 187517735075382530953707520,
    619736226930162587221884928, 187295308752733642409639936, 619736226930162587221884928, 16799260078521919292888317952, 1670124361675921100315295744, 165716922630938076238627995648,
    1487264030105564775463256064, 231623086655784678145916928, 1657933672904564011991826432, 1670124361675921100315295744, 1487264030105564775463256064, 29318606495113797417943695360,
    1487264030105564775463256064, 16799248513537596133981814784, 1657933672904564011991826432, 231623086655784678145916928, 1487264030105564775463256064, 231623086655784678145916928,
    1670124361675921100315295744, 1670124361675921100315295744, 631836293469865842613157888, 5217836502968285931807703040, 187489788875925916864762347520, 187484892509638703652913807360,
    5222548973073856781950648320, 5124554930217427168592396288, 16799260078521919292888317952, 5116767148360111428726685696, 489920122584057697475231744, 1670124361675921100315295744,
    489920912335288353165410304, 187295308752733642409639936, 5116767148360111428726685696, 489920912335288353165410304, 50663633716085722269043654656, 436279936532154591869927424,
    67945236017302764307611648, 486344847281746102412378112, 489920912335288353165410304, 436279936532154591869927424
  ]
def negativeScales : Array ℕ := #[
    37, 42, 28, 46, 27, 25,
    25, 28, 27, 32, 27, 42,
    25, 25, 27, 25, 28, 28,
    38, 35, 40, 44, 38, 37,
    41, 39, 41, 43, 30, 48,
    29, 27, 27, 30, 29, 34,
    29, 44, 27, 27, 29, 27,
    30, 30, 41, 40, 46, 49,
    44, 42, 43, 40, 28, 30,
    27, 39, 40, 27, 45, 26,
    24, 24, 27, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    37277157516521613, 42049485273337709, 28662677016031219, 46357349290076125, 27495382270604491, 25812572447317943,
    25652107774314190, 28662677016031219, 27495382270604491, 32796466112299799, 27495382270604491, 42049484240990116,
    25652107774314190, 25812572447317943, 27495382270604491, 25812572447317943, 28662677016031219, 28662677016031219,
    38304200661402175, 35907509032189431, 40075510301044712, 44075473539755135, 38908780410752944, 37277157516521613,
    41001784771164217, 39275445231447219, 41001784771164217, 43762384348206448, 30432014095372554, 48064635686514539,
    29264719349974890, 27581909525858989, 27421444853662358, 30432014095372554, 29264719349974890, 34565803191071539,
    29264719349974890, 44762383355022742, 27421444853662358, 27581909525858989, 29264719349974890, 27581909525858989,
    30432014095372554, 30432014095372554, 41029681276750604, 40075510301044712, 46242726776999558, 49242689099984485,
    44076812677806366, 42049485273337709, 43762384348206448, 40047291143254797, 28662677016031219, 30432014095372554,
    27662679341653732, 39275445231447219, 40047291143254797, 27662679341653732, 45354937211120716, 26495384596227002,
    24812574772940493, 24652110099936702, 27662679341653732, 26495384596227002
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 44366319 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 187517735075382530953707520, coefficient := (-187517735075382530953707520) }, { argument := 5124554930217427168592396288, coefficient := (-5124554930217427168592396288) }, { argument := 489920122584057697475231744, coefficient := (-489920122584057697475231744) }, { argument := 50748410399141050710973480960, coefficient := (-50748410399141050710973480960) }, { argument := 436279233250036781693272064, coefficient := (-436279233250036781693272064) }, { argument := 67945126489759826657148928, coefficient := (-67945126489759826657148928) }, { argument := 486344063295122969756434432, coefficient := (-486344063295122969756434432) }, { argument := 489920122584057697475231744, coefficient := (-489920122584057697475231744) }, { argument := 436279233250036781693272064, coefficient := (-436279233250036781693272064) }, { argument := 8600422589888020163707535360, coefficient := (-8600422589888020163707535360) }, { argument := 436279233250036781693272064, coefficient := (-436279233250036781693272064) }, { argument := 5124551263246998975086067712, coefficient := (-5124551263246998975086067712) }, { argument := 486344063295122969756434432, coefficient := (-486344063295122969756434432) }, { argument := 67945126489759826657148928, coefficient := (-67945126489759826657148928) }, { argument := 436279233250036781693272064, coefficient := (-436279233250036781693272064) }, { argument := 67945126489759826657148928, coefficient := (-67945126489759826657148928) }, { argument := 489920122584057697475231744, coefficient := (-489920122584057697475231744) }, { argument := 489920122584057697475231744, coefficient := (-489920122584057697475231744) }, { argument := 191065883361358675412254720, coefficient := (-191065883361358675412254720) }, { argument := 145133298457670041290670080, coefficient := (-145133298457670041290670080) }, { argument := 5217836502968285931807703040, coefficient := (-5217836502968285931807703040) }, { argument := 5217703549052573963119493120, coefficient := (-5217703549052573963119493120) }, { argument := 145261253895709585875927040, coefficient := (-145261253895709585875927040) }, { argument := 187517735075382530953707520, coefficient := (-187517735075382530953707520) }, { argument := 619736226930162587221884928, coefficient := (-619736226930162587221884928) }, { argument := 187295308752733642409639936, coefficient := (-187295308752733642409639936) }, { argument := 619736226930162587221884928, coefficient := (-619736226930162587221884928) }, { argument := 16799260078521919292888317952, coefficient := (-16799260078521919292888317952) }, { argument := 1670124361675921100315295744, coefficient := (-1670124361675921100315295744) }, { argument := 165716922630938076238627995648, coefficient := (-165716922630938076238627995648) }, { argument := 1487264030105564775463256064, coefficient := (-1487264030105564775463256064) }, { argument := 231623086655784678145916928, coefficient := (-231623086655784678145916928) }, { argument := 1657933672904564011991826432, coefficient := (-1657933672904564011991826432) }, { argument := 1670124361675921100315295744, coefficient := (-1670124361675921100315295744) }, { argument := 1487264030105564775463256064, coefficient := (-1487264030105564775463256064) }, { argument := 29318606495113797417943695360, coefficient := (-29318606495113797417943695360) }, { argument := 1487264030105564775463256064, coefficient := (-1487264030105564775463256064) }, { argument := 16799248513537596133981814784, coefficient := (-16799248513537596133981814784) }, { argument := 1657933672904564011991826432, coefficient := (-1657933672904564011991826432) }, { argument := 231623086655784678145916928, coefficient := (-231623086655784678145916928) }, { argument := 1487264030105564775463256064, coefficient := (-1487264030105564775463256064) }, { argument := 231623086655784678145916928, coefficient := (-231623086655784678145916928) }, { argument := 1670124361675921100315295744, coefficient := (-1670124361675921100315295744) }, { argument := 1670124361675921100315295744, coefficient := (-1670124361675921100315295744) }, { argument := 631836293469865842613157888, coefficient := (-631836293469865842613157888) }, { argument := 5217836502968285931807703040, coefficient := (-5217836502968285931807703040) }, { argument := 187489788875925916864762347520, coefficient := (-187489788875925916864762347520) }, { argument := 187484892509638703652913807360, coefficient := (-187484892509638703652913807360) }, { argument := 5222548973073856781950648320, coefficient := (-5222548973073856781950648320) }, { argument := 5124554930217427168592396288, coefficient := (-5124554930217427168592396288) }, { argument := 16799260078521919292888317952, coefficient := (-16799260078521919292888317952) }, { argument := 5116767148360111428726685696, coefficient := (-5116767148360111428726685696) }, { argument := 489920122584057697475231744, coefficient := (-489920122584057697475231744) }, { argument := 1670124361675921100315295744, coefficient := (-1670124361675921100315295744) }, { argument := 489920912335288353165410304, coefficient := (-489920912335288353165410304) }, { argument := 187295308752733642409639936, coefficient := (-187295308752733642409639936) }, { argument := 5116767148360111428726685696, coefficient := (-5116767148360111428726685696) }, { argument := 489920912335288353165410304, coefficient := (-489920912335288353165410304) }, { argument := 50663633716085722269043654656, coefficient := (-50663633716085722269043654656) }, { argument := 436279936532154591869927424, coefficient := (-436279936532154591869927424) }, { argument := 67945236017302764307611648, coefficient := (-67945236017302764307611648) }, { argument := 486344847281746102412378112, coefficient := (-486344847281746102412378112) }, { argument := 489920912335288353165410304, coefficient := (-489920912335288353165410304) }, { argument := 436279936532154591869927424, coefficient := (-436279936532154591869927424) }] }

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

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-39676912658411654456714610081792)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3729844755, 94603131, 9089197822563, 26364807, 29466549, 94603131,
    29466549, 212469327, 212469327, 678012361561, 18537006770645, 666080142187435,
    20814460836275, 579804652065, 90147285901205, 294372388919829, 44998346130219, 189205957,
    644997957, 94603131, 58933003, 200901003, 29466549, 52729529,
    179753529, 26364807, 424937969, 1448601969, 212469327, 189205957,
    644997957, 94603131, 7459677485, 25429837485, 3729844755, 189205957,
    644997957, 94603131, 516071643715, 18554221174845, 579804652065, 16141443595,
    4551515842663, 29841459993807, 9089197822563, 52729529, 179753529, 26364807,
    58933003, 200901003, 29466549, 189205957, 644997957, 94603131,
    58933003, 200901003, 29466549, 424937969, 1448601969, 212469327,
    424937969, 1448601969, 212469327, 339401188685
  ]
def negativeCoefficients : Array ℕ := #[
    8600436453769113061042421760, 436279936532154591869927424, 5116763490848931302558662656, 486344847281746102412378112, 67945236017302764307611648, 436279936532154591869927424,
    67945236017302764307611648, 489920912335288353165410304, 489920912335288353165410304, 190843513679919350353494016, 5217703549052573963119493120, 187484892509638703652913807360,
    187479996132331745102843084800, 5222416029975228168252948480, 50748410399141050710973480960, 165716922630938076238627995648, 50663633716085722269043654656, 436279233250036781693272064,
    1487264030105564775463256064, 436279936532154591869927424, 67945126489759826657148928, 231623086655784678145916928, 67945236017302764307611648, 486344063295122969756434432,
    1657933672904564011991826432, 486344847281746102412378112, 489920122584057697475231744, 1670124361675921100315295744, 489920912335288353165410304, 436279233250036781693272064,
    1487264030105564775463256064, 436279936532154591869927424, 8600422589888020163707535360, 29318606495113797417943695360, 8600436453769113061042421760, 436279233250036781693272064,
    1487264030105564775463256064, 436279936532154591869927424, 145261253895709585875927040, 5222548973073856781950648320, 5222416029975228168252948480, 145389198719327758702346240,
    5124551263246998975086067712, 16799248513537596133981814784, 5116763490848931302558662656, 486344063295122969756434432, 1657933672904564011991826432, 486344847281746102412378112,
    67945126489759826657148928, 231623086655784678145916928, 67945236017302764307611648, 436279233250036781693272064, 1487264030105564775463256064, 436279936532154591869927424,
    67945126489759826657148928, 231623086655784678145916928, 67945236017302764307611648, 489920122584057697475231744, 1670124361675921100315295744, 489920912335288353165410304,
    489920122584057697475231744, 1670124361675921100315295744, 489920912335288353165410304, 191065883361358675412254720
  ]
def negativeScales : Array ℕ := #[
    31, 26, 43, 24, 24, 26,
    24, 27, 27, 39, 44, 49,
    44, 39, 46, 48, 45, 27,
    29, 26, 25, 27, 24, 25,
    27, 24, 28, 30, 27, 27,
    29, 26, 32, 34, 31, 27,
    29, 26, 38, 44, 39, 33,
    42, 44, 43, 25, 27, 24,
    25, 27, 24, 27, 29, 26,
    25, 27, 24, 28, 30, 27,
    28, 30, 27, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31796468437922339, 26495384596227002, 43047290112003037, 24652110099936702, 24812574772940493, 26495384596227002,
    24812574772940493, 27662679341653732, 27662679341653732, 39302520620662689, 44075473539755135, 49242689099984485,
    44242651421900624, 39076775952676302, 46357349290076125, 48064635686514539, 45354937211120716, 27495382270604491,
    29264719349974890, 26495384596227002, 25812572447317943, 27581909525858989, 24812574772940493, 25652107774314190,
    27421444853662358, 24652110099936702, 28662677016031219, 30432014095372554, 27662679341653732, 27495382270604491,
    29264719349974890, 26495384596227002, 32796466112299799, 34565803191071539, 31796468437922339, 27495382270604491,
    29264719349974890, 26495384596227002, 38908780410752944, 44076812677806366, 39076775952676302, 33910050564573132,
    42049484240990116, 44762383355022742, 43047290112003037, 25652107774314190, 27421444853662358, 24652110099936702,
    25812572447317943, 27581909525858989, 24812574772940493, 27495382270604491, 29264719349974890, 26495384596227002,
    25812572447317943, 27581909525858989, 24812574772940493, 28662677016031219, 30432014095372554, 27662679341653732,
    28662677016031219, 30432014095372554, 27662679341653732, 38304200661402175
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 421598373 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8600436453769113061042421760, coefficient := (-8600436453769113061042421760) }, { argument := 436279936532154591869927424, coefficient := (-436279936532154591869927424) }, { argument := 5116763490848931302558662656, coefficient := (-5116763490848931302558662656) }, { argument := 486344847281746102412378112, coefficient := (-486344847281746102412378112) }, { argument := 67945236017302764307611648, coefficient := (-67945236017302764307611648) }, { argument := 436279936532154591869927424, coefficient := (-436279936532154591869927424) }, { argument := 67945236017302764307611648, coefficient := (-67945236017302764307611648) }, { argument := 489920912335288353165410304, coefficient := (-489920912335288353165410304) }, { argument := 489920912335288353165410304, coefficient := (-489920912335288353165410304) }, { argument := 190843513679919350353494016, coefficient := (-190843513679919350353494016) }, { argument := 5217703549052573963119493120, coefficient := (-5217703549052573963119493120) }, { argument := 187484892509638703652913807360, coefficient := (-187484892509638703652913807360) }, { argument := 187479996132331745102843084800, coefficient := (-187479996132331745102843084800) }, { argument := 5222416029975228168252948480, coefficient := (-5222416029975228168252948480) }, { argument := 50748410399141050710973480960, coefficient := (-50748410399141050710973480960) }, { argument := 165716922630938076238627995648, coefficient := (-165716922630938076238627995648) }, { argument := 50663633716085722269043654656, coefficient := (-50663633716085722269043654656) }, { argument := 436279233250036781693272064, coefficient := (-436279233250036781693272064) }, { argument := 1487264030105564775463256064, coefficient := (-1487264030105564775463256064) }, { argument := 436279936532154591869927424, coefficient := (-436279936532154591869927424) }, { argument := 67945126489759826657148928, coefficient := (-67945126489759826657148928) }, { argument := 231623086655784678145916928, coefficient := (-231623086655784678145916928) }, { argument := 67945236017302764307611648, coefficient := (-67945236017302764307611648) }, { argument := 486344063295122969756434432, coefficient := (-486344063295122969756434432) }, { argument := 1657933672904564011991826432, coefficient := (-1657933672904564011991826432) }, { argument := 486344847281746102412378112, coefficient := (-486344847281746102412378112) }, { argument := 489920122584057697475231744, coefficient := (-489920122584057697475231744) }, { argument := 1670124361675921100315295744, coefficient := (-1670124361675921100315295744) }, { argument := 489920912335288353165410304, coefficient := (-489920912335288353165410304) }, { argument := 436279233250036781693272064, coefficient := (-436279233250036781693272064) }, { argument := 1487264030105564775463256064, coefficient := (-1487264030105564775463256064) }, { argument := 436279936532154591869927424, coefficient := (-436279936532154591869927424) }, { argument := 8600422589888020163707535360, coefficient := (-8600422589888020163707535360) }, { argument := 29318606495113797417943695360, coefficient := (-29318606495113797417943695360) }, { argument := 8600436453769113061042421760, coefficient := (-8600436453769113061042421760) }, { argument := 436279233250036781693272064, coefficient := (-436279233250036781693272064) }, { argument := 1487264030105564775463256064, coefficient := (-1487264030105564775463256064) }, { argument := 436279936532154591869927424, coefficient := (-436279936532154591869927424) }, { argument := 145261253895709585875927040, coefficient := (-145261253895709585875927040) }, { argument := 5222548973073856781950648320, coefficient := (-5222548973073856781950648320) }, { argument := 5222416029975228168252948480, coefficient := (-5222416029975228168252948480) }, { argument := 145389198719327758702346240, coefficient := (-145389198719327758702346240) }, { argument := 5124551263246998975086067712, coefficient := (-5124551263246998975086067712) }, { argument := 16799248513537596133981814784, coefficient := (-16799248513537596133981814784) }, { argument := 5116763490848931302558662656, coefficient := (-5116763490848931302558662656) }, { argument := 486344063295122969756434432, coefficient := (-486344063295122969756434432) }, { argument := 1657933672904564011991826432, coefficient := (-1657933672904564011991826432) }, { argument := 486344847281746102412378112, coefficient := (-486344847281746102412378112) }, { argument := 67945126489759826657148928, coefficient := (-67945126489759826657148928) }, { argument := 231623086655784678145916928, coefficient := (-231623086655784678145916928) }, { argument := 67945236017302764307611648, coefficient := (-67945236017302764307611648) }, { argument := 436279233250036781693272064, coefficient := (-436279233250036781693272064) }, { argument := 1487264030105564775463256064, coefficient := (-1487264030105564775463256064) }, { argument := 436279936532154591869927424, coefficient := (-436279936532154591869927424) }, { argument := 67945126489759826657148928, coefficient := (-67945126489759826657148928) }, { argument := 231623086655784678145916928, coefficient := (-231623086655784678145916928) }, { argument := 67945236017302764307611648, coefficient := (-67945236017302764307611648) }, { argument := 489920122584057697475231744, coefficient := (-489920122584057697475231744) }, { argument := 1670124361675921100315295744, coefficient := (-1670124361675921100315295744) }, { argument := 489920912335288353165410304, coefficient := (-489920912335288353165410304) }, { argument := 489920122584057697475231744, coefficient := (-489920122584057697475231744) }, { argument := 1670124361675921100315295744, coefficient := (-1670124361675921100315295744) }, { argument := 489920912335288353165410304, coefficient := (-489920912335288353165410304) }, { argument := 191065883361358675412254720, coefficient := (-191065883361358675412254720) }] }

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

end TermShard1


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk1
