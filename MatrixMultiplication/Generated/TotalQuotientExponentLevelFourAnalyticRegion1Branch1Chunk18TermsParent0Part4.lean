import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 18, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-97175518777444004932851625598386176)
def positiveArguments : Array ℕ := #[
    2483, 1065207, 47177, 2483, 47177, 91871,
    1735617, 91871, 1065207, 1735617, 22347, 91871,
    91871, 101803, 455, 2275, 1885, 33865,
    12675, 455, 50765, 50765, 36335, 1885,
    61, 67, 61, 67, 3, 1291845673,
    1291845591, 7845756449, 114134595115, 31381344593, 6045338635, 236226054763,
    236226022615, 6045359283, 40815955, 2810422495, 54795679657, 5620851699,
    40815955, 11077363, 1960245517, 980122867, 5538573
  ]
def positiveCoefficients : Array ℕ := #[
    1536902558772799611287262724096, 20604099928547844788819865894912, 1825071788542699538403624484864, 1536902558772799611287262724096, 1825071788542699538403624484864, 1777043583581049550550897524736,
    67143430536386683018112290258944, 1777043583581049550550897524736, 20604099928547844788819865894912, 67143430536386683018112290258944, 1729015378619399562698170564608, 1777043583581049550550897524736,
    1777043583581049550550897524736, 1969156403427649501961805365248, 35203919867178001567443845120, 704078397343560031348876902400, 36461202719577215909138268160, 655044366099990672022794403840,
    980680624871387186521649971200, 35203919867178001567443845120, 981937907723786400863344394240, 981937907723786400863344394240, 702821114491160817007182479360, 36461202719577215909138268160,
    37757171198204098384423288832, 41470991316060239209120661504, 37757171198204098384423288832, 41470991316060239209120661504, 475368975085586025561263702016, 24402274828861519169433351749632,
    24402273279925312788189721657344, 148202149150063867846789500502016, 538985386506973539788890612695040, 148194209893365767950647299145728, 28548304547520931879099259944960, 1115546003393320511640932133634048,
    1115545851578682820347577803735040, 28548402054944070171533632339968, 385495795716631419816362639360, 53087379972363532244961281966080, 517530562036557714437858649964544, 53087443337076999389860759339008,
    385495795716631419816362639360, 52311367749780341713323163648, 9256997727676279325528091000832, 9256998752429806108241102372864, 52310342996253559000311791616
  ]
def positiveScales : Array ℕ := #[
    11, 20, 15, 11, 15, 16,
    20, 16, 20, 20, 14, 16,
    16, 16, 8, 11, 10, 15,
    13, 8, 15, 15, 15, 10,
    5, 6, 5, 6, 1, 30,
    30, 32, 36, 34, 32, 37,
    37, 32, 25, 31, 35, 32,
    25, 23, 30, 29, 22
  ]
def negativeArguments : Array ℕ := #[
    2483, 65, 1, 3, 77, 659,
    28881, 3941, 235
  ]
def negativeCoefficients : Array ℕ := #[
    196723527522918350244769628684288, 5149830563427181943580356771840, 158456325028528675187087900672, 475368975085586025561263702016, 48804548108786831957623073406976, 835381745550403175586327412342784,
    2288188561574468334039142829654016, 624476376937431508912313416548352, 18618618190852119334482828328960
  ]
def negativeScales : Array ℕ := #[
    11, 6, 0, 1, 6, 9,
    14, 11, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11277868546176840, 20022702383676386, 15525796059620386, 11277868546176840, 15525796059620386, 16487321911805779,
    20727017191543902, 16487321911805779, 20022702383676386, 20727017191543902, 14447793547619150, 16487321911805779,
    16487321911805779, 16635420550794014, 8829722735013603, 11151650829973420, 10880348807966944, 15047507375306962,
    13629698126777281, 8829722735013603, 15631546551169610, 15631546551169610, 15149072285871644, 10880348807966944,
    5930737337099561, 6066089190457772, 5930737337099561, 6066089190457772, 1584962500720924, 30266786586482489,
    30266786494907311, 32869265405245979, 36731945194151170, 34869188117344916, 32493176009565148, 37781377140578596,
    37781376944242238, 32493180937116462, 25282629877679674, 31388139883230725, 35673343097839329, 32388141605220082,
    25282629877679674, 23401111148521937, 30868387214285169, 29868387373992105, 22401082886570938
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    11277868546176841, 6022367813028455, 0, 1584962500724866, 6266786540694902, 9364134655008054,
    14817833076649406, 11944346043609699, 7876516949414244
  ]

abbrev PositiveTerm := Fin 47
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
noncomputable def positiveFloor : ℝ := 1731471082571 / 1000000000000
noncomputable def negativeCeiling : ℝ := 124921768509 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1536902558772799611287262724096, coefficient := 1536902558772799611287262724096 }, { argument := 20604099928547844788819865894912, coefficient := 20604099928547844788819865894912 }, { argument := 1825071788542699538403624484864, coefficient := 1825071788542699538403624484864 }, { argument := 1536902558772799611287262724096, coefficient := 1536902558772799611287262724096 }, { argument := 1825071788542699538403624484864, coefficient := 1825071788542699538403624484864 }, { argument := 1777043583581049550550897524736, coefficient := 1777043583581049550550897524736 }, { argument := 67143430536386683018112290258944, coefficient := 67143430536386683018112290258944 }, { argument := 1777043583581049550550897524736, coefficient := 1777043583581049550550897524736 }, { argument := 20604099928547844788819865894912, coefficient := 20604099928547844788819865894912 }, { argument := 67143430536386683018112290258944, coefficient := 67143430536386683018112290258944 }, { argument := 1729015378619399562698170564608, coefficient := 1729015378619399562698170564608 }, { argument := 1777043583581049550550897524736, coefficient := 1777043583581049550550897524736 }, { argument := 1777043583581049550550897524736, coefficient := 1777043583581049550550897524736 }, { argument := 1969156403427649501961805365248, coefficient := 1969156403427649501961805365248 }, { argument := 196723527522918350244769628684288, coefficient := (-196723527522918350244769628684288) }, { argument := 35203919867178001567443845120, coefficient := 35203919867178001567443845120 }, { argument := 704078397343560031348876902400, coefficient := 704078397343560031348876902400 }, { argument := 36461202719577215909138268160, coefficient := 36461202719577215909138268160 }, { argument := 655044366099990672022794403840, coefficient := 655044366099990672022794403840 }, { argument := 980680624871387186521649971200, coefficient := 980680624871387186521649971200 }, { argument := 35203919867178001567443845120, coefficient := 35203919867178001567443845120 }, { argument := 981937907723786400863344394240, coefficient := 981937907723786400863344394240 }, { argument := 981937907723786400863344394240, coefficient := 981937907723786400863344394240 }, { argument := 702821114491160817007182479360, coefficient := 702821114491160817007182479360 }, { argument := 36461202719577215909138268160, coefficient := 36461202719577215909138268160 }, { argument := 5149830563427181943580356771840, coefficient := (-5149830563427181943580356771840) }, { argument := 37757171198204098384423288832, coefficient := 37757171198204098384423288832 }, { argument := 41470991316060239209120661504, coefficient := 41470991316060239209120661504 }, { argument := 37757171198204098384423288832, coefficient := 37757171198204098384423288832 }, { argument := 41470991316060239209120661504, coefficient := 41470991316060239209120661504 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 24402274828861519169433351749632, coefficient := 24402274828861519169433351749632 }, { argument := 24402273279925312788189721657344, coefficient := 24402273279925312788189721657344 }, { argument := 48804548108786831957623073406976, coefficient := (-48804548108786831957623073406976) }, { argument := 148202149150063867846789500502016, coefficient := 148202149150063867846789500502016 }, { argument := 538985386506973539788890612695040, coefficient := 538985386506973539788890612695040 }, { argument := 148194209893365767950647299145728, coefficient := 148194209893365767950647299145728 }, { argument := 835381745550403175586327412342784, coefficient := (-835381745550403175586327412342784) }, { argument := 28548304547520931879099259944960, coefficient := 28548304547520931879099259944960 }, { argument := 1115546003393320511640932133634048, coefficient := 1115546003393320511640932133634048 }, { argument := 1115545851578682820347577803735040, coefficient := 1115545851578682820347577803735040 }, { argument := 28548402054944070171533632339968, coefficient := 28548402054944070171533632339968 }, { argument := 2288188561574468334039142829654016, coefficient := (-2288188561574468334039142829654016) }, { argument := 385495795716631419816362639360, coefficient := 385495795716631419816362639360 }, { argument := 53087379972363532244961281966080, coefficient := 53087379972363532244961281966080 }, { argument := 517530562036557714437858649964544, coefficient := 517530562036557714437858649964544 }, { argument := 53087443337076999389860759339008, coefficient := 53087443337076999389860759339008 }, { argument := 385495795716631419816362639360, coefficient := 385495795716631419816362639360 }, { argument := 624476376937431508912313416548352, coefficient := (-624476376937431508912313416548352) }, { argument := 52311367749780341713323163648, coefficient := 52311367749780341713323163648 }, { argument := 9256997727676279325528091000832, coefficient := 9256997727676279325528091000832 }, { argument := 9256998752429806108241102372864, coefficient := 9256998752429806108241102372864 }, { argument := 52310342996253559000311791616, coefficient := 52310342996253559000311791616 }, { argument := 18618618190852119334482828328960, coefficient := (-18618618190852119334482828328960) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18
