import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 1,
parent chunk 8, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-175807117909742804420254658199552)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    61178490477, 1042783785, 308119666013, 15631954215587, 5400525, 437067,
    93660699, 167675235, 1953815100941, 93660699, 2728875, 2750763,
    5400525, 5356749, 167675235, 5356749, 38514827763, 437067,
    152801905149, 19221273906543, 12705, 187419556266285, 495, 825,
    25245, 825, 495, 404415, 25905, 9610648374965,
    25245, 825, 25905, 825, 25245, 825,
    152801905149, 280845746751, 44038564656765, 11009643797313, 1123394376579, 432363,
    150754917, 207515, 5439457903, 8085, 13475, 412335,
    13475, 8085, 6605445, 423115, 603020061, 412335,
    13475, 423115, 13475, 412335, 13475, 432363,
    15746596977, 154937299889, 309874579501, 15746596977
  ]
def negativeCoefficients : Array ℕ := #[
    282135989161273997400848990208, 76943862424436660899141386240, 346911903260417120232538112, 17600015795097566823776780288, 199244205077340552481996800, 257998818946048403076808704,
    3455469888435488254662279168, 6186124295088212777914859520, 17598401921097471257290473472, 3455469888435488254662279168, 201355434936576610664448000, 202970484273718029327532032,
    199244205077340552481996800, 197629155740199133818912768, 6186124295088212777914859520, 197629155740199133818912768, 346910727923371268055760896, 257998818946048403076808704,
    344079301545269137036541952, 43282461001546646378369777664, 1919925317275482958080245760, 422031321881392417297064263680, 1196836561418482882959114240, 62335237573879316820787200,
    1907458269760707094716088320, 1994727602364138138265190400, 1196836561418482882959114240, 30556733458715641105549885440, 1957326459819810548172718080, 43282512440281236918386032640,
    1907458269760707094716088320, 62335237573879316820787200, 1957326459819810548172718080, 62335237573879316820787200, 1907458269760707094716088320, 1994727602364138138265190400,
    344079301545269137036541952, 2529633600832784575330516992, 99166031689069174538863902720, 99166055406121438781160554496, 2529659247875647529489006592, 255222067454121051691155456,
    22247498974018602687818366976, 1959923761385388853040250880, 200680575672715670128475242496, 1221770656448034609687429120, 63633888356668469254553600, 1947196983714055159189340160,
    2036284427413391016145715200, 1221770656448034609687429120, 31193332072438883628582174720, 1998104094399389934592983040, 22247513473159444623525937152, 1947196983714055159189340160,
    63633888356668469254553600, 1998104094399389934592983040, 63633888356668469254553600, 1947196983714055159189340160, 2036284427413391016145715200, 255222067454121051691155456,
    18154590279160468165783191552, 714522179630992579852979142656, 714522132875413882026906877952, 18154590279160468165783191552
  ]
def negativeScales : Array ℕ := #[
    35, 29, 38, 43, 22, 18,
    26, 27, 40, 26, 21, 21,
    22, 22, 27, 22, 35, 18,
    37, 44, 13, 47, 8, 9,
    14, 9, 8, 18, 14, 43,
    14, 9, 14, 9, 14, 9,
    37, 38, 45, 43, 40, 18,
    27, 17, 32, 12, 13, 18,
    13, 12, 22, 18, 29, 18,
    13, 18, 13, 18, 13, 18,
    33, 37, 38, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35832305460266145, 29957792920520146, 38164699810377049, 43829563381619518, 22364668231800296, 18737494928609320,
    26480940469279091, 27321094383117268, 40829431084304898, 26480940469279091, 21379874880751789, 21391400414738474,
    22364668231800296, 22352926266923834, 27321094383117268, 22352926266923834, 35164694922519977, 18737494928609320,
    37152871574908730, 44127769188676925, 13633108754954498, 47413264827078444, 8951284725619456, 9688250309187948,
    14623710056949224, 9688250309187948, 8951284725619456, 18625476983123928, 14660942963165521, 43127770903236622,
    14623710056949224, 9688250309187948, 14660942963165521, 9688250309187948, 14623710056949224, 9688250309187948,
    37152871574908730, 38030986998047622, 45323832681631617, 43323833026673856, 40031001624938241, 18721883542494279,
    27167629816718991, 17662856098364221, 32340815733472279, 12981032075801390, 13717997652637148, 18653457400355779,
    13717997652637148, 12981032075801390, 22655224326531029, 18690690306589555, 29167630756951949, 18653457400355779,
    13717997652637148, 18690690306589555, 13717997652637148, 18653457400355779, 13717997652637148, 18721883542494279,
    33874321030706504, 37172893546745295, 38172893452340887, 33874321030706504
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
noncomputable def negativeCeiling : ℝ := 1347190281 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 282135989161273997400848990208, coefficient := (-282135989161273997400848990208) }, { argument := 76943862424436660899141386240, coefficient := (-76943862424436660899141386240) }, { argument := 346911903260417120232538112, coefficient := (-346911903260417120232538112) }, { argument := 17600015795097566823776780288, coefficient := (-17600015795097566823776780288) }, { argument := 199244205077340552481996800, coefficient := (-199244205077340552481996800) }, { argument := 257998818946048403076808704, coefficient := (-257998818946048403076808704) }, { argument := 3455469888435488254662279168, coefficient := (-3455469888435488254662279168) }, { argument := 6186124295088212777914859520, coefficient := (-6186124295088212777914859520) }, { argument := 17598401921097471257290473472, coefficient := (-17598401921097471257290473472) }, { argument := 3455469888435488254662279168, coefficient := (-3455469888435488254662279168) }, { argument := 201355434936576610664448000, coefficient := (-201355434936576610664448000) }, { argument := 202970484273718029327532032, coefficient := (-202970484273718029327532032) }, { argument := 199244205077340552481996800, coefficient := (-199244205077340552481996800) }, { argument := 197629155740199133818912768, coefficient := (-197629155740199133818912768) }, { argument := 6186124295088212777914859520, coefficient := (-6186124295088212777914859520) }, { argument := 197629155740199133818912768, coefficient := (-197629155740199133818912768) }, { argument := 346910727923371268055760896, coefficient := (-346910727923371268055760896) }, { argument := 257998818946048403076808704, coefficient := (-257998818946048403076808704) }, { argument := 344079301545269137036541952, coefficient := (-344079301545269137036541952) }, { argument := 43282461001546646378369777664, coefficient := (-43282461001546646378369777664) }, { argument := 1919925317275482958080245760, coefficient := (-1919925317275482958080245760) }, { argument := 422031321881392417297064263680, coefficient := (-422031321881392417297064263680) }, { argument := 1196836561418482882959114240, coefficient := (-1196836561418482882959114240) }, { argument := 62335237573879316820787200, coefficient := (-62335237573879316820787200) }, { argument := 1907458269760707094716088320, coefficient := (-1907458269760707094716088320) }, { argument := 1994727602364138138265190400, coefficient := (-1994727602364138138265190400) }, { argument := 1196836561418482882959114240, coefficient := (-1196836561418482882959114240) }, { argument := 30556733458715641105549885440, coefficient := (-30556733458715641105549885440) }, { argument := 1957326459819810548172718080, coefficient := (-1957326459819810548172718080) }, { argument := 43282512440281236918386032640, coefficient := (-43282512440281236918386032640) }, { argument := 1907458269760707094716088320, coefficient := (-1907458269760707094716088320) }, { argument := 62335237573879316820787200, coefficient := (-62335237573879316820787200) }, { argument := 1957326459819810548172718080, coefficient := (-1957326459819810548172718080) }, { argument := 62335237573879316820787200, coefficient := (-62335237573879316820787200) }, { argument := 1907458269760707094716088320, coefficient := (-1907458269760707094716088320) }, { argument := 1994727602364138138265190400, coefficient := (-1994727602364138138265190400) }, { argument := 344079301545269137036541952, coefficient := (-344079301545269137036541952) }, { argument := 2529633600832784575330516992, coefficient := (-2529633600832784575330516992) }, { argument := 99166031689069174538863902720, coefficient := (-99166031689069174538863902720) }, { argument := 99166055406121438781160554496, coefficient := (-99166055406121438781160554496) }, { argument := 2529659247875647529489006592, coefficient := (-2529659247875647529489006592) }, { argument := 255222067454121051691155456, coefficient := (-255222067454121051691155456) }, { argument := 22247498974018602687818366976, coefficient := (-22247498974018602687818366976) }, { argument := 1959923761385388853040250880, coefficient := (-1959923761385388853040250880) }, { argument := 200680575672715670128475242496, coefficient := (-200680575672715670128475242496) }, { argument := 1221770656448034609687429120, coefficient := (-1221770656448034609687429120) }, { argument := 63633888356668469254553600, coefficient := (-63633888356668469254553600) }, { argument := 1947196983714055159189340160, coefficient := (-1947196983714055159189340160) }, { argument := 2036284427413391016145715200, coefficient := (-2036284427413391016145715200) }, { argument := 1221770656448034609687429120, coefficient := (-1221770656448034609687429120) }, { argument := 31193332072438883628582174720, coefficient := (-31193332072438883628582174720) }, { argument := 1998104094399389934592983040, coefficient := (-1998104094399389934592983040) }, { argument := 22247513473159444623525937152, coefficient := (-22247513473159444623525937152) }, { argument := 1947196983714055159189340160, coefficient := (-1947196983714055159189340160) }, { argument := 63633888356668469254553600, coefficient := (-63633888356668469254553600) }, { argument := 1998104094399389934592983040, coefficient := (-1998104094399389934592983040) }, { argument := 63633888356668469254553600, coefficient := (-63633888356668469254553600) }, { argument := 1947196983714055159189340160, coefficient := (-1947196983714055159189340160) }, { argument := 2036284427413391016145715200, coefficient := (-2036284427413391016145715200) }, { argument := 255222067454121051691155456, coefficient := (-255222067454121051691155456) }, { argument := 18154590279160468165783191552, coefficient := (-18154590279160468165783191552) }, { argument := 714522179630992579852979142656, coefficient := (-714522179630992579852979142656) }, { argument := 714522132875413882026906877952, coefficient := (-714522132875413882026906877952) }, { argument := 18154590279160468165783191552, coefficient := (-18154590279160468165783191552) }] }

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

end TermShard10


end Parent1

namespace Parent1

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 26989635905600302187537306902069248
def positiveArguments : Array ℕ := #[
    3635, 21, 609, 539, 35, 21,
    35, 1071, 35, 21, 17157, 1099,
    609, 1071, 35, 1099, 35, 1071,
    35, 21, 6157, 4585, 4847, 393,
    84233, 152353, 4585, 84233, 2489, 2489,
    4847, 4847, 152353, 4847, 6157, 393,
    1147, 3515, 10397, 23199, 1147, 11581,
    23569, 1147, 3515, 1147, 6939, 27675,
    13743
  ]
def positiveCoefficients : Array ℕ := #[
    287994370739350867152532259471360, 12998370412496492886440804352, 188476370981199146853391663104, 333624840587409984085313978368, 10831975343747077405367336960, 207973926599943886183052869632,
    10831975343747077405367336960, 331458445518660568604240510976, 346623210999906476971754782720, 207973926599943886183052869632, 5309834313504817344111068577792, 340124025793658230528534380544,
    188476370981199146853391663104, 331458445518660568604240510976, 10831975343747077405367336960, 340124025793658230528534380544, 10831975343747077405367336960, 331458445518660568604240510976,
    346623210999906476971754782720, 12998370412496492886440804352, 476374801367505397034619240448, 354747192507716785025780285440, 375018460651014887027253444608, 486510435439154448035355820032,
    6517212708070339793473620672512, 11787742425327846313856642056192, 354747192507716785025780285440, 6517212708070339793473620672512, 385154094722663938027990024192, 385154094722663938027990024192,
    375018460651014887027253444608, 375018460651014887027253444608, 11787742425327846313856642056192, 375018460651014887027253444608, 476374801367505397034619240448, 486510435439154448035355820032,
    88744826566270698456830967808, 2175679619044055833135210823680, 1608857823556262339765774319616, 1794935685711346062336548929536, 88744826566270698456830967808, 1792072949370498620450844704768,
    1823563049119820481193591177216, 88744826566270698456830967808, 2175679619044055833135210823680, 88744826566270698456830967808, 536879120787578357970313936896, 535312352925357798559894732800,
    531656561246843159935583256576
  ]
def positiveScales : Array ℕ := #[
    11, 4, 9, 9, 5, 4,
    5, 10, 5, 4, 14, 10,
    9, 10, 5, 10, 5, 10,
    5, 4, 12, 12, 12, 8,
    16, 17, 12, 16, 11, 11,
    12, 12, 17, 12, 12, 8,
    10, 11, 13, 14, 10, 13,
    14, 10, 11, 10, 12, 14,
    13
  ]
def negativeArguments : Array ℕ := #[
    8306520311, 30455645881, 519144581, 644324367, 12680180635, 6340089899,
    644324367, 16684969731, 61178490477, 1042783785, 25165821, 25165827,
    7, 131, 37
  ]
def negativeCoefficients : Array ℕ := #[
    76614127160043635806503436288, 280903752583166733032093646848, 76612217783681426315089543168, 742855418656494261677064192, 29238505872781608626967019520, 29238503942791009915105181696,
    742855418656494261677064192, 76945841626336875399635533824, 282135989161273997400848990208, 76943862424436660899141386240, 118842229604297057781380284416, 118842257938495954999251566592,
    8873554201597605810476922437632, 41515557157474512899017029976064, 11725768052111121963844504649728
  ]
def negativeScales : Array ℕ := #[
    32, 34, 28, 29, 33, 32,
    29, 33, 35, 29, 24, 24,
    2, 7, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11827739648737264, 4392317422778759, 9250298417906332, 9074141462752505, 5129283016944966, 4392317422778759,
    5129283016944966, 10064742764750255, 5129283016944966, 4392317422778759, 14066509690924443, 10101975670949231,
    9250298417906332, 10064742764750255, 5129283016944966, 10101975670949231, 5129283016944966, 10064742764750255,
    5129283016944966, 4392317422778759, 12588011853214835, 12162706018482416, 12242876367166399, 8618385502258025,
    16362097928865397, 17217058383010668, 12162706018482416, 16362097928865397, 11281350514981035, 11281350514981035,
    12242876367166399, 12242876367166399, 17217058383010668, 12242876367166399, 12588011853214835, 8618385502258025,
    10163649676015824, 11779308973933791, 13343879685849875, 14501774998430970, 10163649676015824, 13499472212561551,
    14524602927885212, 10163649676015824, 11779308973933791, 10163649676015824, 12760512051339829, 14756295696540282,
    13746409348226269
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32951597108067255, 34825990650325396, 28951561152784146, 29263211914599086, 33561856246353039, 32561856151122867,
    29263211914599086, 33957830030024671, 35832305460266145, 29957792920520146, 24584962328742205, 24584962672707506,
    2807354922807594, 7033423001537451, 5209453365628950
  ]

abbrev PositiveTerm := Fin 49
abbrev NegativeTerm := Fin 15
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
noncomputable def positiveFloor : ℝ := 52487136543 / 1000000000000
noncomputable def negativeCeiling : ℝ := 312486459 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 76614127160043635806503436288, coefficient := (-76614127160043635806503436288) }, { argument := 280903752583166733032093646848, coefficient := (-280903752583166733032093646848) }, { argument := 76612217783681426315089543168, coefficient := (-76612217783681426315089543168) }, { argument := 742855418656494261677064192, coefficient := (-742855418656494261677064192) }, { argument := 29238505872781608626967019520, coefficient := (-29238505872781608626967019520) }, { argument := 29238503942791009915105181696, coefficient := (-29238503942791009915105181696) }, { argument := 742855418656494261677064192, coefficient := (-742855418656494261677064192) }, { argument := 76945841626336875399635533824, coefficient := (-76945841626336875399635533824) }, { argument := 282135989161273997400848990208, coefficient := (-282135989161273997400848990208) }, { argument := 76943862424436660899141386240, coefficient := (-76943862424436660899141386240) }, { argument := 118842229604297057781380284416, coefficient := (-118842229604297057781380284416) }, { argument := 118842257938495954999251566592, coefficient := (-118842257938495954999251566592) }, { argument := 287994370739350867152532259471360, coefficient := 287994370739350867152532259471360 }, { argument := 12998370412496492886440804352, coefficient := 12998370412496492886440804352 }, { argument := 188476370981199146853391663104, coefficient := 188476370981199146853391663104 }, { argument := 333624840587409984085313978368, coefficient := 333624840587409984085313978368 }, { argument := 10831975343747077405367336960, coefficient := 10831975343747077405367336960 }, { argument := 207973926599943886183052869632, coefficient := 207973926599943886183052869632 }, { argument := 10831975343747077405367336960, coefficient := 10831975343747077405367336960 }, { argument := 331458445518660568604240510976, coefficient := 331458445518660568604240510976 }, { argument := 346623210999906476971754782720, coefficient := 346623210999906476971754782720 }, { argument := 207973926599943886183052869632, coefficient := 207973926599943886183052869632 }, { argument := 5309834313504817344111068577792, coefficient := 5309834313504817344111068577792 }, { argument := 340124025793658230528534380544, coefficient := 340124025793658230528534380544 }, { argument := 188476370981199146853391663104, coefficient := 188476370981199146853391663104 }, { argument := 331458445518660568604240510976, coefficient := 331458445518660568604240510976 }, { argument := 10831975343747077405367336960, coefficient := 10831975343747077405367336960 }, { argument := 340124025793658230528534380544, coefficient := 340124025793658230528534380544 }, { argument := 10831975343747077405367336960, coefficient := 10831975343747077405367336960 }, { argument := 331458445518660568604240510976, coefficient := 331458445518660568604240510976 }, { argument := 346623210999906476971754782720, coefficient := 346623210999906476971754782720 }, { argument := 12998370412496492886440804352, coefficient := 12998370412496492886440804352 }, { argument := 8873554201597605810476922437632, coefficient := (-8873554201597605810476922437632) }, { argument := 476374801367505397034619240448, coefficient := 476374801367505397034619240448 }, { argument := 354747192507716785025780285440, coefficient := 354747192507716785025780285440 }, { argument := 375018460651014887027253444608, coefficient := 375018460651014887027253444608 }, { argument := 486510435439154448035355820032, coefficient := 486510435439154448035355820032 }, { argument := 6517212708070339793473620672512, coefficient := 6517212708070339793473620672512 }, { argument := 11787742425327846313856642056192, coefficient := 11787742425327846313856642056192 }, { argument := 354747192507716785025780285440, coefficient := 354747192507716785025780285440 }, { argument := 6517212708070339793473620672512, coefficient := 6517212708070339793473620672512 }, { argument := 385154094722663938027990024192, coefficient := 385154094722663938027990024192 }, { argument := 385154094722663938027990024192, coefficient := 385154094722663938027990024192 }, { argument := 375018460651014887027253444608, coefficient := 375018460651014887027253444608 }, { argument := 375018460651014887027253444608, coefficient := 375018460651014887027253444608 }, { argument := 11787742425327846313856642056192, coefficient := 11787742425327846313856642056192 }, { argument := 375018460651014887027253444608, coefficient := 375018460651014887027253444608 }, { argument := 476374801367505397034619240448, coefficient := 476374801367505397034619240448 }, { argument := 486510435439154448035355820032, coefficient := 486510435439154448035355820032 }, { argument := 41515557157474512899017029976064, coefficient := (-41515557157474512899017029976064) }, { argument := 88744826566270698456830967808, coefficient := 88744826566270698456830967808 }, { argument := 2175679619044055833135210823680, coefficient := 2175679619044055833135210823680 }, { argument := 1608857823556262339765774319616, coefficient := 1608857823556262339765774319616 }, { argument := 1794935685711346062336548929536, coefficient := 1794935685711346062336548929536 }, { argument := 88744826566270698456830967808, coefficient := 88744826566270698456830967808 }, { argument := 1792072949370498620450844704768, coefficient := 1792072949370498620450844704768 }, { argument := 1823563049119820481193591177216, coefficient := 1823563049119820481193591177216 }, { argument := 88744826566270698456830967808, coefficient := 88744826566270698456830967808 }, { argument := 2175679619044055833135210823680, coefficient := 2175679619044055833135210823680 }, { argument := 88744826566270698456830967808, coefficient := 88744826566270698456830967808 }, { argument := 11725768052111121963844504649728, coefficient := (-11725768052111121963844504649728) }, { argument := 536879120787578357970313936896, coefficient := 536879120787578357970313936896 }, { argument := 535312352925357798559894732800, coefficient := 535312352925357798559894732800 }, { argument := 531656561246843159935583256576, coefficient := 531656561246843159935583256576 }] }

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

end TermShard11


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
