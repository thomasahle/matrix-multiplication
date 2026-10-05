import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 1,
parent chunk 5, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1089659813493534791580508668035072)
def positiveArguments : Array ℕ := #[
    4851, 315, 189, 315, 9639, 315,
    189, 154413, 9891, 5481, 9639, 315,
    9891, 315, 9639, 315, 189, 35861,
    26705, 28231, 2289, 490609, 887369, 26705,
    490609, 14497, 14497, 28231, 28231, 887369,
    28231, 35861, 2289, 2201, 6745, 19951,
    44517, 2201, 22223, 45227, 2201, 6745,
    2201, 1799, 7175, 3563, 7175, 1,
    1, 1, 1, 1, 93, 2253,
    1707, 951, 93, 951
  ]
def positiveCoefficients : Array ℕ := #[
    750655891321672464191956451328, 24371944523430924162076508160, 467941334849873743911868956672, 24371944523430924162076508160, 745781502416986279359541149696, 779902224749789573186448261120,
    467941334849873743911868956672, 11947127205385839024249904300032, 765279058035731018689202356224, 424071834707698080420131241984, 745781502416986279359541149696, 24371944523430924162076508160,
    765279058035731018689202356224, 24371944523430924162076508160, 745781502416986279359541149696, 779902224749789573186448261120, 29246333428117108994491809792, 693652621075203469346210840576,
    516549824204938753768454881280, 546066957016649539698080874496, 708411187481058862311023837184, 9489758198965017676374756818944, 17164212730009822018077515055104, 516549824204938753768454881280,
    9489758198965017676374756818944, 560825523422504932662893871104, 560825523422504932662893871104, 546066957016649539698080874496, 546066957016649539698080874496, 17164212730009822018077515055104,
    546066957016649539698080874496, 693652621075203469346210840576, 708411187481058862311023837184, 85147063327097562032905388032, 2087476391244972488548648222720, 1543633857736413866532026712064,
    1722168022777102303052634783744, 85147063327097562032905388032, 1719421343314937865567702351872, 1749634817398746677901959102464, 85147063327097562032905388032, 2087476391244972488548648222720,
    85147063327097562032905388032, 278381766334299889317940559872, 277569368183518858512538009600, 275673772498363119966598725632, 277569368183518858512538009600, 158456325028528675187087900672,
    39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 3597763239173136423925579776, 87158715890936304979616464896,
    66036363970629504039150157824, 73580061085024790089316696064, 3597763239173136423925579776, 73580061085024790089316696064
  ]
def positiveScales : Array ℕ := #[
    12, 8, 7, 8, 13, 8,
    7, 17, 13, 12, 13, 8,
    13, 8, 13, 8, 7, 15,
    14, 14, 11, 18, 19, 14,
    18, 13, 13, 14, 14, 19,
    14, 15, 11, 11, 12, 14,
    15, 11, 14, 15, 11, 12,
    11, 10, 12, 11, 12, 0,
    0, 0, 0, 0, 6, 11,
    10, 9, 6, 9
  ]
def negativeArguments : Array ℕ := #[
    63, 763, 71, 7, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    19965496953594613073573075484672, 60451087998383689583874034106368, 11250399077025535938283240947712, 1109194275199700726309615304704, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    5, 9, 6, 2, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12244066464194817, 8299208018387278, 7562242424220952, 8299208018387278, 13234667766192568, 8299208018387278,
    7562242424220952, 17236434692366755, 13271900672391543, 12420223419348643, 13234667766192568, 8299208018387278,
    13271900672391543, 8299208018387278, 13234667766192568, 8299208018387278, 7562242424220952, 15130128098512167,
    14704822263774464, 14784992612434086, 11160501747555686, 18904214173871410, 19759174628290728, 14704822263774464,
    18904214173871410, 13823466760214044, 13823466760214044, 14784992612434086, 14784992612434086, 19759174628290728,
    14784992612434086, 15130128098512167, 11160501747555686, 11103943429891557, 12719602727828552, 14284173439725607,
    15442068752306718, 11103943429891557, 14439765966437297, 15464896681760976, 11103943429891557, 12719602727828552,
    11103943429891557, 10812979471199464, 12808763116402615, 11798876768094178, 12808763116402615, 0,
    0, 0, 0, 0, 6539158811107971, 11137631598235427,
    10737247343017206, 9893301530621223, 6539158811107971, 9893301530621223
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    5977279939904027, 9575539246837362, 6149747119504683, 2807354922807594, 0, 0
  ]

abbrev PositiveTerm := Fin 58
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 19286016903 / 1000000000000
noncomputable def negativeCeiling : ℝ := 4637230897 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 750655891321672464191956451328, coefficient := 750655891321672464191956451328 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 467941334849873743911868956672, coefficient := 467941334849873743911868956672 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 745781502416986279359541149696, coefficient := 745781502416986279359541149696 }, { argument := 779902224749789573186448261120, coefficient := 779902224749789573186448261120 }, { argument := 467941334849873743911868956672, coefficient := 467941334849873743911868956672 }, { argument := 11947127205385839024249904300032, coefficient := 11947127205385839024249904300032 }, { argument := 765279058035731018689202356224, coefficient := 765279058035731018689202356224 }, { argument := 424071834707698080420131241984, coefficient := 424071834707698080420131241984 }, { argument := 745781502416986279359541149696, coefficient := 745781502416986279359541149696 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 765279058035731018689202356224, coefficient := 765279058035731018689202356224 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 745781502416986279359541149696, coefficient := 745781502416986279359541149696 }, { argument := 779902224749789573186448261120, coefficient := 779902224749789573186448261120 }, { argument := 29246333428117108994491809792, coefficient := 29246333428117108994491809792 }, { argument := 19965496953594613073573075484672, coefficient := (-19965496953594613073573075484672) }, { argument := 693652621075203469346210840576, coefficient := 693652621075203469346210840576 }, { argument := 516549824204938753768454881280, coefficient := 516549824204938753768454881280 }, { argument := 546066957016649539698080874496, coefficient := 546066957016649539698080874496 }, { argument := 708411187481058862311023837184, coefficient := 708411187481058862311023837184 }, { argument := 9489758198965017676374756818944, coefficient := 9489758198965017676374756818944 }, { argument := 17164212730009822018077515055104, coefficient := 17164212730009822018077515055104 }, { argument := 516549824204938753768454881280, coefficient := 516549824204938753768454881280 }, { argument := 9489758198965017676374756818944, coefficient := 9489758198965017676374756818944 }, { argument := 560825523422504932662893871104, coefficient := 560825523422504932662893871104 }, { argument := 560825523422504932662893871104, coefficient := 560825523422504932662893871104 }, { argument := 546066957016649539698080874496, coefficient := 546066957016649539698080874496 }, { argument := 546066957016649539698080874496, coefficient := 546066957016649539698080874496 }, { argument := 17164212730009822018077515055104, coefficient := 17164212730009822018077515055104 }, { argument := 546066957016649539698080874496, coefficient := 546066957016649539698080874496 }, { argument := 693652621075203469346210840576, coefficient := 693652621075203469346210840576 }, { argument := 708411187481058862311023837184, coefficient := 708411187481058862311023837184 }, { argument := 60451087998383689583874034106368, coefficient := (-60451087998383689583874034106368) }, { argument := 85147063327097562032905388032, coefficient := 85147063327097562032905388032 }, { argument := 2087476391244972488548648222720, coefficient := 2087476391244972488548648222720 }, { argument := 1543633857736413866532026712064, coefficient := 1543633857736413866532026712064 }, { argument := 1722168022777102303052634783744, coefficient := 1722168022777102303052634783744 }, { argument := 85147063327097562032905388032, coefficient := 85147063327097562032905388032 }, { argument := 1719421343314937865567702351872, coefficient := 1719421343314937865567702351872 }, { argument := 1749634817398746677901959102464, coefficient := 1749634817398746677901959102464 }, { argument := 85147063327097562032905388032, coefficient := 85147063327097562032905388032 }, { argument := 2087476391244972488548648222720, coefficient := 2087476391244972488548648222720 }, { argument := 85147063327097562032905388032, coefficient := 85147063327097562032905388032 }, { argument := 11250399077025535938283240947712, coefficient := (-11250399077025535938283240947712) }, { argument := 278381766334299889317940559872, coefficient := 278381766334299889317940559872 }, { argument := 277569368183518858512538009600, coefficient := 277569368183518858512538009600 }, { argument := 275673772498363119966598725632, coefficient := 275673772498363119966598725632 }, { argument := 277569368183518858512538009600, coefficient := 277569368183518858512538009600 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 87158715890936304979616464896, coefficient := 87158715890936304979616464896 }, { argument := 66036363970629504039150157824, coefficient := 66036363970629504039150157824 }, { argument := 73580061085024790089316696064, coefficient := 73580061085024790089316696064 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 73580061085024790089316696064, coefficient := 73580061085024790089316696064 }] }

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


end Parent0

namespace Parent0

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-6049934016780931342203895228137472)
def positiveArguments : Array ℕ := #[
    1899, 93, 2253, 93, 8388605, 8388611,
    24002257, 86207101, 12004185, 43802937, 863096497, 863096641,
    43803363, 726745, 600757755, 6271113799, 300379259, 726745,
    1715907, 331731261, 2653850151, 13727193, 24524187, 1108448637,
    3081885
  ]
def positiveCoefficients : Array ℕ := #[
    73464004206341785688544903168, 3597763239173136423925579776, 87158715890936304979616464896, 3597763239173136423925579776, 79228134180065440375672668160, 79228190848463234811415232512,
    226694907940046643835902623744, 814203048695516549542515310592, 226752643592666208118285271040, 206853521540050648507877425152, 8151715937830002583147668045824, 8151717297871549649605489590272,
    206855533268172350976738459648, 54911299673489604973239992320, 11347993146144056064906016849920, 118457990458635716871373157564416, 11348007558806561783063209050112, 54911299673489604973239992320,
    259300534544684937910318792704, 50129810824527433771583633620992, 50129812014563787454734227472384, 259299344508331254759724941312, 115812198708427475844335665152, 5234500691351342085794904932352,
    116430323424469732315291975680
  ]
def positiveScales : Array ℕ := #[
    10, 6, 11, 6, 22, 23,
    24, 26, 23, 25, 29, 29,
    25, 19, 29, 32, 28, 19,
    20, 28, 31, 23, 24, 30,
    21
  ]
def negativeArguments : Array ℕ := #[
    3, 1, 1, 211, 1783, 159,
    69
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 158456325028528675187087900672, 1267650600228229401496703205376, 16717142290509775232237773520896, 141263813762933313929288863449088, 100778222718144237418987904827392,
    5466743213484239293954532573184
  ]
def negativeScales : Array ℕ := #[
    1, 0, 0, 7, 10, 7,
    6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10891024189919810, 6539158811107971, 11137631598235427, 6539158811107971, 22999999482592385, 23000000515947860,
    24516666737112358, 26361303375237552, 23517034122226184, 25384524270414224, 29684946625522795, 29684946866223654,
    25384538301096662, 19471089715101697, 29162208125887797, 32546074553726234, 28162209958199753, 19471089715101697,
    20710539932019127, 28305439731323061, 31305439765571336, 23710533310885513, 24547701974743247, 30045894774518771,
    21555381598267912
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 0, 0, 7721099188825173, 10800090988272228, 7312882955284356,
    6108524456778170
  ]

abbrev PositiveTerm := Fin 25
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
noncomputable def positiveFloor : ℝ := 98736547257 / 1000000000000
noncomputable def negativeCeiling : ℝ := 2920026707 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 73464004206341785688544903168, coefficient := 73464004206341785688544903168 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 87158715890936304979616464896, coefficient := 87158715890936304979616464896 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 79228134180065440375672668160, coefficient := 79228134180065440375672668160 }, { argument := 79228190848463234811415232512, coefficient := 79228190848463234811415232512 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 226694907940046643835902623744, coefficient := 226694907940046643835902623744 }, { argument := 814203048695516549542515310592, coefficient := 814203048695516549542515310592 }, { argument := 226752643592666208118285271040, coefficient := 226752643592666208118285271040 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 206853521540050648507877425152, coefficient := 206853521540050648507877425152 }, { argument := 8151715937830002583147668045824, coefficient := 8151715937830002583147668045824 }, { argument := 8151717297871549649605489590272, coefficient := 8151717297871549649605489590272 }, { argument := 206855533268172350976738459648, coefficient := 206855533268172350976738459648 }, { argument := 16717142290509775232237773520896, coefficient := (-16717142290509775232237773520896) }, { argument := 54911299673489604973239992320, coefficient := 54911299673489604973239992320 }, { argument := 11347993146144056064906016849920, coefficient := 11347993146144056064906016849920 }, { argument := 118457990458635716871373157564416, coefficient := 118457990458635716871373157564416 }, { argument := 11348007558806561783063209050112, coefficient := 11348007558806561783063209050112 }, { argument := 54911299673489604973239992320, coefficient := 54911299673489604973239992320 }, { argument := 141263813762933313929288863449088, coefficient := (-141263813762933313929288863449088) }, { argument := 259300534544684937910318792704, coefficient := 259300534544684937910318792704 }, { argument := 50129810824527433771583633620992, coefficient := 50129810824527433771583633620992 }, { argument := 50129812014563787454734227472384, coefficient := 50129812014563787454734227472384 }, { argument := 259299344508331254759724941312, coefficient := 259299344508331254759724941312 }, { argument := 100778222718144237418987904827392, coefficient := (-100778222718144237418987904827392) }, { argument := 115812198708427475844335665152, coefficient := 115812198708427475844335665152 }, { argument := 5234500691351342085794904932352, coefficient := 5234500691351342085794904932352 }, { argument := 116430323424469732315291975680, coefficient := 116430323424469732315291975680 }, { argument := 5466743213484239293954532573184, coefficient := (-5466743213484239293954532573184) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5
