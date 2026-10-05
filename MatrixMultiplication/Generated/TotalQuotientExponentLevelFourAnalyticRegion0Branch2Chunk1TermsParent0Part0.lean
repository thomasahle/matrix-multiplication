import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 1, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk1

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
def constantNumerator : ℤ := 18964728780223592503773312843776
def positiveArguments : Array ℕ := #[
    3, 233869, 8154737, 2039637, 115031, 22111
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 2208830253964482112963739648, 77019313370833924001999355904, 77055307248166356437818146816, 2172874155563912634306658304, 1670659924843691605120516096
  ]
def positiveScales : Array ℕ := #[
    1, 17, 22, 20, 16, 14
  ]
def negativeArguments : Array ℕ := #[
    39652722819, 1922174689987, 961221468865, 4925047271, 1940662515, 95428740351,
    642733010111, 95230831027, 1918587637, 1382643813087, 67023970961951, 33516662222645,
    171730606483, 95428740351, 72971026407, 31407100377919, 1165269766745, 5901148643,
    39652722819, 1382643813087, 345822492987, 19503621081, 345822492987, 16763823414651,
    8383081439145, 42952715583, 642733010111, 31407100377919, 211114744352395, 31347440457027,
    636086770805, 1922174689987, 67023970961951, 16763823414651, 945442434713, 19503621081,
    945442434713, 472787187635, 2422437829, 95230831027, 1165269766745, 31347440457027,
    581501608711, 23555122191, 961221468865, 33516662222645, 8383081439145, 472787187635,
    1918587637, 5901148643, 636086770805, 23555122191, 59265995, 4925047271,
    171730606483, 42952715583, 2422437829, 1
  ]
def negativeCoefficients : Array ℕ := #[
    11161249231992122731659264, 541044076097903241799401472, 541119581125116852835450880, 11090220527228839115358208, 2184991744851472401039360, 53721604935649926957760512,
    723653036208654209477771264, 53610191890922483612647424, 2160137641767710111039488, 389179635087795932545155072, 18865570665570841746112249856, 18868203437075850280032010240,
    386702947682474042310262784, 53721604935649926957760512, 1314529149341631294354751488, 17680625694847971562228809728, 1311977121824721697903738880, 53152821659345416257273856,
    11161249231992122731659264, 389179635087795932545155072, 389361512638147291552677888, 10979562579095868797878272, 389361512638147291552677888, 18874387220881759863752884224,
    18877021222774971669896232960, 386883667788299393707278336, 723653036208654209477771264, 17680625694847971562228809728, 237694070999465911720062484480, 17647040145160701003561959424,
    716170035993175023492792320, 541044076097903241799401472, 18865570665570841746112249856, 18874387220881759863752884224, 532236774584215161542803456, 10979562579095868797878272,
    532236774584215161542803456, 532311050514632693503754240, 10909690104012593308893184, 53610191890922483612647424, 1311977121824721697903738880, 17647040145160701003561959424,
    1309425214153101785408995328, 53041419761027050654138368, 541119581125116852835450880, 18868203437075850280032010240, 18877021222774971669896232960, 532311050514632693503754240,
    2160137641767710111039488, 53152821659345416257273856, 716170035993175023492792320, 53041419761027050654138368, 2135282503981933432668160, 11090220527228839115358208,
    386702947682474042310262784, 386883667788299393707278336, 10909690104012593308893184, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    35, 40, 39, 32, 30, 36,
    39, 36, 30, 40, 45, 44,
    37, 36, 36, 44, 40, 32,
    35, 40, 38, 34, 38, 43,
    42, 35, 39, 44, 47, 44,
    39, 40, 45, 43, 39, 34,
    39, 38, 31, 36, 40, 44,
    39, 34, 39, 44, 42, 38,
    30, 32, 39, 34, 25, 32,
    37, 35, 31, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 17835341115395375, 22959206917623940, 20959880983065894, 16811663183550531, 14432476654021382
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    35206700883216431, 40805876595636432, 39806077915888465, 32197490425724817, 30853902108231838, 36473704778180275,
    39225428613382243, 36470709671238958, 30837397521030222, 40330566686115071, 45929742405180936, 44929943725455716,
    37321356228623457, 36473704778180275, 36086604695656355, 44836155988947565, 40083801124507923, 32458348652574409,
    35206700883216431, 40330566686115071, 38331240751565512, 34183022951341408, 38331240751565512, 43930416470717809,
    42930617790992870, 35322030294073898, 39225428613382243, 44836155988947565, 47585020669126328, 44833412885453832,
    39210432625734925, 40805876595636432, 45929742405180936, 43930416470717809, 39782198663480911, 34183022951341408,
    39782198663480911, 38782399983731860, 31173812493849794, 36470709671238958, 40083801124507923, 44833412885453832,
    39080992226648081, 34455321764806176, 39806077915888465, 44929943725455716, 42930617790992870, 38782399983731860,
    30837397521030222, 32458348652574409, 39210432625734925, 34455321764806176, 25820701233429470, 32197490425724817,
    37321356228623457, 35322030294073898, 31173812493849794, 0
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 58
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
noncomputable def positiveFloor : ℝ := 50999239 / 1000000000000
noncomputable def negativeCeiling : ℝ := 52503849 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 11161249231992122731659264, coefficient := (-11161249231992122731659264) }, { argument := 541044076097903241799401472, coefficient := (-541044076097903241799401472) }, { argument := 541119581125116852835450880, coefficient := (-541119581125116852835450880) }, { argument := 11090220527228839115358208, coefficient := (-11090220527228839115358208) }, { argument := 2184991744851472401039360, coefficient := (-2184991744851472401039360) }, { argument := 53721604935649926957760512, coefficient := (-53721604935649926957760512) }, { argument := 723653036208654209477771264, coefficient := (-723653036208654209477771264) }, { argument := 53610191890922483612647424, coefficient := (-53610191890922483612647424) }, { argument := 2160137641767710111039488, coefficient := (-2160137641767710111039488) }, { argument := 389179635087795932545155072, coefficient := (-389179635087795932545155072) }, { argument := 18865570665570841746112249856, coefficient := (-18865570665570841746112249856) }, { argument := 18868203437075850280032010240, coefficient := (-18868203437075850280032010240) }, { argument := 386702947682474042310262784, coefficient := (-386702947682474042310262784) }, { argument := 53721604935649926957760512, coefficient := (-53721604935649926957760512) }, { argument := 1314529149341631294354751488, coefficient := (-1314529149341631294354751488) }, { argument := 17680625694847971562228809728, coefficient := (-17680625694847971562228809728) }, { argument := 1311977121824721697903738880, coefficient := (-1311977121824721697903738880) }, { argument := 53152821659345416257273856, coefficient := (-53152821659345416257273856) }, { argument := 11161249231992122731659264, coefficient := (-11161249231992122731659264) }, { argument := 389179635087795932545155072, coefficient := (-389179635087795932545155072) }, { argument := 389361512638147291552677888, coefficient := (-389361512638147291552677888) }, { argument := 10979562579095868797878272, coefficient := (-10979562579095868797878272) }, { argument := 389361512638147291552677888, coefficient := (-389361512638147291552677888) }, { argument := 18874387220881759863752884224, coefficient := (-18874387220881759863752884224) }, { argument := 18877021222774971669896232960, coefficient := (-18877021222774971669896232960) }, { argument := 386883667788299393707278336, coefficient := (-386883667788299393707278336) }, { argument := 723653036208654209477771264, coefficient := (-723653036208654209477771264) }, { argument := 17680625694847971562228809728, coefficient := (-17680625694847971562228809728) }, { argument := 237694070999465911720062484480, coefficient := (-237694070999465911720062484480) }, { argument := 17647040145160701003561959424, coefficient := (-17647040145160701003561959424) }, { argument := 716170035993175023492792320, coefficient := (-716170035993175023492792320) }, { argument := 541044076097903241799401472, coefficient := (-541044076097903241799401472) }, { argument := 18865570665570841746112249856, coefficient := (-18865570665570841746112249856) }, { argument := 18874387220881759863752884224, coefficient := (-18874387220881759863752884224) }, { argument := 532236774584215161542803456, coefficient := (-532236774584215161542803456) }, { argument := 10979562579095868797878272, coefficient := (-10979562579095868797878272) }, { argument := 532236774584215161542803456, coefficient := (-532236774584215161542803456) }, { argument := 532311050514632693503754240, coefficient := (-532311050514632693503754240) }, { argument := 10909690104012593308893184, coefficient := (-10909690104012593308893184) }, { argument := 53610191890922483612647424, coefficient := (-53610191890922483612647424) }, { argument := 1311977121824721697903738880, coefficient := (-1311977121824721697903738880) }, { argument := 17647040145160701003561959424, coefficient := (-17647040145160701003561959424) }, { argument := 1309425214153101785408995328, coefficient := (-1309425214153101785408995328) }, { argument := 53041419761027050654138368, coefficient := (-53041419761027050654138368) }, { argument := 541119581125116852835450880, coefficient := (-541119581125116852835450880) }, { argument := 18868203437075850280032010240, coefficient := (-18868203437075850280032010240) }, { argument := 18877021222774971669896232960, coefficient := (-18877021222774971669896232960) }, { argument := 532311050514632693503754240, coefficient := (-532311050514632693503754240) }, { argument := 2160137641767710111039488, coefficient := (-2160137641767710111039488) }, { argument := 53152821659345416257273856, coefficient := (-53152821659345416257273856) }, { argument := 716170035993175023492792320, coefficient := (-716170035993175023492792320) }, { argument := 53041419761027050654138368, coefficient := (-53041419761027050654138368) }, { argument := 2135282503981933432668160, coefficient := (-2135282503981933432668160) }, { argument := 11090220527228839115358208, coefficient := (-11090220527228839115358208) }, { argument := 386702947682474042310262784, coefficient := (-386702947682474042310262784) }, { argument := 386883667788299393707278336, coefficient := (-386883667788299393707278336) }, { argument := 10909690104012593308893184, coefficient := (-10909690104012593308893184) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 2208830253964482112963739648, coefficient := 2208830253964482112963739648 }, { argument := 77019313370833924001999355904, coefficient := 77019313370833924001999355904 }, { argument := 77055307248166356437818146816, coefficient := 77055307248166356437818146816 }, { argument := 2172874155563912634306658304, coefficient := 2172874155563912634306658304 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1670659924843691605120516096, coefficient := 1670659924843691605120516096 }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-18590302749194571421431441129472)
def positiveArguments : Array ℕ := #[
    2161417, 7264937, 2157297, 43763, 169551, 8219023,
    4110085, 21059
  ]
def positiveCoefficients : Array ℕ := #[
    40828012785218639795404668928, 548923119823352827037647634432, 40750188185580948042282958848, 1653319395118594267895824384, 1601363919074062431254740992, 77626477474269440026414678016,
    77637310582981142992534896640, 1591173052204029736883585024
  ]
def positiveScales : Array ℕ := #[
    21, 22, 21, 15, 17, 22,
    21, 14
  ]
def negativeArguments : Array ℕ := #[
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    633825300114114700748351602688, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    21043546006072685, 22792518856455357, 21040793378613849, 15417424019342894, 17371359767740210, 22970535478526328,
    21970736798772385, 14362149310248596
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 107087447 / 500000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 40828012785218639795404668928, coefficient := 40828012785218639795404668928 }, { argument := 548923119823352827037647634432, coefficient := 548923119823352827037647634432 }, { argument := 40750188185580948042282958848, coefficient := 40750188185580948042282958848 }, { argument := 1653319395118594267895824384, coefficient := 1653319395118594267895824384 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 1601363919074062431254740992, coefficient := 1601363919074062431254740992 }, { argument := 77626477474269440026414678016, coefficient := 77626477474269440026414678016 }, { argument := 77637310582981142992534896640, coefficient := 77637310582981142992534896640 }, { argument := 1591173052204029736883585024, coefficient := 1591173052204029736883585024 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk1
