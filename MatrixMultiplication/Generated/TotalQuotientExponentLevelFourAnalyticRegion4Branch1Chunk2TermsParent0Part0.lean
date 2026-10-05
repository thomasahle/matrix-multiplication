import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 2, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk2

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
def constantNumerator : ℤ := (-24566784759081889055365478219776)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    226178773439, 13240246586945, 13244641961319, 221783399065, 77662212623, 1232088342543,
    33547601, 25554327648813, 14937253, 4652587, 4162841, 33547601,
    14937253, 588919565, 14937253, 616043964755, 4162841, 4652587,
    14937253, 4652587, 33547601, 33547601, 39326218029, 77662212623,
    2766747678553, 2766715643413, 77692866691, 729986498913, 42732574342815, 42746760306873,
    715800534855, 2766747678553, 44345574871985, 139461479, 923513937212467, 62095987,
    19341373, 17305439, 139461479, 62095987, 2448210635, 62095987,
    22172779253913, 17305439, 19341373, 62095987, 19341373, 139461479,
    139461479, 1399819523415, 1232088342543, 44345574871985, 5543096858665, 154107160927,
    33547601, 139461479, 139461479, 33547327, 226178773439, 729986498913,
    7054089831, 7054089831, 412938346905, 413075430351
  ]
def negativeCoefficients : Array ℕ := #[
    127327329972374529762131968, 7453596199407372933623971840, 7456070575206485462014230528, 124852954173262001371873280, 21859969489356939421810688, 693604075045523354252476416,
    38677750620870164218904576, 7192903779806111873082851328, 34442960406906277625593856, 5364067604354256351526912, 38395431273272571779350528, 38677750620870164218904576,
    34442960406906277625593856, 678978030972209817127485440, 34442960406906277625593856, 693603842528615242787717120, 38395431273272571779350528, 5364067604354256351526912,
    34442960406906277625593856, 5364067604354256351526912, 38677750620870164218904576, 38677750620870164218904576, 22138692607661910207234048, 21859969489356939421810688,
    778770238384967227977760768, 778761221294681805373308928, 21868597842433326287159296, 410945865561259972919033856, 24056300735860456499215073280, 24064286723666144005378277376,
    402959877755572466755829760, 778770238384967227977760768, 24964339308625259607170744320, 1286305105627009542397100032, 259946063968845376289454948352, 1145468780193395358922964992,
    178392678882577965733904384, 1276916017264768596832157696, 1286305105627009542397100032, 1145468780193395358922964992, 22580757511189474083686318080, 1145468780193395358922964992,
    24964330096422712778227187712, 1276916017264768596832157696, 178392678882577965733904384, 1145468780193395358922964992, 178392678882577965733904384, 1286305105627009542397100032,
    1286305105627009542397100032, 788028335504717412544020480, 693604075045523354252476416, 24964339308625259607170744320, 24963888947162260931702947840, 694036952525962260923809792,
    38677750620870164218904576, 1286305105627009542397100032, 1286305105627009542397100032, 38677434720377901942833152, 127327329972374529762131968, 410945865561259972919033856,
    127075185337318420412104704, 127075185337318420412104704, 7438835940993386440839659520, 7441305416818683494881296384
  ]
def negativeScales : Array ℕ := #[
    37, 43, 43, 37, 36, 40,
    24, 44, 23, 22, 21, 24,
    23, 29, 23, 39, 21, 22,
    23, 22, 24, 24, 35, 36,
    41, 41, 36, 39, 45, 45,
    39, 41, 45, 27, 49, 25,
    24, 24, 27, 25, 31, 25,
    44, 24, 24, 25, 24, 27,
    27, 40, 40, 45, 42, 37,
    24, 27, 27, 24, 37, 39,
    32, 32, 38, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    37718672584644959, 43589995224752333, 43590474077805436, 37690360424724289, 36176493759580695, 40164242841742325,
    24999706290293667, 44538632867117631, 23832411522563677, 22149601697210973, 21989137044907655, 24999706290293667,
    23832411522563677, 29133495362424792, 23832411522563677, 39164242358107557, 21989137044907655, 22149601697210973,
    23832411522563677, 22149601697210973, 24999706290293667, 24999706290293667, 35194772398994805, 36176493759580695,
    41331328217905633, 41331311513380845, 36177063093684940, 39409078825381894, 45280401465596611, 45280880318649655,
    39380766665515241, 41331328217905633, 45333855382509430, 27055291445812235, 49714127062330799, 25887996703930951,
    24205186876295294, 24044722204102048, 27055291445812235, 25887996703930951, 31189080541509113, 25887996703930951,
    44333854850133980, 24044722204102048, 24205186876295294, 25887996703930951, 24205186876295294, 27055291445812235,
    27055291445812235, 40348377973348463, 40164242841742325, 45333855382509430, 42333829355779783, 37165142945158398,
    24999706290293667, 27055291445812235, 27055291445812235, 24999694507030712, 37718672584644959, 39409078825381894,
    32715812802113693, 32715812802113693, 38587135442227819, 38587614295280917
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
noncomputable def negativeCeiling : ℝ := 67773069 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 127327329972374529762131968, coefficient := (-127327329972374529762131968) }, { argument := 7453596199407372933623971840, coefficient := (-7453596199407372933623971840) }, { argument := 7456070575206485462014230528, coefficient := (-7456070575206485462014230528) }, { argument := 124852954173262001371873280, coefficient := (-124852954173262001371873280) }, { argument := 21859969489356939421810688, coefficient := (-21859969489356939421810688) }, { argument := 693604075045523354252476416, coefficient := (-693604075045523354252476416) }, { argument := 38677750620870164218904576, coefficient := (-38677750620870164218904576) }, { argument := 7192903779806111873082851328, coefficient := (-7192903779806111873082851328) }, { argument := 34442960406906277625593856, coefficient := (-34442960406906277625593856) }, { argument := 5364067604354256351526912, coefficient := (-5364067604354256351526912) }, { argument := 38395431273272571779350528, coefficient := (-38395431273272571779350528) }, { argument := 38677750620870164218904576, coefficient := (-38677750620870164218904576) }, { argument := 34442960406906277625593856, coefficient := (-34442960406906277625593856) }, { argument := 678978030972209817127485440, coefficient := (-678978030972209817127485440) }, { argument := 34442960406906277625593856, coefficient := (-34442960406906277625593856) }, { argument := 693603842528615242787717120, coefficient := (-693603842528615242787717120) }, { argument := 38395431273272571779350528, coefficient := (-38395431273272571779350528) }, { argument := 5364067604354256351526912, coefficient := (-5364067604354256351526912) }, { argument := 34442960406906277625593856, coefficient := (-34442960406906277625593856) }, { argument := 5364067604354256351526912, coefficient := (-5364067604354256351526912) }, { argument := 38677750620870164218904576, coefficient := (-38677750620870164218904576) }, { argument := 38677750620870164218904576, coefficient := (-38677750620870164218904576) }, { argument := 22138692607661910207234048, coefficient := (-22138692607661910207234048) }, { argument := 21859969489356939421810688, coefficient := (-21859969489356939421810688) }, { argument := 778770238384967227977760768, coefficient := (-778770238384967227977760768) }, { argument := 778761221294681805373308928, coefficient := (-778761221294681805373308928) }, { argument := 21868597842433326287159296, coefficient := (-21868597842433326287159296) }, { argument := 410945865561259972919033856, coefficient := (-410945865561259972919033856) }, { argument := 24056300735860456499215073280, coefficient := (-24056300735860456499215073280) }, { argument := 24064286723666144005378277376, coefficient := (-24064286723666144005378277376) }, { argument := 402959877755572466755829760, coefficient := (-402959877755572466755829760) }, { argument := 778770238384967227977760768, coefficient := (-778770238384967227977760768) }, { argument := 24964339308625259607170744320, coefficient := (-24964339308625259607170744320) }, { argument := 1286305105627009542397100032, coefficient := (-1286305105627009542397100032) }, { argument := 259946063968845376289454948352, coefficient := (-259946063968845376289454948352) }, { argument := 1145468780193395358922964992, coefficient := (-1145468780193395358922964992) }, { argument := 178392678882577965733904384, coefficient := (-178392678882577965733904384) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 1286305105627009542397100032, coefficient := (-1286305105627009542397100032) }, { argument := 1145468780193395358922964992, coefficient := (-1145468780193395358922964992) }, { argument := 22580757511189474083686318080, coefficient := (-22580757511189474083686318080) }, { argument := 1145468780193395358922964992, coefficient := (-1145468780193395358922964992) }, { argument := 24964330096422712778227187712, coefficient := (-24964330096422712778227187712) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 178392678882577965733904384, coefficient := (-178392678882577965733904384) }, { argument := 1145468780193395358922964992, coefficient := (-1145468780193395358922964992) }, { argument := 178392678882577965733904384, coefficient := (-178392678882577965733904384) }, { argument := 1286305105627009542397100032, coefficient := (-1286305105627009542397100032) }, { argument := 1286305105627009542397100032, coefficient := (-1286305105627009542397100032) }, { argument := 788028335504717412544020480, coefficient := (-788028335504717412544020480) }, { argument := 693604075045523354252476416, coefficient := (-693604075045523354252476416) }, { argument := 24964339308625259607170744320, coefficient := (-24964339308625259607170744320) }, { argument := 24963888947162260931702947840, coefficient := (-24963888947162260931702947840) }, { argument := 694036952525962260923809792, coefficient := (-694036952525962260923809792) }, { argument := 38677750620870164218904576, coefficient := (-38677750620870164218904576) }, { argument := 1286305105627009542397100032, coefficient := (-1286305105627009542397100032) }, { argument := 1286305105627009542397100032, coefficient := (-1286305105627009542397100032) }, { argument := 38677434720377901942833152, coefficient := (-38677434720377901942833152) }, { argument := 127327329972374529762131968, coefficient := (-127327329972374529762131968) }, { argument := 410945865561259972919033856, coefficient := (-410945865561259972919033856) }, { argument := 127075185337318420412104704, coefficient := (-127075185337318420412104704) }, { argument := 127075185337318420412104704, coefficient := (-127075185337318420412104704) }, { argument := 7438835940993386440839659520, coefficient := (-7438835940993386440839659520) }, { argument := 7441305416818683494881296384, coefficient := (-7441305416818683494881296384) }] }

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
def constantNumerator : ℤ := (-50118832248754454849331535020032)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    6917006385, 2766715643413, 5543096858665, 139461479, 230874015499783, 62095987,
    19341373, 17305439, 139461479, 62095987, 2448210635, 62095987,
    44344758503811, 17305439, 19341373, 62095987, 19341373, 139461479,
    139461479, 2799607016505, 25554327648813, 923513937212467, 230874015499783, 6392880471649,
    14937253, 62095987, 62095987, 14937131, 13240246586945, 42732574342815,
    412938346905, 4652587, 19341373, 19341373, 4652549, 4162841,
    17305439, 17305439, 4162807, 33547601, 139461479, 139461479,
    33547327, 14937253, 62095987, 62095987, 14937131, 588919565,
    2448210635, 2448210635, 588914755, 14937253, 62095987, 62095987,
    14937131, 77692866691, 154107160927, 33547327, 6392880471649, 14937131,
    4652549, 4162807, 33547327, 14937131
  ]
def negativeCoefficients : Array ℕ := #[
    124605709512021366370467840, 778761221294681805373308928, 24963888947162260931702947840, 1286305105627009542397100032, 259941032543588209156887150592, 1145468780193395358922964992,
    178392678882577965733904384, 1276916017264768596832157696, 1286305105627009542397100032, 1145468780193395358922964992, 22580757511189474083686318080, 1145468780193395358922964992,
    24963879734199731665640620032, 1276916017264768596832157696, 178392678882577965733904384, 1145468780193395358922964992, 178392678882577965733904384, 1286305105627009542397100032,
    1286305105627009542397100032, 788019319769734002801377280, 7192903779806111873082851328, 259946063968845376289454948352, 259941032543588209156887150592, 7197743527485639279536766976,
    34442960406906277625593856, 1145468780193395358922964992, 1145468780193395358922964992, 34442679094059153554931712, 7453596199407372933623971840, 24056300735860456499215073280,
    7438835940993386440839659520, 5364067604354256351526912, 178392678882577965733904384, 178392678882577965733904384, 5364023793337081291341824, 38395431273272571779350528,
    1276916017264768596832157696, 1276916017264768596832157696, 38395117678623318716973056, 38677750620870164218904576, 1286305105627009542397100032, 1286305105627009542397100032,
    38677434720377901942833152, 34442960406906277625593856, 1145468780193395358922964992, 1145468780193395358922964992, 34442679094059153554931712, 678978030972209817127485440,
    22580757511189474083686318080, 22580757511189474083686318080, 678972485419772658193530880, 34442960406906277625593856, 1145468780193395358922964992, 1145468780193395358922964992,
    34442679094059153554931712, 21868597842433326287159296, 694036952525962260923809792, 38677434720377901942833152, 7197743527485639279536766976, 34442679094059153554931712,
    5364023793337081291341824, 38395117678623318716973056, 38677434720377901942833152, 34442679094059153554931712
  ]
def negativeScales : Array ℕ := #[
    32, 41, 42, 27, 47, 25,
    24, 24, 27, 25, 31, 25,
    45, 24, 24, 25, 24, 27,
    27, 41, 44, 49, 47, 42,
    23, 25, 25, 23, 43, 45,
    38, 22, 24, 24, 22, 21,
    24, 24, 21, 24, 27, 27,
    24, 23, 25, 25, 23, 29,
    31, 31, 29, 23, 25, 25,
    23, 36, 37, 24, 42, 23,
    22, 21, 24, 23
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32687500642196297, 41331311513380845, 42333829355779783, 27055291445812235, 47714099137758972, 25887996703930951,
    24205186876295294, 24044722204102048, 27055291445812235, 25887996703930951, 31189080541509113, 25887996703930951,
    45333828823350808, 24044722204102048, 24205186876295294, 25887996703930951, 24205186876295294, 27055291445812235,
    27055291445812235, 41348361467558036, 44538632867117631, 49714127062330799, 47714099137758972, 42539603258524044,
    23832411522563677, 25887996703930951, 25887996703930951, 23832399739304867, 43589995224752333, 45280401465596611,
    38587135442227819, 22149601697210973, 24205186876295294, 24205186876295294, 22149589913952447, 21989137044907655,
    24044722204102048, 24044722204102048, 21989125261645347, 24999706290293667, 27055291445812235, 27055291445812235,
    24999694507030712, 23832411522563677, 25887996703930951, 25887996703930951, 23832399739304867, 29133495362424792,
    31189080541509113, 31189080541509113, 29133483579166266, 23832411522563677, 25887996703930951, 25887996703930951,
    23832399739304867, 36177063093684940, 37165142945158398, 24999694507030712, 42539603258524044, 23832399739304867,
    22149589913952447, 21989125261645347, 24999694507030712, 23832399739304867
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
noncomputable def negativeCeiling : ℝ := 109445951 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 124605709512021366370467840, coefficient := (-124605709512021366370467840) }, { argument := 778761221294681805373308928, coefficient := (-778761221294681805373308928) }, { argument := 24963888947162260931702947840, coefficient := (-24963888947162260931702947840) }, { argument := 1286305105627009542397100032, coefficient := (-1286305105627009542397100032) }, { argument := 259941032543588209156887150592, coefficient := (-259941032543588209156887150592) }, { argument := 1145468780193395358922964992, coefficient := (-1145468780193395358922964992) }, { argument := 178392678882577965733904384, coefficient := (-178392678882577965733904384) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 1286305105627009542397100032, coefficient := (-1286305105627009542397100032) }, { argument := 1145468780193395358922964992, coefficient := (-1145468780193395358922964992) }, { argument := 22580757511189474083686318080, coefficient := (-22580757511189474083686318080) }, { argument := 1145468780193395358922964992, coefficient := (-1145468780193395358922964992) }, { argument := 24963879734199731665640620032, coefficient := (-24963879734199731665640620032) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 178392678882577965733904384, coefficient := (-178392678882577965733904384) }, { argument := 1145468780193395358922964992, coefficient := (-1145468780193395358922964992) }, { argument := 178392678882577965733904384, coefficient := (-178392678882577965733904384) }, { argument := 1286305105627009542397100032, coefficient := (-1286305105627009542397100032) }, { argument := 1286305105627009542397100032, coefficient := (-1286305105627009542397100032) }, { argument := 788019319769734002801377280, coefficient := (-788019319769734002801377280) }, { argument := 7192903779806111873082851328, coefficient := (-7192903779806111873082851328) }, { argument := 259946063968845376289454948352, coefficient := (-259946063968845376289454948352) }, { argument := 259941032543588209156887150592, coefficient := (-259941032543588209156887150592) }, { argument := 7197743527485639279536766976, coefficient := (-7197743527485639279536766976) }, { argument := 34442960406906277625593856, coefficient := (-34442960406906277625593856) }, { argument := 1145468780193395358922964992, coefficient := (-1145468780193395358922964992) }, { argument := 1145468780193395358922964992, coefficient := (-1145468780193395358922964992) }, { argument := 34442679094059153554931712, coefficient := (-34442679094059153554931712) }, { argument := 7453596199407372933623971840, coefficient := (-7453596199407372933623971840) }, { argument := 24056300735860456499215073280, coefficient := (-24056300735860456499215073280) }, { argument := 7438835940993386440839659520, coefficient := (-7438835940993386440839659520) }, { argument := 5364067604354256351526912, coefficient := (-5364067604354256351526912) }, { argument := 178392678882577965733904384, coefficient := (-178392678882577965733904384) }, { argument := 178392678882577965733904384, coefficient := (-178392678882577965733904384) }, { argument := 5364023793337081291341824, coefficient := (-5364023793337081291341824) }, { argument := 38395431273272571779350528, coefficient := (-38395431273272571779350528) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 38395117678623318716973056, coefficient := (-38395117678623318716973056) }, { argument := 38677750620870164218904576, coefficient := (-38677750620870164218904576) }, { argument := 1286305105627009542397100032, coefficient := (-1286305105627009542397100032) }, { argument := 1286305105627009542397100032, coefficient := (-1286305105627009542397100032) }, { argument := 38677434720377901942833152, coefficient := (-38677434720377901942833152) }, { argument := 34442960406906277625593856, coefficient := (-34442960406906277625593856) }, { argument := 1145468780193395358922964992, coefficient := (-1145468780193395358922964992) }, { argument := 1145468780193395358922964992, coefficient := (-1145468780193395358922964992) }, { argument := 34442679094059153554931712, coefficient := (-34442679094059153554931712) }, { argument := 678978030972209817127485440, coefficient := (-678978030972209817127485440) }, { argument := 22580757511189474083686318080, coefficient := (-22580757511189474083686318080) }, { argument := 22580757511189474083686318080, coefficient := (-22580757511189474083686318080) }, { argument := 678972485419772658193530880, coefficient := (-678972485419772658193530880) }, { argument := 34442960406906277625593856, coefficient := (-34442960406906277625593856) }, { argument := 1145468780193395358922964992, coefficient := (-1145468780193395358922964992) }, { argument := 1145468780193395358922964992, coefficient := (-1145468780193395358922964992) }, { argument := 34442679094059153554931712, coefficient := (-34442679094059153554931712) }, { argument := 21868597842433326287159296, coefficient := (-21868597842433326287159296) }, { argument := 694036952525962260923809792, coefficient := (-694036952525962260923809792) }, { argument := 38677434720377901942833152, coefficient := (-38677434720377901942833152) }, { argument := 7197743527485639279536766976, coefficient := (-7197743527485639279536766976) }, { argument := 34442679094059153554931712, coefficient := (-34442679094059153554931712) }, { argument := 5364023793337081291341824, coefficient := (-5364023793337081291341824) }, { argument := 38395117678623318716973056, coefficient := (-38395117678623318716973056) }, { argument := 38677434720377901942833152, coefficient := (-38677434720377901942833152) }, { argument := 34442679094059153554931712, coefficient := (-34442679094059153554931712) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk2
