import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 15, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-167534118637535299402722673095081984)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1165813, 58974793, 1013, 9752037527, 159, 71,
    2019, 1031, 159, 31695, 2029, 943598385,
    2019, 71, 2029, 71, 2019, 517,
    1165813, 19888750774684111, 263, 389441057689310527, 2867, 127,
    194720559400165627, 127, 251, 4999, 255, 2867,
    4999, 19888899890595783, 251, 255, 263, 126889571714585737,
    232106593476133923, 126883386830136113, 9954373659264273, 9954373829655279, 19, 19,
    2304549, 19888751095084593, 263, 389441064030300865, 2867, 127,
    194720562570649349, 127, 251, 4999, 255, 2867,
    4999, 19888900210964537, 251, 255, 263, 232106269669219117,
    1698754070939079971, 464188588358153347, 389819255766635791, 389819262508477169
  ]
def negativeCoefficients : Array ℕ := #[
    44043169891949677564116598784, 8912018745516011918757195677696, 39188539368627819327275401216, 92105390314383565546278652739584, 24604058280796932963620093952, 1373339731082218742466215936,
    39053139676830980859708309504, 39884880640725845731906158592, 24604058280796932963620093952, 613070461642970747076995973120, 39246567807969321527661297664, 8912034773227854778333050961920,
    39053139676830980859708309504, 1373339731082218742466215936, 39246567807969321527661297664, 1373339731082218742466215936, 39053139676830980859708309504, 40000937519408850132677951488,
    44043169891949677564116598784, 5598185661108251621840247586816, 2543579924469179783581794304, 219235825286543840674254027751424, 27727922598681134751060852736, 2456537265456926483002949632,
    219235859688990112467736223285248, 2456537265456926483002949632, 2427523045786175382810001408, 96694722756056499909698781184, 2466208672013843516400599040, 27727922598681134751060852736,
    96694722756056499909698781184, 5598227633506016686277444763648, 2427523045786175382810001408, 2466208672013843516400599040, 2543579924469179783581794304, 71432478486376269296835907026944,
    261328791972337983370345108733952, 71428996705963437269130995040256, 5603814187821157575061118386176, 5603814283742766466171611906048, 2940107593302778152885420032, 2940107593302778152885420032,
    43531699822923032030311612416, 5598185751292969830873204523008, 2543579924469179783581794304, 219235828856204056096343463034880, 27727922598681134751060852736, 2456537265456926483002949632,
    219235863258637439713592031051776, 2456537265456926483002949632, 2427523045786175382810001408, 96694722756056499909698781184, 2466208672013843516400599040, 27727922598681134751060852736,
    96694722756056499909698781184, 5598227723681804257249326006272, 2427523045786175382810001408, 2466208672013843516400599040, 2543579924469179783581794304, 261328427398162768297459091243008,
    956313525109419210673177023741952, 261314944194926996398792993931264, 219448731876558127797120681377792, 219448735671877417516094590025728
  ]
def negativeScales : Array ℕ := #[
    20, 25, 9, 33, 7, 6,
    10, 10, 7, 14, 10, 29,
    10, 6, 10, 6, 10, 9,
    20, 54, 8, 58, 11, 6,
    57, 6, 7, 12, 7, 11,
    12, 54, 7, 7, 8, 56,
    57, 56, 53, 53, 4, 4,
    21, 54, 8, 58, 11, 6,
    57, 6, 7, 12, 7, 11,
    12, 54, 7, 7, 8, 57,
    60, 58, 58, 58
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    20152904963687130, 25813595114713062, 9984418477228694, 33183056531617134, 7312882955284356, 6149747119504683,
    10979425212320825, 10009828617368109, 7312882955284356, 14951967658319262, 10986553168832949, 29813597709308142,
    10979425212320825, 6149747119504683, 10986553168832949, 6149747119504683, 10979425212320825, 9014020470314935,
    20152904963687130, 54142802180605389, 8038918989292303, 58434182604493741, 11485326189240689, 6988684706517367,
    57434182830881170, 6988684706517367, 7971543568880765, 12287423811683524, 7994353458490620, 11485326189240689,
    12287423811683524, 54142812997171108, 7971543568880765, 7994353458490620, 8038918989292303, 56816351121666425,
    57687565119191575, 56816280799735068, 53144251966066750, 53144251990761650, 4247927513443586, 4247927513443586,
    21136053012331980, 54142802203846676, 8038918989292303, 58434182627984113, 11485326189240689, 6988684706517367,
    57434182854371453, 6988684706517367, 7971543568880765, 12287423811683524, 7994353458490620, 11485326189240689,
    12287423811683524, 54142813020409920, 7971543568880765, 7994353458490620, 8038918989292303, 57687563106517356,
    60559182716283548, 58687488668950441, 58435582969747943, 58435582994699048
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
noncomputable def negativeCeiling : ℝ := 72730721009 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 44043169891949677564116598784, coefficient := (-44043169891949677564116598784) }, { argument := 8912018745516011918757195677696, coefficient := (-8912018745516011918757195677696) }, { argument := 39188539368627819327275401216, coefficient := (-39188539368627819327275401216) }, { argument := 92105390314383565546278652739584, coefficient := (-92105390314383565546278652739584) }, { argument := 24604058280796932963620093952, coefficient := (-24604058280796932963620093952) }, { argument := 1373339731082218742466215936, coefficient := (-1373339731082218742466215936) }, { argument := 39053139676830980859708309504, coefficient := (-39053139676830980859708309504) }, { argument := 39884880640725845731906158592, coefficient := (-39884880640725845731906158592) }, { argument := 24604058280796932963620093952, coefficient := (-24604058280796932963620093952) }, { argument := 613070461642970747076995973120, coefficient := (-613070461642970747076995973120) }, { argument := 39246567807969321527661297664, coefficient := (-39246567807969321527661297664) }, { argument := 8912034773227854778333050961920, coefficient := (-8912034773227854778333050961920) }, { argument := 39053139676830980859708309504, coefficient := (-39053139676830980859708309504) }, { argument := 1373339731082218742466215936, coefficient := (-1373339731082218742466215936) }, { argument := 39246567807969321527661297664, coefficient := (-39246567807969321527661297664) }, { argument := 1373339731082218742466215936, coefficient := (-1373339731082218742466215936) }, { argument := 39053139676830980859708309504, coefficient := (-39053139676830980859708309504) }, { argument := 40000937519408850132677951488, coefficient := (-40000937519408850132677951488) }, { argument := 44043169891949677564116598784, coefficient := (-44043169891949677564116598784) }, { argument := 5598185661108251621840247586816, coefficient := (-5598185661108251621840247586816) }, { argument := 2543579924469179783581794304, coefficient := (-2543579924469179783581794304) }, { argument := 219235825286543840674254027751424, coefficient := (-219235825286543840674254027751424) }, { argument := 27727922598681134751060852736, coefficient := (-27727922598681134751060852736) }, { argument := 2456537265456926483002949632, coefficient := (-2456537265456926483002949632) }, { argument := 219235859688990112467736223285248, coefficient := (-219235859688990112467736223285248) }, { argument := 2456537265456926483002949632, coefficient := (-2456537265456926483002949632) }, { argument := 2427523045786175382810001408, coefficient := (-2427523045786175382810001408) }, { argument := 96694722756056499909698781184, coefficient := (-96694722756056499909698781184) }, { argument := 2466208672013843516400599040, coefficient := (-2466208672013843516400599040) }, { argument := 27727922598681134751060852736, coefficient := (-27727922598681134751060852736) }, { argument := 96694722756056499909698781184, coefficient := (-96694722756056499909698781184) }, { argument := 5598227633506016686277444763648, coefficient := (-5598227633506016686277444763648) }, { argument := 2427523045786175382810001408, coefficient := (-2427523045786175382810001408) }, { argument := 2466208672013843516400599040, coefficient := (-2466208672013843516400599040) }, { argument := 2543579924469179783581794304, coefficient := (-2543579924469179783581794304) }, { argument := 71432478486376269296835907026944, coefficient := (-71432478486376269296835907026944) }, { argument := 261328791972337983370345108733952, coefficient := (-261328791972337983370345108733952) }, { argument := 71428996705963437269130995040256, coefficient := (-71428996705963437269130995040256) }, { argument := 5603814187821157575061118386176, coefficient := (-5603814187821157575061118386176) }, { argument := 5603814283742766466171611906048, coefficient := (-5603814283742766466171611906048) }, { argument := 2940107593302778152885420032, coefficient := (-2940107593302778152885420032) }, { argument := 2940107593302778152885420032, coefficient := (-2940107593302778152885420032) }, { argument := 43531699822923032030311612416, coefficient := (-43531699822923032030311612416) }, { argument := 5598185751292969830873204523008, coefficient := (-5598185751292969830873204523008) }, { argument := 2543579924469179783581794304, coefficient := (-2543579924469179783581794304) }, { argument := 219235828856204056096343463034880, coefficient := (-219235828856204056096343463034880) }, { argument := 27727922598681134751060852736, coefficient := (-27727922598681134751060852736) }, { argument := 2456537265456926483002949632, coefficient := (-2456537265456926483002949632) }, { argument := 219235863258637439713592031051776, coefficient := (-219235863258637439713592031051776) }, { argument := 2456537265456926483002949632, coefficient := (-2456537265456926483002949632) }, { argument := 2427523045786175382810001408, coefficient := (-2427523045786175382810001408) }, { argument := 96694722756056499909698781184, coefficient := (-96694722756056499909698781184) }, { argument := 2466208672013843516400599040, coefficient := (-2466208672013843516400599040) }, { argument := 27727922598681134751060852736, coefficient := (-27727922598681134751060852736) }, { argument := 96694722756056499909698781184, coefficient := (-96694722756056499909698781184) }, { argument := 5598227723681804257249326006272, coefficient := (-5598227723681804257249326006272) }, { argument := 2427523045786175382810001408, coefficient := (-2427523045786175382810001408) }, { argument := 2466208672013843516400599040, coefficient := (-2466208672013843516400599040) }, { argument := 2543579924469179783581794304, coefficient := (-2543579924469179783581794304) }, { argument := 261328427398162768297459091243008, coefficient := (-261328427398162768297459091243008) }, { argument := 956313525109419210673177023741952, coefficient := (-956313525109419210673177023741952) }, { argument := 261314944194926996398792993931264, coefficient := (-261314944194926996398792993931264) }, { argument := 219448731876558127797120681377792, coefficient := (-219448731876558127797120681377792) }, { argument := 219448735671877417516094590025728, coefficient := (-219448735671877417516094590025728) }] }

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


end Parent1

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 372663966320724488793692221791535104
def positiveArguments : Array ℕ := #[
    13595, 31, 35, 15, 395, 35,
    15, 35, 35, 1451, 9, 395,
    1451, 31, 35, 9, 35
  ]
def positiveCoefficients : Array ℕ := #[
    4308427477525694678336920019271680, 4797017652230848565234106368, 5415987671873538702683668480, 4642275147320176030871715840, 61123289439715651073144258560, 5415987671873538702683668480,
    4642275147320176030871715840, 5415987671873538702683668480, 5415987671873538702683668480, 224531374625385847359828656128, 5570730176784211237046059008, 61123289439715651073144258560,
    224531374625385847359828656128, 4797017652230848565234106368, 5415987671873538702683668480, 5570730176784211237046059008, 5415987671873538702683668480
  ]
def positiveScales : Array ℕ := #[
    13, 4, 5, 3, 8, 5,
    3, 5, 5, 10, 3, 8,
    10, 4, 5, 3, 5
  ]
def negativeArguments : Array ℕ := #[
    103, 103, 232583735, 73, 73, 1013,
    126883407714284829, 464189311090549399, 31719306470205971, 779638633008727007, 779638646492363809, 9610897189,
    73, 73, 159, 71, 9, 9,
    2849, 2849, 2019, 73, 73, 1031,
    103, 103, 159, 2849, 2849, 31695,
    2029, 19908896258279393, 19908896599029791, 930336619, 2019, 9,
    9, 71, 73, 73, 2029, 71,
    19, 19, 2019, 517, 2304549
  ]
def negativeCoefficients : Array ℕ := #[
    31876956011598542078652448768, 31876956011598542078652448768, 8786765076997084815410310676480, 2824050714619773752113627136, 2824050714619773752113627136, 39188539368627819327275401216,
    71429008462693984185083806875648, 261315351057095689945409795391488, 71425528399835086889379124215808, 219448766068859114465326731886592, 219448769864165469283220879048704, 90772357511279379675476381401088,
    2824050714619773752113627136, 2824050714619773752113627136, 24604058280796932963620093952, 1373339731082218742466215936, 2785365088392105618523029504, 2785365088392105618523029504,
    110215349122626512599612653568, 110215349122626512599612653568, 39053139676830980859708309504, 2824050714619773752113627136, 2824050714619773752113627136, 39884880640725845731906158592,
    31876956011598542078652448768, 31876956011598542078652448768, 24604058280796932963620093952, 110215349122626512599612653568, 110215349122626512599612653568, 613070461642970747076995973120,
    39246567807969321527661297664, 5603856110634058525293368311808, 5603856206546768866490131152896, 8786780934703734291678938267648, 39053139676830980859708309504, 2785365088392105618523029504,
    2785365088392105618523029504, 1373339731082218742466215936, 2824050714619773752113627136, 2824050714619773752113627136, 39246567807969321527661297664, 1373339731082218742466215936,
    2940107593302778152885420032, 2940107593302778152885420032, 39053139676830980859708309504, 40000937519408850132677951488, 43531699822923032030311612416
  ]
def negativeScales : Array ℕ := #[
    6, 6, 27, 6, 6, 9,
    56, 58, 54, 59, 59, 33,
    6, 6, 7, 6, 3, 3,
    11, 11, 10, 6, 6, 10,
    6, 6, 7, 11, 11, 14,
    10, 54, 54, 29, 10, 3,
    3, 6, 6, 6, 10, 6,
    4, 4, 10, 9, 21
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13730788530903005, 4954196309696329, 5129283016944966, 3906890595303263, 8625708843063759, 5129283016944966,
    3906890595303263, 5129283016944966, 5129283016944966, 10502831804066725, 3169925001442312, 8625708843063759,
    10502831804066725, 4954196309696329, 5129283016944966, 3169925001442312, 5129283016944966
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6686500527235738, 6686500527235738, 27793174969733558, 6189824558880018, 6189824558880018, 9984418477228694,
    56816281037192915, 58687490915196168, 54816210746537406, 59435583194534201, 59435583219485217, 33162023968617300,
    6189824558880018, 6189824558880018, 7312882955284356, 6149747119504683, 3169925001442313, 3169925001442313,
    11476239906323972, 11476239906323972, 10979425212320825, 6189824558880018, 6189824558880018, 10009828617368109,
    6686500527235738, 6686500527235738, 7312882955284356, 11476239906323972, 11476239906323972, 14951967658319262,
    10986553168832949, 54144262759002777, 54144262783695201, 29793177573401024, 10979425212320825, 3169925001442313,
    3169925001442313, 6149747119504683, 6189824558880018, 6189824558880018, 10986553168832949, 6149747119504683,
    4247927513443586, 4247927513443586, 10979425212320825, 9014020470314935, 21136053012331980
  ]

abbrev PositiveTerm := Fin 17
abbrev NegativeTerm := Fin 47
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
noncomputable def positiveFloor : ℝ := 356081355367 / 500000000000
noncomputable def negativeCeiling : ℝ := 2013897969 / 3125000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 31876956011598542078652448768, coefficient := (-31876956011598542078652448768) }, { argument := 31876956011598542078652448768, coefficient := (-31876956011598542078652448768) }, { argument := 8786765076997084815410310676480, coefficient := (-8786765076997084815410310676480) }, { argument := 2824050714619773752113627136, coefficient := (-2824050714619773752113627136) }, { argument := 2824050714619773752113627136, coefficient := (-2824050714619773752113627136) }, { argument := 39188539368627819327275401216, coefficient := (-39188539368627819327275401216) }, { argument := 71429008462693984185083806875648, coefficient := (-71429008462693984185083806875648) }, { argument := 261315351057095689945409795391488, coefficient := (-261315351057095689945409795391488) }, { argument := 71425528399835086889379124215808, coefficient := (-71425528399835086889379124215808) }, { argument := 219448766068859114465326731886592, coefficient := (-219448766068859114465326731886592) }, { argument := 219448769864165469283220879048704, coefficient := (-219448769864165469283220879048704) }, { argument := 90772357511279379675476381401088, coefficient := (-90772357511279379675476381401088) }, { argument := 2824050714619773752113627136, coefficient := (-2824050714619773752113627136) }, { argument := 2824050714619773752113627136, coefficient := (-2824050714619773752113627136) }, { argument := 24604058280796932963620093952, coefficient := (-24604058280796932963620093952) }, { argument := 1373339731082218742466215936, coefficient := (-1373339731082218742466215936) }, { argument := 2785365088392105618523029504, coefficient := (-2785365088392105618523029504) }, { argument := 2785365088392105618523029504, coefficient := (-2785365088392105618523029504) }, { argument := 110215349122626512599612653568, coefficient := (-110215349122626512599612653568) }, { argument := 110215349122626512599612653568, coefficient := (-110215349122626512599612653568) }, { argument := 39053139676830980859708309504, coefficient := (-39053139676830980859708309504) }, { argument := 2824050714619773752113627136, coefficient := (-2824050714619773752113627136) }, { argument := 2824050714619773752113627136, coefficient := (-2824050714619773752113627136) }, { argument := 39884880640725845731906158592, coefficient := (-39884880640725845731906158592) }, { argument := 31876956011598542078652448768, coefficient := (-31876956011598542078652448768) }, { argument := 31876956011598542078652448768, coefficient := (-31876956011598542078652448768) }, { argument := 24604058280796932963620093952, coefficient := (-24604058280796932963620093952) }, { argument := 110215349122626512599612653568, coefficient := (-110215349122626512599612653568) }, { argument := 110215349122626512599612653568, coefficient := (-110215349122626512599612653568) }, { argument := 613070461642970747076995973120, coefficient := (-613070461642970747076995973120) }, { argument := 39246567807969321527661297664, coefficient := (-39246567807969321527661297664) }, { argument := 5603856110634058525293368311808, coefficient := (-5603856110634058525293368311808) }, { argument := 5603856206546768866490131152896, coefficient := (-5603856206546768866490131152896) }, { argument := 8786780934703734291678938267648, coefficient := (-8786780934703734291678938267648) }, { argument := 39053139676830980859708309504, coefficient := (-39053139676830980859708309504) }, { argument := 2785365088392105618523029504, coefficient := (-2785365088392105618523029504) }, { argument := 2785365088392105618523029504, coefficient := (-2785365088392105618523029504) }, { argument := 1373339731082218742466215936, coefficient := (-1373339731082218742466215936) }, { argument := 2824050714619773752113627136, coefficient := (-2824050714619773752113627136) }, { argument := 2824050714619773752113627136, coefficient := (-2824050714619773752113627136) }, { argument := 39246567807969321527661297664, coefficient := (-39246567807969321527661297664) }, { argument := 1373339731082218742466215936, coefficient := (-1373339731082218742466215936) }, { argument := 2940107593302778152885420032, coefficient := (-2940107593302778152885420032) }, { argument := 2940107593302778152885420032, coefficient := (-2940107593302778152885420032) }, { argument := 39053139676830980859708309504, coefficient := (-39053139676830980859708309504) }, { argument := 40000937519408850132677951488, coefficient := (-40000937519408850132677951488) }, { argument := 43531699822923032030311612416, coefficient := (-43531699822923032030311612416) }, { argument := 4308427477525694678336920019271680, coefficient := 4308427477525694678336920019271680 }, { argument := 4797017652230848565234106368, coefficient := 4797017652230848565234106368 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 61123289439715651073144258560, coefficient := 61123289439715651073144258560 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 224531374625385847359828656128, coefficient := 224531374625385847359828656128 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 61123289439715651073144258560, coefficient := 61123289439715651073144258560 }, { argument := 224531374625385847359828656128, coefficient := 224531374625385847359828656128 }, { argument := 4797017652230848565234106368, coefficient := 4797017652230848565234106368 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15
