import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 10, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk10

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    225, 257, 719, 723, 1171, 2609,
    2613, 4695, 8191, 8581, 17115, 20079,
    35939, 36051, 55773
  ]
def positiveCoefficients : Array ℕ := #[
    1952815749651587393005671287881728, 161466995204070720015642570784768, 1071402441680396637277494840393728, 1073145461255710452704552807301120, 56489679872670472704196836589568, 74870613575979799025899033067520,
    75266754388551120713866752819200, 56648136197699001379383924490240, 2258794913281676264791938024079360, 919046685165466316085109823897600, 917779034565238086683613120692224, 2467402665181734265675739245314048,
    1004375416193329007673356658409472, 1003900047218243421647795394707456, 8837584615816129801209453484179456
  ]
def positiveScales : Array ℕ := #[
    7, 8, 9, 9, 10, 11,
    11, 12, 12, 13, 14, 14,
    15, 15, 15
  ]
def negativeArguments : Array ℕ := #[
    3, 7, 59, 95, 97, 117,
    229, 377, 383, 387, 399, 453,
    695, 721, 1019, 1385, 1733, 2019,
    2883, 3081, 3973, 3977, 6919, 8253,
    13523, 13545, 15929472825091
  ]
def negativeCoefficients : Array ℕ := #[
    1901475900342344102245054808064, 1109194275199700726309615304704, 18697846353366383672076372279296, 7526675438855112071386675281920, 7685131763883640746573763182592, 18539390028337854996889284378624,
    36286498431533066617843129253888, 29869017267877655272766069276672, 30344386242963241298327332978688, 30661298893020298648701508780032, 31612036843191470699824036184064, 35890357618961744929875409502208,
    110127145894827429255026090967040, 456988041382276699239561505538048, 161466995204070720015642570784768, 109731005082256107567058371215360, 549209622548880388198446663729152, 159961660116299697601365235728384,
    456829585057248170564374417637376, 1952815749651587393005671287881728, 314773489669172213259150114684928, 315090402319229270609524290486272, 548179656436194951809730592374784, 1307740050460447156319036444246016,
    1071402441680396637277494840393728, 1073145461255710452704552807301120, 4418792307908064900604726742089728
  ]
def negativeScales : Array ℕ := #[
    1, 2, 5, 6, 6, 6,
    7, 8, 8, 8, 8, 8,
    9, 9, 9, 10, 10, 10,
    11, 11, 11, 11, 12, 13,
    13, 13, 43
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7813781191164178, 8005624549193878, 9489847960439285, 9497851836951101, 10193525360501214, 11349281228817451,
    11351491409320020, 12196909442541136, 12999823877560230, 13066930068864097, 14062973671897200, 14293399799686452,
    15133262646073649, 15137751657740418, 15767279254393674
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2807354922807594, 5882643052550791, 6569855608333349, 6599912842192769, 6870364722125690,
    7839203789504465, 8558420713270378, 8581200581928289, 8596189756149498, 8640244936238936, 8823367241078867,
    9440869167610903, 9493855449241043, 9992938357311545, 10435670260936578, 10759055939433919, 10979425212320825,
    11493355121495124, 11589182967043532, 11956013089622061, 11957464858623144, 12756347825774770, 13010702925037367,
    13723127620420826, 13725472773219691, 43856763758162026
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 27
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
noncomputable def positiveFloor : ℝ := 1800568045721 / 500000000000
noncomputable def negativeCeiling : ℝ := 72329890203 / 20000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-1901475900342344102245054808064) }, { argument := 7, coefficient := (-1109194275199700726309615304704) }, { argument := 59, coefficient := (-18697846353366383672076372279296) }, { argument := 95, coefficient := (-7526675438855112071386675281920) }, { argument := 97, coefficient := (-7685131763883640746573763182592) }, { argument := 117, coefficient := (-18539390028337854996889284378624) }, { argument := 225, coefficient := 1952815749651587393005671287881728 }, { argument := 229, coefficient := (-36286498431533066617843129253888) }, { argument := 257, coefficient := 161466995204070720015642570784768 }, { argument := 377, coefficient := (-29869017267877655272766069276672) }, { argument := 383, coefficient := (-30344386242963241298327332978688) }, { argument := 387, coefficient := (-30661298893020298648701508780032) }, { argument := 399, coefficient := (-31612036843191470699824036184064) }, { argument := 453, coefficient := (-35890357618961744929875409502208) }, { argument := 695, coefficient := (-110127145894827429255026090967040) }, { argument := 719, coefficient := 1071402441680396637277494840393728 }, { argument := 721, coefficient := (-456988041382276699239561505538048) }, { argument := 723, coefficient := 1073145461255710452704552807301120 }, { argument := 1019, coefficient := (-161466995204070720015642570784768) }, { argument := 1171, coefficient := 56489679872670472704196836589568 }, { argument := 1385, coefficient := (-109731005082256107567058371215360) }, { argument := 1733, coefficient := (-549209622548880388198446663729152) }, { argument := 2019, coefficient := (-159961660116299697601365235728384) }, { argument := 2609, coefficient := 74870613575979799025899033067520 }, { argument := 2613, coefficient := 75266754388551120713866752819200 }, { argument := 2883, coefficient := (-456829585057248170564374417637376) }, { argument := 3081, coefficient := (-1952815749651587393005671287881728) }, { argument := 3973, coefficient := (-314773489669172213259150114684928) }, { argument := 3977, coefficient := (-315090402319229270609524290486272) }, { argument := 4695, coefficient := 56648136197699001379383924490240 }, { argument := 6919, coefficient := (-548179656436194951809730592374784) }, { argument := 8191, coefficient := 2258794913281676264791938024079360 }, { argument := 8253, coefficient := (-1307740050460447156319036444246016) }, { argument := 8581, coefficient := 919046685165466316085109823897600 }, { argument := 13523, coefficient := (-1071402441680396637277494840393728) }, { argument := 13545, coefficient := (-1073145461255710452704552807301120) }, { argument := 17115, coefficient := 917779034565238086683613120692224 }, { argument := 20079, coefficient := 2467402665181734265675739245314048 }, { argument := 35939, coefficient := 1004375416193329007673356658409472 }, { argument := 36051, coefficient := 1003900047218243421647795394707456 }, { argument := 55773, coefficient := 8837584615816129801209453484179456 }, { argument := 15929472825091, coefficient := (-4418792307908064900604726742089728) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  rfl

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk10
