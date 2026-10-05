import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 3, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk3

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
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    1, 25557, 1288241, 7074807, 644125, 12777,
    183905, 2051143, 512803, 183891
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 241379040405399045452857344, 12167092240516949239473897472, 133639325798286184181491826688, 12167177243113640893087744000, 241350706206501827581575168,
    1736933616064284206049525760, 77489991638181541540448436224, 77492598384480085584606396416, 1736801389802763855983542272
  ]
def positiveScales : Array ℕ := #[
    0, 14, 20, 22, 19, 13,
    17, 20, 18, 17
  ]
def negativeArguments : Array ℕ := #[
    4700060085, 52421061651, 13105706271, 4699702287, 236913961105, 2642366509463,
    660613849523, 236895925731, 4700060085, 236913961105, 1301092381335, 118457808125,
    2349754185, 1301092381335, 14511440854401, 3627982254021, 1300993334037, 52421061651,
    2642366509463, 14511440854401, 1321192484875, 26207454111, 118457808125, 1321192484875,
    330309232375, 118448790375, 13105706271, 660613849523, 3627982254021, 330309232375,
    6552083931, 2349754185, 26207454111, 6552083931, 2349575307, 4699702287,
    236895925731, 1300993334037, 118448790375, 2349575307, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1322949302964058859765760, 59020868429452349458612224, 59022853878502772667580416, 1322848591780341740470272, 66685351684459136423034880, 2975040206848461248147750912,
    2975140286547571716713873408, 66680275177982518452289536, 1322949302964058859765760, 66685351684459136423034880, 732449895469362160620011520, 66685817566359464181760000,
    1322794008997282940190720, 732449895469362160620011520, 32676859812244667849609576448, 32677959054631495526705528832, 732394136797566553810796544, 59020868429452349458612224,
    2975040206848461248147750912, 32676859812244667849609576448, 2975060991283874836250624000, 59013940284314486757654528, 66685817566359464181760000, 2975060991283874836250624000,
    2975161071682169146966016000, 66680741024416999145472000, 59022853878502772667580416, 2975140286547571716713873408, 32677959054631495526705528832, 2975161071682169146966016000,
    59015925500303629250199552, 1322794008997282940190720, 59013940284314486757654528, 59015925500303629250199552, 1322693309635514842742784, 1322848591780341740470272,
    66680275177982518452289536, 732394136797566553810796544, 66680741024416999145472000, 1322693309635514842742784, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    32, 35, 33, 32, 37, 41,
    39, 37, 32, 37, 40, 36,
    31, 40, 43, 41, 40, 35,
    41, 43, 40, 34, 36, 40,
    38, 36, 33, 39, 41, 38,
    32, 31, 34, 32, 31, 32,
    37, 40, 36, 31, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 14641430875491424, 20296971082792624, 22754259361219359, 19296981161815115, 13641261515270434,
    17488601178640939, 20967996644475525, 18968045175602842, 17488491347481371
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32130032054133441, 35609427520844171, 33609476051972194, 32129922222973873, 37785572261913585, 41264967728136983,
    39265016259264997, 37785462430752923, 32130032054133441, 37785572261913585, 40242860539875616, 36785582340936177,
    31129862693912446, 40242860539875616, 43722256006700159, 41722304537828306, 40242750708716048, 35609427520844171,
    41264967728136983, 43722256006700159, 40264977807159474, 34609258160623143, 36785582340936177, 40264977807159474,
    38265026338287487, 36785472509775514, 33609476051972194, 39265016259264997, 41722304537828306, 38265026338287487,
    32609306691751166, 31129862693912446, 34609258160623143, 32609306691751166, 31129752862752878, 32129922222973873,
    37785462430752923, 40242750708716048, 36785472509775514, 31129752862752878, 0, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 80466301 / 1000000000000
noncomputable def negativeCeiling : ℝ := 40233151 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1322949302964058859765760, coefficient := (-1322949302964058859765760) }, { argument := 59020868429452349458612224, coefficient := (-59020868429452349458612224) }, { argument := 59022853878502772667580416, coefficient := (-59022853878502772667580416) }, { argument := 1322848591780341740470272, coefficient := (-1322848591780341740470272) }, { argument := 66685351684459136423034880, coefficient := (-66685351684459136423034880) }, { argument := 2975040206848461248147750912, coefficient := (-2975040206848461248147750912) }, { argument := 2975140286547571716713873408, coefficient := (-2975140286547571716713873408) }, { argument := 66680275177982518452289536, coefficient := (-66680275177982518452289536) }, { argument := 1322949302964058859765760, coefficient := (-1322949302964058859765760) }, { argument := 66685351684459136423034880, coefficient := (-66685351684459136423034880) }, { argument := 732449895469362160620011520, coefficient := (-732449895469362160620011520) }, { argument := 66685817566359464181760000, coefficient := (-66685817566359464181760000) }, { argument := 1322794008997282940190720, coefficient := (-1322794008997282940190720) }, { argument := 732449895469362160620011520, coefficient := (-732449895469362160620011520) }, { argument := 32676859812244667849609576448, coefficient := (-32676859812244667849609576448) }, { argument := 32677959054631495526705528832, coefficient := (-32677959054631495526705528832) }, { argument := 732394136797566553810796544, coefficient := (-732394136797566553810796544) }, { argument := 59020868429452349458612224, coefficient := (-59020868429452349458612224) }, { argument := 2975040206848461248147750912, coefficient := (-2975040206848461248147750912) }, { argument := 32676859812244667849609576448, coefficient := (-32676859812244667849609576448) }, { argument := 2975060991283874836250624000, coefficient := (-2975060991283874836250624000) }, { argument := 59013940284314486757654528, coefficient := (-59013940284314486757654528) }, { argument := 66685817566359464181760000, coefficient := (-66685817566359464181760000) }, { argument := 2975060991283874836250624000, coefficient := (-2975060991283874836250624000) }, { argument := 2975161071682169146966016000, coefficient := (-2975161071682169146966016000) }, { argument := 66680741024416999145472000, coefficient := (-66680741024416999145472000) }, { argument := 59022853878502772667580416, coefficient := (-59022853878502772667580416) }, { argument := 2975140286547571716713873408, coefficient := (-2975140286547571716713873408) }, { argument := 32677959054631495526705528832, coefficient := (-32677959054631495526705528832) }, { argument := 2975161071682169146966016000, coefficient := (-2975161071682169146966016000) }, { argument := 59015925500303629250199552, coefficient := (-59015925500303629250199552) }, { argument := 1322794008997282940190720, coefficient := (-1322794008997282940190720) }, { argument := 59013940284314486757654528, coefficient := (-59013940284314486757654528) }, { argument := 59015925500303629250199552, coefficient := (-59015925500303629250199552) }, { argument := 1322693309635514842742784, coefficient := (-1322693309635514842742784) }, { argument := 1322848591780341740470272, coefficient := (-1322848591780341740470272) }, { argument := 66680275177982518452289536, coefficient := (-66680275177982518452289536) }, { argument := 732394136797566553810796544, coefficient := (-732394136797566553810796544) }, { argument := 66680741024416999145472000, coefficient := (-66680741024416999145472000) }, { argument := 1322693309635514842742784, coefficient := (-1322693309635514842742784) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 241379040405399045452857344, coefficient := 241379040405399045452857344 }, { argument := 12167092240516949239473897472, coefficient := 12167092240516949239473897472 }, { argument := 133639325798286184181491826688, coefficient := 133639325798286184181491826688 }, { argument := 12167177243113640893087744000, coefficient := 12167177243113640893087744000 }, { argument := 241350706206501827581575168, coefficient := 241350706206501827581575168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1736933616064284206049525760, coefficient := 1736933616064284206049525760 }, { argument := 77489991638181541540448436224, coefficient := 77489991638181541540448436224 }, { argument := 77492598384480085584606396416, coefficient := 77492598384480085584606396416 }, { argument := 1736801389802763855983542272, coefficient := 1736801389802763855983542272 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk3
