import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 13, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-163447879960063877782262088948776960)
def positiveArguments : Array ℕ := #[
    79725403213, 509, 79725265843, 257, 124033419849, 285,
    93, 424163455295, 939, 15504177295, 1881, 843,
    285, 93, 1077899491, 5217, 9639886155, 129093,
    4107, 4819910835, 2109, 2109, 71373, 3885,
    129093, 71373, 1078160473, 4107, 3885, 5217,
    14190223, 1493072677, 20349, 15448318393, 20881, 665,
    20349, 11571, 20881, 325983, 399, 746536719,
    20349, 665, 399, 665, 10241, 11571,
    14190197
  ]
def positiveCoefficients : Array ℕ := #[
    752985143932678243960338300010496, 39381967499766159995228389376, 752983846509710740354012289171456, 39768823762042841331134365696, 585731264650616171128029293051904, 176406455598166689173125201920,
    7195526478346272847851159552, 2003055284543285140912054017720320, 145303212111121509766284705792, 585731257619012478135127569858560, 145535325868487518567828291584, 130447931639696946467495215104,
    176406455598166689173125201920, 7195526478346272847851159552, 20360945712802603180774018514944, 100911456014872326471073923072, 728369204432818201044321388462080, 2497021773304181184805510053888,
    79440933458516512328292237312, 728364332083975835459175705477120, 81587985714152093742570405888, 81587985714152093742570405888, 1380554600373678849380862394368, 75146828947245349499735900160,
    2497021773304181184805510053888, 1380554600373678849380862394368, 20365875523400332323762661752832, 79440933458516512328292237312, 75146828947245349499735900160, 100911456014872326471073923072,
    134022866959291891026457788416, 14101672732706511642506647568384, 393606904053409425217535606784, 145905241991603719152248664621056, 403897280629969148752634576896, 12862970720699654418873712640,
    393606904053409425217535606784, 223815690540173986888402599936, 403897280629969148752634576896, 6305428247286970596131893936128, 246969037837433364842375282688, 14101679920148298570106662813696,
    393606904053409425217535606784, 12862970720699654418873712640, 246969037837433364842375282688, 12862970720699654418873712640, 396179498197549356101310349312, 223815690540173986888402599936,
    134022621396234781804906676224
  ]
def positiveScales : Array ℕ := #[
    36, 8, 36, 8, 36, 8,
    6, 38, 9, 33, 10, 9,
    8, 6, 30, 12, 33, 16,
    12, 32, 11, 11, 16, 11,
    16, 16, 30, 12, 11, 12,
    23, 30, 14, 33, 14, 9,
    14, 13, 14, 18, 8, 29,
    14, 9, 8, 9, 13, 13,
    23
  ]
def negativeArguments : Array ℕ := #[
    2325, 19009, 20039, 19007, 2323
  ]
def negativeCoefficients : Array ℕ := #[
    184205477845664584904989684531200, 1506048141233650793315676951937024, 3175306297246686122074054441566208, 1505889684908622264640489864036352, 184047021520636056229802596630528
  ]
def negativeScales : Array ℕ := #[
    11, 14, 14, 14, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    36214320437831868, 8991521844801183, 36214317952009526, 8005624549193878, 36851937939699839, 8154818109052103,
    6539158811107971, 38625829371522111, 9874981347482478, 33851937922380532, 10877284133344468, 9719388820935039,
    8154818109052103, 6539158811107971, 30005575513898466, 12349004718027742, 33166368962621293, 16978051246798597,
    12003869231979055, 32166359311832956, 11042343379793691, 11042343379793691, 16123090793678053, 11923698882884927,
    16978051246798597, 16123090793678053, 30005924778246663, 12003869231979055, 11923698882884927, 12349004718027742,
    23758393925789612, 30475637245979525, 14312670278193841, 33846730752720243, 14349903184392816, 9377210530388551,
    14312670278193841, 13498225931349901, 14349903184392816, 18314437204368028, 8640244936221314, 29475637981302502,
    14312670278193841, 9377210530388551, 8640244936221314, 9377210530388551, 13322068976196090, 13498225931349901,
    23758391282412872
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    11183015000882757, 14214395018164642, 14290522895515831, 14214243219443869, 11181773438808808
  ]

abbrev PositiveTerm := Fin 49
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
noncomputable def positiveFloor : ℝ := 13735754189 / 5000000000
noncomputable def negativeCeiling : ℝ := 555554820039 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 184205477845664584904989684531200, coefficient := (-184205477845664584904989684531200) }, { argument := 752985143932678243960338300010496, coefficient := 752985143932678243960338300010496 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 752983846509710740354012289171456, coefficient := 752983846509710740354012289171456 }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 1506048141233650793315676951937024, coefficient := (-1506048141233650793315676951937024) }, { argument := 585731264650616171128029293051904, coefficient := 585731264650616171128029293051904 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 2003055284543285140912054017720320, coefficient := 2003055284543285140912054017720320 }, { argument := 145303212111121509766284705792, coefficient := 145303212111121509766284705792 }, { argument := 585731257619012478135127569858560, coefficient := 585731257619012478135127569858560 }, { argument := 145535325868487518567828291584, coefficient := 145535325868487518567828291584 }, { argument := 130447931639696946467495215104, coefficient := 130447931639696946467495215104 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 3175306297246686122074054441566208, coefficient := (-3175306297246686122074054441566208) }, { argument := 20360945712802603180774018514944, coefficient := 20360945712802603180774018514944 }, { argument := 100911456014872326471073923072, coefficient := 100911456014872326471073923072 }, { argument := 728369204432818201044321388462080, coefficient := 728369204432818201044321388462080 }, { argument := 2497021773304181184805510053888, coefficient := 2497021773304181184805510053888 }, { argument := 79440933458516512328292237312, coefficient := 79440933458516512328292237312 }, { argument := 728364332083975835459175705477120, coefficient := 728364332083975835459175705477120 }, { argument := 81587985714152093742570405888, coefficient := 81587985714152093742570405888 }, { argument := 81587985714152093742570405888, coefficient := 81587985714152093742570405888 }, { argument := 1380554600373678849380862394368, coefficient := 1380554600373678849380862394368 }, { argument := 75146828947245349499735900160, coefficient := 75146828947245349499735900160 }, { argument := 2497021773304181184805510053888, coefficient := 2497021773304181184805510053888 }, { argument := 1380554600373678849380862394368, coefficient := 1380554600373678849380862394368 }, { argument := 20365875523400332323762661752832, coefficient := 20365875523400332323762661752832 }, { argument := 79440933458516512328292237312, coefficient := 79440933458516512328292237312 }, { argument := 75146828947245349499735900160, coefficient := 75146828947245349499735900160 }, { argument := 100911456014872326471073923072, coefficient := 100911456014872326471073923072 }, { argument := 1505889684908622264640489864036352, coefficient := (-1505889684908622264640489864036352) }, { argument := 134022866959291891026457788416, coefficient := 134022866959291891026457788416 }, { argument := 14101672732706511642506647568384, coefficient := 14101672732706511642506647568384 }, { argument := 393606904053409425217535606784, coefficient := 393606904053409425217535606784 }, { argument := 145905241991603719152248664621056, coefficient := 145905241991603719152248664621056 }, { argument := 403897280629969148752634576896, coefficient := 403897280629969148752634576896 }, { argument := 12862970720699654418873712640, coefficient := 12862970720699654418873712640 }, { argument := 393606904053409425217535606784, coefficient := 393606904053409425217535606784 }, { argument := 223815690540173986888402599936, coefficient := 223815690540173986888402599936 }, { argument := 403897280629969148752634576896, coefficient := 403897280629969148752634576896 }, { argument := 6305428247286970596131893936128, coefficient := 6305428247286970596131893936128 }, { argument := 246969037837433364842375282688, coefficient := 246969037837433364842375282688 }, { argument := 14101679920148298570106662813696, coefficient := 14101679920148298570106662813696 }, { argument := 393606904053409425217535606784, coefficient := 393606904053409425217535606784 }, { argument := 12862970720699654418873712640, coefficient := 12862970720699654418873712640 }, { argument := 246969037837433364842375282688, coefficient := 246969037837433364842375282688 }, { argument := 12862970720699654418873712640, coefficient := 12862970720699654418873712640 }, { argument := 396179498197549356101310349312, coefficient := 396179498197549356101310349312 }, { argument := 223815690540173986888402599936, coefficient := 223815690540173986888402599936 }, { argument := 134022621396234781804906676224, coefficient := 134022621396234781804906676224 }, { argument := 184047021520636056229802596630528, coefficient := (-184047021520636056229802596630528) }] }

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

end TermShard4


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13
