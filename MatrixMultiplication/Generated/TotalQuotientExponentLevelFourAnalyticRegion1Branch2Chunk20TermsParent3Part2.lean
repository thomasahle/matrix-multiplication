import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 20, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk20

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 18348227337972764429434716732522496
def positiveArguments : Array ℕ := #[
    297, 135, 105, 15, 141, 1665,
    117, 105, 1665, 15, 117, 117,
    117, 117, 117, 135, 141, 5,
    21, 91, 3, 3, 7, 91,
    91, 3, 1123, 45, 21, 91,
    7, 45, 7, 91, 91, 3,
    727, 13813
  ]
def positiveCoefficients : Array ℕ := #[
    188246114133892066122260425998336, 5222559540735198034730680320, 4061990753905154027012751360, 4642275147320176030871715840, 5454673298101206836274266112, 64411567669067442428345057280,
    144838984596389492163197534208, 4061990753905154027012751360, 64411567669067442428345057280, 4642275147320176030871715840, 4526218268637171630099922944, 4526218268637171630099922944,
    4526218268637171630099922944, 144838984596389492163197534208, 4526218268637171630099922944, 5222559540735198034730680320, 5454673298101206836274266112, 24758800785707605497982484480,
    415947853199887772366105739264, 901220348599756840126562435072, 29710560942849126597578981376, 475368975085586025561263702016, 34662321099990647697175478272, 901220348599756840126562435072,
    901220348599756840126562435072, 475368975085586025561263702016, 11121653312939856389693732028416, 891316828285473797927369441280, 415947853199887772366105739264, 901220348599756840126562435072,
    34662321099990647697175478272, 891316828285473797927369441280, 34662321099990647697175478272, 901220348599756840126562435072, 901220348599756840126562435072, 29710560942849126597578981376,
    449991204280235729925831655424, 534364555082779929286925090816
  ]
def positiveScales : Array ℕ := #[
    8, 7, 6, 3, 7, 10,
    6, 6, 10, 3, 6, 6,
    6, 6, 6, 7, 7, 2,
    4, 6, 1, 1, 2, 6,
    6, 1, 10, 5, 4, 6,
    2, 5, 2, 6, 6, 1,
    9, 13
  ]
def negativeArguments : Array ℕ := #[
    17779914675, 9776662605, 5715, 5715, 117, 889,
    889, 117, 20639621055, 37535375425, 20639621055, 11557,
    11557, 117, 11557, 11557, 117, 117,
    222710373, 2470747, 222710373, 2470747, 375275, 141,
    3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    163990767831058869232494182400, 45086898242360384228866129920, 221088353891123383470265466880, 221088353891123383470265466880, 2263109134318585815049961472, 8597880429099242690510323712,
    8597880429099242690510323712, 2263109134318585815049961472, 47591725922491516686025359360, 173101366043895473078743859200, 47591725922491516686025359360, 223544891156580309953268416512,
    223544891156580309953268416512, 2263109134318585815049961472, 223544891156580309953268416512, 223544891156580309953268416512, 72419492298194746081598767104, 2263109134318585815049961472,
    8216562506582787468124225536, 91154475159771307053154304, 8216562506582787468124225536, 91154475159771307053154304, 3544372163717812215139532800, 2727336649050603418137133056,
    475368975085586025561263702016, 20282409603651670423947251286016
  ]
def negativeScales : Array ℕ := #[
    34, 33, 12, 12, 6, 9,
    9, 6, 34, 35, 34, 13,
    13, 6, 13, 13, 6, 6,
    27, 21, 27, 21, 18, 7,
    1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8214319120800765, 7076815597050830, 6714245517659862, 3906890595303263, 7139551352398793, 10701306461953989,
    6870364719426147, 6714245517659862, 10701306461953989, 3906890595303263, 6870364719426147, 6870364719426147,
    6870364719426147, 6870364719426147, 6870364719426147, 7076815597050830, 7139551352398793, 2321928094887362,
    4392317422778759, 6507794640198673, 1584962500720924, 1584962500720924, 2807354922011143, 6507794640198673,
    6507794640198673, 1584962500720924, 10133142212400601, 5491853096329661, 4392317422778759, 6507794640198673,
    2807354922011143, 5491853096329661, 2807354922011143, 6507794640198673, 6507794640198673, 1584962500720924,
    9505811553919573, 13753739067348048
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    34049529349630186, 33186694919886862, 12480537783101981, 12480537783101981, 6870364722125690, 9796039609425563,
    9796039609425563, 6870364722125690, 34264697431888135, 35127531861631459, 34264697431888135, 13496479326971103,
    13496479326971103, 6870364722125690, 13496479326971103, 13496479326971103, 6870364722125690, 6870364722125690,
    27730593514169912, 21236515858205170, 27730593514169912, 21236515858205170, 18517588658674013, 7139551352398794,
    1584962500724866, 0
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 5190856389 / 250000000000
noncomputable def negativeCeiling : ℝ := 433759627 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 163990767831058869232494182400, coefficient := (-163990767831058869232494182400) }, { argument := 45086898242360384228866129920, coefficient := (-45086898242360384228866129920) }, { argument := 221088353891123383470265466880, coefficient := (-221088353891123383470265466880) }, { argument := 221088353891123383470265466880, coefficient := (-221088353891123383470265466880) }, { argument := 2263109134318585815049961472, coefficient := (-2263109134318585815049961472) }, { argument := 8597880429099242690510323712, coefficient := (-8597880429099242690510323712) }, { argument := 8597880429099242690510323712, coefficient := (-8597880429099242690510323712) }, { argument := 2263109134318585815049961472, coefficient := (-2263109134318585815049961472) }, { argument := 47591725922491516686025359360, coefficient := (-47591725922491516686025359360) }, { argument := 173101366043895473078743859200, coefficient := (-173101366043895473078743859200) }, { argument := 47591725922491516686025359360, coefficient := (-47591725922491516686025359360) }, { argument := 223544891156580309953268416512, coefficient := (-223544891156580309953268416512) }, { argument := 223544891156580309953268416512, coefficient := (-223544891156580309953268416512) }, { argument := 2263109134318585815049961472, coefficient := (-2263109134318585815049961472) }, { argument := 223544891156580309953268416512, coefficient := (-223544891156580309953268416512) }, { argument := 223544891156580309953268416512, coefficient := (-223544891156580309953268416512) }, { argument := 72419492298194746081598767104, coefficient := (-72419492298194746081598767104) }, { argument := 2263109134318585815049961472, coefficient := (-2263109134318585815049961472) }, { argument := 8216562506582787468124225536, coefficient := (-8216562506582787468124225536) }, { argument := 91154475159771307053154304, coefficient := (-91154475159771307053154304) }, { argument := 8216562506582787468124225536, coefficient := (-8216562506582787468124225536) }, { argument := 91154475159771307053154304, coefficient := (-91154475159771307053154304) }, { argument := 3544372163717812215139532800, coefficient := (-3544372163717812215139532800) }, { argument := 2727336649050603418137133056, coefficient := (-2727336649050603418137133056) }, { argument := 188246114133892066122260425998336, coefficient := 188246114133892066122260425998336 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 64411567669067442428345057280, coefficient := 64411567669067442428345057280 }, { argument := 144838984596389492163197534208, coefficient := 144838984596389492163197534208 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 64411567669067442428345057280, coefficient := 64411567669067442428345057280 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 144838984596389492163197534208, coefficient := 144838984596389492163197534208 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 24758800785707605497982484480, coefficient := 24758800785707605497982484480 }, { argument := 415947853199887772366105739264, coefficient := 415947853199887772366105739264 }, { argument := 901220348599756840126562435072, coefficient := 901220348599756840126562435072 }, { argument := 29710560942849126597578981376, coefficient := 29710560942849126597578981376 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 34662321099990647697175478272, coefficient := 34662321099990647697175478272 }, { argument := 901220348599756840126562435072, coefficient := 901220348599756840126562435072 }, { argument := 901220348599756840126562435072, coefficient := 901220348599756840126562435072 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 11121653312939856389693732028416, coefficient := 11121653312939856389693732028416 }, { argument := 891316828285473797927369441280, coefficient := 891316828285473797927369441280 }, { argument := 415947853199887772366105739264, coefficient := 415947853199887772366105739264 }, { argument := 901220348599756840126562435072, coefficient := 901220348599756840126562435072 }, { argument := 34662321099990647697175478272, coefficient := 34662321099990647697175478272 }, { argument := 891316828285473797927369441280, coefficient := 891316828285473797927369441280 }, { argument := 34662321099990647697175478272, coefficient := 34662321099990647697175478272 }, { argument := 901220348599756840126562435072, coefficient := 901220348599756840126562435072 }, { argument := 901220348599756840126562435072, coefficient := 901220348599756840126562435072 }, { argument := 29710560942849126597578981376, coefficient := 29710560942849126597578981376 }, { argument := 20282409603651670423947251286016, coefficient := (-20282409603651670423947251286016) }, { argument := 449991204280235729925831655424, coefficient := 449991204280235729925831655424 }, { argument := 534364555082779929286925090816, coefficient := 534364555082779929286925090816 }] }

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


end Parent3

namespace Parent3

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-6616131558147661405480631014522880)
def positiveArguments : Array ℕ := #[
    21083, 217373, 6543, 21083, 6543, 6543,
    560517, 6543, 217373, 560517, 727, 6543,
    6543, 13813, 1215, 21627, 1215, 38475,
    65691, 1215, 65691, 65691, 21627, 1215,
    7245, 8115, 7245, 8115, 1, 1,
    83, 83, 5562763121, 2503720625, 5562761991, 35643869,
    1319116323, 659551763, 17828333, 401537, 31642727, 79498673,
    31642727, 401499, 197591, 16579625, 8289813, 98795
  ]
def positiveCoefficients : Array ℕ := #[
    407804528878963630245284937728, 4204605314993452601494489530368, 506240104815265196166560612352, 407804528878963630245284937728, 506240104815265196166560612352, 506240104815265196166560612352,
    21683951156253859235801012895744, 506240104815265196166560612352, 4204605314993452601494489530368, 21683951156253859235801012895744, 449991204280235729925831655424, 506240104815265196166560612352,
    506240104815265196166560612352, 534364555082779929286925090816, 94006071733233564625152245760, 1673308076851557450327709974528, 94006071733233564625152245760, 1488429469109531439898243891200,
    2541297472521747363699949043712, 94006071733233564625152245760, 2541297472521747363699949043712, 2541297472521747363699949043712, 1673308076851557450327709974528, 94006071733233564625152245760,
    280277362019455627863879843840, 313933856837526904087699783680, 280277362019455627863879843840, 313933856837526904087699783680, 158456325028528675187087900672, 633825300114114700748351602688,
    13151874977367880040528295755776, 13151874977367880040528295755776, 26269406114753740645102272905216, 94587890895755519263705661440000, 26269400778479615002403181428736, 1346587298283171024587657838592,
    49834805685931591060841734078464, 49834322228940540798043336736768, 1347070755274221287386055180288, 3792409740864057460343701504, 597714213645577440335356755968, 6006749900925024423514134806528,
    597714213645577440335356755968, 3792050841011359367307460608, 1866194231433392134838812672, 156590130797095283052249088000, 156590140241828248791539515392, 1866184786700426395548385280
  ]
def positiveScales : Array ℕ := #[
    14, 17, 12, 14, 12, 12,
    19, 12, 17, 19, 9, 12,
    12, 13, 10, 14, 10, 15,
    16, 10, 16, 16, 14, 10,
    12, 12, 12, 12, 0, 0,
    6, 6, 32, 31, 32, 25,
    30, 29, 24, 18, 24, 26,
    24, 18, 17, 23, 22, 16
  ]
def negativeArguments : Array ℕ := #[
    727, 81, 15, 1, 1, 83,
    1857, 323, 91, 1
  ]
def negativeCoefficients : Array ℕ := #[
    57598874147870173430506451894272, 12834962327310822690154119954432, 1188422437713965063903159255040, 158456325028528675187087900672, 633825300114114700748351602688, 26303749954735760081056591511552,
    147126697788988874911211115773952, 102362785968429524170858783834112, 7209762788798054721012499480576, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    9, 6, 3, 0, 0, 6,
    10, 8, 6, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14363792549047166, 17729813228108780, 12675736555359392, 14363792549047166, 12675736555359392, 12675736555359392,
    19096398603834628, 12675736555359392, 17729813228108780, 19096398603834628, 9505811553919573, 12675736555359392,
    12675736555359392, 13753739067348048, 10246740598493143, 14400545934572177, 10246740598493143, 15231633706102934,
    16003408107101897, 10246740598493143, 16003408107101897, 16003408107101897, 14400545934572177, 10246740598493143,
    12822769974381095, 12986375378262269, 12822769974381095, 12986375378262269, 0, 0,
    6375039431346924, 6375039431346924, 32373154526639672, 31221426443647635, 32373154233575681, 25087150608371086,
    30296924644667977, 29296910648739286, 24087668477378282, 18615173406779306, 24915370601842252, 26244427443195984,
    24915370601842252, 18615036868911529, 17592157710068273, 23982908039251116, 22982908126267256, 16592150408628979
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    9505811553919924, 6339850002884626, 3906890600547867, 0, 0, 6375039431346928,
    10858758101980811, 8335390354693926, 6507794640199048, 0
  ]

abbrev PositiveTerm := Fin 48
abbrev NegativeTerm := Fin 10
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
noncomputable def positiveFloor : ℝ := 27997994307 / 250000000000
noncomputable def negativeCeiling : ℝ := 39710182759 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 407804528878963630245284937728, coefficient := 407804528878963630245284937728 }, { argument := 4204605314993452601494489530368, coefficient := 4204605314993452601494489530368 }, { argument := 506240104815265196166560612352, coefficient := 506240104815265196166560612352 }, { argument := 407804528878963630245284937728, coefficient := 407804528878963630245284937728 }, { argument := 506240104815265196166560612352, coefficient := 506240104815265196166560612352 }, { argument := 506240104815265196166560612352, coefficient := 506240104815265196166560612352 }, { argument := 21683951156253859235801012895744, coefficient := 21683951156253859235801012895744 }, { argument := 506240104815265196166560612352, coefficient := 506240104815265196166560612352 }, { argument := 4204605314993452601494489530368, coefficient := 4204605314993452601494489530368 }, { argument := 21683951156253859235801012895744, coefficient := 21683951156253859235801012895744 }, { argument := 449991204280235729925831655424, coefficient := 449991204280235729925831655424 }, { argument := 506240104815265196166560612352, coefficient := 506240104815265196166560612352 }, { argument := 506240104815265196166560612352, coefficient := 506240104815265196166560612352 }, { argument := 534364555082779929286925090816, coefficient := 534364555082779929286925090816 }, { argument := 57598874147870173430506451894272, coefficient := (-57598874147870173430506451894272) }, { argument := 94006071733233564625152245760, coefficient := 94006071733233564625152245760 }, { argument := 1673308076851557450327709974528, coefficient := 1673308076851557450327709974528 }, { argument := 94006071733233564625152245760, coefficient := 94006071733233564625152245760 }, { argument := 1488429469109531439898243891200, coefficient := 1488429469109531439898243891200 }, { argument := 2541297472521747363699949043712, coefficient := 2541297472521747363699949043712 }, { argument := 94006071733233564625152245760, coefficient := 94006071733233564625152245760 }, { argument := 2541297472521747363699949043712, coefficient := 2541297472521747363699949043712 }, { argument := 2541297472521747363699949043712, coefficient := 2541297472521747363699949043712 }, { argument := 1673308076851557450327709974528, coefficient := 1673308076851557450327709974528 }, { argument := 94006071733233564625152245760, coefficient := 94006071733233564625152245760 }, { argument := 12834962327310822690154119954432, coefficient := (-12834962327310822690154119954432) }, { argument := 280277362019455627863879843840, coefficient := 280277362019455627863879843840 }, { argument := 313933856837526904087699783680, coefficient := 313933856837526904087699783680 }, { argument := 280277362019455627863879843840, coefficient := 280277362019455627863879843840 }, { argument := 313933856837526904087699783680, coefficient := 313933856837526904087699783680 }, { argument := 1188422437713965063903159255040, coefficient := (-1188422437713965063903159255040) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 633825300114114700748351602688, coefficient := 633825300114114700748351602688 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 13151874977367880040528295755776, coefficient := 13151874977367880040528295755776 }, { argument := 13151874977367880040528295755776, coefficient := 13151874977367880040528295755776 }, { argument := 26303749954735760081056591511552, coefficient := (-26303749954735760081056591511552) }, { argument := 26269406114753740645102272905216, coefficient := 26269406114753740645102272905216 }, { argument := 94587890895755519263705661440000, coefficient := 94587890895755519263705661440000 }, { argument := 26269400778479615002403181428736, coefficient := 26269400778479615002403181428736 }, { argument := 147126697788988874911211115773952, coefficient := (-147126697788988874911211115773952) }, { argument := 1346587298283171024587657838592, coefficient := 1346587298283171024587657838592 }, { argument := 49834805685931591060841734078464, coefficient := 49834805685931591060841734078464 }, { argument := 49834322228940540798043336736768, coefficient := 49834322228940540798043336736768 }, { argument := 1347070755274221287386055180288, coefficient := 1347070755274221287386055180288 }, { argument := 102362785968429524170858783834112, coefficient := (-102362785968429524170858783834112) }, { argument := 3792409740864057460343701504, coefficient := 3792409740864057460343701504 }, { argument := 597714213645577440335356755968, coefficient := 597714213645577440335356755968 }, { argument := 6006749900925024423514134806528, coefficient := 6006749900925024423514134806528 }, { argument := 597714213645577440335356755968, coefficient := 597714213645577440335356755968 }, { argument := 3792050841011359367307460608, coefficient := 3792050841011359367307460608 }, { argument := 7209762788798054721012499480576, coefficient := (-7209762788798054721012499480576) }, { argument := 1866194231433392134838812672, coefficient := 1866194231433392134838812672 }, { argument := 156590130797095283052249088000, coefficient := 156590130797095283052249088000 }, { argument := 156590140241828248791539515392, coefficient := 156590140241828248791539515392 }, { argument := 1866184786700426395548385280, coefficient := 1866184786700426395548385280 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end TermShard5


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk20
