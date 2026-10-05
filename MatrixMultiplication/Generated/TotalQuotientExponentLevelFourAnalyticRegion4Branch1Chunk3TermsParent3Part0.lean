import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 3, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk3

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
def constantNumerator : ℤ := (-140670984748559121564934619529216)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    950960400237, 52001020917433, 52015655439137, 936576308921, 58103424009, 2363095828219,
    52168211920985, 2363101247327, 116185514721, 58103424009, 4079893110249, 1019965586475,
    116236020057, 3148518180573, 172475134161981, 172523908099353, 3100552501197, 4079893110249,
    20907155545913, 461818310707935, 83628818091291, 4079151080093, 2363095828219, 20907155545913,
    83628115258499, 1181787858895, 950960400237, 3148518180573, 474971670747, 474971670747,
    25974372698757, 25981683885027, 467785451709, 1019965586475, 83628115258499, 923631047425419,
    83628311157519, 2039560159885, 52168211920985, 461818310707935, 923631047425419, 52178766586133,
    52001020917433, 172475134161981, 25974372698757, 116236020057, 1181787858895, 52178766586133,
    2363581145207, 14526835373, 2363101247327, 83628818091291, 83628311157519, 2363581145207,
    52015655439137, 172523908099353, 25981683885027, 116185514721, 4079151080093, 2039560159885,
    14526835373, 936576308921, 3100552501197, 467785451709
  ]
def negativeCoefficients : Array ℕ := #[
    267671556509465683502825472, 14636986151664789177707266048, 14641105403320594167467343872, 263622794741290634288562176, 32709319839485291353079808, 1330304686425982753285603328,
    14684046235495819582279516160, 1330307737112578938344833024, 32703315050209054845566976, 32709319839485291353079808, 1148387818189303147181113344, 1148379158794884853687910400,
    32717531038483418701627392, 886229081549862177381285888, 48547434371410871030472769536, 48561163014296741724781805568, 872727943064591784562655232, 1148387818189303147181113344,
    47078728962975392837794791424, 519961193004282002196073021440, 47078839249171642767000993792, 1148178955268424442742571008, 1330304686425982753285603328, 47078728962975392837794791424,
    47078443589484123396335730688, 1330574840237624576683540480, 267671556509465683502825472, 886229081549862177381285888, 267385279923466389436760064, 267385279923466389436760064,
    14622271900913051218879709184, 14626387732883202254699495424, 263339798250748943907422208, 1148379158794884853687910400, 47078443589484123396335730688, 519958055126617240908205129728,
    47078553870828307677003644928, 1148170297007224405486469120, 14684046235495819582279516160, 519961193004282002196073021440, 519958055126617240908205129728, 14687017109622541654842933248,
    14636986151664789177707266048, 48547434371410871030472769536, 14622271900913051218879709184, 32717531038483418701627392, 1330574840237624576683540480, 14687017109622541654842933248,
    1330577895601771924720451584, 32711525186357670134677504, 1330307737112578938344833024, 47078839249171642767000993792, 47078553870828307677003644928, 1330577895601771924720451584,
    14641105403320594167467343872, 48561163014296741724781805568, 14626387732883202254699495424, 32703315050209054845566976, 1148178955268424442742571008, 1148170297007224405486469120,
    32711525186357670134677504, 263622794741290634288562176, 872727943064591784562655232, 263339798250748943907422208
  ]
def negativeScales : Array ℕ := #[
    39, 45, 45, 39, 35, 41,
    45, 41, 36, 35, 41, 39,
    36, 41, 47, 47, 41, 41,
    44, 48, 46, 41, 41, 44,
    46, 40, 39, 41, 38, 38,
    44, 44, 38, 39, 46, 49,
    46, 40, 45, 48, 49, 45,
    45, 47, 44, 36, 40, 45,
    41, 33, 41, 46, 46, 41,
    45, 47, 44, 36, 41, 40,
    33, 39, 41, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    39790594310120598, 45563605180984890, 45564011138044243, 39768605589037074, 35757904132654295, 41103815273289400,
    45568236219003785, 41103818581708458, 36757639257839232, 35757904132654295, 41891668497708328, 39891657619054672,
    36758266254811978, 41517810136616790, 47293381711142588, 47293789630640444, 41495662457281713, 41891668497708328,
    44249062027699023, 48714318704416160, 46249065407339161, 41891406083808623, 41103815273289400, 44249062027699023,
    46249053282599537, 40104108221212646, 39790594310120598, 41517810136616790, 38789050512053898, 38789050512053898,
    44562154140883835, 44562560169090690, 38767056038154155, 39891657619054672, 46249053282599537, 49714309997969839,
    46249056662111473, 40891395204599957, 45568236219003785, 48714318704416160, 49714309997969839, 45568528075334233,
    45563605180984890, 47293381711142588, 44562154140883835, 36758266254811978, 40104108221212646, 45568528075334233,
    41104111534031670, 33758001399603829, 41103818581708458, 46249065407339161, 46249056662111473, 41104111534031670,
    45564011138044243, 47293789630640444, 44562560169090690, 36757639257839232, 41891406083808623, 40891395204599957,
    33758001399603829, 39768605589037074, 41495662457281713, 38767056038154155
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
noncomputable def negativeCeiling : ℝ := 51825817 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 267671556509465683502825472, coefficient := (-267671556509465683502825472) }, { argument := 14636986151664789177707266048, coefficient := (-14636986151664789177707266048) }, { argument := 14641105403320594167467343872, coefficient := (-14641105403320594167467343872) }, { argument := 263622794741290634288562176, coefficient := (-263622794741290634288562176) }, { argument := 32709319839485291353079808, coefficient := (-32709319839485291353079808) }, { argument := 1330304686425982753285603328, coefficient := (-1330304686425982753285603328) }, { argument := 14684046235495819582279516160, coefficient := (-14684046235495819582279516160) }, { argument := 1330307737112578938344833024, coefficient := (-1330307737112578938344833024) }, { argument := 32703315050209054845566976, coefficient := (-32703315050209054845566976) }, { argument := 32709319839485291353079808, coefficient := (-32709319839485291353079808) }, { argument := 1148387818189303147181113344, coefficient := (-1148387818189303147181113344) }, { argument := 1148379158794884853687910400, coefficient := (-1148379158794884853687910400) }, { argument := 32717531038483418701627392, coefficient := (-32717531038483418701627392) }, { argument := 886229081549862177381285888, coefficient := (-886229081549862177381285888) }, { argument := 48547434371410871030472769536, coefficient := (-48547434371410871030472769536) }, { argument := 48561163014296741724781805568, coefficient := (-48561163014296741724781805568) }, { argument := 872727943064591784562655232, coefficient := (-872727943064591784562655232) }, { argument := 1148387818189303147181113344, coefficient := (-1148387818189303147181113344) }, { argument := 47078728962975392837794791424, coefficient := (-47078728962975392837794791424) }, { argument := 519961193004282002196073021440, coefficient := (-519961193004282002196073021440) }, { argument := 47078839249171642767000993792, coefficient := (-47078839249171642767000993792) }, { argument := 1148178955268424442742571008, coefficient := (-1148178955268424442742571008) }, { argument := 1330304686425982753285603328, coefficient := (-1330304686425982753285603328) }, { argument := 47078728962975392837794791424, coefficient := (-47078728962975392837794791424) }, { argument := 47078443589484123396335730688, coefficient := (-47078443589484123396335730688) }, { argument := 1330574840237624576683540480, coefficient := (-1330574840237624576683540480) }, { argument := 267671556509465683502825472, coefficient := (-267671556509465683502825472) }, { argument := 886229081549862177381285888, coefficient := (-886229081549862177381285888) }, { argument := 267385279923466389436760064, coefficient := (-267385279923466389436760064) }, { argument := 267385279923466389436760064, coefficient := (-267385279923466389436760064) }, { argument := 14622271900913051218879709184, coefficient := (-14622271900913051218879709184) }, { argument := 14626387732883202254699495424, coefficient := (-14626387732883202254699495424) }, { argument := 263339798250748943907422208, coefficient := (-263339798250748943907422208) }, { argument := 1148379158794884853687910400, coefficient := (-1148379158794884853687910400) }, { argument := 47078443589484123396335730688, coefficient := (-47078443589484123396335730688) }, { argument := 519958055126617240908205129728, coefficient := (-519958055126617240908205129728) }, { argument := 47078553870828307677003644928, coefficient := (-47078553870828307677003644928) }, { argument := 1148170297007224405486469120, coefficient := (-1148170297007224405486469120) }, { argument := 14684046235495819582279516160, coefficient := (-14684046235495819582279516160) }, { argument := 519961193004282002196073021440, coefficient := (-519961193004282002196073021440) }, { argument := 519958055126617240908205129728, coefficient := (-519958055126617240908205129728) }, { argument := 14687017109622541654842933248, coefficient := (-14687017109622541654842933248) }, { argument := 14636986151664789177707266048, coefficient := (-14636986151664789177707266048) }, { argument := 48547434371410871030472769536, coefficient := (-48547434371410871030472769536) }, { argument := 14622271900913051218879709184, coefficient := (-14622271900913051218879709184) }, { argument := 32717531038483418701627392, coefficient := (-32717531038483418701627392) }, { argument := 1330574840237624576683540480, coefficient := (-1330574840237624576683540480) }, { argument := 14687017109622541654842933248, coefficient := (-14687017109622541654842933248) }, { argument := 1330577895601771924720451584, coefficient := (-1330577895601771924720451584) }, { argument := 32711525186357670134677504, coefficient := (-32711525186357670134677504) }, { argument := 1330307737112578938344833024, coefficient := (-1330307737112578938344833024) }, { argument := 47078839249171642767000993792, coefficient := (-47078839249171642767000993792) }, { argument := 47078553870828307677003644928, coefficient := (-47078553870828307677003644928) }, { argument := 1330577895601771924720451584, coefficient := (-1330577895601771924720451584) }, { argument := 14641105403320594167467343872, coefficient := (-14641105403320594167467343872) }, { argument := 48561163014296741724781805568, coefficient := (-48561163014296741724781805568) }, { argument := 14626387732883202254699495424, coefficient := (-14626387732883202254699495424) }, { argument := 32703315050209054845566976, coefficient := (-32703315050209054845566976) }, { argument := 1148178955268424442742571008, coefficient := (-1148178955268424442742571008) }, { argument := 1148170297007224405486469120, coefficient := (-1148170297007224405486469120) }, { argument := 32711525186357670134677504, coefficient := (-32711525186357670134677504) }, { argument := 263622794741290634288562176, coefficient := (-263622794741290634288562176) }, { argument := 872727943064591784562655232, coefficient := (-872727943064591784562655232) }, { argument := 263339798250748943907422208, coefficient := (-263339798250748943907422208) }] }

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

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 124428981750526485424793047793664
def positiveArguments : Array ℕ := #[
    9, 6312383, 20936019, 3153015, 1843363, 130531023,
    65265117, 3687473, 250107, 5125505, 226431031, 5125517,
    500123, 300969, 1029763, 16480859, 74099
  ]
def positiveCoefficients : Array ℕ := #[
    2852213850513516153367582212096, 59618771812472279325931995136, 197735108820644133434397032448, 59558769423940937613846773760, 34820142587848151240217198592, 1232830655979773530781584982016,
    1232823204085463562481437769728, 34827197803373558490166460416, 4724387655724313421847461888, 193636104158246247128199331840, 2138580622952035208682801201152, 193636557505428602614139846656,
    4723528185024431146418569216, 2842571835965588500641742848, 155613384847977422854119489536, 155657312301001076293897289728, 2799381072113262725517279232
  ]
def positiveScales : Array ℕ := #[
    3, 22, 24, 21, 20, 26,
    25, 21, 17, 22, 27, 22,
    18, 18, 19, 23, 16
  ]
def negativeArguments : Array ℕ := #[
    1, 1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    316912650057057350374175801344, 2535301200456458802993406410752, 2535301200456458802993406410752, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    0, 0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 22589753311975254, 24319483802995244, 21588300602768617, 20813908767604114, 26959817487811465,
    25959808767357224, 21814201055132043, 17932185910225004, 22289262725181877, 27754496443410836, 22289266102862754,
    18931923428185429, 18199255370559777, 19973880907651264, 23974288102537513, 16177166452380480
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0, 0, 0
  ]

abbrev PositiveTerm := Fin 17
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 952771211 / 500000000000
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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2852213850513516153367582212096, coefficient := 2852213850513516153367582212096 }, { argument := 59618771812472279325931995136, coefficient := 59618771812472279325931995136 }, { argument := 197735108820644133434397032448, coefficient := 197735108820644133434397032448 }, { argument := 59558769423940937613846773760, coefficient := 59558769423940937613846773760 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 34820142587848151240217198592, coefficient := 34820142587848151240217198592 }, { argument := 1232830655979773530781584982016, coefficient := 1232830655979773530781584982016 }, { argument := 1232823204085463562481437769728, coefficient := 1232823204085463562481437769728 }, { argument := 34827197803373558490166460416, coefficient := 34827197803373558490166460416 }, { argument := 2535301200456458802993406410752, coefficient := (-2535301200456458802993406410752) }, { argument := 4724387655724313421847461888, coefficient := 4724387655724313421847461888 }, { argument := 193636104158246247128199331840, coefficient := 193636104158246247128199331840 }, { argument := 2138580622952035208682801201152, coefficient := 2138580622952035208682801201152 }, { argument := 193636557505428602614139846656, coefficient := 193636557505428602614139846656 }, { argument := 4723528185024431146418569216, coefficient := 4723528185024431146418569216 }, { argument := 2535301200456458802993406410752, coefficient := (-2535301200456458802993406410752) }, { argument := 2842571835965588500641742848, coefficient := 2842571835965588500641742848 }, { argument := 155613384847977422854119489536, coefficient := 155613384847977422854119489536 }, { argument := 155657312301001076293897289728, coefficient := 155657312301001076293897289728 }, { argument := 2799381072113262725517279232, coefficient := 2799381072113262725517279232 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk3
