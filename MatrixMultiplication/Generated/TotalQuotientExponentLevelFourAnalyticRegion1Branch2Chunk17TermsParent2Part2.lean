import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 17, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17

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
def constantNumerator : ℤ := (-5331194885760663997807439674081280)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    44902455, 84937, 329396987637, 558283413771, 329396987637, 1049940057,
    1325991, 1049940057, 1325991, 31421, 2628009, 1623,
    2628009, 1623, 67787, 5422839796826881, 1928797587, 108359415,
    2415676937301933, 5858632371, 5422839616173975, 5858632371, 5858632371, 1928797587,
    108359415, 4492572703728405, 2705, 4492571394825451, 2705, 256788609,
    85057707, 82773, 85057707, 82773, 31421, 2195,
    52432425, 917502075, 917502525, 52431975, 3845101023, 6516927009,
    3845101023, 3271023, 2705, 3271023, 2705, 3845101023,
    6516927009, 3845101023, 2628009, 1623, 2628009, 1623,
    2141, 3271023, 2705, 3271023, 2705, 267,
    8117435493, 13757957019, 8117435493, 42529095
  ]
def negativeCoefficients : Array ℕ := #[
    424091696981125030147900047360, 802207283910998111031394304, 3038150964795304095192182685696, 10298511254430531727710209703936, 3038150964795304095192182685696, 9916403468398089638475510841344,
    12523630909973607453107945472, 9916403468398089638475510841344, 12523630909973607453107945472, 607770530849780212775084097536, 794266983569905500697600720896, 490521651308635787637030912,
    794266983569905500697600720896, 490521651308635787637030912, 1311191272547469885852920840192, 3052787411034929688567319887872, 4447504432172191661974093824, 249859799560235486627758080,
    10879241754680486487741607968768, 6754543248111699321837060096, 3052787309336384670442664755200, 6754543248111699321837060096, 6754543248111699321837060096, 4447504432172191661974093824,
    249859799560235486627758080, 10116374377223053241872747069440, 817536085514392979395051520, 10116371429835625292602013646848, 817536085514392979395051520, 2425299840648637045497007177728,
    803347329293093603561013510144, 781768881773138286546518016, 803347329293093603561013510144, 781768881773138286546518016, 607770530849780212775084097536, 42457474784865776615680901120,
    241801881284742634222387200, 8462462982311233277499801600, 8462467132828649862148915200, 241799806026034341897830400, 70929594508839784323552903168, 240432169364136927495179993088,
    70929594508839784323552903168, 30893938759791430991679062016, 25548002672324780606095360, 30893938759791430991679062016, 25548002672324780606095360, 70929594508839784323552903168,
    240432169364136927495179993088, 70929594508839784323552903168, 794266983569905500697600720896, 490521651308635787637030912, 794266983569905500697600720896, 490521651308635787637030912,
    41412962876718737008734765056, 30893938759791430991679062016, 25548002672324780606095360, 30893938759791430991679062016, 25548002672324780606095360, 41316248811149566674758270976,
    74870127537108661230416953344, 253789512106588979022689992704, 74870127537108661230416953344, 803351891099116055638289940480
  ]
def negativeScales : Array ℕ := #[
    25, 16, 38, 39, 38, 29,
    20, 29, 20, 14, 21, 10,
    21, 10, 16, 52, 30, 26,
    51, 32, 52, 32, 32, 30,
    26, 51, 11, 51, 11, 27,
    26, 16, 26, 16, 14, 11,
    25, 29, 29, 25, 31, 32,
    31, 21, 11, 21, 11, 31,
    32, 31, 21, 10, 21, 10,
    11, 21, 11, 21, 11, 8,
    32, 33, 32, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    25420290989345031, 16374105532718445, 38261036405318778, 39022206739005524, 38261036405318778, 29967659832130691,
    20338639552693656, 29967659832130691, 20338639552693656, 14939441484618788, 21325538785712399, 10664447284578613,
    21325538785712399, 10664447284578613, 16048721003444837, 52267969973759937, 30845054606749079, 26691249269153261,
    51101348950772731, 32447916777703220, 52267969925698946, 32447916777703220, 32447916777703220, 30845054606749079,
    26691249269153261, 51996463296880407, 11401412878714185, 51996462876553597, 11401412878714185, 27936005974042335,
    26341938627283391, 16336872626519468, 26341938627283391, 16336872626519468, 14939441484618788, 11100005224422721,
    25643955936282215, 29773136180191675, 29773136887778755, 25643943554334315, 31840374358285807, 32601544690538703,
    31840374358285807, 21641310473020336, 11401412878714185, 21641310473020336, 11401412878714185, 31840374358285807,
    32601544690538703, 31840374358285807, 21325538785712399, 10664447284578613, 21325538785712399, 10664447284578613,
    11064069080385510, 21641310473020336, 11401412878714185, 21641310473020336, 11401412878714185, 8060695931687554,
    32918376874897093, 33679547202578477, 32918376874897093, 25341946819600711
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
noncomputable def negativeCeiling : ℝ := 2594096411 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 424091696981125030147900047360, coefficient := (-424091696981125030147900047360) }, { argument := 802207283910998111031394304, coefficient := (-802207283910998111031394304) }, { argument := 3038150964795304095192182685696, coefficient := (-3038150964795304095192182685696) }, { argument := 10298511254430531727710209703936, coefficient := (-10298511254430531727710209703936) }, { argument := 3038150964795304095192182685696, coefficient := (-3038150964795304095192182685696) }, { argument := 9916403468398089638475510841344, coefficient := (-9916403468398089638475510841344) }, { argument := 12523630909973607453107945472, coefficient := (-12523630909973607453107945472) }, { argument := 9916403468398089638475510841344, coefficient := (-9916403468398089638475510841344) }, { argument := 12523630909973607453107945472, coefficient := (-12523630909973607453107945472) }, { argument := 607770530849780212775084097536, coefficient := (-607770530849780212775084097536) }, { argument := 794266983569905500697600720896, coefficient := (-794266983569905500697600720896) }, { argument := 490521651308635787637030912, coefficient := (-490521651308635787637030912) }, { argument := 794266983569905500697600720896, coefficient := (-794266983569905500697600720896) }, { argument := 490521651308635787637030912, coefficient := (-490521651308635787637030912) }, { argument := 1311191272547469885852920840192, coefficient := (-1311191272547469885852920840192) }, { argument := 3052787411034929688567319887872, coefficient := (-3052787411034929688567319887872) }, { argument := 4447504432172191661974093824, coefficient := (-4447504432172191661974093824) }, { argument := 249859799560235486627758080, coefficient := (-249859799560235486627758080) }, { argument := 10879241754680486487741607968768, coefficient := (-10879241754680486487741607968768) }, { argument := 6754543248111699321837060096, coefficient := (-6754543248111699321837060096) }, { argument := 3052787309336384670442664755200, coefficient := (-3052787309336384670442664755200) }, { argument := 6754543248111699321837060096, coefficient := (-6754543248111699321837060096) }, { argument := 6754543248111699321837060096, coefficient := (-6754543248111699321837060096) }, { argument := 4447504432172191661974093824, coefficient := (-4447504432172191661974093824) }, { argument := 249859799560235486627758080, coefficient := (-249859799560235486627758080) }, { argument := 10116374377223053241872747069440, coefficient := (-10116374377223053241872747069440) }, { argument := 817536085514392979395051520, coefficient := (-817536085514392979395051520) }, { argument := 10116371429835625292602013646848, coefficient := (-10116371429835625292602013646848) }, { argument := 817536085514392979395051520, coefficient := (-817536085514392979395051520) }, { argument := 2425299840648637045497007177728, coefficient := (-2425299840648637045497007177728) }, { argument := 803347329293093603561013510144, coefficient := (-803347329293093603561013510144) }, { argument := 781768881773138286546518016, coefficient := (-781768881773138286546518016) }, { argument := 803347329293093603561013510144, coefficient := (-803347329293093603561013510144) }, { argument := 781768881773138286546518016, coefficient := (-781768881773138286546518016) }, { argument := 607770530849780212775084097536, coefficient := (-607770530849780212775084097536) }, { argument := 42457474784865776615680901120, coefficient := (-42457474784865776615680901120) }, { argument := 241801881284742634222387200, coefficient := (-241801881284742634222387200) }, { argument := 8462462982311233277499801600, coefficient := (-8462462982311233277499801600) }, { argument := 8462467132828649862148915200, coefficient := (-8462467132828649862148915200) }, { argument := 241799806026034341897830400, coefficient := (-241799806026034341897830400) }, { argument := 70929594508839784323552903168, coefficient := (-70929594508839784323552903168) }, { argument := 240432169364136927495179993088, coefficient := (-240432169364136927495179993088) }, { argument := 70929594508839784323552903168, coefficient := (-70929594508839784323552903168) }, { argument := 30893938759791430991679062016, coefficient := (-30893938759791430991679062016) }, { argument := 25548002672324780606095360, coefficient := (-25548002672324780606095360) }, { argument := 30893938759791430991679062016, coefficient := (-30893938759791430991679062016) }, { argument := 25548002672324780606095360, coefficient := (-25548002672324780606095360) }, { argument := 70929594508839784323552903168, coefficient := (-70929594508839784323552903168) }, { argument := 240432169364136927495179993088, coefficient := (-240432169364136927495179993088) }, { argument := 70929594508839784323552903168, coefficient := (-70929594508839784323552903168) }, { argument := 794266983569905500697600720896, coefficient := (-794266983569905500697600720896) }, { argument := 490521651308635787637030912, coefficient := (-490521651308635787637030912) }, { argument := 794266983569905500697600720896, coefficient := (-794266983569905500697600720896) }, { argument := 490521651308635787637030912, coefficient := (-490521651308635787637030912) }, { argument := 41412962876718737008734765056, coefficient := (-41412962876718737008734765056) }, { argument := 30893938759791430991679062016, coefficient := (-30893938759791430991679062016) }, { argument := 25548002672324780606095360, coefficient := (-25548002672324780606095360) }, { argument := 30893938759791430991679062016, coefficient := (-30893938759791430991679062016) }, { argument := 25548002672324780606095360, coefficient := (-25548002672324780606095360) }, { argument := 41316248811149566674758270976, coefficient := (-41316248811149566674758270976) }, { argument := 74870127537108661230416953344, coefficient := (-74870127537108661230416953344) }, { argument := 253789512106588979022689992704, coefficient := (-253789512106588979022689992704) }, { argument := 74870127537108661230416953344, coefficient := (-74870127537108661230416953344) }, { argument := 803351891099116055638289940480, coefficient := (-803351891099116055638289940480) }] }

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

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 319002584579224796763226622782341120
def positiveArguments : Array ℕ := #[
    5041, 2385, 1855, 265, 2491, 29415,
    2067, 1855, 29415, 265, 2067, 2067,
    2067, 2067, 2067, 2385, 2491, 4545,
    19089, 82719, 2727, 2727, 6363, 82719,
    82719, 2727, 1020807, 40905, 19089, 82719,
    6363, 40905, 6363, 82719, 82719, 2727,
    547, 10393, 15863, 163553, 4923, 15863,
    4923, 4923, 421737, 4923
  ]
def positiveCoefficients : Array ℕ := #[
    3195113337875252206472440429150208, 92265218552988498613575352320, 71761836652324387810558607360, 82013527602656443212066979840, 96365894933121320774178701312, 1137937695486858149567429345280,
    2558822061202881028216489771008, 71761836652324387810558607360, 1137937695486858149567429345280, 82013527602656443212066979840, 79963189412590032131765305344, 79963189412590032131765305344,
    79963189412590032131765305344, 2558822061202881028216489771008, 79963189412590032131765305344, 92265218552988498613575352320, 96365894933121320774178701312, 87913085602375833584633118720,
    1476939838119914004221836394496, 3200036315926480342480645521408, 105495702722851000301559742464, 1687931243565616004824955879424, 123078319843326167018486366208, 3200036315926480342480645521408,
    3200036315926480342480645521408, 1687931243565616004824955879424, 39490558052587224446217196929024, 3164871081685530009046792273920, 1476939838119914004221836394496, 3200036315926480342480645521408,
    123078319843326167018486366208, 3164871081685530009046792273920, 123078319843326167018486366208, 3200036315926480342480645521408, 3200036315926480342480645521408, 105495702722851000301559742464,
    677153201489103010369820950528, 804119426768309824814162378752, 613670088849499603147650236416, 6327150226413806253143014506496, 761797351675240886666048569344, 613670088849499603147650236416,
    761797351675240886666048569344, 761797351675240886666048569344, 32630319896756151312195747053568, 761797351675240886666048569344
  ]
def positiveScales : Array ℕ := #[
    12, 11, 10, 8, 11, 14,
    11, 10, 14, 8, 11, 11,
    11, 11, 11, 11, 11, 12,
    14, 16, 11, 11, 12, 16,
    16, 11, 19, 15, 14, 16,
    12, 15, 12, 16, 16, 11,
    9, 13, 13, 17, 12, 13,
    12, 12, 18, 12
  ]
def negativeArguments : Array ℕ := #[
    41657, 42529095, 41657, 2141, 85025829, 47067,
    85025829, 47067, 67787, 267, 159279935532341, 1623,
    159279902741195, 1623, 8056703, 2569, 53, 909
  ]
def negativeCoefficients : Array ℕ := #[
    786878482307603242667737088, 803351891099116055638289940480, 786878482307603242667737088, 41412962876718737008734765056, 803046250095611766460769107968, 444535246498451182546059264,
    803046250095611766460769107968, 444535246498451182546059264, 1311191272547469885852920840192, 41316248811149566674758270976, 89666632288880944128974651392, 30657603206789736727314432,
    89666613829106830797533347840, 30657603206789736727314432, 76093408419270638404240408576, 49691686889439717597122658304, 8398185226512019784915658735616, 72018399725466282872531450855424
  ]
def negativeScales : Array ℕ := #[
    15, 25, 15, 11, 26, 15,
    26, 15, 16, 8, 47, 10,
    47, 10, 22, 11, 5, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12299494239009363, 11219773550892873, 10857203471385268, 8049848549450561, 11282509306240836, 14844264415704613,
    11013322673425447, 10857203471385268, 14844264415704613, 8049848549450561, 11013322673425447, 11013322673425447,
    11013322673425447, 11013322673425447, 11013322673425447, 11219773550892873, 11282509306240836, 12150064579081469,
    14220453906972867, 16335931124392803, 11413098984915262, 11413098984915262, 12635491406250799, 16335931124392803,
    16335931124392803, 11413098984915262, 19961278695817421, 15319989580523781, 14220453906972867, 16335931124392803,
    12635491406250799, 15319989580523781, 12635491406250799, 16335931124392803, 16335931124392803, 11413098984915262,
    9095397022792556, 13343324536236141, 13953378017239002, 17319398696990661, 12265322024234868, 13953378017239002,
    12265322024234868, 12265322024234868, 18685984072704368, 12265322024234868
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    15346271324521718, 25341946819600711, 15346271324521718, 11064069080385510, 26341397831458779, 15522428279676108,
    26341397831458779, 15522428279676108, 16048721003444837, 8060695931687554, 47178557870671533, 10664447284578613,
    47178557573662192, 10664447284578613, 22941758151797540, 11326991174900818, 5727920454700926, 9828136485328458
  ]

abbrev PositiveTerm := Fin 46
abbrev NegativeTerm := Fin 18
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
noncomputable def positiveFloor : ℝ := 99853098859 / 200000000000
noncomputable def negativeCeiling : ℝ := 1024616471 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 786878482307603242667737088, coefficient := (-786878482307603242667737088) }, { argument := 803351891099116055638289940480, coefficient := (-803351891099116055638289940480) }, { argument := 786878482307603242667737088, coefficient := (-786878482307603242667737088) }, { argument := 41412962876718737008734765056, coefficient := (-41412962876718737008734765056) }, { argument := 803046250095611766460769107968, coefficient := (-803046250095611766460769107968) }, { argument := 444535246498451182546059264, coefficient := (-444535246498451182546059264) }, { argument := 803046250095611766460769107968, coefficient := (-803046250095611766460769107968) }, { argument := 444535246498451182546059264, coefficient := (-444535246498451182546059264) }, { argument := 1311191272547469885852920840192, coefficient := (-1311191272547469885852920840192) }, { argument := 41316248811149566674758270976, coefficient := (-41316248811149566674758270976) }, { argument := 89666632288880944128974651392, coefficient := (-89666632288880944128974651392) }, { argument := 30657603206789736727314432, coefficient := (-30657603206789736727314432) }, { argument := 89666613829106830797533347840, coefficient := (-89666613829106830797533347840) }, { argument := 30657603206789736727314432, coefficient := (-30657603206789736727314432) }, { argument := 76093408419270638404240408576, coefficient := (-76093408419270638404240408576) }, { argument := 49691686889439717597122658304, coefficient := (-49691686889439717597122658304) }, { argument := 3195113337875252206472440429150208, coefficient := 3195113337875252206472440429150208 }, { argument := 92265218552988498613575352320, coefficient := 92265218552988498613575352320 }, { argument := 71761836652324387810558607360, coefficient := 71761836652324387810558607360 }, { argument := 82013527602656443212066979840, coefficient := 82013527602656443212066979840 }, { argument := 96365894933121320774178701312, coefficient := 96365894933121320774178701312 }, { argument := 1137937695486858149567429345280, coefficient := 1137937695486858149567429345280 }, { argument := 2558822061202881028216489771008, coefficient := 2558822061202881028216489771008 }, { argument := 71761836652324387810558607360, coefficient := 71761836652324387810558607360 }, { argument := 1137937695486858149567429345280, coefficient := 1137937695486858149567429345280 }, { argument := 82013527602656443212066979840, coefficient := 82013527602656443212066979840 }, { argument := 79963189412590032131765305344, coefficient := 79963189412590032131765305344 }, { argument := 79963189412590032131765305344, coefficient := 79963189412590032131765305344 }, { argument := 79963189412590032131765305344, coefficient := 79963189412590032131765305344 }, { argument := 2558822061202881028216489771008, coefficient := 2558822061202881028216489771008 }, { argument := 79963189412590032131765305344, coefficient := 79963189412590032131765305344 }, { argument := 92265218552988498613575352320, coefficient := 92265218552988498613575352320 }, { argument := 96365894933121320774178701312, coefficient := 96365894933121320774178701312 }, { argument := 8398185226512019784915658735616, coefficient := (-8398185226512019784915658735616) }, { argument := 87913085602375833584633118720, coefficient := 87913085602375833584633118720 }, { argument := 1476939838119914004221836394496, coefficient := 1476939838119914004221836394496 }, { argument := 3200036315926480342480645521408, coefficient := 3200036315926480342480645521408 }, { argument := 105495702722851000301559742464, coefficient := 105495702722851000301559742464 }, { argument := 1687931243565616004824955879424, coefficient := 1687931243565616004824955879424 }, { argument := 123078319843326167018486366208, coefficient := 123078319843326167018486366208 }, { argument := 3200036315926480342480645521408, coefficient := 3200036315926480342480645521408 }, { argument := 3200036315926480342480645521408, coefficient := 3200036315926480342480645521408 }, { argument := 1687931243565616004824955879424, coefficient := 1687931243565616004824955879424 }, { argument := 39490558052587224446217196929024, coefficient := 39490558052587224446217196929024 }, { argument := 3164871081685530009046792273920, coefficient := 3164871081685530009046792273920 }, { argument := 1476939838119914004221836394496, coefficient := 1476939838119914004221836394496 }, { argument := 3200036315926480342480645521408, coefficient := 3200036315926480342480645521408 }, { argument := 123078319843326167018486366208, coefficient := 123078319843326167018486366208 }, { argument := 3164871081685530009046792273920, coefficient := 3164871081685530009046792273920 }, { argument := 123078319843326167018486366208, coefficient := 123078319843326167018486366208 }, { argument := 3200036315926480342480645521408, coefficient := 3200036315926480342480645521408 }, { argument := 3200036315926480342480645521408, coefficient := 3200036315926480342480645521408 }, { argument := 105495702722851000301559742464, coefficient := 105495702722851000301559742464 }, { argument := 72018399725466282872531450855424, coefficient := (-72018399725466282872531450855424) }, { argument := 677153201489103010369820950528, coefficient := 677153201489103010369820950528 }, { argument := 804119426768309824814162378752, coefficient := 804119426768309824814162378752 }, { argument := 613670088849499603147650236416, coefficient := 613670088849499603147650236416 }, { argument := 6327150226413806253143014506496, coefficient := 6327150226413806253143014506496 }, { argument := 761797351675240886666048569344, coefficient := 761797351675240886666048569344 }, { argument := 613670088849499603147650236416, coefficient := 613670088849499603147650236416 }, { argument := 761797351675240886666048569344, coefficient := 761797351675240886666048569344 }, { argument := 761797351675240886666048569344, coefficient := 761797351675240886666048569344 }, { argument := 32630319896756151312195747053568, coefficient := 32630319896756151312195747053568 }, { argument := 761797351675240886666048569344, coefficient := 761797351675240886666048569344 }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17
