import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 1, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-811698492679118874452062820630528)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    31318529445, 40996246473, 1305612945, 39951756117, 22717665243, 40996246473,
    640011465639, 783367767, 5570500509, 39951756117, 1305612945, 783367767,
    1305612945, 20106439353, 22717665243, 796645953, 1863175095, 156002038857,
    78001047657, 931559319, 1070369327, 112226293453, 1209687273375, 56113189531,
    1070369327, 8353374253, 326788603, 100482183595, 8086279687, 257259113,
    100482232373, 132106031, 132106031, 4470746207, 243353215, 8086279687,
    4470746207, 8353325475, 257259113, 243353215, 326788603, 25818695,
    2707043605, 29179224375, 1353522835, 25818695, 5453671299, 95432449161,
    95432495967, 5453624493, 207042325, 5663133895, 1656338065, 159358149,
    771777339, 159358149, 60888075, 5098105845, 2549053845, 30443115,
    150744195, 730059645, 150744195, 36532845
  ]
def negativeCoefficients : Array ℕ := #[
    144431224359212960665860833280, 189061816667537214365962862592, 6021076963934306189998817280, 184244955096389769413963808768, 104766739172456927705979420672, 189061816667537214365962862592,
    2951531927720596894337420230656, 115604677707538678847977291776, 205515194503983581590179545088, 184244955096389769413963808768, 6021076963934306189998817280, 115604677707538678847977291776,
    6021076963934306189998817280, 185449170489176630651963572224, 104766739172456927705979420672, 7347762006173723996165505024, 2148094633873405052159262720, 179858105360748246458204946432,
    179858170451237632046964670464, 2148029543384019463399538688, 4936207259879432789172420608, 517552428417129200486566592512, 5578697885293036879013216256000, 517552823218957552036817666048,
    4936207259879432789172420608, 9630784812312856416829308928, 3014092862873036700174516224, 231696140593057672273005117440, 74582765947262588985169412096, 2372796509070262934179938304,
    231696253067467975698568708096, 2436926144450540310779396096, 2436926144450540310779396096, 41235355549518353153451360256, 2244537238309708180981022720, 74582765947262588985169412096,
    41235355549518353153451360256, 9630728575107704704047513600, 2372796509070262934179938304, 2244537238309708180981022720, 3014092862873036700174516224, 119067714745541107940065280,
    12484035144451772582377553920, 134565421078743136295976960000, 12484044667583400634933575680, 119067714745541107940065280, 6287654919674257631896141824, 220052245750033102659253174272,
    220052353677320991915412291584, 6287600956030313003816583168, 3819256781700796941284147200, 13058297702026867517727703040, 3819255548074787011957882880, 183727436916442106821607424,
    1779597381802697200634953728, 183727436916442106821607424, 70199171041614544188211200, 5877715861462360995366174720, 5877717988602536994998845440, 70197043901438544555540480,
    173796224110147938885304320, 1683402928732281135735767040, 173796224110147938885304320, 1347824083998999248413655040
  ]
def negativeScales : Array ℕ := #[
    34, 35, 30, 35, 34, 35,
    39, 29, 32, 35, 30, 29,
    30, 34, 34, 29, 30, 37,
    36, 29, 29, 36, 40, 35,
    29, 32, 28, 36, 32, 27,
    36, 26, 26, 32, 27, 32,
    32, 32, 27, 27, 28, 24,
    31, 34, 30, 24, 32, 36,
    36, 32, 27, 32, 30, 27,
    29, 27, 25, 32, 31, 24,
    27, 29, 27, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34866297424005600, 35254772774636470, 30282080120632205, 35217539868437495, 34403095521593579, 35254772774636470,
    39219306794611683, 29545114526467145, 32375159813402873, 35217539868437495, 30282080120632205, 29545114526467145,
    30282080120632205, 34226938566439744, 34403095521593579, 29569363460311139, 30795116114904183, 37182773928166852,
    36182774450276818, 29795072398417646, 29995461555151818, 36707619767835194, 40137771270888864, 35707620868358335,
    29995461555151818, 32959711942256018, 28283782428377789, 36548148764890330, 32912828963660608, 27938646950923612,
    36548149465231018, 26977121106505271, 26977121106505271, 32057868504028099, 27858476595679667, 32912828963660608,
    32057868504028099, 32959703517876066, 27938646950923612, 27858476595679667, 28283782428377789, 24621912746020716,
    31334070980626907, 34764222484072990, 30334072081150045, 24621912746020716, 32344580603452276, 36473760847010287,
    36473761554597361, 32344568221504381, 27625350482515018, 32398953494242435, 30625350016522151, 27247697554313128,
    29523609443050843, 27247697554313128, 25859656368594626, 32247314180361563, 31247314702471529, 24859612652106899,
    27167527205629145, 29443439094366311, 27167527205629145, 25122690772348074
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
noncomputable def negativeCeiling : ℝ := 187588969 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 144431224359212960665860833280, coefficient := (-144431224359212960665860833280) }, { argument := 189061816667537214365962862592, coefficient := (-189061816667537214365962862592) }, { argument := 6021076963934306189998817280, coefficient := (-6021076963934306189998817280) }, { argument := 184244955096389769413963808768, coefficient := (-184244955096389769413963808768) }, { argument := 104766739172456927705979420672, coefficient := (-104766739172456927705979420672) }, { argument := 189061816667537214365962862592, coefficient := (-189061816667537214365962862592) }, { argument := 2951531927720596894337420230656, coefficient := (-2951531927720596894337420230656) }, { argument := 115604677707538678847977291776, coefficient := (-115604677707538678847977291776) }, { argument := 205515194503983581590179545088, coefficient := (-205515194503983581590179545088) }, { argument := 184244955096389769413963808768, coefficient := (-184244955096389769413963808768) }, { argument := 6021076963934306189998817280, coefficient := (-6021076963934306189998817280) }, { argument := 115604677707538678847977291776, coefficient := (-115604677707538678847977291776) }, { argument := 6021076963934306189998817280, coefficient := (-6021076963934306189998817280) }, { argument := 185449170489176630651963572224, coefficient := (-185449170489176630651963572224) }, { argument := 104766739172456927705979420672, coefficient := (-104766739172456927705979420672) }, { argument := 7347762006173723996165505024, coefficient := (-7347762006173723996165505024) }, { argument := 2148094633873405052159262720, coefficient := (-2148094633873405052159262720) }, { argument := 179858105360748246458204946432, coefficient := (-179858105360748246458204946432) }, { argument := 179858170451237632046964670464, coefficient := (-179858170451237632046964670464) }, { argument := 2148029543384019463399538688, coefficient := (-2148029543384019463399538688) }, { argument := 4936207259879432789172420608, coefficient := (-4936207259879432789172420608) }, { argument := 517552428417129200486566592512, coefficient := (-517552428417129200486566592512) }, { argument := 5578697885293036879013216256000, coefficient := (-5578697885293036879013216256000) }, { argument := 517552823218957552036817666048, coefficient := (-517552823218957552036817666048) }, { argument := 4936207259879432789172420608, coefficient := (-4936207259879432789172420608) }, { argument := 9630784812312856416829308928, coefficient := (-9630784812312856416829308928) }, { argument := 3014092862873036700174516224, coefficient := (-3014092862873036700174516224) }, { argument := 231696140593057672273005117440, coefficient := (-231696140593057672273005117440) }, { argument := 74582765947262588985169412096, coefficient := (-74582765947262588985169412096) }, { argument := 2372796509070262934179938304, coefficient := (-2372796509070262934179938304) }, { argument := 231696253067467975698568708096, coefficient := (-231696253067467975698568708096) }, { argument := 2436926144450540310779396096, coefficient := (-2436926144450540310779396096) }, { argument := 2436926144450540310779396096, coefficient := (-2436926144450540310779396096) }, { argument := 41235355549518353153451360256, coefficient := (-41235355549518353153451360256) }, { argument := 2244537238309708180981022720, coefficient := (-2244537238309708180981022720) }, { argument := 74582765947262588985169412096, coefficient := (-74582765947262588985169412096) }, { argument := 41235355549518353153451360256, coefficient := (-41235355549518353153451360256) }, { argument := 9630728575107704704047513600, coefficient := (-9630728575107704704047513600) }, { argument := 2372796509070262934179938304, coefficient := (-2372796509070262934179938304) }, { argument := 2244537238309708180981022720, coefficient := (-2244537238309708180981022720) }, { argument := 3014092862873036700174516224, coefficient := (-3014092862873036700174516224) }, { argument := 119067714745541107940065280, coefficient := (-119067714745541107940065280) }, { argument := 12484035144451772582377553920, coefficient := (-12484035144451772582377553920) }, { argument := 134565421078743136295976960000, coefficient := (-134565421078743136295976960000) }, { argument := 12484044667583400634933575680, coefficient := (-12484044667583400634933575680) }, { argument := 119067714745541107940065280, coefficient := (-119067714745541107940065280) }, { argument := 6287654919674257631896141824, coefficient := (-6287654919674257631896141824) }, { argument := 220052245750033102659253174272, coefficient := (-220052245750033102659253174272) }, { argument := 220052353677320991915412291584, coefficient := (-220052353677320991915412291584) }, { argument := 6287600956030313003816583168, coefficient := (-6287600956030313003816583168) }, { argument := 3819256781700796941284147200, coefficient := (-3819256781700796941284147200) }, { argument := 13058297702026867517727703040, coefficient := (-13058297702026867517727703040) }, { argument := 3819255548074787011957882880, coefficient := (-3819255548074787011957882880) }, { argument := 183727436916442106821607424, coefficient := (-183727436916442106821607424) }, { argument := 1779597381802697200634953728, coefficient := (-1779597381802697200634953728) }, { argument := 183727436916442106821607424, coefficient := (-183727436916442106821607424) }, { argument := 70199171041614544188211200, coefficient := (-70199171041614544188211200) }, { argument := 5877715861462360995366174720, coefficient := (-5877715861462360995366174720) }, { argument := 5877717988602536994998845440, coefficient := (-5877717988602536994998845440) }, { argument := 70197043901438544555540480, coefficient := (-70197043901438544555540480) }, { argument := 173796224110147938885304320, coefficient := (-173796224110147938885304320) }, { argument := 1683402928732281135735767040, coefficient := (-1683402928732281135735767040) }, { argument := 173796224110147938885304320, coefficient := (-173796224110147938885304320) }, { argument := 1347824083998999248413655040, coefficient := (-1347824083998999248413655040) }] }

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


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-248791666223375766216827719385088)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3058863507, 1529432307, 18265869, 25818695, 2707043605, 29179224375,
    1353522835, 25818695, 60888075, 5098105845, 2549053845, 30443115,
    11065155, 1160161545, 12505381875, 580081215, 11065155, 168948925,
    2956395575, 2956397025, 168947475, 202427919, 980365809, 202427919,
    937676355, 78510830013, 39255429213, 468823971, 25818695, 2707043605,
    29179224375, 1353522835, 25818695, 1059452505, 88707041703, 44353536903,
    529710201, 291382415, 30550920685, 329308389375, 15275471995, 291382415,
    5453671299, 95432449161, 95432495967, 5453624493, 11065155, 1160161545,
    12505381875, 580081215, 11065155, 3642538823, 63739888597, 63739919859,
    3642507561, 189240555, 5176210233, 1513923951, 89045445, 3112876467,
    6564075, 5813895, 272127795, 74080275
  ]
def negativeCoefficients : Array ℕ := #[
    112852144540077331111030554624, 112852185381168710303977832448, 1347783242907620055466377216, 119067714745541107940065280, 12484035144451772582377553920, 134565421078743136295976960000,
    12484044667583400634933575680, 119067714745541107940065280, 70199171041614544188211200, 5877715861462360995366174720, 5877717988602536994998845440, 70197043901438544555540480,
    102058041210463806805770240, 10700601552387233642037903360, 115341789496065545396551680000, 10700609715071486258514493440, 102058041210463806805770240, 194784848812709344234700800,
    6816984069084049029097062400, 6816987412556412388953292800, 194783177076527664306585600, 233383500947912946503122944, 2260569647154777525130887168, 233383500947912946503122944,
    2162134468081727960996904960, 181033648533040718657278181376, 181033714048958139445964439552, 2162068952164307172310646784, 119067714745541107940065280, 12484035144451772582377553920,
    134565421078743136295976960000, 12484044667583400634933575680, 119067714745541107940065280, 1221465576124093068874874880, 102272255989445081319371440128, 102272293001684143712979910656,
    1221428563885030675266404352, 1343764209271106789609308160, 140891253773098576286832394240, 1518666895031529681054597120000, 140891361248441235737107496960, 1343764209271106789609308160,
    6287654919674257631896141824, 220052245750033102659253174272, 220052353677320991915412291584, 6287600956030313003816583168, 102058041210463806805770240, 10700601552387233642037903360,
    115341789496065545396551680000, 10700609715071486258514493440, 102058041210463806805770240, 4199561340402013461700149248, 146974176529452097067332665344, 146974248614716251105832992768,
    4199525297769936442449985536, 3490872086451756456612986880, 11935528179983435918072610816, 3490870958894524951116644352, 205324816855572478049648640, 7177804439977772077321027584,
    121085811605635025023795200, 107247433136419593592504320, 5019871789707897751700766720, 1366539873835023853839974400
  ]
def negativeScales : Array ℕ := #[
    31, 30, 24, 24, 31, 34,
    30, 24, 25, 32, 31, 24,
    23, 30, 33, 29, 23, 27,
    31, 31, 27, 27, 29, 27,
    29, 36, 35, 28, 24, 31,
    34, 30, 24, 29, 36, 35,
    28, 28, 34, 38, 33, 28,
    32, 36, 36, 32, 23, 30,
    33, 29, 23, 31, 35, 35,
    31, 27, 32, 30, 26, 31,
    22, 22, 28, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31510348586195738, 30510349108305704, 24122647055862061, 24621912746020716, 31334070980626907, 34764222484072990,
    30334072081150045, 24621912746020716, 25859656368594626, 32247314180361563, 31247314702471529, 24859612652106899,
    23399520324674021, 30111678559290459, 33541830062431674, 29111679659813597, 23399520324674021, 27332011929949220,
    31461192173507191, 31461192881094266, 27331999548001325, 27592833040366447, 29868744931565702, 27592833040366447,
    29804514813029942, 36192172626169102, 35192173148279068, 28804471096543302, 24621912746020716, 31334070980626907,
    34764222484072990, 30334072081150045, 24621912746020716, 29980671784813928, 36368329581322930, 35368330103432896,
    28980628068315566, 28118338572129962, 34830496807934487, 38260648309886585, 33830497908457651, 28118338572129962,
    32344580603452276, 36473760847010287, 36473761554597361, 32344568221504381, 23399520324674021, 30111678559290459,
    33541830062431674, 29111679659813597, 23399520324674021, 31762297203220530, 35891477450230651, 35891478157817773,
    31762284821272558, 27495646056167742, 32269249067906154, 30495645590174876, 26408038478301092, 31535601179273895,
    22646160292276457, 22471073585699149, 28019709079378918, 26142586118376639
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
noncomputable def negativeCeiling : ℝ := 434659427 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 112852144540077331111030554624, coefficient := (-112852144540077331111030554624) }, { argument := 112852185381168710303977832448, coefficient := (-112852185381168710303977832448) }, { argument := 1347783242907620055466377216, coefficient := (-1347783242907620055466377216) }, { argument := 119067714745541107940065280, coefficient := (-119067714745541107940065280) }, { argument := 12484035144451772582377553920, coefficient := (-12484035144451772582377553920) }, { argument := 134565421078743136295976960000, coefficient := (-134565421078743136295976960000) }, { argument := 12484044667583400634933575680, coefficient := (-12484044667583400634933575680) }, { argument := 119067714745541107940065280, coefficient := (-119067714745541107940065280) }, { argument := 70199171041614544188211200, coefficient := (-70199171041614544188211200) }, { argument := 5877715861462360995366174720, coefficient := (-5877715861462360995366174720) }, { argument := 5877717988602536994998845440, coefficient := (-5877717988602536994998845440) }, { argument := 70197043901438544555540480, coefficient := (-70197043901438544555540480) }, { argument := 102058041210463806805770240, coefficient := (-102058041210463806805770240) }, { argument := 10700601552387233642037903360, coefficient := (-10700601552387233642037903360) }, { argument := 115341789496065545396551680000, coefficient := (-115341789496065545396551680000) }, { argument := 10700609715071486258514493440, coefficient := (-10700609715071486258514493440) }, { argument := 102058041210463806805770240, coefficient := (-102058041210463806805770240) }, { argument := 194784848812709344234700800, coefficient := (-194784848812709344234700800) }, { argument := 6816984069084049029097062400, coefficient := (-6816984069084049029097062400) }, { argument := 6816987412556412388953292800, coefficient := (-6816987412556412388953292800) }, { argument := 194783177076527664306585600, coefficient := (-194783177076527664306585600) }, { argument := 233383500947912946503122944, coefficient := (-233383500947912946503122944) }, { argument := 2260569647154777525130887168, coefficient := (-2260569647154777525130887168) }, { argument := 233383500947912946503122944, coefficient := (-233383500947912946503122944) }, { argument := 2162134468081727960996904960, coefficient := (-2162134468081727960996904960) }, { argument := 181033648533040718657278181376, coefficient := (-181033648533040718657278181376) }, { argument := 181033714048958139445964439552, coefficient := (-181033714048958139445964439552) }, { argument := 2162068952164307172310646784, coefficient := (-2162068952164307172310646784) }, { argument := 119067714745541107940065280, coefficient := (-119067714745541107940065280) }, { argument := 12484035144451772582377553920, coefficient := (-12484035144451772582377553920) }, { argument := 134565421078743136295976960000, coefficient := (-134565421078743136295976960000) }, { argument := 12484044667583400634933575680, coefficient := (-12484044667583400634933575680) }, { argument := 119067714745541107940065280, coefficient := (-119067714745541107940065280) }, { argument := 1221465576124093068874874880, coefficient := (-1221465576124093068874874880) }, { argument := 102272255989445081319371440128, coefficient := (-102272255989445081319371440128) }, { argument := 102272293001684143712979910656, coefficient := (-102272293001684143712979910656) }, { argument := 1221428563885030675266404352, coefficient := (-1221428563885030675266404352) }, { argument := 1343764209271106789609308160, coefficient := (-1343764209271106789609308160) }, { argument := 140891253773098576286832394240, coefficient := (-140891253773098576286832394240) }, { argument := 1518666895031529681054597120000, coefficient := (-1518666895031529681054597120000) }, { argument := 140891361248441235737107496960, coefficient := (-140891361248441235737107496960) }, { argument := 1343764209271106789609308160, coefficient := (-1343764209271106789609308160) }, { argument := 6287654919674257631896141824, coefficient := (-6287654919674257631896141824) }, { argument := 220052245750033102659253174272, coefficient := (-220052245750033102659253174272) }, { argument := 220052353677320991915412291584, coefficient := (-220052353677320991915412291584) }, { argument := 6287600956030313003816583168, coefficient := (-6287600956030313003816583168) }, { argument := 102058041210463806805770240, coefficient := (-102058041210463806805770240) }, { argument := 10700601552387233642037903360, coefficient := (-10700601552387233642037903360) }, { argument := 115341789496065545396551680000, coefficient := (-115341789496065545396551680000) }, { argument := 10700609715071486258514493440, coefficient := (-10700609715071486258514493440) }, { argument := 102058041210463806805770240, coefficient := (-102058041210463806805770240) }, { argument := 4199561340402013461700149248, coefficient := (-4199561340402013461700149248) }, { argument := 146974176529452097067332665344, coefficient := (-146974176529452097067332665344) }, { argument := 146974248614716251105832992768, coefficient := (-146974248614716251105832992768) }, { argument := 4199525297769936442449985536, coefficient := (-4199525297769936442449985536) }, { argument := 3490872086451756456612986880, coefficient := (-3490872086451756456612986880) }, { argument := 11935528179983435918072610816, coefficient := (-11935528179983435918072610816) }, { argument := 3490870958894524951116644352, coefficient := (-3490870958894524951116644352) }, { argument := 205324816855572478049648640, coefficient := (-205324816855572478049648640) }, { argument := 7177804439977772077321027584, coefficient := (-7177804439977772077321027584) }, { argument := 121085811605635025023795200, coefficient := (-121085811605635025023795200) }, { argument := 107247433136419593592504320, coefficient := (-107247433136419593592504320) }, { argument := 5019871789707897751700766720, coefficient := (-5019871789707897751700766720) }, { argument := 1366539873835023853839974400, coefficient := (-1366539873835023853839974400) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1
