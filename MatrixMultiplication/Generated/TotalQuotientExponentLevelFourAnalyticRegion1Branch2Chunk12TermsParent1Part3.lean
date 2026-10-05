import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 12, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-114473342285736709209084655566848)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    49365425283, 21789, 21789, 1866591, 21789, 723879,
    1866591, 1356408189, 21789, 21789, 45999, 13799631043,
    50096025745, 3449907627, 675, 13527, 22707, 21789,
    675, 21789, 14553, 351, 13527, 81,
    24256225, 2030952735, 1015476735, 12127745, 675, 13527,
    22707, 21789, 675, 21789, 14553, 351,
    13527, 81, 155932875, 13056124725, 6528064725, 77964075,
    65011245, 4800910335, 50039085525, 4800910335, 65011245, 24256225,
    2030952735, 1015476735, 12127745, 65011245, 4800910335, 50039085525,
    4800910335, 65011245, 128865525, 1425, 4751697675, 22425,
    675, 9502676925, 675, 675
  ]
def negativeCoefficients : Array ℕ := #[
    455315683142665957471539953664, 411582573180986798244888576, 411582573180986798244888576, 17629453551252267858156060672, 411582573180986798244888576, 3418421927253195907645046784,
    17629453551252267858156060672, 12510657360983427709730291712, 411582573180986798244888576, 411582573180986798244888576, 434448271691041620369604608, 31819782770229826080720551936,
    115513570753497484425942794240, 31819781536603816151394287616, 12750389503748042076979200, 255517805655110763222663168, 428923102906084135469580288, 411582573180986798244888576,
    12750389503748042076979200, 411582573180986798244888576, 274898397700807787179671552, 13260405083897963760058368, 255517805655110763222663168, 12240373923598120393900032,
    111862093692328867161702400, 9366116332086363862534717440, 9366119721675587406664826880, 111858704103105323031592960, 12750389503748042076979200, 255517805655110763222663168,
    428923102906084135469580288, 411582573180986798244888576, 12750389503748042076979200, 411582573180986798244888576, 274898397700807787179671552, 13260405083897963760058368,
    255517805655110763222663168, 12240373923598120393900032, 2876453837802742298443776000, 240842991396506499322321305600, 240843078557372247599952691200, 2876366676936994020812390400,
    149905724803528714868490240, 22140291067643047035367587840, 230764551090534789330606489600, 22140291067643047035367587840, 149905724803528714868490240, 111862093692328867161702400,
    9366116332086363862534717440, 9366119721675587406664826880, 111858704103105323031592960, 149905724803528714868490240, 22140291067643047035367587840, 230764551090534789330606489600,
    22140291067643047035367587840, 149905724803528714868490240, 594287339899805016627609600, 13458744476178488859033600, 21913337731591426259759923200, 105899068378351793917132800,
    12750389503748042076979200, 21911681156327531911682457600, 12750389503748042076979200, 12750389503748042076979200
  ]
def negativeScales : Array ℕ := #[
    35, 14, 14, 20, 14, 19,
    20, 30, 14, 14, 15, 33,
    35, 31, 9, 13, 14, 14,
    9, 14, 13, 8, 13, 6,
    24, 30, 29, 23, 9, 13,
    14, 14, 9, 14, 13, 8,
    13, 6, 27, 33, 32, 26,
    25, 32, 35, 32, 25, 24,
    30, 29, 23, 25, 32, 35,
    32, 25, 26, 10, 32, 14,
    9, 33, 9, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35522781904924870, 14411312365441260, 14411312365441260, 20831974415136888, 14411312365441260, 19465389038197124,
    20831974415136888, 30337144253425401, 14411312365441260, 14411312365441260, 15489314877442711, 33683910643495253,
    35543977103883911, 31683910587563188, 9398743691938200, 13723554295483443, 14470849492418713, 14411312365441260,
    9398743691938200, 14411312365441260, 13829028966070369, 8455327220304618, 13723554295483443, 6339850002884626,
    24531851705291009, 30919509525308549, 29919510047418571, 23531807988804994, 9398743691938200, 13723554295483443,
    14470849492418713, 14411312365441260, 9398743691938200, 14411312365441260, 13829028966070369, 8455327220304618,
    13723554295483443, 6339850002884626, 27216349879562319, 33604007693415917, 32604008215525883, 26216306163076306,
    25954185958193574, 32160660845500612, 35542336373058610, 32160660845500612, 25954185958193574, 24531851705291009,
    30919509525308549, 29919510047418571, 23531807988804994, 25954185958193574, 32160660845500612, 35542336373058610,
    32160660845500612, 25954185958193574, 26941291123613888, 10476746203939589, 32145795902108676, 14452820364694038,
    9398743691938200, 33145686835051553, 9398743691938200, 9398743691938200
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
noncomputable def negativeCeiling : ℝ := 741502729 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 455315683142665957471539953664, coefficient := (-455315683142665957471539953664) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 17629453551252267858156060672, coefficient := (-17629453551252267858156060672) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 3418421927253195907645046784, coefficient := (-3418421927253195907645046784) }, { argument := 17629453551252267858156060672, coefficient := (-17629453551252267858156060672) }, { argument := 12510657360983427709730291712, coefficient := (-12510657360983427709730291712) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 31819782770229826080720551936, coefficient := (-31819782770229826080720551936) }, { argument := 115513570753497484425942794240, coefficient := (-115513570753497484425942794240) }, { argument := 31819781536603816151394287616, coefficient := (-31819781536603816151394287616) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 428923102906084135469580288, coefficient := (-428923102906084135469580288) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 274898397700807787179671552, coefficient := (-274898397700807787179671552) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 12240373923598120393900032, coefficient := (-12240373923598120393900032) }, { argument := 111862093692328867161702400, coefficient := (-111862093692328867161702400) }, { argument := 9366116332086363862534717440, coefficient := (-9366116332086363862534717440) }, { argument := 9366119721675587406664826880, coefficient := (-9366119721675587406664826880) }, { argument := 111858704103105323031592960, coefficient := (-111858704103105323031592960) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 428923102906084135469580288, coefficient := (-428923102906084135469580288) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 274898397700807787179671552, coefficient := (-274898397700807787179671552) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 12240373923598120393900032, coefficient := (-12240373923598120393900032) }, { argument := 2876453837802742298443776000, coefficient := (-2876453837802742298443776000) }, { argument := 240842991396506499322321305600, coefficient := (-240842991396506499322321305600) }, { argument := 240843078557372247599952691200, coefficient := (-240843078557372247599952691200) }, { argument := 2876366676936994020812390400, coefficient := (-2876366676936994020812390400) }, { argument := 149905724803528714868490240, coefficient := (-149905724803528714868490240) }, { argument := 22140291067643047035367587840, coefficient := (-22140291067643047035367587840) }, { argument := 230764551090534789330606489600, coefficient := (-230764551090534789330606489600) }, { argument := 22140291067643047035367587840, coefficient := (-22140291067643047035367587840) }, { argument := 149905724803528714868490240, coefficient := (-149905724803528714868490240) }, { argument := 111862093692328867161702400, coefficient := (-111862093692328867161702400) }, { argument := 9366116332086363862534717440, coefficient := (-9366116332086363862534717440) }, { argument := 9366119721675587406664826880, coefficient := (-9366119721675587406664826880) }, { argument := 111858704103105323031592960, coefficient := (-111858704103105323031592960) }, { argument := 149905724803528714868490240, coefficient := (-149905724803528714868490240) }, { argument := 22140291067643047035367587840, coefficient := (-22140291067643047035367587840) }, { argument := 230764551090534789330606489600, coefficient := (-230764551090534789330606489600) }, { argument := 22140291067643047035367587840, coefficient := (-22140291067643047035367587840) }, { argument := 149905724803528714868490240, coefficient := (-149905724803528714868490240) }, { argument := 594287339899805016627609600, coefficient := (-594287339899805016627609600) }, { argument := 13458744476178488859033600, coefficient := (-13458744476178488859033600) }, { argument := 21913337731591426259759923200, coefficient := (-21913337731591426259759923200) }, { argument := 105899068378351793917132800, coefficient := (-105899068378351793917132800) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 21911681156327531911682457600, coefficient := (-21911681156327531911682457600) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }] }

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

end TermShard6


end Parent1

namespace Parent1

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-806205478663532104958515320193024)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    57825, 675, 22425, 57825, 258449475, 675,
    675, 1425, 1425, 28557, 47937, 45999,
    1425, 45999, 30723, 741, 28557, 171,
    315330925, 26402385555, 13201197555, 157660685, 65011245, 4800910335,
    50039085525, 4800910335, 65011245, 315330925, 26402385555, 13201197555,
    157660685, 65011245, 4800910335, 50039085525, 4800910335, 65011245,
    2701276353, 45999, 98585104191, 723879, 21789, 197155306857,
    21789, 21789, 1866591, 21789, 723879, 1866591,
    5417454231, 21789, 21789, 45999, 65011245, 4800910335,
    50039085525, 4800910335, 65011245, 1343581953, 30723, 49510427391,
    483483, 14553, 99013369257, 14553
  ]
def negativeCoefficients : Array ℕ := #[
    546141683743874468963942400, 12750389503748042076979200, 105899068378351793917132800, 546141683743874468963942400, 595943915163699364705075200, 12750389503748042076979200,
    12750389503748042076979200, 13458744476178488859033600, 13458744476178488859033600, 269713239302616916735033344, 452752164178644365217890304, 434448271691041620369604608,
    13458744476178488859033600, 434448271691041620369604608, 290170530906408219800764416, 13997094255225628413394944, 269713239302616916735033344, 12920394697131349304672256,
    2908414436000550546204262400, 243519024634245460425902653440, 243519112763565272573285498880, 2908326306680738398821416960, 149905724803528714868490240, 22140291067643047035367587840,
    230764551090534789330606489600, 22140291067643047035367587840, 149905724803528714868490240, 2908414436000550546204262400, 243519024634245460425902653440, 243519112763565272573285498880,
    2908326306680738398821416960, 4796983193712918875791687680, 708489314164577505131762810880, 7384465634897113258579407667200, 708489314164577505131762810880, 4796983193712918875791687680,
    12457438389038625192633434112, 434448271691041620369604608, 454643546622841982483813105664, 3418421927253195907645046784, 411582573180986798244888576, 454609186045594109393045028864,
    411582573180986798244888576, 411582573180986798244888576, 17629453551252267858156060672, 411582573180986798244888576, 3418421927253195907645046784, 17629453551252267858156060672,
    12491798966286498283401510912, 411582573180986798244888576, 411582573180986798244888576, 434448271691041620369604608, 149905724803528714868490240, 22140291067643047035367587840,
    230764551090534789330606489600, 22140291067643047035367587840, 149905724803528714868490240, 12392356214522927657489793024, 290170530906408219800764416, 456653091530878153653567356928,
    2283183914237264676853383168, 274898397700807787179671552, 456618570639895064980727267328, 274898397700807787179671552
  ]
def negativeScales : Array ℕ := #[
    15, 9, 14, 15, 27, 9,
    9, 10, 10, 14, 15, 15,
    10, 15, 14, 9, 14, 7,
    28, 34, 33, 27, 25, 32,
    35, 32, 25, 28, 34, 33,
    27, 25, 32, 35, 32, 25,
    31, 15, 36, 19, 14, 37,
    14, 14, 20, 14, 19, 20,
    32, 14, 14, 15, 25, 32,
    35, 32, 25, 30, 14, 35,
    18, 13, 36, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15819405741365596, 9398743691938200, 14452820364694038, 15819405741365596, 27945307040402581, 9398743691938200,
    9398743691938200, 10476746203939589, 10476746203939589, 14801556808026795, 15548852004421171, 15489314877442711,
    10476746203939589, 15489314877442711, 14907031481868981, 9533329732306630, 14801556808026795, 7417852514885912,
    28232291423431341, 34619949237288353, 33619949759398319, 27232247706945328, 25954185958193574, 32160660845500612,
    35542336373058610, 32160660845500612, 25954185958193574, 28232291423431341, 34619949237288353, 33619949759398319,
    27232247706945328, 25954185958193574, 32160660845500612, 35542336373058610, 32160660845500612, 25954185958193574,
    31330994095724245, 15489314877442711, 36520650626580521, 19465389038197124, 14411312365441260, 37520541587954315,
    14411312365441260, 14411312365441260, 20831974415136888, 14411312365441260, 19465389038197124, 20831974415136888,
    32334967913844066, 14411312365441260, 14411312365441260, 15489314877442711, 25954185958193574, 32160660845500612,
    35542336373058610, 32160660845500612, 25954185958193574, 30323437176513926, 14907031481868981, 35527013352066794,
    18883105640887843, 13829028966070369, 36526904286779178, 13829028966070369
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
noncomputable def negativeCeiling : ℝ := 258725323 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 546141683743874468963942400, coefficient := (-546141683743874468963942400) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 105899068378351793917132800, coefficient := (-105899068378351793917132800) }, { argument := 546141683743874468963942400, coefficient := (-546141683743874468963942400) }, { argument := 595943915163699364705075200, coefficient := (-595943915163699364705075200) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 13458744476178488859033600, coefficient := (-13458744476178488859033600) }, { argument := 13458744476178488859033600, coefficient := (-13458744476178488859033600) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 452752164178644365217890304, coefficient := (-452752164178644365217890304) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 13458744476178488859033600, coefficient := (-13458744476178488859033600) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 290170530906408219800764416, coefficient := (-290170530906408219800764416) }, { argument := 13997094255225628413394944, coefficient := (-13997094255225628413394944) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 12920394697131349304672256, coefficient := (-12920394697131349304672256) }, { argument := 2908414436000550546204262400, coefficient := (-2908414436000550546204262400) }, { argument := 243519024634245460425902653440, coefficient := (-243519024634245460425902653440) }, { argument := 243519112763565272573285498880, coefficient := (-243519112763565272573285498880) }, { argument := 2908326306680738398821416960, coefficient := (-2908326306680738398821416960) }, { argument := 149905724803528714868490240, coefficient := (-149905724803528714868490240) }, { argument := 22140291067643047035367587840, coefficient := (-22140291067643047035367587840) }, { argument := 230764551090534789330606489600, coefficient := (-230764551090534789330606489600) }, { argument := 22140291067643047035367587840, coefficient := (-22140291067643047035367587840) }, { argument := 149905724803528714868490240, coefficient := (-149905724803528714868490240) }, { argument := 2908414436000550546204262400, coefficient := (-2908414436000550546204262400) }, { argument := 243519024634245460425902653440, coefficient := (-243519024634245460425902653440) }, { argument := 243519112763565272573285498880, coefficient := (-243519112763565272573285498880) }, { argument := 2908326306680738398821416960, coefficient := (-2908326306680738398821416960) }, { argument := 4796983193712918875791687680, coefficient := (-4796983193712918875791687680) }, { argument := 708489314164577505131762810880, coefficient := (-708489314164577505131762810880) }, { argument := 7384465634897113258579407667200, coefficient := (-7384465634897113258579407667200) }, { argument := 708489314164577505131762810880, coefficient := (-708489314164577505131762810880) }, { argument := 4796983193712918875791687680, coefficient := (-4796983193712918875791687680) }, { argument := 12457438389038625192633434112, coefficient := (-12457438389038625192633434112) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 454643546622841982483813105664, coefficient := (-454643546622841982483813105664) }, { argument := 3418421927253195907645046784, coefficient := (-3418421927253195907645046784) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 454609186045594109393045028864, coefficient := (-454609186045594109393045028864) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 17629453551252267858156060672, coefficient := (-17629453551252267858156060672) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 3418421927253195907645046784, coefficient := (-3418421927253195907645046784) }, { argument := 17629453551252267858156060672, coefficient := (-17629453551252267858156060672) }, { argument := 12491798966286498283401510912, coefficient := (-12491798966286498283401510912) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 149905724803528714868490240, coefficient := (-149905724803528714868490240) }, { argument := 22140291067643047035367587840, coefficient := (-22140291067643047035367587840) }, { argument := 230764551090534789330606489600, coefficient := (-230764551090534789330606489600) }, { argument := 22140291067643047035367587840, coefficient := (-22140291067643047035367587840) }, { argument := 149905724803528714868490240, coefficient := (-149905724803528714868490240) }, { argument := 12392356214522927657489793024, coefficient := (-12392356214522927657489793024) }, { argument := 290170530906408219800764416, coefficient := (-290170530906408219800764416) }, { argument := 456653091530878153653567356928, coefficient := (-456653091530878153653567356928) }, { argument := 2283183914237264676853383168, coefficient := (-2283183914237264676853383168) }, { argument := 274898397700807787179671552, coefficient := (-274898397700807787179671552) }, { argument := 456618570639895064980727267328, coefficient := (-456618570639895064980727267328) }, { argument := 274898397700807787179671552, coefficient := (-274898397700807787179671552) }] }

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

end TermShard7


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
