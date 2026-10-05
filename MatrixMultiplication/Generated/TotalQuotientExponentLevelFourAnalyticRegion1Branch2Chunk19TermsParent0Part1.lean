import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 19, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-8961995665066428269943253905702912)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    14763192741, 31166740231, 174080339, 12855377537, 133989450155, 12855377537,
    174080339, 6518788731, 244927638917, 489818229043, 13074626253, 816795501758369,
    2071119801, 116355045, 2957440311507451, 6290929433, 204198824458137, 6290929433,
    6290929433, 2071119801, 116355045, 196217721, 7372403847, 14743692513,
    393550623, 213143149401, 387623789735, 213143149401, 10959803031, 53561705,
    10959803031, 53561705, 3931464749589, 203697191563161, 210976510017, 6155549911048875,
    6955269561, 16228962309, 210976510017, 210976510017, 6955269561, 2603589239001,
    104329043415, 203697191563161, 210976510017, 16228962309, 104329043415, 16228962309,
    210976510017, 210976510017, 18099485918265, 85394580789581, 62328766049, 2669691741580851,
    980857949929, 29524152339, 21357521391204069, 29524152339, 29524152339, 2529235717041,
    29524152339, 980857949929, 2529235717041, 683169187759387
  ]
def negativeCoefficients : Array ℕ := #[
    272332838204073621359696019456, 287462440326522155879679131648, 401401932724699966606409728, 59284964848988410526667112448, 617917273896586903049857925120, 59284964848988410526667112448,
    401401932724699966606409728, 60125213695669429220721819648, 2259058735839921345468810919936, 2258887878448467007025679695872, 60296071087123767663853043712, 919629979339221984686957920256,
    38205416915039255874729148416, 2146371736799958195209502720, 3329781771218859984243260391424, 58023582618158869877163556864, 919629749739159117981340925952, 58023582618158869877163556864,
    58023582618158869877163556864, 38205416915039255874729148416, 2146371736799958195209502720, 7239156164027088468046774272, 271993693947281499788886933504, 271973122488778636297406251008,
    7259727622529951959527456768, 491474641008085789546226122752, 1787599211530737144265378365440, 491474641008085789546226122752, 25271585201390403901835968512, 123504883035816157417308160,
    25271585201390403901835968512, 123504883035816157417308160, 17705743181269260767166726144, 917370596020268421226331897856, 486478710731002325357700317184, 6930533071415050812153397248000,
    256604155110858369419446321152, 18710719643500089436834627584, 486478710731002325357700317184, 486478710731002325357700317184, 256604155110858369419446321152, 6003468045614457267875796221952,
    481132790832859442661461852160, 917370596020268421226331897856, 486478710731002325357700317184, 18710719643500089436834627584, 481132790832859442661461852160, 18710719643500089436834627584,
    486478710731002325357700317184, 486478710731002325357700317184, 20378209509273948405482127360, 1538332008893666830762014408704, 287440698934004963562588471296, 48092890930310444261725263888384,
    2261704446875460108031946129408, 272312241095373123375083814912, 48092862689492021237318902874112, 272312241095373123375083814912, 272312241095373123375083814912, 11664040993585148784566090072064,
    272312241095373123375083814912, 2261704446875460108031946129408, 11664040993585148784566090072064, 1538360249712089855168375422976
  ]
def negativeScales : Array ℕ := #[
    33, 34, 27, 33, 36, 33,
    27, 32, 37, 38, 33, 49,
    30, 26, 51, 32, 47, 32,
    32, 30, 26, 27, 32, 33,
    28, 37, 38, 37, 33, 25,
    33, 25, 41, 47, 37, 52,
    32, 33, 37, 37, 32, 41,
    36, 47, 37, 33, 36, 33,
    37, 37, 44, 46, 35, 51,
    39, 34, 54, 34, 34, 41,
    34, 39, 41, 49
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33781285706855895, 34859288220484159, 27375178030273267, 33581652928769270, 36963328469355220, 33581652928769270,
    27375178030273267, 32601956773337866, 37833564629371802, 38833455511164541, 33606050655532244, 49536968249477138,
    30947763870652839, 26793958525107394, 51393270474999368, 32550626033146626, 47536967889285626, 32550626033146626,
    32550626033146626, 30947763870652839, 26793958525107394, 27547880100577351, 32779487955777283, 33779378837571737,
    28551973982771183, 37633031730397105, 38495866160126912, 37633031730397105, 33351502819366134, 25674698550153947,
    33351502819366134, 25674698550153947, 41838204058941067, 47533419417977396, 37618291422946842, 52450809170110326,
    32695459283525025, 33917851710790743, 37618291422946842, 37618291422946842, 32695459283525025, 41243638995139440,
    36602349879074547, 47533419417977396, 37618291422946842, 33917851710790743, 36602349879074547, 33917851710790743,
    37618291422946842, 37618291422946842, 44041013954396547, 46279209751671071, 35859179102275331, 51245594592726336,
    39835253262271796, 34781176588650315, 54245593745555375, 34781176588650315, 34781176588650315, 41201838636685076,
    34781176588650315, 39835253262271796, 41201838636685076, 49279236236535508
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
noncomputable def negativeCeiling : ℝ := 47494569977 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 272332838204073621359696019456, coefficient := (-272332838204073621359696019456) }, { argument := 287462440326522155879679131648, coefficient := (-287462440326522155879679131648) }, { argument := 401401932724699966606409728, coefficient := (-401401932724699966606409728) }, { argument := 59284964848988410526667112448, coefficient := (-59284964848988410526667112448) }, { argument := 617917273896586903049857925120, coefficient := (-617917273896586903049857925120) }, { argument := 59284964848988410526667112448, coefficient := (-59284964848988410526667112448) }, { argument := 401401932724699966606409728, coefficient := (-401401932724699966606409728) }, { argument := 60125213695669429220721819648, coefficient := (-60125213695669429220721819648) }, { argument := 2259058735839921345468810919936, coefficient := (-2259058735839921345468810919936) }, { argument := 2258887878448467007025679695872, coefficient := (-2258887878448467007025679695872) }, { argument := 60296071087123767663853043712, coefficient := (-60296071087123767663853043712) }, { argument := 919629979339221984686957920256, coefficient := (-919629979339221984686957920256) }, { argument := 38205416915039255874729148416, coefficient := (-38205416915039255874729148416) }, { argument := 2146371736799958195209502720, coefficient := (-2146371736799958195209502720) }, { argument := 3329781771218859984243260391424, coefficient := (-3329781771218859984243260391424) }, { argument := 58023582618158869877163556864, coefficient := (-58023582618158869877163556864) }, { argument := 919629749739159117981340925952, coefficient := (-919629749739159117981340925952) }, { argument := 58023582618158869877163556864, coefficient := (-58023582618158869877163556864) }, { argument := 58023582618158869877163556864, coefficient := (-58023582618158869877163556864) }, { argument := 38205416915039255874729148416, coefficient := (-38205416915039255874729148416) }, { argument := 2146371736799958195209502720, coefficient := (-2146371736799958195209502720) }, { argument := 7239156164027088468046774272, coefficient := (-7239156164027088468046774272) }, { argument := 271993693947281499788886933504, coefficient := (-271993693947281499788886933504) }, { argument := 271973122488778636297406251008, coefficient := (-271973122488778636297406251008) }, { argument := 7259727622529951959527456768, coefficient := (-7259727622529951959527456768) }, { argument := 491474641008085789546226122752, coefficient := (-491474641008085789546226122752) }, { argument := 1787599211530737144265378365440, coefficient := (-1787599211530737144265378365440) }, { argument := 491474641008085789546226122752, coefficient := (-491474641008085789546226122752) }, { argument := 25271585201390403901835968512, coefficient := (-25271585201390403901835968512) }, { argument := 123504883035816157417308160, coefficient := (-123504883035816157417308160) }, { argument := 25271585201390403901835968512, coefficient := (-25271585201390403901835968512) }, { argument := 123504883035816157417308160, coefficient := (-123504883035816157417308160) }, { argument := 17705743181269260767166726144, coefficient := (-17705743181269260767166726144) }, { argument := 917370596020268421226331897856, coefficient := (-917370596020268421226331897856) }, { argument := 486478710731002325357700317184, coefficient := (-486478710731002325357700317184) }, { argument := 6930533071415050812153397248000, coefficient := (-6930533071415050812153397248000) }, { argument := 256604155110858369419446321152, coefficient := (-256604155110858369419446321152) }, { argument := 18710719643500089436834627584, coefficient := (-18710719643500089436834627584) }, { argument := 486478710731002325357700317184, coefficient := (-486478710731002325357700317184) }, { argument := 486478710731002325357700317184, coefficient := (-486478710731002325357700317184) }, { argument := 256604155110858369419446321152, coefficient := (-256604155110858369419446321152) }, { argument := 6003468045614457267875796221952, coefficient := (-6003468045614457267875796221952) }, { argument := 481132790832859442661461852160, coefficient := (-481132790832859442661461852160) }, { argument := 917370596020268421226331897856, coefficient := (-917370596020268421226331897856) }, { argument := 486478710731002325357700317184, coefficient := (-486478710731002325357700317184) }, { argument := 18710719643500089436834627584, coefficient := (-18710719643500089436834627584) }, { argument := 481132790832859442661461852160, coefficient := (-481132790832859442661461852160) }, { argument := 18710719643500089436834627584, coefficient := (-18710719643500089436834627584) }, { argument := 486478710731002325357700317184, coefficient := (-486478710731002325357700317184) }, { argument := 486478710731002325357700317184, coefficient := (-486478710731002325357700317184) }, { argument := 20378209509273948405482127360, coefficient := (-20378209509273948405482127360) }, { argument := 1538332008893666830762014408704, coefficient := (-1538332008893666830762014408704) }, { argument := 287440698934004963562588471296, coefficient := (-287440698934004963562588471296) }, { argument := 48092890930310444261725263888384, coefficient := (-48092890930310444261725263888384) }, { argument := 2261704446875460108031946129408, coefficient := (-2261704446875460108031946129408) }, { argument := 272312241095373123375083814912, coefficient := (-272312241095373123375083814912) }, { argument := 48092862689492021237318902874112, coefficient := (-48092862689492021237318902874112) }, { argument := 272312241095373123375083814912, coefficient := (-272312241095373123375083814912) }, { argument := 272312241095373123375083814912, coefficient := (-272312241095373123375083814912) }, { argument := 11664040993585148784566090072064, coefficient := (-11664040993585148784566090072064) }, { argument := 272312241095373123375083814912, coefficient := (-272312241095373123375083814912) }, { argument := 2261704446875460108031946129408, coefficient := (-2261704446875460108031946129408) }, { argument := 11664040993585148784566090072064, coefficient := (-11664040993585148784566090072064) }, { argument := 1538360249712089855168375422976, coefficient := (-1538360249712089855168375422976) }] }

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

end TermShard2


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4300012469037651077012742142427136)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    29524152339, 29524152339, 62328766049, 24621065120699843, 21586935315, 1212749175,
    89057759361802129, 65569305395, 6155264245301931, 65569305395, 65569305395, 21586935315,
    1212749175, 196217721, 7372403847, 14743692513, 393550623, 7026697233,
    12778806255, 7026697233, 88185154921, 4484675223, 88185154921, 4484675223,
    16395626877, 29817214595, 16395626877, 265, 265, 53561705,
    4484675223, 2242338423, 26780041, 174080339, 12855377537, 133989450155,
    12855377537, 174080339, 196217721, 7372403847, 14743692513, 393550623,
    174080339, 12855377537, 133989450155, 12855377537, 174080339, 16809318099,
    631569262893, 1263042991947, 33714170037, 213143149401, 387623789735, 213143149401,
    196217721, 7372403847, 14743692513, 393550623, 213143149401, 387623789735,
    213143149401, 2491, 2491, 57311283
  ]
def negativeCoefficients : Array ℕ := #[
    272312241095373123375083814912, 272312241095373123375083814912, 287440698934004963562588471296, 6930213731440533066044835627008, 398208671091527682832245719040, 22371273656827397911923916800,
    25067530742266460614044757786624, 604770097856233990219009884160, 6930211440377178433951780306944, 604770097856233990219009884160, 604770097856233990219009884160, 398208671091527682832245719040,
    22371273656827397911923916800, 7239156164027088468046774272, 271993693947281499788886933504, 271973122488778636297406251008, 7259727622529951959527456768, 259239371081188108771635757056,
    942909474214015196975144632320, 259239371081188108771635757056, 203341122991014431551800737792, 10340957011548413978839351296, 203341122991014431551800737792, 10340957011548413978839351296,
    18902870808003299597931773952, 68753815828105274779437629440, 18902870808003299597931773952, 20503381900664110803016744960, 20503381900664110803016744960, 123504883035816157417308160,
    10340957011548413978839351296, 10340960753931617932664635392, 123501140652612203592024064, 401401932724699966606409728, 59284964848988410526667112448, 617917273896586903049857925120,
    59284964848988410526667112448, 401401932724699966606409728, 7239156164027088468046774272, 271993693947281499788886933504, 271973122488778636297406251008, 7259727622529951959527456768,
    401401932724699966606409728, 59284964848988410526667112448, 617917273896586903049857925120, 59284964848988410526667112448, 401401932724699966606409728, 310077189025826956048003497984,
    11650396557408557574290656985088, 11649515413269351588072234418176, 310958333165032942266426064896, 491474641008085789546226122752, 1787599211530737144265378365440, 491474641008085789546226122752,
    7239156164027088468046774272, 271993693947281499788886933504, 271973122488778636297406251008, 7259727622529951959527456768, 491474641008085789546226122752, 1787599211530737144265378365440,
    491474641008085789546226122752, 24091473733280330193544675328, 24091473733280330193544675328, 264301642509235243116920832
  ]
def negativeScales : Array ℕ := #[
    34, 34, 35, 54, 34, 30,
    56, 35, 52, 35, 35, 34,
    30, 27, 32, 33, 28, 32,
    33, 32, 36, 32, 36, 32,
    33, 34, 33, 8, 8, 25,
    32, 31, 24, 27, 33, 36,
    33, 27, 27, 32, 33, 28,
    27, 33, 36, 33, 27, 33,
    39, 40, 34, 37, 38, 37,
    27, 32, 33, 28, 37, 38,
    37, 11, 11, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34781176588650315, 34781176588650315, 35859179102275331, 54450742693144225, 34329439388172497, 30175634052093461,
    56305590833119410, 35932301568409180, 52450742216202760, 35932301568409180, 35932301568409180, 34329439388172497,
    30175634052093461, 27547880100577351, 32779487955777283, 33779378837571737, 28551973982771183, 32710199590997660,
    33573034020651769, 32710199590997660, 36359816761975980, 32062356363961776, 36359816761975980, 32062356363961776,
    33932592019987913, 34795426442573932, 33932592019987913, 8049848549450562, 8049848549450562, 25674698550153947,
    32062356363961776, 31062356886071742, 24674654833667892, 27375178030273267, 33581652928769270, 36963328469355220,
    33581652928769270, 27375178030273267, 27547880100577351, 32779487955777283, 33779378837571737, 28551973982771183,
    27375178030273267, 33581652928769270, 36963328469355220, 33581652928769270, 27375178030273267, 33968542163257568,
    39200150003827261, 40200040885622682, 34972636046443361, 37633031730397105, 38495866160126912, 37633031730397105,
    27547880100577351, 32779487955777283, 33779378837571737, 28551973982771183, 37633031730397105, 38495866160126912,
    37633031730397105, 11282509306240837, 11282509306240837, 25772315858106994
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
noncomputable def negativeCeiling : ℝ := 21738645097 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 272312241095373123375083814912, coefficient := (-272312241095373123375083814912) }, { argument := 272312241095373123375083814912, coefficient := (-272312241095373123375083814912) }, { argument := 287440698934004963562588471296, coefficient := (-287440698934004963562588471296) }, { argument := 6930213731440533066044835627008, coefficient := (-6930213731440533066044835627008) }, { argument := 398208671091527682832245719040, coefficient := (-398208671091527682832245719040) }, { argument := 22371273656827397911923916800, coefficient := (-22371273656827397911923916800) }, { argument := 25067530742266460614044757786624, coefficient := (-25067530742266460614044757786624) }, { argument := 604770097856233990219009884160, coefficient := (-604770097856233990219009884160) }, { argument := 6930211440377178433951780306944, coefficient := (-6930211440377178433951780306944) }, { argument := 604770097856233990219009884160, coefficient := (-604770097856233990219009884160) }, { argument := 604770097856233990219009884160, coefficient := (-604770097856233990219009884160) }, { argument := 398208671091527682832245719040, coefficient := (-398208671091527682832245719040) }, { argument := 22371273656827397911923916800, coefficient := (-22371273656827397911923916800) }, { argument := 7239156164027088468046774272, coefficient := (-7239156164027088468046774272) }, { argument := 271993693947281499788886933504, coefficient := (-271993693947281499788886933504) }, { argument := 271973122488778636297406251008, coefficient := (-271973122488778636297406251008) }, { argument := 7259727622529951959527456768, coefficient := (-7259727622529951959527456768) }, { argument := 259239371081188108771635757056, coefficient := (-259239371081188108771635757056) }, { argument := 942909474214015196975144632320, coefficient := (-942909474214015196975144632320) }, { argument := 259239371081188108771635757056, coefficient := (-259239371081188108771635757056) }, { argument := 203341122991014431551800737792, coefficient := (-203341122991014431551800737792) }, { argument := 10340957011548413978839351296, coefficient := (-10340957011548413978839351296) }, { argument := 203341122991014431551800737792, coefficient := (-203341122991014431551800737792) }, { argument := 10340957011548413978839351296, coefficient := (-10340957011548413978839351296) }, { argument := 18902870808003299597931773952, coefficient := (-18902870808003299597931773952) }, { argument := 68753815828105274779437629440, coefficient := (-68753815828105274779437629440) }, { argument := 18902870808003299597931773952, coefficient := (-18902870808003299597931773952) }, { argument := 20503381900664110803016744960, coefficient := (-20503381900664110803016744960) }, { argument := 20503381900664110803016744960, coefficient := (-20503381900664110803016744960) }, { argument := 123504883035816157417308160, coefficient := (-123504883035816157417308160) }, { argument := 10340957011548413978839351296, coefficient := (-10340957011548413978839351296) }, { argument := 10340960753931617932664635392, coefficient := (-10340960753931617932664635392) }, { argument := 123501140652612203592024064, coefficient := (-123501140652612203592024064) }, { argument := 401401932724699966606409728, coefficient := (-401401932724699966606409728) }, { argument := 59284964848988410526667112448, coefficient := (-59284964848988410526667112448) }, { argument := 617917273896586903049857925120, coefficient := (-617917273896586903049857925120) }, { argument := 59284964848988410526667112448, coefficient := (-59284964848988410526667112448) }, { argument := 401401932724699966606409728, coefficient := (-401401932724699966606409728) }, { argument := 7239156164027088468046774272, coefficient := (-7239156164027088468046774272) }, { argument := 271993693947281499788886933504, coefficient := (-271993693947281499788886933504) }, { argument := 271973122488778636297406251008, coefficient := (-271973122488778636297406251008) }, { argument := 7259727622529951959527456768, coefficient := (-7259727622529951959527456768) }, { argument := 401401932724699966606409728, coefficient := (-401401932724699966606409728) }, { argument := 59284964848988410526667112448, coefficient := (-59284964848988410526667112448) }, { argument := 617917273896586903049857925120, coefficient := (-617917273896586903049857925120) }, { argument := 59284964848988410526667112448, coefficient := (-59284964848988410526667112448) }, { argument := 401401932724699966606409728, coefficient := (-401401932724699966606409728) }, { argument := 310077189025826956048003497984, coefficient := (-310077189025826956048003497984) }, { argument := 11650396557408557574290656985088, coefficient := (-11650396557408557574290656985088) }, { argument := 11649515413269351588072234418176, coefficient := (-11649515413269351588072234418176) }, { argument := 310958333165032942266426064896, coefficient := (-310958333165032942266426064896) }, { argument := 491474641008085789546226122752, coefficient := (-491474641008085789546226122752) }, { argument := 1787599211530737144265378365440, coefficient := (-1787599211530737144265378365440) }, { argument := 491474641008085789546226122752, coefficient := (-491474641008085789546226122752) }, { argument := 7239156164027088468046774272, coefficient := (-7239156164027088468046774272) }, { argument := 271993693947281499788886933504, coefficient := (-271993693947281499788886933504) }, { argument := 271973122488778636297406251008, coefficient := (-271973122488778636297406251008) }, { argument := 7259727622529951959527456768, coefficient := (-7259727622529951959527456768) }, { argument := 491474641008085789546226122752, coefficient := (-491474641008085789546226122752) }, { argument := 1787599211530737144265378365440, coefficient := (-1787599211530737144265378365440) }, { argument := 491474641008085789546226122752, coefficient := (-491474641008085789546226122752) }, { argument := 24091473733280330193544675328, coefficient := (-24091473733280330193544675328) }, { argument := 24091473733280330193544675328, coefficient := (-24091473733280330193544675328) }, { argument := 264301642509235243116920832, coefficient := (-264301642509235243116920832) }] }

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

end TermShard3


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19
