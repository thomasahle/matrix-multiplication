import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 23, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23

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
def constantNumerator : ℤ := (-298455761897312362369794499936256)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    711, 711, 47557, 1406389875, 6206286645, 732139095,
    64938950505, 2876084055, 1464277875, 2876084055, 5600795265, 105809618655,
    5600795265, 64938950505, 105809618655, 1406390085, 5600795265, 5600795265,
    6206286645, 2847558957, 8301602785, 6878470879, 140920927171, 46251786945,
    2847558557, 185244336431, 185244336431, 132588455909, 6878470879, 4248435207,
    4635217785, 4248435207, 4635217785, 44057675, 5149486875, 1409845125,
    225, 225, 8341051, 27, 27, 258285,
    122110515, 4635217785, 488442395, 258285, 2456483205, 47908035615,
    95816036085, 307061865, 85796525, 10027948125, 2745487875, 2456483205,
    47908035615, 95816036085, 307061865, 1620858675, 189446911875, 51867460125,
    711, 711, 85796525, 10027948125
  ]
def negativeCoefficients : Array ℕ := #[
    13752740123936021491457458176, 13752740123936021491457458176, 224581582825831717427740672, 6485828522995341770883072000, 7155361336774780362707435520, 13505582511822324412994027520,
    74869512523814165258572922880, 6631798312132723262997135360, 13505579606460132803739648000, 6631798312132723262997135360, 6457277303918704229760368640, 243980369483198608464999874560,
    6457277303918704229760368640, 74869512523814165258572922880, 243980369483198608464999874560, 6485829491449405640634531840, 6457277303918704229760368640, 6457277303918704229760368640,
    7155361336774780362707435520, 13132047828644575480148656128, 153137541976489458976486850560, 7930336995211061268425211904, 162470767384581223692837584896, 213298719181538889288678113280,
    13132045983970168109193494528, 213572179077925477608278982656, 213572179077925477608278982656, 152864082080102870656885981184, 7930336995211061268425211904, 78369796977266262177598144512,
    85504676205801864574858690560, 78369796977266262177598144512, 85504676205801864574858690560, 6501765241661371755947622400, 23747816623512842152181760000, 6501763051110513002938368000,
    8704265901225330057884467200, 8704265901225330057884467200, 39389499674306337079344234496, 522255954073519803473068032, 522255954073519803473068032, 76232276689249144626216960,
    9010165675655485232995368960, 85504676205801864574858690560, 9010171855314749925695160320, 76232276689249144626216960, 5664264625500099449098076160, 220936818016016845996252200960,
    220936736977164287180978257920, 5664291638450952387522723840, 6330666156354493551843737600, 23122874080788819990282240000, 6330664023449710029176832000, 5664264625500099449098076160,
    220936818016016845996252200960, 220936736977164287180978257920, 5664291638450952387522723840, 239196521259015729337230950400, 873669674728182982335528960000, 239196440669802557318627328000,
    13752740123936021491457458176, 13752740123936021491457458176, 6330666156354493551843737600, 23122874080788819990282240000
  ]
def negativeScales : Array ℕ := #[
    9, 9, 15, 30, 32, 29,
    35, 31, 30, 31, 32, 36,
    32, 35, 36, 30, 32, 32,
    32, 31, 32, 32, 37, 35,
    31, 37, 37, 36, 32, 31,
    32, 31, 32, 25, 32, 30,
    7, 7, 22, 4, 4, 17,
    26, 32, 28, 17, 31, 35,
    36, 28, 26, 33, 31, 31,
    35, 36, 28, 30, 37, 35,
    9, 9, 26, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    9473705749619526, 9473705749619526, 15537370089132821, 30389349443246411, 32531083185041501, 29447542523186488,
    35918365023970728, 31421458693866276, 30447542212829487, 31421458693866276, 32382984546051628, 36622679825808576,
    32382984546051628, 35918365023970728, 36622679825808576, 30389349658667427, 32382984546051628, 32382984546051628,
    32531083185041501, 31407078566364256, 32950742768078096, 32679440735749431, 37036094915763011, 35428790054327203,
    31407078363707150, 37430638478719574, 37430638478719574, 36948164223526298, 32679440735749431, 31984284434848281,
    32109989979235796, 31984284434848281, 32109989979235796, 25392890027737089, 32261781534869557, 30392889541669495,
    7813781192070436, 7813781192070436, 22991797769553624, 4754887502413606, 4754887502413606, 17978604352023330,
    26863612198235179, 32109989979235796, 28863613187713221, 17978604352023330, 31193947229388630, 35479548608376228,
    36479548079200633, 28193954109603430, 26354415879922450, 33223307387054921, 31354415393854855, 31193947229388630,
    35479548608376228, 36479548079200633, 28193954109603430, 30594111159673736, 37463002666801482, 35594110673606141,
    9473705749619526, 9473705749619526, 26354415879922450, 33223307387054921
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
noncomputable def negativeCeiling : ℝ := 1007055057 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 224581582825831717427740672, coefficient := (-224581582825831717427740672) }, { argument := 6485828522995341770883072000, coefficient := (-6485828522995341770883072000) }, { argument := 7155361336774780362707435520, coefficient := (-7155361336774780362707435520) }, { argument := 13505582511822324412994027520, coefficient := (-13505582511822324412994027520) }, { argument := 74869512523814165258572922880, coefficient := (-74869512523814165258572922880) }, { argument := 6631798312132723262997135360, coefficient := (-6631798312132723262997135360) }, { argument := 13505579606460132803739648000, coefficient := (-13505579606460132803739648000) }, { argument := 6631798312132723262997135360, coefficient := (-6631798312132723262997135360) }, { argument := 6457277303918704229760368640, coefficient := (-6457277303918704229760368640) }, { argument := 243980369483198608464999874560, coefficient := (-243980369483198608464999874560) }, { argument := 6457277303918704229760368640, coefficient := (-6457277303918704229760368640) }, { argument := 74869512523814165258572922880, coefficient := (-74869512523814165258572922880) }, { argument := 243980369483198608464999874560, coefficient := (-243980369483198608464999874560) }, { argument := 6485829491449405640634531840, coefficient := (-6485829491449405640634531840) }, { argument := 6457277303918704229760368640, coefficient := (-6457277303918704229760368640) }, { argument := 6457277303918704229760368640, coefficient := (-6457277303918704229760368640) }, { argument := 7155361336774780362707435520, coefficient := (-7155361336774780362707435520) }, { argument := 13132047828644575480148656128, coefficient := (-13132047828644575480148656128) }, { argument := 153137541976489458976486850560, coefficient := (-153137541976489458976486850560) }, { argument := 7930336995211061268425211904, coefficient := (-7930336995211061268425211904) }, { argument := 162470767384581223692837584896, coefficient := (-162470767384581223692837584896) }, { argument := 213298719181538889288678113280, coefficient := (-213298719181538889288678113280) }, { argument := 13132045983970168109193494528, coefficient := (-13132045983970168109193494528) }, { argument := 213572179077925477608278982656, coefficient := (-213572179077925477608278982656) }, { argument := 213572179077925477608278982656, coefficient := (-213572179077925477608278982656) }, { argument := 152864082080102870656885981184, coefficient := (-152864082080102870656885981184) }, { argument := 7930336995211061268425211904, coefficient := (-7930336995211061268425211904) }, { argument := 78369796977266262177598144512, coefficient := (-78369796977266262177598144512) }, { argument := 85504676205801864574858690560, coefficient := (-85504676205801864574858690560) }, { argument := 78369796977266262177598144512, coefficient := (-78369796977266262177598144512) }, { argument := 85504676205801864574858690560, coefficient := (-85504676205801864574858690560) }, { argument := 6501765241661371755947622400, coefficient := (-6501765241661371755947622400) }, { argument := 23747816623512842152181760000, coefficient := (-23747816623512842152181760000) }, { argument := 6501763051110513002938368000, coefficient := (-6501763051110513002938368000) }, { argument := 8704265901225330057884467200, coefficient := (-8704265901225330057884467200) }, { argument := 8704265901225330057884467200, coefficient := (-8704265901225330057884467200) }, { argument := 39389499674306337079344234496, coefficient := (-39389499674306337079344234496) }, { argument := 522255954073519803473068032, coefficient := (-522255954073519803473068032) }, { argument := 522255954073519803473068032, coefficient := (-522255954073519803473068032) }, { argument := 76232276689249144626216960, coefficient := (-76232276689249144626216960) }, { argument := 9010165675655485232995368960, coefficient := (-9010165675655485232995368960) }, { argument := 85504676205801864574858690560, coefficient := (-85504676205801864574858690560) }, { argument := 9010171855314749925695160320, coefficient := (-9010171855314749925695160320) }, { argument := 76232276689249144626216960, coefficient := (-76232276689249144626216960) }, { argument := 5664264625500099449098076160, coefficient := (-5664264625500099449098076160) }, { argument := 220936818016016845996252200960, coefficient := (-220936818016016845996252200960) }, { argument := 220936736977164287180978257920, coefficient := (-220936736977164287180978257920) }, { argument := 5664291638450952387522723840, coefficient := (-5664291638450952387522723840) }, { argument := 6330666156354493551843737600, coefficient := (-6330666156354493551843737600) }, { argument := 23122874080788819990282240000, coefficient := (-23122874080788819990282240000) }, { argument := 6330664023449710029176832000, coefficient := (-6330664023449710029176832000) }, { argument := 5664264625500099449098076160, coefficient := (-5664264625500099449098076160) }, { argument := 220936818016016845996252200960, coefficient := (-220936818016016845996252200960) }, { argument := 220936736977164287180978257920, coefficient := (-220936736977164287180978257920) }, { argument := 5664291638450952387522723840, coefficient := (-5664291638450952387522723840) }, { argument := 239196521259015729337230950400, coefficient := (-239196521259015729337230950400) }, { argument := 873669674728182982335528960000, coefficient := (-873669674728182982335528960000) }, { argument := 239196440669802557318627328000, coefficient := (-239196440669802557318627328000) }, { argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 6330666156354493551843737600, coefficient := (-6330666156354493551843737600) }, { argument := 23122874080788819990282240000, coefficient := (-23122874080788819990282240000) }] }

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
def constantNumerator : ℤ := (-199681123501393824133091212394496)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2745487875, 1413, 1413, 1758225495, 34290130485, 68580235815,
    219779235, 994775925, 116269993125, 31832818875, 225, 225,
    1620858675, 189446911875, 51867460125, 21807, 21807, 1395,
    1395, 172276233, 26604165, 22043451, 177203289, 148223205,
    689104707, 593652939, 593652939, 424906521, 22043451, 869374565,
    488442395, 869374565, 488442395, 2085263, 711, 711,
    91213845, 1778915535, 3557829765, 11401785, 85796525, 10027948125,
    2745487875, 27, 27, 85796525, 10027948125, 2745487875,
    1395, 1395, 27, 27, 95071825, 11112050625,
    3042297375, 711, 711, 711, 711, 2004627,
    258285, 2004627, 258285, 11889
  ]
def negativeCoefficients : Array ℕ := #[
    6330664023449710029176832000, 13665697464923768190878613504, 13665697464923768190878613504, 4054191966267036609533706240, 158135315327725245725870653440, 158135257324244348955399290880,
    4054211300760668866357493760, 73401507596650749560566579200, 268100350828605507454894080000, 73401482866484475743698944000, 8704265901225330057884467200, 8704265901225330057884467200,
    239196521259015729337230950400, 873669674728182982335528960000, 239196440669802557318627328000, 210904362786689747302540640256, 210904362786689747302540640256, 13491612146899261589720924160,
    13491612146899261589720924160, 6355871160267511777047085056, 3926081784397928586144645120, 203314949549178444639633408, 26150589769620727816563720192, 5468471056839971959272898560,
    6355869085008803484722528256, 5475481917169253974605299712, 5475481917169253974605299712, 3919070924068646570812243968, 203314949549178444639633408, 16037130104747569372505047040,
    9010171855314749925695160320, 16037130104747569372505047040, 9010171855314749925695160320, 39389504396672819948989448192, 13752740123936021491457458176, 13752740123936021491457458176,
    210324806836751452015165440, 8203799900722776611896688640, 8203796891597649588026081280, 210325809878460459972034560, 6330666156354493551843737600, 23122874080788819990282240000,
    6330664023449710029176832000, 522255954073519803473068032, 522255954073519803473068032, 6330666156354493551843737600, 23122874080788819990282240000, 6330664023449710029176832000,
    13491612146899261589720924160, 13491612146899261589720924160, 522255954073519803473068032, 522255954073519803473068032, 7015062497582006368259276800, 25622644251684908637880320000,
    7015060134092921924222976000, 13752740123936021491457458176, 13752740123936021491457458176, 13752740123936021491457458176, 13752740123936021491457458176, 591661459715970517237235712,
    76232276689249144626216960, 591661459715970517237235712, 76232276689249144626216960, 224576860459348847782526976
  ]
def negativeScales : Array ℕ := #[
    31, 10, 10, 30, 34, 35,
    27, 29, 36, 34, 7, 7,
    30, 37, 35, 14, 14, 10,
    10, 27, 24, 24, 27, 27,
    29, 29, 29, 28, 24, 29,
    28, 29, 28, 20, 9, 9,
    26, 30, 31, 23, 26, 33,
    31, 4, 4, 26, 33, 31,
    10, 10, 4, 4, 26, 33,
    31, 9, 9, 9, 9, 20,
    17, 20, 17, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31354415393854855, 10464545750334019, 10464545750334019, 30711472964184435, 34997074365672897, 35997073836497111,
    27711479844399250, 29889796355426317, 36758687859197099, 34889795869358690, 7813781192070436, 7813781192070436,
    30594111159673736, 37463002666801482, 35594110673606141, 14412503690893670, 14412503690893670, 10446049406716591,
    10446049406716591, 27360148442100367, 24665148787956650, 24393846766108081, 27400830140531081, 27143196084730115,
    29360147971045203, 29145044509122483, 29145044509122483, 28662570243852936, 24393846766108081, 29695402646952436,
    28863613187713221, 29695402646952436, 28863613187713221, 20991797942516892, 9473705749619526, 9473705749619526,
    26442749486374258, 30728350865500756, 31728350336325159, 23442756366589058, 26354415879922450, 33223307387054921,
    31354415393854855, 4754887502413606, 4754887502413606, 26354415879922450, 33223307387054921, 31354415393854855,
    10446049406716591, 10446049406716591, 4754887502413606, 4754887502413606, 26502514518911877, 33371406026044057,
    31502514032844283, 9473705749619526, 9473705749619526, 9473705749619526, 9473705749619526, 20934902397450046,
    17978604352023330, 20934902397450046, 17978604352023330, 13537339752690042
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
noncomputable def negativeCeiling : ℝ := 1093407067 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6330664023449710029176832000, coefficient := (-6330664023449710029176832000) }, { argument := 13665697464923768190878613504, coefficient := (-13665697464923768190878613504) }, { argument := 13665697464923768190878613504, coefficient := (-13665697464923768190878613504) }, { argument := 4054191966267036609533706240, coefficient := (-4054191966267036609533706240) }, { argument := 158135315327725245725870653440, coefficient := (-158135315327725245725870653440) }, { argument := 158135257324244348955399290880, coefficient := (-158135257324244348955399290880) }, { argument := 4054211300760668866357493760, coefficient := (-4054211300760668866357493760) }, { argument := 73401507596650749560566579200, coefficient := (-73401507596650749560566579200) }, { argument := 268100350828605507454894080000, coefficient := (-268100350828605507454894080000) }, { argument := 73401482866484475743698944000, coefficient := (-73401482866484475743698944000) }, { argument := 8704265901225330057884467200, coefficient := (-8704265901225330057884467200) }, { argument := 8704265901225330057884467200, coefficient := (-8704265901225330057884467200) }, { argument := 239196521259015729337230950400, coefficient := (-239196521259015729337230950400) }, { argument := 873669674728182982335528960000, coefficient := (-873669674728182982335528960000) }, { argument := 239196440669802557318627328000, coefficient := (-239196440669802557318627328000) }, { argument := 210904362786689747302540640256, coefficient := (-210904362786689747302540640256) }, { argument := 210904362786689747302540640256, coefficient := (-210904362786689747302540640256) }, { argument := 13491612146899261589720924160, coefficient := (-13491612146899261589720924160) }, { argument := 13491612146899261589720924160, coefficient := (-13491612146899261589720924160) }, { argument := 6355871160267511777047085056, coefficient := (-6355871160267511777047085056) }, { argument := 3926081784397928586144645120, coefficient := (-3926081784397928586144645120) }, { argument := 203314949549178444639633408, coefficient := (-203314949549178444639633408) }, { argument := 26150589769620727816563720192, coefficient := (-26150589769620727816563720192) }, { argument := 5468471056839971959272898560, coefficient := (-5468471056839971959272898560) }, { argument := 6355869085008803484722528256, coefficient := (-6355869085008803484722528256) }, { argument := 5475481917169253974605299712, coefficient := (-5475481917169253974605299712) }, { argument := 5475481917169253974605299712, coefficient := (-5475481917169253974605299712) }, { argument := 3919070924068646570812243968, coefficient := (-3919070924068646570812243968) }, { argument := 203314949549178444639633408, coefficient := (-203314949549178444639633408) }, { argument := 16037130104747569372505047040, coefficient := (-16037130104747569372505047040) }, { argument := 9010171855314749925695160320, coefficient := (-9010171855314749925695160320) }, { argument := 16037130104747569372505047040, coefficient := (-16037130104747569372505047040) }, { argument := 9010171855314749925695160320, coefficient := (-9010171855314749925695160320) }, { argument := 39389504396672819948989448192, coefficient := (-39389504396672819948989448192) }, { argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 210324806836751452015165440, coefficient := (-210324806836751452015165440) }, { argument := 8203799900722776611896688640, coefficient := (-8203799900722776611896688640) }, { argument := 8203796891597649588026081280, coefficient := (-8203796891597649588026081280) }, { argument := 210325809878460459972034560, coefficient := (-210325809878460459972034560) }, { argument := 6330666156354493551843737600, coefficient := (-6330666156354493551843737600) }, { argument := 23122874080788819990282240000, coefficient := (-23122874080788819990282240000) }, { argument := 6330664023449710029176832000, coefficient := (-6330664023449710029176832000) }, { argument := 522255954073519803473068032, coefficient := (-522255954073519803473068032) }, { argument := 522255954073519803473068032, coefficient := (-522255954073519803473068032) }, { argument := 6330666156354493551843737600, coefficient := (-6330666156354493551843737600) }, { argument := 23122874080788819990282240000, coefficient := (-23122874080788819990282240000) }, { argument := 6330664023449710029176832000, coefficient := (-6330664023449710029176832000) }, { argument := 13491612146899261589720924160, coefficient := (-13491612146899261589720924160) }, { argument := 13491612146899261589720924160, coefficient := (-13491612146899261589720924160) }, { argument := 522255954073519803473068032, coefficient := (-522255954073519803473068032) }, { argument := 522255954073519803473068032, coefficient := (-522255954073519803473068032) }, { argument := 7015062497582006368259276800, coefficient := (-7015062497582006368259276800) }, { argument := 25622644251684908637880320000, coefficient := (-25622644251684908637880320000) }, { argument := 7015060134092921924222976000, coefficient := (-7015060134092921924222976000) }, { argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 591661459715970517237235712, coefficient := (-591661459715970517237235712) }, { argument := 76232276689249144626216960, coefficient := (-76232276689249144626216960) }, { argument := 591661459715970517237235712, coefficient := (-591661459715970517237235712) }, { argument := 76232276689249144626216960, coefficient := (-76232276689249144626216960) }, { argument := 224576860459348847782526976, coefficient := (-224576860459348847782526976) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23
