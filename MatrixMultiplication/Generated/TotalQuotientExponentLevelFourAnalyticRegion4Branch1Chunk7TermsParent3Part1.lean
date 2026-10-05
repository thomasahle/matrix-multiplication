import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 4, branch 1,
parent chunk 7, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 162429513014820599870715255062528
def positiveArguments : Array ℕ := #[
    5, 9, 67, 17, 5, 15,
    5, 133, 17, 15, 2423, 15,
    133, 133, 5, 15
  ]
def positiveCoefficients : Array ℕ := #[
    1584563250285286751870879006720, 696341272098026404630757376, 5183873914507529901140082688, 5261245166962866168321277952, 773712524553362671811952640, 4642275147320176030871715840,
    773712524553362671811952640, 5145188288279861767549485056, 5261245166962866168321277952, 4642275147320176030871715840, 93735272349639887690018062336, 4642275147320176030871715840,
    5145188288279861767549485056, 5145188288279861767549485056, 773712524553362671811952640, 4642275147320176030871715840
  ]
def positiveScales : Array ℕ := #[
    2, 3, 6, 4, 2, 3,
    2, 7, 4, 3, 11, 3,
    7, 7, 2, 3
  ]
def negativeArguments : Array ℕ := #[
    33614279, 208095, 2463532226301, 1845109, 69365, 208095,
    69365, 235841, 235841, 78294255883, 2469562433129, 2747637117879,
    43965229259229, 2463532226301, 12631060056095, 43776611823731, 6316988867511, 29522941,
    1086161923, 67885195, 1845109, 1109885, 40833155, 2552075,
    69365, 3329655, 122499465, 7656225, 208095, 1109885,
    40833155, 2552075, 69365, 3773609, 138832727, 8677055,
    235841, 3773609, 138832727, 8677055, 235841, 39208836931,
    693750134347, 2775124664131, 78294255883, 485699386965, 1683332470257, 242905789917
  ]
def negativeCoefficients : Array ℕ := #[
    620074001935269432985124864, 30709401664148713148252160, 693422676024024501590163456, 34036253511098157072646144, 5118233610691452191375360, 30709401664148713148252160,
    5118233610691452191375360, 34803988552701874901352448, 34803988552701874901352448, 22037873851245566516789248, 695120028350496240381722624, 24748515000458415985517395968,
    24750223763640269035901288448, 693422676024024501590163456, 7110654670240474787888496640, 24644041587112222615322755072, 7112297177456527781463588864, 34037633558139171468476416,
    1252259438511826270418894848, 1252260818558867284814725120, 34036253511098157072646144, 5118441136562281423831040, 188309690001778386529157120, 188309897527649215761612800,
    5118233610691452191375360, 30710646819373688542986240, 1129858140010670319174942720, 1129859385165895294569676800, 30709401664148713148252160, 5118441136562281423831040,
    188309690001778386529157120, 188309897527649215761612800, 5118233610691452191375360, 34805399728623513682051072, 1280505892012093028398268416, 1280507303188014667178967040,
    34803988552701874901352448, 34805399728623513682051072, 1280505892012093028398268416, 1280507303188014667178967040, 34803988552701874901352448, 22072612924010267748073472,
    781093211633345184586006528, 781128150205440279168679936, 22037873851245566516789248, 136712223634353271382999040, 473815967861880108814958592, 136743803119542148062511104
  ]
def negativeScales : Array ℕ := #[
    25, 17, 41, 20, 16, 17,
    16, 17, 17, 36, 41, 41,
    45, 41, 43, 45, 42, 24,
    30, 26, 20, 20, 25, 21,
    16, 21, 26, 22, 17, 20,
    25, 21, 16, 21, 27, 23,
    17, 21, 27, 23, 17, 35,
    39, 41, 36, 38, 40, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 3169925001442312, 6066089190457772, 4087462841250339, 2321928094887362, 3906890595303263,
    2321928094887362, 7055282435501189, 4087462841250339, 3906890595303263, 11242578689451346, 3906890595303263,
    7055282435501189, 7055282435501189, 2321928094887362, 3906890595303263
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    25002570869432347, 17666882775622068, 41163865482805263, 20815274616361455, 16081920274868363, 17666882775622068,
    16081920274868363, 17847455022881199, 17847455022881199, 36188187415865111, 41167392580669840, 41321328617765709,
    45321428225320610, 41163865482805263, 43522040955282084, 45315225532178410, 42522374168394408, 24815333111245271,
    30016592047455887, 26016593637370775, 20815274616361455, 20081978769751151, 25283237706842060, 21283239296756948,
    16081920274868363, 21666941270504904, 26868200210005047, 22868201799920008, 17666882775622068, 20081978769751151,
    25283237706842060, 21283239296756948, 16081920274868363, 21847513517765837, 27048772453205037, 23048774043119925,
    17847455022881199, 21847513517765837, 27048772453205037, 23048774043119925, 17847455022881199, 35190459796064387,
    39335625189493769, 41335689720303470, 36188187415865111, 38821272710188656, 40614457286103228, 37821605923307536
  ]

abbrev PositiveTerm := Fin 16
abbrev NegativeTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 60144033 / 1000000000000
noncomputable def negativeCeiling : ℝ := 52368701 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 620074001935269432985124864, coefficient := (-620074001935269432985124864) }, { argument := 30709401664148713148252160, coefficient := (-30709401664148713148252160) }, { argument := 693422676024024501590163456, coefficient := (-693422676024024501590163456) }, { argument := 34036253511098157072646144, coefficient := (-34036253511098157072646144) }, { argument := 5118233610691452191375360, coefficient := (-5118233610691452191375360) }, { argument := 30709401664148713148252160, coefficient := (-30709401664148713148252160) }, { argument := 5118233610691452191375360, coefficient := (-5118233610691452191375360) }, { argument := 34803988552701874901352448, coefficient := (-34803988552701874901352448) }, { argument := 34803988552701874901352448, coefficient := (-34803988552701874901352448) }, { argument := 22037873851245566516789248, coefficient := (-22037873851245566516789248) }, { argument := 695120028350496240381722624, coefficient := (-695120028350496240381722624) }, { argument := 24748515000458415985517395968, coefficient := (-24748515000458415985517395968) }, { argument := 24750223763640269035901288448, coefficient := (-24750223763640269035901288448) }, { argument := 693422676024024501590163456, coefficient := (-693422676024024501590163456) }, { argument := 7110654670240474787888496640, coefficient := (-7110654670240474787888496640) }, { argument := 24644041587112222615322755072, coefficient := (-24644041587112222615322755072) }, { argument := 7112297177456527781463588864, coefficient := (-7112297177456527781463588864) }, { argument := 34037633558139171468476416, coefficient := (-34037633558139171468476416) }, { argument := 1252259438511826270418894848, coefficient := (-1252259438511826270418894848) }, { argument := 1252260818558867284814725120, coefficient := (-1252260818558867284814725120) }, { argument := 34036253511098157072646144, coefficient := (-34036253511098157072646144) }, { argument := 5118441136562281423831040, coefficient := (-5118441136562281423831040) }, { argument := 188309690001778386529157120, coefficient := (-188309690001778386529157120) }, { argument := 188309897527649215761612800, coefficient := (-188309897527649215761612800) }, { argument := 5118233610691452191375360, coefficient := (-5118233610691452191375360) }, { argument := 30710646819373688542986240, coefficient := (-30710646819373688542986240) }, { argument := 1129858140010670319174942720, coefficient := (-1129858140010670319174942720) }, { argument := 1129859385165895294569676800, coefficient := (-1129859385165895294569676800) }, { argument := 30709401664148713148252160, coefficient := (-30709401664148713148252160) }, { argument := 5118441136562281423831040, coefficient := (-5118441136562281423831040) }, { argument := 188309690001778386529157120, coefficient := (-188309690001778386529157120) }, { argument := 188309897527649215761612800, coefficient := (-188309897527649215761612800) }, { argument := 5118233610691452191375360, coefficient := (-5118233610691452191375360) }, { argument := 34805399728623513682051072, coefficient := (-34805399728623513682051072) }, { argument := 1280505892012093028398268416, coefficient := (-1280505892012093028398268416) }, { argument := 1280507303188014667178967040, coefficient := (-1280507303188014667178967040) }, { argument := 34803988552701874901352448, coefficient := (-34803988552701874901352448) }, { argument := 34805399728623513682051072, coefficient := (-34805399728623513682051072) }, { argument := 1280505892012093028398268416, coefficient := (-1280505892012093028398268416) }, { argument := 1280507303188014667178967040, coefficient := (-1280507303188014667178967040) }, { argument := 34803988552701874901352448, coefficient := (-34803988552701874901352448) }, { argument := 22072612924010267748073472, coefficient := (-22072612924010267748073472) }, { argument := 781093211633345184586006528, coefficient := (-781093211633345184586006528) }, { argument := 781128150205440279168679936, coefficient := (-781128150205440279168679936) }, { argument := 22037873851245566516789248, coefficient := (-22037873851245566516789248) }, { argument := 136712223634353271382999040, coefficient := (-136712223634353271382999040) }, { argument := 473815967861880108814958592, coefficient := (-473815967861880108814958592) }, { argument := 136743803119542148062511104, coefficient := (-136743803119542148062511104) }, { argument := 1584563250285286751870879006720, coefficient := 1584563250285286751870879006720 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 5183873914507529901140082688, coefficient := 5183873914507529901140082688 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 773712524553362671811952640, coefficient := 773712524553362671811952640 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 773712524553362671811952640, coefficient := 773712524553362671811952640 }, { argument := 5145188288279861767549485056, coefficient := 5145188288279861767549485056 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 93735272349639887690018062336, coefficient := 93735272349639887690018062336 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 5145188288279861767549485056, coefficient := 5145188288279861767549485056 }, { argument := 5145188288279861767549485056, coefficient := 5145188288279861767549485056 }, { argument := 773712524553362671811952640, coefficient := 773712524553362671811952640 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }] }

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


end Parent3

namespace Parent3

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-90263851964480753355890035261440)
def positiveArguments : Array ℕ := #[
    5, 17, 17, 9, 3069365, 10637777,
    1535037, 2057685, 73439771, 73444553, 2052935, 266463,
    10230927, 113222879, 10231033, 133213, 40019, 8228493,
    4115203, 158241
  ]
def positiveCoefficients : Array ℕ := #[
    773712524553362671811952640, 5261245166962866168321277952, 5261245166962866168321277952, 696341272098026404630757376, 28989332799386377162672046080, 100470963114083211704830787584,
    28996029115059086319585067008, 19434285352607251823088107520, 693619026160044334690160607232, 693664190873086499976984395776, 19389422871019990193557995520, 2516671880249788545154154496,
    96628373506972181394446352384, 1069359857767210825606462701568, 96629374648666549759231655936, 2516322425130056191408340992, 1511875074223682654455201792, 77715919095454991106762080256,
    77733986869618450369349681152, 1494543989231551056520937472
  ]
def positiveScales : Array ℕ := #[
    2, 4, 4, 3, 21, 23,
    20, 20, 26, 26, 20, 18,
    23, 26, 23, 17, 15, 22,
    21, 17
  ]
def negativeArguments : Array ℕ := #[
    1, 1, 9, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 158456325028528675187087900672, 1426106925256758076683791106048, 1267650600228229401496703205376, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 0, 3, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 4087462841250339, 4087462841250339, 3169925001442312, 21549508786447740, 23342693363344704,
    20549841999560057, 20972590713048163, 26130058224356510, 26130152161782916, 20969256518016003, 18023575694391658,
    23286433534388887, 26754590272771862, 23286448481703253, 17023375353545445, 15288397496991357, 22972196802137821,
    21972532167897502, 17271763922750127
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0, 3169925001442313, 0, 0
  ]

abbrev PositiveTerm := Fin 20
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
noncomputable def positiveFloor : ℝ := 465941937 / 500000000000
noncomputable def negativeCeiling : ℝ := 5441537 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 773712524553362671811952640, coefficient := 773712524553362671811952640 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 28989332799386377162672046080, coefficient := 28989332799386377162672046080 }, { argument := 100470963114083211704830787584, coefficient := 100470963114083211704830787584 }, { argument := 28996029115059086319585067008, coefficient := 28996029115059086319585067008 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 19434285352607251823088107520, coefficient := 19434285352607251823088107520 }, { argument := 693619026160044334690160607232, coefficient := 693619026160044334690160607232 }, { argument := 693664190873086499976984395776, coefficient := 693664190873086499976984395776 }, { argument := 19389422871019990193557995520, coefficient := 19389422871019990193557995520 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 2516671880249788545154154496, coefficient := 2516671880249788545154154496 }, { argument := 96628373506972181394446352384, coefficient := 96628373506972181394446352384 }, { argument := 1069359857767210825606462701568, coefficient := 1069359857767210825606462701568 }, { argument := 96629374648666549759231655936, coefficient := 96629374648666549759231655936 }, { argument := 2516322425130056191408340992, coefficient := 2516322425130056191408340992 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 1511875074223682654455201792, coefficient := 1511875074223682654455201792 }, { argument := 77715919095454991106762080256, coefficient := 77715919095454991106762080256 }, { argument := 77733986869618450369349681152, coefficient := 77733986869618450369349681152 }, { argument := 1494543989231551056520937472, coefficient := 1494543989231551056520937472 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7
