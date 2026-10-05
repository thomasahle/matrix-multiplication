import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
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

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-25294640523732686446181893537792)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    122832917935, 25256248416945, 12631060056095, 485699386965, 78426241059, 2470445940935,
    3773609, 25994894686759, 3329655, 1109885, 29522941, 3773609,
    3329655, 537850271, 3329655, 2469562433129, 29522941, 1109885,
    3329655, 1109885, 3773609, 3773609, 39208836931, 78426241059,
    693825587157, 2775426494463, 39151402053, 425713197763, 87532873580061, 43776611823731,
    1683332470257, 693825587157, 10994621851273, 138832727, 115559302681995, 122499465,
    40833155, 1086161923, 138832727, 122499465, 19787746913, 122499465,
    2747637117879, 1086161923, 40833155, 122499465, 40833155, 138832727,
    138832727, 693750134347, 2470445940935, 10994621851273, 10995380697979, 2464415706905,
    3773609, 138832727, 8677055, 235841, 122832917935, 425713197763,
    61430645703, 61430645703, 12631041209241, 6316988867511
  ]
def negativeCoefficients : Array ℕ := #[
    138297570860224178752061440, 7109001934958136343312465920, 7110654670240474787888496640, 136712223634353271382999040, 22075024375586318350024704, 695368713689613773161103360,
    34805399728623513682051072, 7316912376551444921297403904, 30710646819373688542986240, 5118441136562281423831040, 34037633558139171468476416, 34805399728623513682051072,
    30710646819373688542986240, 620099143694520394497130496, 30710646819373688542986240, 695120028350496240381722624, 34037633558139171468476416, 5118441136562281423831040,
    30710646819373688542986240, 5118441136562281423831040, 34805399728623513682051072, 34805399728623513682051072, 22072612924010267748073472, 22075024375586318350024704,
    781178163945095198794579968, 781213107891110548737097728, 22040279962115409010753536, 479310449703037267829850112, 24638313552364465860447830016, 24644041587112222615322755072,
    473815967861880108814958592, 781178163945095198794579968, 24757687436236297846290120704, 1280505892012093028398268416, 260216416248913520511166709760, 1129858140010670319174942720,
    188309690001778386529157120, 1252259438511826270418894848, 1280505892012093028398268416, 1129858140010670319174942720, 22813718943715451528007385088, 1129858140010670319174942720,
    24748515000458415985517395968, 1252259438511826270418894848, 188309690001778386529157120, 1129858140010670319174942720, 188309690001778386529157120, 1280505892012093028398268416,
    1280505892012093028398268416, 781093211633345184586006528, 695368713689613773161103360, 24757687436236297846290120704, 24759396207107484310455713792, 693671353706459717886279680,
    34805399728623513682051072, 1280505892012093028398268416, 1280507303188014667178967040, 34803988552701874901352448, 138297570860224178752061440, 479310449703037267829850112,
    138329516548579880645689344, 138329516548579880645689344, 7110644060404893349620744192, 7112297177456527781463588864
  ]
def negativeScales : Array ℕ := #[
    36, 44, 43, 38, 36, 41,
    21, 44, 21, 20, 24, 21,
    21, 29, 21, 41, 24, 20,
    21, 20, 21, 21, 35, 36,
    39, 41, 35, 38, 46, 45,
    40, 39, 43, 27, 46, 26,
    25, 30, 27, 26, 34, 26,
    41, 30, 25, 26, 25, 27,
    27, 39, 41, 43, 43, 41,
    21, 27, 23, 17, 36, 38,
    35, 35, 43, 42
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36837906284811764, 44521705589517254, 43522040955282084, 38821272710188656, 36190617403105052, 41167908625278422,
    21847513517765837, 44563293543971459, 21666941270504904, 20081978769751151, 24815333111245271, 21847513517765837,
    21666941270504904, 29002629364315135, 21666941270504904, 41167392580669840, 24815333111245271, 20081978769751151,
    21666941270504904, 20081978769751151, 21847513517765837, 21847513517765837, 35190459796064387, 36190617403105052,
    39335782089608449, 41335846623324865, 35188344921746047, 38631090860349134, 46314890166413586, 45315225532178410,
    40614457286103228, 39335782089608449, 43321863218567617, 27048772453205037, 46715626731932586, 26868200210005047,
    25283237706842060, 30016592047455887, 27048772453205037, 26868200210005047, 34203888301406044, 26868200210005047,
    41321328617765709, 30016592047455887, 25283237706842060, 26868200210005047, 25283237706842060, 27048772453205037,
    27048772453205037, 39335625189493769, 41167908625278422, 43321863218567617, 43321962789668395, 41164382774431329,
    21847513517765837, 27048772453205037, 23048774043119925, 17847455022881199, 36837906284811764, 38631090860349134,
    35838239497932976, 35838239497932976, 43522038802629578, 42522374168394408
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
noncomputable def negativeCeiling : ℝ := 261963267 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 138297570860224178752061440, coefficient := (-138297570860224178752061440) }, { argument := 7109001934958136343312465920, coefficient := (-7109001934958136343312465920) }, { argument := 7110654670240474787888496640, coefficient := (-7110654670240474787888496640) }, { argument := 136712223634353271382999040, coefficient := (-136712223634353271382999040) }, { argument := 22075024375586318350024704, coefficient := (-22075024375586318350024704) }, { argument := 695368713689613773161103360, coefficient := (-695368713689613773161103360) }, { argument := 34805399728623513682051072, coefficient := (-34805399728623513682051072) }, { argument := 7316912376551444921297403904, coefficient := (-7316912376551444921297403904) }, { argument := 30710646819373688542986240, coefficient := (-30710646819373688542986240) }, { argument := 5118441136562281423831040, coefficient := (-5118441136562281423831040) }, { argument := 34037633558139171468476416, coefficient := (-34037633558139171468476416) }, { argument := 34805399728623513682051072, coefficient := (-34805399728623513682051072) }, { argument := 30710646819373688542986240, coefficient := (-30710646819373688542986240) }, { argument := 620099143694520394497130496, coefficient := (-620099143694520394497130496) }, { argument := 30710646819373688542986240, coefficient := (-30710646819373688542986240) }, { argument := 695120028350496240381722624, coefficient := (-695120028350496240381722624) }, { argument := 34037633558139171468476416, coefficient := (-34037633558139171468476416) }, { argument := 5118441136562281423831040, coefficient := (-5118441136562281423831040) }, { argument := 30710646819373688542986240, coefficient := (-30710646819373688542986240) }, { argument := 5118441136562281423831040, coefficient := (-5118441136562281423831040) }, { argument := 34805399728623513682051072, coefficient := (-34805399728623513682051072) }, { argument := 34805399728623513682051072, coefficient := (-34805399728623513682051072) }, { argument := 22072612924010267748073472, coefficient := (-22072612924010267748073472) }, { argument := 22075024375586318350024704, coefficient := (-22075024375586318350024704) }, { argument := 781178163945095198794579968, coefficient := (-781178163945095198794579968) }, { argument := 781213107891110548737097728, coefficient := (-781213107891110548737097728) }, { argument := 22040279962115409010753536, coefficient := (-22040279962115409010753536) }, { argument := 479310449703037267829850112, coefficient := (-479310449703037267829850112) }, { argument := 24638313552364465860447830016, coefficient := (-24638313552364465860447830016) }, { argument := 24644041587112222615322755072, coefficient := (-24644041587112222615322755072) }, { argument := 473815967861880108814958592, coefficient := (-473815967861880108814958592) }, { argument := 781178163945095198794579968, coefficient := (-781178163945095198794579968) }, { argument := 24757687436236297846290120704, coefficient := (-24757687436236297846290120704) }, { argument := 1280505892012093028398268416, coefficient := (-1280505892012093028398268416) }, { argument := 260216416248913520511166709760, coefficient := (-260216416248913520511166709760) }, { argument := 1129858140010670319174942720, coefficient := (-1129858140010670319174942720) }, { argument := 188309690001778386529157120, coefficient := (-188309690001778386529157120) }, { argument := 1252259438511826270418894848, coefficient := (-1252259438511826270418894848) }, { argument := 1280505892012093028398268416, coefficient := (-1280505892012093028398268416) }, { argument := 1129858140010670319174942720, coefficient := (-1129858140010670319174942720) }, { argument := 22813718943715451528007385088, coefficient := (-22813718943715451528007385088) }, { argument := 1129858140010670319174942720, coefficient := (-1129858140010670319174942720) }, { argument := 24748515000458415985517395968, coefficient := (-24748515000458415985517395968) }, { argument := 1252259438511826270418894848, coefficient := (-1252259438511826270418894848) }, { argument := 188309690001778386529157120, coefficient := (-188309690001778386529157120) }, { argument := 1129858140010670319174942720, coefficient := (-1129858140010670319174942720) }, { argument := 188309690001778386529157120, coefficient := (-188309690001778386529157120) }, { argument := 1280505892012093028398268416, coefficient := (-1280505892012093028398268416) }, { argument := 1280505892012093028398268416, coefficient := (-1280505892012093028398268416) }, { argument := 781093211633345184586006528, coefficient := (-781093211633345184586006528) }, { argument := 695368713689613773161103360, coefficient := (-695368713689613773161103360) }, { argument := 24757687436236297846290120704, coefficient := (-24757687436236297846290120704) }, { argument := 24759396207107484310455713792, coefficient := (-24759396207107484310455713792) }, { argument := 693671353706459717886279680, coefficient := (-693671353706459717886279680) }, { argument := 34805399728623513682051072, coefficient := (-34805399728623513682051072) }, { argument := 1280505892012093028398268416, coefficient := (-1280505892012093028398268416) }, { argument := 1280507303188014667178967040, coefficient := (-1280507303188014667178967040) }, { argument := 34803988552701874901352448, coefficient := (-34803988552701874901352448) }, { argument := 138297570860224178752061440, coefficient := (-138297570860224178752061440) }, { argument := 479310449703037267829850112, coefficient := (-479310449703037267829850112) }, { argument := 138329516548579880645689344, coefficient := (-138329516548579880645689344) }, { argument := 138329516548579880645689344, coefficient := (-138329516548579880645689344) }, { argument := 7110644060404893349620744192, coefficient := (-7110644060404893349620744192) }, { argument := 7112297177456527781463588864, coefficient := (-7112297177456527781463588864) }] }

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
def constantNumerator : ℤ := (-50838847567373802667288433786880)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    242905789917, 2775426494463, 10995380697979, 8677055, 231135530305611, 7656225,
    2552075, 67885195, 8677055, 7656225, 1236735545, 7656225,
    43965229259229, 67885195, 2552075, 7656225, 2552075, 8677055,
    8677055, 2775124664131, 25994894686759, 115559302681995, 231135530305611, 25927649294421,
    3329655, 122499465, 7656225, 208095, 25256248416945, 87532873580061,
    12631041209241, 1109885, 40833155, 2552075, 69365, 29522941,
    1086161923, 67885195, 1845109, 3773609, 138832727, 8677055,
    235841, 3329655, 122499465, 7656225, 208095, 537850271,
    19787746913, 1236735545, 33614279, 3329655, 122499465, 7656225,
    208095, 39151402053, 2464415706905, 235841, 25927649294421, 208095,
    69365, 1845109, 235841, 208095
  ]
def negativeCoefficients : Array ℕ := #[
    136743803119542148062511104, 781213107891110548737097728, 24759396207107484310455713792, 1280507303188014667178967040, 260235472039107921260801163264, 1129859385165895294569676800,
    188309897527649215761612800, 1252260818558867284814725120, 1280507303188014667178967040, 1129859385165895294569676800, 22813744085474702489519390720, 1129859385165895294569676800,
    24750223763640269035901288448, 1252260818558867284814725120, 188309897527649215761612800, 1129859385165895294569676800, 188309897527649215761612800, 1280507303188014667178967040,
    1280507303188014667178967040, 781128150205440279168679936, 7316912376551444921297403904, 260216416248913520511166709760, 260235472039107921260801163264, 7297984481309207445872050176,
    30710646819373688542986240, 1129858140010670319174942720, 1129859385165895294569676800, 30709401664148713148252160, 7109001934958136343312465920, 24638313552364465860447830016,
    7110644060404893349620744192, 5118441136562281423831040, 188309690001778386529157120, 188309897527649215761612800, 5118233610691452191375360, 34037633558139171468476416,
    1252259438511826270418894848, 1252260818558867284814725120, 34036253511098157072646144, 34805399728623513682051072, 1280505892012093028398268416, 1280507303188014667178967040,
    34803988552701874901352448, 30710646819373688542986240, 1129858140010670319174942720, 1129859385165895294569676800, 30709401664148713148252160, 620099143694520394497130496,
    22813718943715451528007385088, 22813744085474702489519390720, 620074001935269432985124864, 30710646819373688542986240, 1129858140010670319174942720, 1129859385165895294569676800,
    30709401664148713148252160, 22040279962115409010753536, 693671353706459717886279680, 34803988552701874901352448, 7297984481309207445872050176, 30709401664148713148252160,
    5118233610691452191375360, 34036253511098157072646144, 34803988552701874901352448, 30709401664148713148252160
  ]
def negativeScales : Array ℕ := #[
    37, 41, 43, 23, 47, 22,
    21, 26, 23, 22, 30, 22,
    45, 26, 21, 22, 21, 23,
    23, 41, 44, 46, 47, 44,
    21, 26, 22, 17, 44, 46,
    43, 20, 25, 21, 16, 24,
    30, 26, 20, 21, 27, 23,
    17, 21, 26, 22, 17, 29,
    34, 30, 25, 21, 26, 22,
    17, 35, 41, 17, 44, 17,
    16, 20, 17, 17
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    37821605923307536, 41335846623324865, 43321962789668395, 23048774043119925, 47715732377409951, 22868201799920008,
    21283239296756948, 26016593637370775, 23048774043119925, 22868201799920008, 30203889891320932, 22868201799920008,
    45321428225320610, 26016593637370775, 21283239296756948, 22868201799920008, 21283239296756948, 23048774043119925,
    23048774043119925, 41335689720303470, 44563293543971459, 46715626731932586, 47715732377409951, 44559556645088753,
    21666941270504904, 26868200210005047, 22868201799920008, 17666882775622068, 44521705589517254, 46314890166413586,
    43522038802629578, 20081978769751151, 25283237706842060, 21283239296756948, 16081920274868363, 24815333111245271,
    30016592047455887, 26016593637370775, 20815274616361455, 21847513517765837, 27048772453205037, 23048774043119925,
    17847455022881199, 21666941270504904, 26868200210005047, 22868201799920008, 17666882775622068, 29002629364315135,
    34203888301406044, 30203889891320932, 25002570869432347, 21666941270504904, 26868200210005047, 22868201799920008,
    17666882775622068, 35188344921746047, 41164382774431329, 17847455022881199, 44559556645088753, 17666882775622068,
    16081920274868363, 20815274616361455, 17847455022881199, 17666882775622068
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
noncomputable def negativeCeiling : ℝ := 539740163 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 136743803119542148062511104, coefficient := (-136743803119542148062511104) }, { argument := 781213107891110548737097728, coefficient := (-781213107891110548737097728) }, { argument := 24759396207107484310455713792, coefficient := (-24759396207107484310455713792) }, { argument := 1280507303188014667178967040, coefficient := (-1280507303188014667178967040) }, { argument := 260235472039107921260801163264, coefficient := (-260235472039107921260801163264) }, { argument := 1129859385165895294569676800, coefficient := (-1129859385165895294569676800) }, { argument := 188309897527649215761612800, coefficient := (-188309897527649215761612800) }, { argument := 1252260818558867284814725120, coefficient := (-1252260818558867284814725120) }, { argument := 1280507303188014667178967040, coefficient := (-1280507303188014667178967040) }, { argument := 1129859385165895294569676800, coefficient := (-1129859385165895294569676800) }, { argument := 22813744085474702489519390720, coefficient := (-22813744085474702489519390720) }, { argument := 1129859385165895294569676800, coefficient := (-1129859385165895294569676800) }, { argument := 24750223763640269035901288448, coefficient := (-24750223763640269035901288448) }, { argument := 1252260818558867284814725120, coefficient := (-1252260818558867284814725120) }, { argument := 188309897527649215761612800, coefficient := (-188309897527649215761612800) }, { argument := 1129859385165895294569676800, coefficient := (-1129859385165895294569676800) }, { argument := 188309897527649215761612800, coefficient := (-188309897527649215761612800) }, { argument := 1280507303188014667178967040, coefficient := (-1280507303188014667178967040) }, { argument := 1280507303188014667178967040, coefficient := (-1280507303188014667178967040) }, { argument := 781128150205440279168679936, coefficient := (-781128150205440279168679936) }, { argument := 7316912376551444921297403904, coefficient := (-7316912376551444921297403904) }, { argument := 260216416248913520511166709760, coefficient := (-260216416248913520511166709760) }, { argument := 260235472039107921260801163264, coefficient := (-260235472039107921260801163264) }, { argument := 7297984481309207445872050176, coefficient := (-7297984481309207445872050176) }, { argument := 30710646819373688542986240, coefficient := (-30710646819373688542986240) }, { argument := 1129858140010670319174942720, coefficient := (-1129858140010670319174942720) }, { argument := 1129859385165895294569676800, coefficient := (-1129859385165895294569676800) }, { argument := 30709401664148713148252160, coefficient := (-30709401664148713148252160) }, { argument := 7109001934958136343312465920, coefficient := (-7109001934958136343312465920) }, { argument := 24638313552364465860447830016, coefficient := (-24638313552364465860447830016) }, { argument := 7110644060404893349620744192, coefficient := (-7110644060404893349620744192) }, { argument := 5118441136562281423831040, coefficient := (-5118441136562281423831040) }, { argument := 188309690001778386529157120, coefficient := (-188309690001778386529157120) }, { argument := 188309897527649215761612800, coefficient := (-188309897527649215761612800) }, { argument := 5118233610691452191375360, coefficient := (-5118233610691452191375360) }, { argument := 34037633558139171468476416, coefficient := (-34037633558139171468476416) }, { argument := 1252259438511826270418894848, coefficient := (-1252259438511826270418894848) }, { argument := 1252260818558867284814725120, coefficient := (-1252260818558867284814725120) }, { argument := 34036253511098157072646144, coefficient := (-34036253511098157072646144) }, { argument := 34805399728623513682051072, coefficient := (-34805399728623513682051072) }, { argument := 1280505892012093028398268416, coefficient := (-1280505892012093028398268416) }, { argument := 1280507303188014667178967040, coefficient := (-1280507303188014667178967040) }, { argument := 34803988552701874901352448, coefficient := (-34803988552701874901352448) }, { argument := 30710646819373688542986240, coefficient := (-30710646819373688542986240) }, { argument := 1129858140010670319174942720, coefficient := (-1129858140010670319174942720) }, { argument := 1129859385165895294569676800, coefficient := (-1129859385165895294569676800) }, { argument := 30709401664148713148252160, coefficient := (-30709401664148713148252160) }, { argument := 620099143694520394497130496, coefficient := (-620099143694520394497130496) }, { argument := 22813718943715451528007385088, coefficient := (-22813718943715451528007385088) }, { argument := 22813744085474702489519390720, coefficient := (-22813744085474702489519390720) }, { argument := 620074001935269432985124864, coefficient := (-620074001935269432985124864) }, { argument := 30710646819373688542986240, coefficient := (-30710646819373688542986240) }, { argument := 1129858140010670319174942720, coefficient := (-1129858140010670319174942720) }, { argument := 1129859385165895294569676800, coefficient := (-1129859385165895294569676800) }, { argument := 30709401664148713148252160, coefficient := (-30709401664148713148252160) }, { argument := 22040279962115409010753536, coefficient := (-22040279962115409010753536) }, { argument := 693671353706459717886279680, coefficient := (-693671353706459717886279680) }, { argument := 34803988552701874901352448, coefficient := (-34803988552701874901352448) }, { argument := 7297984481309207445872050176, coefficient := (-7297984481309207445872050176) }, { argument := 30709401664148713148252160, coefficient := (-30709401664148713148252160) }, { argument := 5118233610691452191375360, coefficient := (-5118233610691452191375360) }, { argument := 34036253511098157072646144, coefficient := (-34036253511098157072646144) }, { argument := 34803988552701874901352448, coefficient := (-34803988552701874901352448) }, { argument := 30709401664148713148252160, coefficient := (-30709401664148713148252160) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7
