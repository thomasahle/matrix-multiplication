import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 9, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-48393445482319848775801731284992)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    15435, 6615, 15435, 174195, 6615, 15435,
    13671, 161459901, 13574777079, 42315, 139470121485, 1395,
    3255, 42315, 42315, 1395, 522195, 20925,
    6787393473, 42315, 3255, 20925, 3255, 42315,
    42315, 169078461, 80271173, 2922850491, 23382808895, 642164417,
    200655, 51597, 200655, 177723, 8318583, 2264535,
    51597, 8318583, 200655, 200655, 85995, 200655,
    2264535, 85995, 200655, 177723, 167808701, 13681436919,
    98735, 139477740045, 3255, 7595, 98735, 98735,
    3255, 1218455, 48825, 6840723393, 98735, 7595,
    48825, 7595, 98735, 98735
  ]
def negativeCoefficients : Array ℕ := #[
    72889726663092973873397760, 62476908568365406177198080, 72889726663092973873397760, 822612629483477847999774720, 62476908568365406177198080, 72889726663092973873397760,
    64559472187310919716438016, 186150591994592556667109376, 15650652414623219236265263104, 1598615501781032297740369920, 160798102310185934905524879360, 843225759181203849357557760,
    61485211606962780682321920, 1598615501781032297740369920, 1598615501781032297740369920, 843225759181203849357557760, 19727969324176915058927861760, 1581048298464757217545420800,
    15650663790499705192024375296, 1598615501781032297740369920, 61485211606962780682321920, 1581048298464757217545420800, 61485211606962780682321920, 1598615501781032297740369920,
    1598615501781032297740369920, 194934193652730096764583936, 740370892413732084760182784, 26958537486596651566107721728, 26958543213157764948316651520, 740365165852618702551252992,
    1895132893240417320708341760, 1949279547333000672728580096, 1895132893240417320708341760, 1678546276870083912627388416, 78566795088338443781365825536, 21387928366570424047994142720,
    1949279547333000672728580096, 78566795088338443781365825536, 1895132893240417320708341760, 1895132893240417320708341760, 1624399622777500560607150080, 1895132893240417320708341760,
    21387928366570424047994142720, 1624399622777500560607150080, 1895132893240417320708341760, 1678546276870083912627388416, 193470260043040506748338176, 15773622837837144797629906944,
    1865051418744537680697098240, 160806885911844072445622353920, 983763385711404490917150720, 71732746874789910796042240, 1865051418744537680697098240, 1865051418744537680697098240,
    983763385711404490917150720, 23015964211539734235415838720, 1844556348208883420469657600, 15773634213713630753389019136, 1865051418744537680697098240, 71732746874789910796042240,
    1844556348208883420469657600, 71732746874789910796042240, 1865051418744537680697098240, 1865051418744537680697098240
  ]
def negativeScales : Array ℕ := #[
    13, 12, 13, 17, 12, 13,
    13, 27, 33, 15, 37, 10,
    11, 15, 15, 10, 18, 14,
    32, 15, 11, 14, 11, 15,
    15, 27, 26, 31, 34, 29,
    17, 15, 17, 17, 22, 21,
    15, 22, 17, 17, 16, 17,
    21, 16, 17, 17, 27, 33,
    16, 37, 11, 12, 16, 16,
    11, 20, 15, 32, 16, 12,
    15, 12, 16, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13913917868096136, 12691525441225267, 13913917868096136, 17410343688621996, 12691525441225267, 13913917868096136,
    13738831156120225, 27266600671315131, 33660209455611354, 15368881546194092, 37021165132107072, 10446049406716591,
    11668441828086828, 15368881546194092, 15368881546194092, 10446049406716591, 18994229139984646, 14352940002325070,
    32660210504252280, 15368881546194092, 11668441828086828, 14352940002325070, 11668441828086828, 15368881546194092,
    15368881546194092, 27333117644821473, 26258378644025138, 31444728888600882, 34444729195059659, 29258367485140645,
    17614357580651952, 15654999565165109, 17614357580651952, 17439270874085520, 22987906387263822, 21110783406763079,
    15654999565165109, 22987906387263822, 17614357580651952, 17614357580651952, 16391965159307136, 17614357580651952,
    21110783406763079, 16391965159307136, 17614357580651952, 17439270874085520, 27322242281575724, 33671500708888984,
    16591273967534972, 37021243937219061, 11668441828086828, 12890834253091783, 16591273967534972, 16591273967534972,
    11668441828086828, 20216621539732443, 15575332423664331, 32671501749354757, 16591273967534972, 12890834253091783,
    15575332423664331, 12890834253091783, 16591273967534972, 16591273967534972
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
noncomputable def negativeCeiling : ℝ := 265457111 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 72889726663092973873397760, coefficient := (-72889726663092973873397760) }, { argument := 62476908568365406177198080, coefficient := (-62476908568365406177198080) }, { argument := 72889726663092973873397760, coefficient := (-72889726663092973873397760) }, { argument := 822612629483477847999774720, coefficient := (-822612629483477847999774720) }, { argument := 62476908568365406177198080, coefficient := (-62476908568365406177198080) }, { argument := 72889726663092973873397760, coefficient := (-72889726663092973873397760) }, { argument := 64559472187310919716438016, coefficient := (-64559472187310919716438016) }, { argument := 186150591994592556667109376, coefficient := (-186150591994592556667109376) }, { argument := 15650652414623219236265263104, coefficient := (-15650652414623219236265263104) }, { argument := 1598615501781032297740369920, coefficient := (-1598615501781032297740369920) }, { argument := 160798102310185934905524879360, coefficient := (-160798102310185934905524879360) }, { argument := 843225759181203849357557760, coefficient := (-843225759181203849357557760) }, { argument := 61485211606962780682321920, coefficient := (-61485211606962780682321920) }, { argument := 1598615501781032297740369920, coefficient := (-1598615501781032297740369920) }, { argument := 1598615501781032297740369920, coefficient := (-1598615501781032297740369920) }, { argument := 843225759181203849357557760, coefficient := (-843225759181203849357557760) }, { argument := 19727969324176915058927861760, coefficient := (-19727969324176915058927861760) }, { argument := 1581048298464757217545420800, coefficient := (-1581048298464757217545420800) }, { argument := 15650663790499705192024375296, coefficient := (-15650663790499705192024375296) }, { argument := 1598615501781032297740369920, coefficient := (-1598615501781032297740369920) }, { argument := 61485211606962780682321920, coefficient := (-61485211606962780682321920) }, { argument := 1581048298464757217545420800, coefficient := (-1581048298464757217545420800) }, { argument := 61485211606962780682321920, coefficient := (-61485211606962780682321920) }, { argument := 1598615501781032297740369920, coefficient := (-1598615501781032297740369920) }, { argument := 1598615501781032297740369920, coefficient := (-1598615501781032297740369920) }, { argument := 194934193652730096764583936, coefficient := (-194934193652730096764583936) }, { argument := 740370892413732084760182784, coefficient := (-740370892413732084760182784) }, { argument := 26958537486596651566107721728, coefficient := (-26958537486596651566107721728) }, { argument := 26958543213157764948316651520, coefficient := (-26958543213157764948316651520) }, { argument := 740365165852618702551252992, coefficient := (-740365165852618702551252992) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1949279547333000672728580096, coefficient := (-1949279547333000672728580096) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1678546276870083912627388416, coefficient := (-1678546276870083912627388416) }, { argument := 78566795088338443781365825536, coefficient := (-78566795088338443781365825536) }, { argument := 21387928366570424047994142720, coefficient := (-21387928366570424047994142720) }, { argument := 1949279547333000672728580096, coefficient := (-1949279547333000672728580096) }, { argument := 78566795088338443781365825536, coefficient := (-78566795088338443781365825536) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1624399622777500560607150080, coefficient := (-1624399622777500560607150080) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 21387928366570424047994142720, coefficient := (-21387928366570424047994142720) }, { argument := 1624399622777500560607150080, coefficient := (-1624399622777500560607150080) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1678546276870083912627388416, coefficient := (-1678546276870083912627388416) }, { argument := 193470260043040506748338176, coefficient := (-193470260043040506748338176) }, { argument := 15773622837837144797629906944, coefficient := (-15773622837837144797629906944) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 160806885911844072445622353920, coefficient := (-160806885911844072445622353920) }, { argument := 983763385711404490917150720, coefficient := (-983763385711404490917150720) }, { argument := 71732746874789910796042240, coefficient := (-71732746874789910796042240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 983763385711404490917150720, coefficient := (-983763385711404490917150720) }, { argument := 23015964211539734235415838720, coefficient := (-23015964211539734235415838720) }, { argument := 1844556348208883420469657600, coefficient := (-1844556348208883420469657600) }, { argument := 15773634213713630753389019136, coefficient := (-15773634213713630753389019136) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 71732746874789910796042240, coefficient := (-71732746874789910796042240) }, { argument := 1844556348208883420469657600, coefficient := (-1844556348208883420469657600) }, { argument := 71732746874789910796042240, coefficient := (-71732746874789910796042240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }] }

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

end TermShard8


end Parent3

namespace Parent3

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-622486684130971704734618933526528)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    176697021, 200655, 51597, 200655, 177723, 8318583,
    2264535, 51597, 8318583, 200655, 200655, 85995,
    200655, 2264535, 85995, 200655, 177723, 139040701,
    13198134519, 1114295, 139443218445, 36735, 85715, 1114295,
    1114295, 36735, 13751135, 551025, 6599072193, 1114295,
    85715, 551025, 85715, 1114295, 1114295, 142175421,
    1896240957, 69165754563, 553326122799, 15169841361, 161459901, 13574777079,
    42315, 139470121485, 1395, 3255, 42315, 42315,
    1395, 522195, 20925, 6787393473, 42315, 3255,
    20925, 3255, 42315, 42315, 169078461, 210900593,
    7680289167, 122884652287, 3374383873, 3827014977
  ]
def negativeCoefficients : Array ℕ := #[
    203717795310867636862058496, 1895132893240417320708341760, 1949279547333000672728580096, 1895132893240417320708341760, 1678546276870083912627388416, 78566795088338443781365825536,
    21387928366570424047994142720, 1949279547333000672728580096, 78566795088338443781365825536, 1895132893240417320708341760, 1895132893240417320708341760, 1624399622777500560607150080,
    1895132893240417320708341760, 21387928366570424047994142720, 1624399622777500560607150080, 1895132893240417320708341760, 1678546276870083912627388416, 5129696454352343454168645632,
    486925219444769427126283665408, 21048437440116925253581537280, 5144546726938580374945781514240, 11102472495885850683207843840, 809555286158343278983905280, 21048437440116925253581537280,
    21048437440116925253581537280, 11102472495885850683207843840, 259751596101662714942550179840, 20817135929785970031014707200, 486925583472816977710575255552, 21048437440116925253581537280,
    809555286158343278983905280, 20817135929785970031014707200, 809555286158343278983905280, 21048437440116925253581537280, 21048437440116925253581537280, 5245347209517821065452060672,
    17489735817932539348182368256, 637941486544334814010518011904, 637941586035696054058377805824, 17489636326571299300322574336, 186150591994592556667109376, 15650652414623219236265263104,
    1598615501781032297740369920, 160798102310185934905524879360, 843225759181203849357557760, 61485211606962780682321920, 1598615501781032297740369920, 1598615501781032297740369920,
    843225759181203849357557760, 19727969324176915058927861760, 1581048298464757217545420800, 15650663790499705192024375296, 1598615501781032297740369920, 61485211606962780682321920,
    1581048298464757217545420800, 61485211606962780682321920, 1598615501781032297740369920, 1598615501781032297740369920, 194934193652730096764583936, 15561717056258320582314033152,
    566705314702931675123168575488, 566705432831269037140709736448, 15561598927920958564772872192, 70595965846972445982386552832
  ]
def negativeScales : Array ℕ := #[
    27, 17, 15, 17, 17, 22,
    21, 15, 22, 17, 17, 16,
    17, 21, 16, 17, 17, 27,
    33, 20, 37, 15, 16, 20,
    20, 15, 23, 19, 32, 20,
    16, 19, 16, 20, 20, 27,
    30, 36, 39, 33, 27, 33,
    15, 37, 10, 11, 15, 15,
    10, 18, 14, 32, 15, 11,
    14, 11, 15, 15, 27, 27,
    32, 36, 31, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    27396702476267690, 17614357580651952, 15654999565165109, 17614357580651952, 17439270874085520, 22987906387263822,
    21110783406763079, 15654999565165109, 22987906387263822, 17614357580651952, 17614357580651952, 16391965159307136,
    17614357580651952, 21110783406763079, 16391965159307136, 17614357580651952, 17439270874085520, 27050932020002186,
    33619614976165481, 20087699793650037, 37020886817111289, 15164867654172497, 16387260075508949, 20087699793650037,
    20087699793650037, 15164867654172497, 23713047365950039, 19071758249781016, 32619616054732049, 20087699793650037,
    16387260075508949, 19071758249781016, 16387260075508949, 20087699793650037, 20087699793650037, 27083096835403906,
    30820495155369592, 36009338854495348, 39009339079493542, 33820486948492941, 27266600671315131, 33660209455611354,
    15368881546194092, 37021165132107072, 10446049406716591, 11668441828086828, 15368881546194092, 15368881546194092,
    10446049406716591, 18994229139984646, 14352940002325070, 32660210504252280, 15368881546194092, 11668441828086828,
    14352940002325070, 11668441828086828, 15368881546194092, 15368881546194092, 27333117644821473, 27651987910758160,
    32838513485584971, 36838513786311202, 31651976959279424, 31833572402243709
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
noncomputable def negativeCeiling : ℝ := 4056298989 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 203717795310867636862058496, coefficient := (-203717795310867636862058496) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1949279547333000672728580096, coefficient := (-1949279547333000672728580096) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1678546276870083912627388416, coefficient := (-1678546276870083912627388416) }, { argument := 78566795088338443781365825536, coefficient := (-78566795088338443781365825536) }, { argument := 21387928366570424047994142720, coefficient := (-21387928366570424047994142720) }, { argument := 1949279547333000672728580096, coefficient := (-1949279547333000672728580096) }, { argument := 78566795088338443781365825536, coefficient := (-78566795088338443781365825536) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1624399622777500560607150080, coefficient := (-1624399622777500560607150080) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 21387928366570424047994142720, coefficient := (-21387928366570424047994142720) }, { argument := 1624399622777500560607150080, coefficient := (-1624399622777500560607150080) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1678546276870083912627388416, coefficient := (-1678546276870083912627388416) }, { argument := 5129696454352343454168645632, coefficient := (-5129696454352343454168645632) }, { argument := 486925219444769427126283665408, coefficient := (-486925219444769427126283665408) }, { argument := 21048437440116925253581537280, coefficient := (-21048437440116925253581537280) }, { argument := 5144546726938580374945781514240, coefficient := (-5144546726938580374945781514240) }, { argument := 11102472495885850683207843840, coefficient := (-11102472495885850683207843840) }, { argument := 809555286158343278983905280, coefficient := (-809555286158343278983905280) }, { argument := 21048437440116925253581537280, coefficient := (-21048437440116925253581537280) }, { argument := 21048437440116925253581537280, coefficient := (-21048437440116925253581537280) }, { argument := 11102472495885850683207843840, coefficient := (-11102472495885850683207843840) }, { argument := 259751596101662714942550179840, coefficient := (-259751596101662714942550179840) }, { argument := 20817135929785970031014707200, coefficient := (-20817135929785970031014707200) }, { argument := 486925583472816977710575255552, coefficient := (-486925583472816977710575255552) }, { argument := 21048437440116925253581537280, coefficient := (-21048437440116925253581537280) }, { argument := 809555286158343278983905280, coefficient := (-809555286158343278983905280) }, { argument := 20817135929785970031014707200, coefficient := (-20817135929785970031014707200) }, { argument := 809555286158343278983905280, coefficient := (-809555286158343278983905280) }, { argument := 21048437440116925253581537280, coefficient := (-21048437440116925253581537280) }, { argument := 21048437440116925253581537280, coefficient := (-21048437440116925253581537280) }, { argument := 5245347209517821065452060672, coefficient := (-5245347209517821065452060672) }, { argument := 17489735817932539348182368256, coefficient := (-17489735817932539348182368256) }, { argument := 637941486544334814010518011904, coefficient := (-637941486544334814010518011904) }, { argument := 637941586035696054058377805824, coefficient := (-637941586035696054058377805824) }, { argument := 17489636326571299300322574336, coefficient := (-17489636326571299300322574336) }, { argument := 186150591994592556667109376, coefficient := (-186150591994592556667109376) }, { argument := 15650652414623219236265263104, coefficient := (-15650652414623219236265263104) }, { argument := 1598615501781032297740369920, coefficient := (-1598615501781032297740369920) }, { argument := 160798102310185934905524879360, coefficient := (-160798102310185934905524879360) }, { argument := 843225759181203849357557760, coefficient := (-843225759181203849357557760) }, { argument := 61485211606962780682321920, coefficient := (-61485211606962780682321920) }, { argument := 1598615501781032297740369920, coefficient := (-1598615501781032297740369920) }, { argument := 1598615501781032297740369920, coefficient := (-1598615501781032297740369920) }, { argument := 843225759181203849357557760, coefficient := (-843225759181203849357557760) }, { argument := 19727969324176915058927861760, coefficient := (-19727969324176915058927861760) }, { argument := 1581048298464757217545420800, coefficient := (-1581048298464757217545420800) }, { argument := 15650663790499705192024375296, coefficient := (-15650663790499705192024375296) }, { argument := 1598615501781032297740369920, coefficient := (-1598615501781032297740369920) }, { argument := 61485211606962780682321920, coefficient := (-61485211606962780682321920) }, { argument := 1581048298464757217545420800, coefficient := (-1581048298464757217545420800) }, { argument := 61485211606962780682321920, coefficient := (-61485211606962780682321920) }, { argument := 1598615501781032297740369920, coefficient := (-1598615501781032297740369920) }, { argument := 1598615501781032297740369920, coefficient := (-1598615501781032297740369920) }, { argument := 194934193652730096764583936, coefficient := (-194934193652730096764583936) }, { argument := 15561717056258320582314033152, coefficient := (-15561717056258320582314033152) }, { argument := 566705314702931675123168575488, coefficient := (-566705314702931675123168575488) }, { argument := 566705432831269037140709736448, coefficient := (-566705432831269037140709736448) }, { argument := 15561598927920958564772872192, coefficient := (-15561598927920958564772872192) }, { argument := 70595965846972445982386552832, coefficient := (-70595965846972445982386552832) }] }

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

end TermShard9


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9
