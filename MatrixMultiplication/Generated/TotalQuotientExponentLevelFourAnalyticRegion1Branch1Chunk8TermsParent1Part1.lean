import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 8, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2582262204298833438842320492429312)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1539, 3249, 8379, 7011, 196137, 5985,
    7011, 6327, 3249, 3249, 6327, 196137,
    6327, 513, 8379, 31225594121409, 903790357486365, 38115,
    37941187739028045, 1485, 2475, 75735, 2475, 1485,
    1213245, 77715, 1807583999852095, 75735, 2475, 77715,
    2475, 75735, 2475, 31225594121409, 855, 2565,
    5415, 13965, 11685, 326895, 9975, 11685,
    10545, 5415, 5415, 10545, 326895, 10545,
    855, 13965, 5342157, 1859872083, 80465, 67086776537,
    3135, 5225, 159885, 5225, 3135, 2561295,
    164065, 7439493179, 159885, 5225
  ]
def negativeCoefficients : Array ℕ := #[
    930268418193457149936402432, 981949996981982547155091456, 1266198680318872231857881088, 16951557842636330287729999872, 29639385435219315304918155264, 904427628799194451327057920,
    16951557842636330287729999872, 956109207587719848545746944, 981949996981982547155091456, 981949996981982547155091456, 956109207587719848545746944, 29639385435219315304918155264,
    956109207587719848545746944, 1240357890924609533248536576, 1266198680318872231857881088, 17578446756199990354256068608, 4070309917196640783873123287040, 1439943987956612218560184320,
    42717979740870183774274537390080, 897627421063862162219335680, 46751428180409487615590400, 1430593702320530321037066240, 1496045701773103603698892800, 897627421063862162219335680,
    22917550094036730829162414080, 1467994844864857911129538560, 4070317314087382869388883394560, 1430593702320530321037066240, 46751428180409487615590400, 1467994844864857911129538560,
    46751428180409487615590400, 1430593702320530321037066240, 1496045701773103603698892800, 17578446756199990354256068608, 64601973485656746523361280, 48451480114242559892520960,
    51143229009478257664327680, 65947847933274595409264640, 882893637637308869152604160, 1543717991417672672131153920, 47105605666624711006617600, 882893637637308869152604160,
    49797354561860408778424320, 51143229009478257664327680, 51143229009478257664327680, 49797354561860408778424320, 1543717991417672672131153920, 49797354561860408778424320,
    64601973485656746523361280, 65947847933274595409264640, 197090805961151994264551424, 17154292162469044650522968064, 1519940876176424008480194560, 154691574688522718238132404224,
    947495611122965615675965440, 49348729745987792483123200, 1510071130227226449983569920, 1579159351871609359459942400, 947495611122965615675965440, 24190747321483215875226992640,
    1549550114024016683970068480, 17154303338890110309297553408, 1510071130227226449983569920, 49348729745987792483123200
  ]
def negativeScales : Array ℕ := #[
    10, 11, 13, 12, 17, 12,
    12, 12, 11, 11, 12, 17,
    12, 9, 13, 44, 49, 15,
    55, 10, 11, 16, 11, 10,
    20, 16, 50, 16, 11, 16,
    11, 16, 11, 44, 9, 11,
    12, 13, 13, 18, 13, 13,
    13, 12, 12, 13, 18, 13,
    9, 13, 22, 30, 16, 35,
    11, 12, 17, 12, 11, 21,
    17, 32, 17, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    10587777516332228, 11665780028361156, 13032562359001107, 12775404519891943, 17581502190905084, 12547135531832084,
    12775404519891943, 12627305880526679, 11665780028361156, 11665780028361156, 12627305880526679, 17581502190905084,
    12627305880526679, 9002815015607055, 13032562359001107, 44827794256547133, 49682981493489965, 15218071255661874,
    55074614360847669, 10536247215689000, 11273212809854335, 16208672557659624, 11273212809854335, 10536247215689000,
    20210439483833812, 16245905463858600, 50682984115267698, 16208672557659624, 11273212809854335, 16245905463858600,
    11273212809854335, 16208672557659624, 11273212809854335, 44827794256547133, 9739780609952834, 11324743110494417,
    12402745622495697, 13769527953509885, 13512370113670596, 18318467785067930, 13284101125997071, 13512370113670596,
    13364271474681056, 12402745622495697, 12402745622495697, 13364271474681056, 18318467785067930, 13364271474681056,
    9739780609952834, 13769527953509885, 22348990945108702, 30792556254601274, 16296073767663147, 35965309387417924,
    11614249727697750, 12351215321855609, 17286675069660898, 12351215321855609, 11614249727697750, 21288441995835085,
    17323907975859873, 32792557194550415, 17286675069660898, 12351215321855609
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
noncomputable def negativeCeiling : ℝ := 16686075801 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 930268418193457149936402432, coefficient := (-930268418193457149936402432) }, { argument := 981949996981982547155091456, coefficient := (-981949996981982547155091456) }, { argument := 1266198680318872231857881088, coefficient := (-1266198680318872231857881088) }, { argument := 16951557842636330287729999872, coefficient := (-16951557842636330287729999872) }, { argument := 29639385435219315304918155264, coefficient := (-29639385435219315304918155264) }, { argument := 904427628799194451327057920, coefficient := (-904427628799194451327057920) }, { argument := 16951557842636330287729999872, coefficient := (-16951557842636330287729999872) }, { argument := 956109207587719848545746944, coefficient := (-956109207587719848545746944) }, { argument := 981949996981982547155091456, coefficient := (-981949996981982547155091456) }, { argument := 981949996981982547155091456, coefficient := (-981949996981982547155091456) }, { argument := 956109207587719848545746944, coefficient := (-956109207587719848545746944) }, { argument := 29639385435219315304918155264, coefficient := (-29639385435219315304918155264) }, { argument := 956109207587719848545746944, coefficient := (-956109207587719848545746944) }, { argument := 1240357890924609533248536576, coefficient := (-1240357890924609533248536576) }, { argument := 1266198680318872231857881088, coefficient := (-1266198680318872231857881088) }, { argument := 17578446756199990354256068608, coefficient := (-17578446756199990354256068608) }, { argument := 4070309917196640783873123287040, coefficient := (-4070309917196640783873123287040) }, { argument := 1439943987956612218560184320, coefficient := (-1439943987956612218560184320) }, { argument := 42717979740870183774274537390080, coefficient := (-42717979740870183774274537390080) }, { argument := 897627421063862162219335680, coefficient := (-897627421063862162219335680) }, { argument := 46751428180409487615590400, coefficient := (-46751428180409487615590400) }, { argument := 1430593702320530321037066240, coefficient := (-1430593702320530321037066240) }, { argument := 1496045701773103603698892800, coefficient := (-1496045701773103603698892800) }, { argument := 897627421063862162219335680, coefficient := (-897627421063862162219335680) }, { argument := 22917550094036730829162414080, coefficient := (-22917550094036730829162414080) }, { argument := 1467994844864857911129538560, coefficient := (-1467994844864857911129538560) }, { argument := 4070317314087382869388883394560, coefficient := (-4070317314087382869388883394560) }, { argument := 1430593702320530321037066240, coefficient := (-1430593702320530321037066240) }, { argument := 46751428180409487615590400, coefficient := (-46751428180409487615590400) }, { argument := 1467994844864857911129538560, coefficient := (-1467994844864857911129538560) }, { argument := 46751428180409487615590400, coefficient := (-46751428180409487615590400) }, { argument := 1430593702320530321037066240, coefficient := (-1430593702320530321037066240) }, { argument := 1496045701773103603698892800, coefficient := (-1496045701773103603698892800) }, { argument := 17578446756199990354256068608, coefficient := (-17578446756199990354256068608) }, { argument := 64601973485656746523361280, coefficient := (-64601973485656746523361280) }, { argument := 48451480114242559892520960, coefficient := (-48451480114242559892520960) }, { argument := 51143229009478257664327680, coefficient := (-51143229009478257664327680) }, { argument := 65947847933274595409264640, coefficient := (-65947847933274595409264640) }, { argument := 882893637637308869152604160, coefficient := (-882893637637308869152604160) }, { argument := 1543717991417672672131153920, coefficient := (-1543717991417672672131153920) }, { argument := 47105605666624711006617600, coefficient := (-47105605666624711006617600) }, { argument := 882893637637308869152604160, coefficient := (-882893637637308869152604160) }, { argument := 49797354561860408778424320, coefficient := (-49797354561860408778424320) }, { argument := 51143229009478257664327680, coefficient := (-51143229009478257664327680) }, { argument := 51143229009478257664327680, coefficient := (-51143229009478257664327680) }, { argument := 49797354561860408778424320, coefficient := (-49797354561860408778424320) }, { argument := 1543717991417672672131153920, coefficient := (-1543717991417672672131153920) }, { argument := 49797354561860408778424320, coefficient := (-49797354561860408778424320) }, { argument := 64601973485656746523361280, coefficient := (-64601973485656746523361280) }, { argument := 65947847933274595409264640, coefficient := (-65947847933274595409264640) }, { argument := 197090805961151994264551424, coefficient := (-197090805961151994264551424) }, { argument := 17154292162469044650522968064, coefficient := (-17154292162469044650522968064) }, { argument := 1519940876176424008480194560, coefficient := (-1519940876176424008480194560) }, { argument := 154691574688522718238132404224, coefficient := (-154691574688522718238132404224) }, { argument := 947495611122965615675965440, coefficient := (-947495611122965615675965440) }, { argument := 49348729745987792483123200, coefficient := (-49348729745987792483123200) }, { argument := 1510071130227226449983569920, coefficient := (-1510071130227226449983569920) }, { argument := 1579159351871609359459942400, coefficient := (-1579159351871609359459942400) }, { argument := 947495611122965615675965440, coefficient := (-947495611122965615675965440) }, { argument := 24190747321483215875226992640, coefficient := (-24190747321483215875226992640) }, { argument := 1549550114024016683970068480, coefficient := (-1549550114024016683970068480) }, { argument := 17154303338890110309297553408, coefficient := (-17154303338890110309297553408) }, { argument := 1510071130227226449983569920, coefficient := (-1510071130227226449983569920) }, { argument := 49348729745987792483123200, coefficient := (-49348729745987792483123200) }] }

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


end Parent1

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-56487844236897914234637526237184)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    164065, 5225, 159885, 5225, 5342157, 2238340761513,
    350989597490875, 87747420316759, 8953453678917, 26163, 78489, 165699,
    427329, 357561, 10002987, 305235, 357561, 322677,
    165699, 165699, 322677, 10002987, 322677, 26163,
    427329, 855, 2565, 5415, 13965, 11685,
    326895, 9975, 11685, 10545, 5415, 5415,
    10545, 326895, 10545, 855, 13965, 432363,
    150754917, 207515, 5439457903, 8085, 13475, 412335,
    13475, 8085, 6605445, 423115, 603020061, 412335,
    13475, 423115, 13475, 412335, 13475, 432363,
    513, 1539, 3249, 8379
  ]
def negativeCoefficients : Array ℕ := #[
    1549550114024016683970068480, 49348729745987792483123200, 1510071130227226449983569920, 1579159351871609359459942400, 197090805961151994264551424, 2520147654869534763607130112,
    98794788779426564238475264000, 98794812360319530621642735616, 2520173165753099858636439552, 1976820388661096443614855168, 1482615291495822332711141376, 1564982807690034684528427008,
    2018004146758202619523497984, 27016545311701651396069687296, 47237770537380783767213309952, 1441431533398716156802498560, 27016545311701651396069687296, 1523799049592928508619784192,
    1564982807690034684528427008, 1564982807690034684528427008, 1523799049592928508619784192, 47237770537380783767213309952, 1523799049592928508619784192, 1976820388661096443614855168,
    2018004146758202619523497984, 2067263151541015888747560960, 1550447363655761916560670720, 1636583328303304245258485760, 2110331133864787053096468480, 28252596404393883812883333120,
    49398975725365525508196925440, 1507379381331990752211763200, 28252596404393883812883333120, 1593515345979533080909578240, 1636583328303304245258485760, 1636583328303304245258485760,
    1593515345979533080909578240, 49398975725365525508196925440, 1593515345979533080909578240, 2067263151541015888747560960, 2110331133864787053096468480, 255222067454121051691155456,
    22247498974018602687818366976, 1959923761385388853040250880, 200680575672715670128475242496, 1221770656448034609687429120, 63633888356668469254553600, 1947196983714055159189340160,
    2036284427413391016145715200, 1221770656448034609687429120, 31193332072438883628582174720, 1998104094399389934592983040, 22247513473159444623525937152, 1947196983714055159189340160,
    63633888356668469254553600, 1998104094399389934592983040, 63633888356668469254553600, 1947196983714055159189340160, 2036284427413391016145715200, 255222067454121051691155456,
    1240357890924609533248536576, 930268418193457149936402432, 981949996981982547155091456, 1266198680318872231857881088
  ]
def negativeScales : Array ℕ := #[
    17, 12, 17, 12, 22, 41,
    48, 46, 43, 14, 16, 17,
    18, 18, 23, 18, 18, 18,
    17, 17, 18, 23, 18, 14,
    18, 9, 11, 12, 13, 13,
    18, 13, 13, 13, 12, 12,
    13, 18, 13, 9, 13, 18,
    27, 17, 32, 12, 13, 18,
    13, 12, 22, 18, 29, 18,
    13, 18, 13, 18, 13, 18,
    9, 10, 11, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    17323907975859873, 12351215321855609, 17286675069660898, 12351215321855609, 22348990945108702, 41025566825329807,
    48318421601486468, 46318421945836952, 43025581429330829, 14675240357618530, 16260202858299706, 17338205370300980,
    18704987701053965, 18447829861475521, 23253927532873219, 18219560873802360, 18447829861475521, 18299731222486344,
    17338205370300980, 17338205370300980, 18299731222486344, 23253927532873219, 18299731222486344, 14675240357618530,
    18704987701053965, 9739780609952834, 11324743110494417, 12402745622495697, 13769527953509885, 13512370113670596,
    18318467785067930, 13284101125997071, 13512370113670596, 13364271474681056, 12402745622495697, 12402745622495697,
    13364271474681056, 18318467785067930, 13364271474681056, 9739780609952834, 13769527953509885, 18721883542494279,
    27167629816718991, 17662856098364221, 32340815733472279, 12981032075801390, 13717997652637148, 18653457400355779,
    13717997652637148, 12981032075801390, 22655224326531029, 18690690306589555, 29167630756951949, 18653457400355779,
    13717997652637148, 18690690306589555, 13717997652637148, 18653457400355779, 13717997652637148, 18721883542494279,
    9002815015607055, 10587777516332228, 11665780028361156, 13032562359001107
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
noncomputable def negativeCeiling : ℝ := 74728709 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1549550114024016683970068480, coefficient := (-1549550114024016683970068480) }, { argument := 49348729745987792483123200, coefficient := (-49348729745987792483123200) }, { argument := 1510071130227226449983569920, coefficient := (-1510071130227226449983569920) }, { argument := 1579159351871609359459942400, coefficient := (-1579159351871609359459942400) }, { argument := 197090805961151994264551424, coefficient := (-197090805961151994264551424) }, { argument := 2520147654869534763607130112, coefficient := (-2520147654869534763607130112) }, { argument := 98794788779426564238475264000, coefficient := (-98794788779426564238475264000) }, { argument := 98794812360319530621642735616, coefficient := (-98794812360319530621642735616) }, { argument := 2520173165753099858636439552, coefficient := (-2520173165753099858636439552) }, { argument := 1976820388661096443614855168, coefficient := (-1976820388661096443614855168) }, { argument := 1482615291495822332711141376, coefficient := (-1482615291495822332711141376) }, { argument := 1564982807690034684528427008, coefficient := (-1564982807690034684528427008) }, { argument := 2018004146758202619523497984, coefficient := (-2018004146758202619523497984) }, { argument := 27016545311701651396069687296, coefficient := (-27016545311701651396069687296) }, { argument := 47237770537380783767213309952, coefficient := (-47237770537380783767213309952) }, { argument := 1441431533398716156802498560, coefficient := (-1441431533398716156802498560) }, { argument := 27016545311701651396069687296, coefficient := (-27016545311701651396069687296) }, { argument := 1523799049592928508619784192, coefficient := (-1523799049592928508619784192) }, { argument := 1564982807690034684528427008, coefficient := (-1564982807690034684528427008) }, { argument := 1564982807690034684528427008, coefficient := (-1564982807690034684528427008) }, { argument := 1523799049592928508619784192, coefficient := (-1523799049592928508619784192) }, { argument := 47237770537380783767213309952, coefficient := (-47237770537380783767213309952) }, { argument := 1523799049592928508619784192, coefficient := (-1523799049592928508619784192) }, { argument := 1976820388661096443614855168, coefficient := (-1976820388661096443614855168) }, { argument := 2018004146758202619523497984, coefficient := (-2018004146758202619523497984) }, { argument := 2067263151541015888747560960, coefficient := (-2067263151541015888747560960) }, { argument := 1550447363655761916560670720, coefficient := (-1550447363655761916560670720) }, { argument := 1636583328303304245258485760, coefficient := (-1636583328303304245258485760) }, { argument := 2110331133864787053096468480, coefficient := (-2110331133864787053096468480) }, { argument := 28252596404393883812883333120, coefficient := (-28252596404393883812883333120) }, { argument := 49398975725365525508196925440, coefficient := (-49398975725365525508196925440) }, { argument := 1507379381331990752211763200, coefficient := (-1507379381331990752211763200) }, { argument := 28252596404393883812883333120, coefficient := (-28252596404393883812883333120) }, { argument := 1593515345979533080909578240, coefficient := (-1593515345979533080909578240) }, { argument := 1636583328303304245258485760, coefficient := (-1636583328303304245258485760) }, { argument := 1636583328303304245258485760, coefficient := (-1636583328303304245258485760) }, { argument := 1593515345979533080909578240, coefficient := (-1593515345979533080909578240) }, { argument := 49398975725365525508196925440, coefficient := (-49398975725365525508196925440) }, { argument := 1593515345979533080909578240, coefficient := (-1593515345979533080909578240) }, { argument := 2067263151541015888747560960, coefficient := (-2067263151541015888747560960) }, { argument := 2110331133864787053096468480, coefficient := (-2110331133864787053096468480) }, { argument := 255222067454121051691155456, coefficient := (-255222067454121051691155456) }, { argument := 22247498974018602687818366976, coefficient := (-22247498974018602687818366976) }, { argument := 1959923761385388853040250880, coefficient := (-1959923761385388853040250880) }, { argument := 200680575672715670128475242496, coefficient := (-200680575672715670128475242496) }, { argument := 1221770656448034609687429120, coefficient := (-1221770656448034609687429120) }, { argument := 63633888356668469254553600, coefficient := (-63633888356668469254553600) }, { argument := 1947196983714055159189340160, coefficient := (-1947196983714055159189340160) }, { argument := 2036284427413391016145715200, coefficient := (-2036284427413391016145715200) }, { argument := 1221770656448034609687429120, coefficient := (-1221770656448034609687429120) }, { argument := 31193332072438883628582174720, coefficient := (-31193332072438883628582174720) }, { argument := 1998104094399389934592983040, coefficient := (-1998104094399389934592983040) }, { argument := 22247513473159444623525937152, coefficient := (-22247513473159444623525937152) }, { argument := 1947196983714055159189340160, coefficient := (-1947196983714055159189340160) }, { argument := 63633888356668469254553600, coefficient := (-63633888356668469254553600) }, { argument := 1998104094399389934592983040, coefficient := (-1998104094399389934592983040) }, { argument := 63633888356668469254553600, coefficient := (-63633888356668469254553600) }, { argument := 1947196983714055159189340160, coefficient := (-1947196983714055159189340160) }, { argument := 2036284427413391016145715200, coefficient := (-2036284427413391016145715200) }, { argument := 255222067454121051691155456, coefficient := (-255222067454121051691155456) }, { argument := 1240357890924609533248536576, coefficient := (-1240357890924609533248536576) }, { argument := 930268418193457149936402432, coefficient := (-930268418193457149936402432) }, { argument := 981949996981982547155091456, coefficient := (-981949996981982547155091456) }, { argument := 1266198680318872231857881088, coefficient := (-1266198680318872231857881088) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
