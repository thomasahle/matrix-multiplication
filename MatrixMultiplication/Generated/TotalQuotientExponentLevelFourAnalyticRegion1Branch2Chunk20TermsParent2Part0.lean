import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 20, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk20

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-171096360786352914810141872750592)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    306924039, 2222241273, 15, 141, 1665, 117,
    1111120395, 1665, 15, 117, 117, 117,
    117, 117, 153462261, 141, 1947555945, 8442636657,
    35311534167, 7027901571, 1164116511, 2716271859, 35311534167, 35311534167,
    1164116511, 435767613951, 17461747665, 8442636657, 35311534167, 2716271859,
    17461747665, 2716271859, 35311534167, 35311534167, 1167796971, 26667513,
    2242450951, 1121225205, 13334027, 4094979, 653751903, 26093843517,
    653751903, 16378047, 6344757, 7616473, 475127363, 119859233,
    3607803, 950254499, 3607803, 3607803, 309068457, 3607803,
    119859233, 309068457, 50758283, 3607803, 3607803, 7616473,
    230055, 36727635, 1465946265, 36727635
  ]
def negativeCoefficients : Array ℕ := #[
    1415437299375562323715424256, 10248279008266379953849761792, 1160568786830044007717928960, 1363668324525301709068566528, 16102891917266860607086264320, 36209746149097373040799383552,
    10248276780822033053421404160, 16102891917266860607086264320, 1160568786830044007717928960, 1131554567159292907524980736, 1131554567159292907524980736, 1131554567159292907524980736,
    36209746149097373040799383552, 1131554567159292907524980736, 1415439526819909224143781888, 1363668324525301709068566528, 2245379130415409715814072320, 38934789429749442611068796928,
    81422854203587449790329257984, 16205237706932287199973998592, 42948318700793380109184663552, 3131648238599517299628048384, 81422854203587449790329257984, 81422854203587449790329257984,
    42948318700793380109184663552, 1004811706270645122137799524352, 80528097563987587704721244160, 38934789429749442611068796928, 81422854203587449790329257984, 3131648238599517299628048384,
    80528097563987587704721244160, 3131648238599517299628048384, 81422854203587449790329257984, 81422854203587449790329257984, 2692756481761276888866619392, 122982196848330606485962752,
    10341479697735899529770696704, 10341477202813763560553840640, 122984691770466575702818816, 151078059200430131933872128, 24119188084683183276473450496, 240673226628762076788069236736,
    24119188084683183276473450496, 151060820718093250357886976, 3745283474844070194639273984, 2247986050805100955605925888, 70116422941419975097779748864, 17688100768176978571741364224,
    2129670995499569326363508736, 70116406191776356169506881536, 2129670995499569326363508736, 2129670995499569326363508736, 91220907640564886145903624192, 2129670995499569326363508736,
    17688100768176978571741364224, 91220907640564886145903624192, 3745300224487689122912141312, 2129670995499569326363508736, 2129670995499569326363508736, 2247986050805100955605925888,
    8487531415754501794037760, 1355010566555235015532216320, 13520967788132700943149957120, 1355010566555235015532216320
  ]
def negativeScales : Array ℕ := #[
    28, 31, 3, 7, 10, 6,
    30, 10, 3, 6, 6, 6,
    6, 6, 27, 7, 30, 32,
    35, 32, 30, 31, 35, 35,
    30, 38, 34, 32, 35, 31,
    34, 31, 35, 35, 30, 24,
    31, 30, 23, 21, 29, 34,
    29, 23, 22, 22, 28, 26,
    21, 29, 21, 21, 28, 21,
    26, 28, 25, 21, 21, 22,
    17, 25, 30, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    28193306404538053, 31049368315386479, 3906890600547867, 7139551352398794, 10701306462033270, 6870364722125690,
    30049368001819366, 10701306462033270, 3906890600547867, 6870364722125690, 6870364722125690, 6870364722125690,
    6870364722125690, 6870364722125690, 27193308674875556, 7139551352398794, 30859017627417112, 32975046496450796,
    35039420451563919, 32710446839957569, 30116588312086379, 31338980733422828, 35039420451563919, 35039420451563919,
    30116588312086379, 38664768023796710, 34023478907694898, 32975046496450796, 35039420451563919, 31338980733422828,
    34023478907694898, 31338980733422828, 35039420451563919, 35039420451563919, 30121142328211015, 24668579950331610,
    31062429283490687, 30062428935434864, 23668609217781520, 21965424636229379, 29284167999991430, 34602990411797712,
    29284167999991430, 23965260010752695, 22597133480187229, 22860691647460680, 28823739055348519, 26836765807436419,
    21782689133790108, 29823738710712696, 21782689133790108, 21782689133790108, 28203351181810805, 21782689133790108,
    26836765807436419, 28203351181810805, 25597139932188504, 21782689133790108, 21782689133790108, 22860691647460680,
    17811619287473556, 25130362663912394, 30449185075712581, 25130362663912394
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
noncomputable def negativeCeiling : ℝ := 546595417 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1415437299375562323715424256, coefficient := (-1415437299375562323715424256) }, { argument := 10248279008266379953849761792, coefficient := (-10248279008266379953849761792) }, { argument := 1160568786830044007717928960, coefficient := (-1160568786830044007717928960) }, { argument := 1363668324525301709068566528, coefficient := (-1363668324525301709068566528) }, { argument := 16102891917266860607086264320, coefficient := (-16102891917266860607086264320) }, { argument := 36209746149097373040799383552, coefficient := (-36209746149097373040799383552) }, { argument := 10248276780822033053421404160, coefficient := (-10248276780822033053421404160) }, { argument := 16102891917266860607086264320, coefficient := (-16102891917266860607086264320) }, { argument := 1160568786830044007717928960, coefficient := (-1160568786830044007717928960) }, { argument := 1131554567159292907524980736, coefficient := (-1131554567159292907524980736) }, { argument := 1131554567159292907524980736, coefficient := (-1131554567159292907524980736) }, { argument := 1131554567159292907524980736, coefficient := (-1131554567159292907524980736) }, { argument := 36209746149097373040799383552, coefficient := (-36209746149097373040799383552) }, { argument := 1131554567159292907524980736, coefficient := (-1131554567159292907524980736) }, { argument := 1415439526819909224143781888, coefficient := (-1415439526819909224143781888) }, { argument := 1363668324525301709068566528, coefficient := (-1363668324525301709068566528) }, { argument := 2245379130415409715814072320, coefficient := (-2245379130415409715814072320) }, { argument := 38934789429749442611068796928, coefficient := (-38934789429749442611068796928) }, { argument := 81422854203587449790329257984, coefficient := (-81422854203587449790329257984) }, { argument := 16205237706932287199973998592, coefficient := (-16205237706932287199973998592) }, { argument := 42948318700793380109184663552, coefficient := (-42948318700793380109184663552) }, { argument := 3131648238599517299628048384, coefficient := (-3131648238599517299628048384) }, { argument := 81422854203587449790329257984, coefficient := (-81422854203587449790329257984) }, { argument := 81422854203587449790329257984, coefficient := (-81422854203587449790329257984) }, { argument := 42948318700793380109184663552, coefficient := (-42948318700793380109184663552) }, { argument := 1004811706270645122137799524352, coefficient := (-1004811706270645122137799524352) }, { argument := 80528097563987587704721244160, coefficient := (-80528097563987587704721244160) }, { argument := 38934789429749442611068796928, coefficient := (-38934789429749442611068796928) }, { argument := 81422854203587449790329257984, coefficient := (-81422854203587449790329257984) }, { argument := 3131648238599517299628048384, coefficient := (-3131648238599517299628048384) }, { argument := 80528097563987587704721244160, coefficient := (-80528097563987587704721244160) }, { argument := 3131648238599517299628048384, coefficient := (-3131648238599517299628048384) }, { argument := 81422854203587449790329257984, coefficient := (-81422854203587449790329257984) }, { argument := 81422854203587449790329257984, coefficient := (-81422854203587449790329257984) }, { argument := 2692756481761276888866619392, coefficient := (-2692756481761276888866619392) }, { argument := 122982196848330606485962752, coefficient := (-122982196848330606485962752) }, { argument := 10341479697735899529770696704, coefficient := (-10341479697735899529770696704) }, { argument := 10341477202813763560553840640, coefficient := (-10341477202813763560553840640) }, { argument := 122984691770466575702818816, coefficient := (-122984691770466575702818816) }, { argument := 151078059200430131933872128, coefficient := (-151078059200430131933872128) }, { argument := 24119188084683183276473450496, coefficient := (-24119188084683183276473450496) }, { argument := 240673226628762076788069236736, coefficient := (-240673226628762076788069236736) }, { argument := 24119188084683183276473450496, coefficient := (-24119188084683183276473450496) }, { argument := 151060820718093250357886976, coefficient := (-151060820718093250357886976) }, { argument := 3745283474844070194639273984, coefficient := (-3745283474844070194639273984) }, { argument := 2247986050805100955605925888, coefficient := (-2247986050805100955605925888) }, { argument := 70116422941419975097779748864, coefficient := (-70116422941419975097779748864) }, { argument := 17688100768176978571741364224, coefficient := (-17688100768176978571741364224) }, { argument := 2129670995499569326363508736, coefficient := (-2129670995499569326363508736) }, { argument := 70116406191776356169506881536, coefficient := (-70116406191776356169506881536) }, { argument := 2129670995499569326363508736, coefficient := (-2129670995499569326363508736) }, { argument := 2129670995499569326363508736, coefficient := (-2129670995499569326363508736) }, { argument := 91220907640564886145903624192, coefficient := (-91220907640564886145903624192) }, { argument := 2129670995499569326363508736, coefficient := (-2129670995499569326363508736) }, { argument := 17688100768176978571741364224, coefficient := (-17688100768176978571741364224) }, { argument := 91220907640564886145903624192, coefficient := (-91220907640564886145903624192) }, { argument := 3745300224487689122912141312, coefficient := (-3745300224487689122912141312) }, { argument := 2129670995499569326363508736, coefficient := (-2129670995499569326363508736) }, { argument := 2129670995499569326363508736, coefficient := (-2129670995499569326363508736) }, { argument := 2247986050805100955605925888, coefficient := (-2247986050805100955605925888) }, { argument := 8487531415754501794037760, coefficient := (-8487531415754501794037760) }, { argument := 1355010566555235015532216320, coefficient := (-1355010566555235015532216320) }, { argument := 13520967788132700943149957120, coefficient := (-13520967788132700943149957120) }, { argument := 1355010566555235015532216320, coefficient := (-1355010566555235015532216320) }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1043443549407716949423413228732416)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    920115, 59618599, 2201635545, 17613080047, 476953105, 1947555945,
    4094979, 230055, 7057477795, 12438307, 486888825, 12438307,
    12438307, 4094979, 230055, 306924039, 2222241273, 15,
    141, 1665, 117, 1111120395, 1665, 15,
    117, 117, 117, 117, 117, 153462261,
    141, 7057477795, 33804016799, 126324682029, 97007813407, 4164549957,
    9717283233, 126324682029, 126324682029, 4164549957, 1558929867237, 62468249355,
    33804016799, 126324682029, 9717283233, 62468249355, 9717283233, 126324682029,
    126324682029, 4222823907, 3880688969, 281266215, 6794799615, 4426242015,
    133231365, 54358390337, 133231365, 133231365, 11413486935, 133231365,
    4426242015, 11413486935, 31045518335, 133231365
  ]
def negativeCoefficients : Array ℕ := #[
    8486562961690632042577920, 2199538075572232400528211968, 81226014884394097687595581440, 81225994994192300210271551488, 2199557965774029877852241920, 2245379130415409715814072320,
    151078059200430131933872128, 8487531415754501794037760, 8136717918140812738082897920, 229446265939230031832154112, 2245378386781039244397772800, 229446265939230031832154112,
    229446265939230031832154112, 151078059200430131933872128, 8487531415754501794037760, 1415437299375562323715424256, 10248279008266379953849761792, 1160568786830044007717928960,
    1363668324525301709068566528, 16102891917266860607086264320, 36209746149097373040799383552, 10248276780822033053421404160, 16102891917266860607086264320, 1160568786830044007717928960,
    1131554567159292907524980736, 1131554567159292907524980736, 1131554567159292907524980736, 36209746149097373040799383552, 1131554567159292907524980736, 1415439526819909224143781888,
    1363668324525301709068566528, 8136717918140812738082897920, 155893511638632844268505399296, 291284884947712405798920388608, 223684788383637404684820414464, 153644774477914236025804161024,
    11203264805681246376881553408, 291284884947712405798920388608, 291284884947712405798920388608, 153644774477914236025804161024, 3594647536222868480353709850624, 288083952146089192548382801920,
    155893511638632844268505399296, 291284884947712405798920388608, 11203264805681246376881553408, 288083952146089192548382801920, 11203264805681246376881553408, 291284884947712405798920388608,
    291284884947712405798920388608, 9737168985096408092286910464, 71586076240810779866147323904, 83015134154975465478071255040, 125341929530045192942219427840, 653198029272043794156402769920,
    78645916567871493610804346880, 125341914350680663288472141824, 78645916567871493610804346880, 78645916567871493610804346880, 3368666759657162309662786191360, 78645916567871493610804346880,
    653198029272043794156402769920, 3368666759657162309662786191360, 71586091420175309519894609920, 78645916567871493610804346880
  ]
def negativeScales : Array ℕ := #[
    19, 25, 31, 34, 28, 30,
    21, 17, 32, 23, 28, 23,
    23, 21, 17, 28, 31, 3,
    7, 10, 6, 30, 10, 3,
    6, 6, 6, 6, 6, 27,
    7, 32, 34, 36, 36, 31,
    33, 36, 36, 31, 40, 35,
    34, 36, 33, 35, 33, 36,
    36, 31, 31, 28, 32, 32,
    26, 35, 26, 26, 33, 26,
    32, 33, 34, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19811454662030972, 25829259138662317, 31035928521372408, 34035928168092747, 28829272184749913, 30859017627417112,
    21965424636229379, 17811619287473556, 32716505538611407, 23568286795267393, 28859017149619032, 23568286795267393,
    23568286795267393, 21965424636229379, 17811619287473556, 28193306404538053, 31049368315386479, 3906890600547867,
    7139551352398794, 10701306462033270, 6870364722125690, 30049368001819366, 10701306462033270, 3906890600547867,
    6870364722125690, 6870364722125690, 6870364722125690, 6870364722125690, 6870364722125690, 27193308674875556,
    7139551352398794, 32716505538611407, 34976475651561316, 36878345595270461, 36497381901426812, 31955513464283695,
    33177905874182432, 36878345595270461, 36878345595270461, 31955513464283695, 40503693164525735, 35862404050645261,
    34976475651561316, 36878345595270461, 33177905874182432, 35862404050645261, 33177905874182432, 36878345595270461,
    36878345595270461, 31975560957520664, 31853665663905656, 28067361029209065, 32661783859207961, 32043435189963584,
    26989358537168946, 35661783684492322, 26989358537168946, 26989358537168946, 33410020565680524, 26989358537168946,
    32043435189963584, 33410020565680524, 34853665969819788, 26989358537168946
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
noncomputable def negativeCeiling : ℝ := 6764432321 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8486562961690632042577920, coefficient := (-8486562961690632042577920) }, { argument := 2199538075572232400528211968, coefficient := (-2199538075572232400528211968) }, { argument := 81226014884394097687595581440, coefficient := (-81226014884394097687595581440) }, { argument := 81225994994192300210271551488, coefficient := (-81225994994192300210271551488) }, { argument := 2199557965774029877852241920, coefficient := (-2199557965774029877852241920) }, { argument := 2245379130415409715814072320, coefficient := (-2245379130415409715814072320) }, { argument := 151078059200430131933872128, coefficient := (-151078059200430131933872128) }, { argument := 8487531415754501794037760, coefficient := (-8487531415754501794037760) }, { argument := 8136717918140812738082897920, coefficient := (-8136717918140812738082897920) }, { argument := 229446265939230031832154112, coefficient := (-229446265939230031832154112) }, { argument := 2245378386781039244397772800, coefficient := (-2245378386781039244397772800) }, { argument := 229446265939230031832154112, coefficient := (-229446265939230031832154112) }, { argument := 229446265939230031832154112, coefficient := (-229446265939230031832154112) }, { argument := 151078059200430131933872128, coefficient := (-151078059200430131933872128) }, { argument := 8487531415754501794037760, coefficient := (-8487531415754501794037760) }, { argument := 1415437299375562323715424256, coefficient := (-1415437299375562323715424256) }, { argument := 10248279008266379953849761792, coefficient := (-10248279008266379953849761792) }, { argument := 1160568786830044007717928960, coefficient := (-1160568786830044007717928960) }, { argument := 1363668324525301709068566528, coefficient := (-1363668324525301709068566528) }, { argument := 16102891917266860607086264320, coefficient := (-16102891917266860607086264320) }, { argument := 36209746149097373040799383552, coefficient := (-36209746149097373040799383552) }, { argument := 10248276780822033053421404160, coefficient := (-10248276780822033053421404160) }, { argument := 16102891917266860607086264320, coefficient := (-16102891917266860607086264320) }, { argument := 1160568786830044007717928960, coefficient := (-1160568786830044007717928960) }, { argument := 1131554567159292907524980736, coefficient := (-1131554567159292907524980736) }, { argument := 1131554567159292907524980736, coefficient := (-1131554567159292907524980736) }, { argument := 1131554567159292907524980736, coefficient := (-1131554567159292907524980736) }, { argument := 36209746149097373040799383552, coefficient := (-36209746149097373040799383552) }, { argument := 1131554567159292907524980736, coefficient := (-1131554567159292907524980736) }, { argument := 1415439526819909224143781888, coefficient := (-1415439526819909224143781888) }, { argument := 1363668324525301709068566528, coefficient := (-1363668324525301709068566528) }, { argument := 8136717918140812738082897920, coefficient := (-8136717918140812738082897920) }, { argument := 155893511638632844268505399296, coefficient := (-155893511638632844268505399296) }, { argument := 291284884947712405798920388608, coefficient := (-291284884947712405798920388608) }, { argument := 223684788383637404684820414464, coefficient := (-223684788383637404684820414464) }, { argument := 153644774477914236025804161024, coefficient := (-153644774477914236025804161024) }, { argument := 11203264805681246376881553408, coefficient := (-11203264805681246376881553408) }, { argument := 291284884947712405798920388608, coefficient := (-291284884947712405798920388608) }, { argument := 291284884947712405798920388608, coefficient := (-291284884947712405798920388608) }, { argument := 153644774477914236025804161024, coefficient := (-153644774477914236025804161024) }, { argument := 3594647536222868480353709850624, coefficient := (-3594647536222868480353709850624) }, { argument := 288083952146089192548382801920, coefficient := (-288083952146089192548382801920) }, { argument := 155893511638632844268505399296, coefficient := (-155893511638632844268505399296) }, { argument := 291284884947712405798920388608, coefficient := (-291284884947712405798920388608) }, { argument := 11203264805681246376881553408, coefficient := (-11203264805681246376881553408) }, { argument := 288083952146089192548382801920, coefficient := (-288083952146089192548382801920) }, { argument := 11203264805681246376881553408, coefficient := (-11203264805681246376881553408) }, { argument := 291284884947712405798920388608, coefficient := (-291284884947712405798920388608) }, { argument := 291284884947712405798920388608, coefficient := (-291284884947712405798920388608) }, { argument := 9737168985096408092286910464, coefficient := (-9737168985096408092286910464) }, { argument := 71586076240810779866147323904, coefficient := (-71586076240810779866147323904) }, { argument := 83015134154975465478071255040, coefficient := (-83015134154975465478071255040) }, { argument := 125341929530045192942219427840, coefficient := (-125341929530045192942219427840) }, { argument := 653198029272043794156402769920, coefficient := (-653198029272043794156402769920) }, { argument := 78645916567871493610804346880, coefficient := (-78645916567871493610804346880) }, { argument := 125341914350680663288472141824, coefficient := (-125341914350680663288472141824) }, { argument := 78645916567871493610804346880, coefficient := (-78645916567871493610804346880) }, { argument := 78645916567871493610804346880, coefficient := (-78645916567871493610804346880) }, { argument := 3368666759657162309662786191360, coefficient := (-3368666759657162309662786191360) }, { argument := 78645916567871493610804346880, coefficient := (-78645916567871493610804346880) }, { argument := 653198029272043794156402769920, coefficient := (-653198029272043794156402769920) }, { argument := 3368666759657162309662786191360, coefficient := (-3368666759657162309662786191360) }, { argument := 71586091420175309519894609920, coefficient := (-71586091420175309519894609920) }, { argument := 78645916567871493610804346880, coefficient := (-78645916567871493610804346880) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk20
