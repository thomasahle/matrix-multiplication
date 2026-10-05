import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 4, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4

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
def constantNumerator : ℤ := (-8970810025904074799801827034398720)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    10750114165, 14435867593, 58608311, 4328070413, 45110754095, 4328070413,
    58608311, 19942673919, 722729103873, 5781834955785, 159539266551, 516984670620383,
    1313631595, 428658731, 14197287171032117, 4328070413, 4135876734411987, 8669968527,
    3885583981, 1313631595, 428658731, 634461681, 22993101327, 183944878215,
    5075625849, 127042417953, 215319743199, 127042417953, 8398632648325, 25090137,
    8398257023355, 12668301, 50050839563713, 2066907621139715, 15835652847, 10613557597183825,
    16249656843, 517504995, 15835652847, 9004586913, 16249656843, 253680948549,
    310502997, 1033454183632917, 15835652847, 517504995, 310502997, 517504995,
    7969576923, 9004586913, 50050839563713, 340112789262009, 115486983185, 4918927255697707,
    2857688541365, 90915284635, 4918929653934733, 46686227245, 46686227245, 1579960216765,
    86000944925, 2857688541365, 1579960216765, 340110382372311
  ]
def negativeCoefficients : Array ℕ := #[
    198304604764914854922960240640, 266294754970028519467975180288, 270283128402344081195270144, 39919403620802700752352968704, 416073267881255068701042933760, 39919403620802700752352968704,
    270283128402344081195270144, 183938700964617644296793751552, 6665999406883338849156159504384, 6666001856612104759289220956160, 183936251235851734163732299776, 1164145984981107744961655209984,
    48464451680207751712121815040, 1976839476429526714573389824, 3996181075820760339621192138752, 39919403620802700752352968704, 1164145807496758031507597033472, 39983172636171395162500497408,
    35838186637206258502911131648, 48464451680207751712121815040, 1976839476429526714573389824, 5851876126991275012021813248, 212073927820020238537212297216, 212074005756361028455461027840,
    5851798190650485093773082624, 585879742621058673882024640512, 1985974098404407890635277729792, 585879742621058673882024640512, 18912039432709075988224409600, 115707834003327687063502848,
    18911193600471614461354967040, 116844453197859393223262208, 28176117801089793173756051456, 1163565549046757349361010606080, 584232470617438077798007701504, 5974901754969046394494936678400,
    599506522136848223622792216576, 19092564399262682280980643840, 584232470617438077798007701504, 332210620547170671689063202816, 599506522136848223622792216576, 9359175068518566854136711610368,
    366577236465843499794828361728, 1163565969078421286835305054208, 584232470617438077798007701504, 19092564399262682280980643840, 366577236465843499794828361728, 19092564399262682280980643840,
    588050983497290614254203830272, 332210620547170671689063202816, 28176117801089793173756051456, 1531731830984323765641060286464, 266294852832311673506360197120, 44305757911645539484964533305344,
    6589381145616563325274402324480, 209636373506287913185858027520, 44305779513044292764417587675136, 215302221438890289217908244480, 215302221438890289217908244480, 3643140220663327788608289505280,
    198304677641083161121757593600, 6589381145616563325274402324480, 3643140220663327788608289505280, 1531720991316776730955408736256
  ]
def negativeScales : Array ℕ := #[
    33, 33, 25, 32, 35, 32,
    25, 34, 39, 42, 37, 48,
    30, 28, 53, 32, 51, 33,
    31, 30, 28, 29, 34, 37,
    32, 36, 37, 36, 42, 24,
    42, 23, 45, 50, 33, 53,
    33, 28, 33, 33, 33, 37,
    28, 49, 33, 28, 28, 28,
    32, 33, 45, 48, 36, 52,
    41, 36, 52, 35, 35, 40,
    36, 41, 40, 48
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33323632930028338, 33748938764980729, 25804601926638430, 32011076824421686, 35392752351978636, 32011076824421686,
    25804601926638430, 34215139808512047, 39394664035703225, 42394664565887925, 37215120594311563, 48877114834382176,
    30290913585820016, 28675254287915937, 53656464802966969, 32011076824421686, 51877114614430531, 33013379610291107,
    31855484299632569, 30290913585820016, 28675254287915937, 29240957792667778, 34420482019858966, 37420482550043666,
    32240938578467295, 36886519323338630, 37647689653622455, 36886519323338630, 42933291613420542, 24580617012549822,
    42933227088098859, 23594719715669611, 45508459502881983, 50876395336202634, 33882457297770502, 53236757837742000,
    33919690206981930, 28946997556694945, 33882457297770502, 33068012947748463, 33919690206981930, 37884224224049136,
    28210031952620891, 49876395856996260, 33882457297770502, 28946997556694945, 28210031952620891, 28946997556694945,
    32891855996366156, 33068012947748463, 45508459502881983, 48273006585153821, 36748939295165432, 52127265143014859,
    41377985824741292, 36403803808897028, 52127265846404774, 35442277956711691, 35442277956711691, 40523025370596593,
    36323633460213038, 41377985824741292, 40523025370596593, 48272996375540341
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
noncomputable def negativeCeiling : ℝ := 92306505447 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 198304604764914854922960240640, coefficient := (-198304604764914854922960240640) }, { argument := 266294754970028519467975180288, coefficient := (-266294754970028519467975180288) }, { argument := 270283128402344081195270144, coefficient := (-270283128402344081195270144) }, { argument := 39919403620802700752352968704, coefficient := (-39919403620802700752352968704) }, { argument := 416073267881255068701042933760, coefficient := (-416073267881255068701042933760) }, { argument := 39919403620802700752352968704, coefficient := (-39919403620802700752352968704) }, { argument := 270283128402344081195270144, coefficient := (-270283128402344081195270144) }, { argument := 183938700964617644296793751552, coefficient := (-183938700964617644296793751552) }, { argument := 6665999406883338849156159504384, coefficient := (-6665999406883338849156159504384) }, { argument := 6666001856612104759289220956160, coefficient := (-6666001856612104759289220956160) }, { argument := 183936251235851734163732299776, coefficient := (-183936251235851734163732299776) }, { argument := 1164145984981107744961655209984, coefficient := (-1164145984981107744961655209984) }, { argument := 48464451680207751712121815040, coefficient := (-48464451680207751712121815040) }, { argument := 1976839476429526714573389824, coefficient := (-1976839476429526714573389824) }, { argument := 3996181075820760339621192138752, coefficient := (-3996181075820760339621192138752) }, { argument := 39919403620802700752352968704, coefficient := (-39919403620802700752352968704) }, { argument := 1164145807496758031507597033472, coefficient := (-1164145807496758031507597033472) }, { argument := 39983172636171395162500497408, coefficient := (-39983172636171395162500497408) }, { argument := 35838186637206258502911131648, coefficient := (-35838186637206258502911131648) }, { argument := 48464451680207751712121815040, coefficient := (-48464451680207751712121815040) }, { argument := 1976839476429526714573389824, coefficient := (-1976839476429526714573389824) }, { argument := 5851876126991275012021813248, coefficient := (-5851876126991275012021813248) }, { argument := 212073927820020238537212297216, coefficient := (-212073927820020238537212297216) }, { argument := 212074005756361028455461027840, coefficient := (-212074005756361028455461027840) }, { argument := 5851798190650485093773082624, coefficient := (-5851798190650485093773082624) }, { argument := 585879742621058673882024640512, coefficient := (-585879742621058673882024640512) }, { argument := 1985974098404407890635277729792, coefficient := (-1985974098404407890635277729792) }, { argument := 585879742621058673882024640512, coefficient := (-585879742621058673882024640512) }, { argument := 18912039432709075988224409600, coefficient := (-18912039432709075988224409600) }, { argument := 115707834003327687063502848, coefficient := (-115707834003327687063502848) }, { argument := 18911193600471614461354967040, coefficient := (-18911193600471614461354967040) }, { argument := 116844453197859393223262208, coefficient := (-116844453197859393223262208) }, { argument := 28176117801089793173756051456, coefficient := (-28176117801089793173756051456) }, { argument := 1163565549046757349361010606080, coefficient := (-1163565549046757349361010606080) }, { argument := 584232470617438077798007701504, coefficient := (-584232470617438077798007701504) }, { argument := 5974901754969046394494936678400, coefficient := (-5974901754969046394494936678400) }, { argument := 599506522136848223622792216576, coefficient := (-599506522136848223622792216576) }, { argument := 19092564399262682280980643840, coefficient := (-19092564399262682280980643840) }, { argument := 584232470617438077798007701504, coefficient := (-584232470617438077798007701504) }, { argument := 332210620547170671689063202816, coefficient := (-332210620547170671689063202816) }, { argument := 599506522136848223622792216576, coefficient := (-599506522136848223622792216576) }, { argument := 9359175068518566854136711610368, coefficient := (-9359175068518566854136711610368) }, { argument := 366577236465843499794828361728, coefficient := (-366577236465843499794828361728) }, { argument := 1163565969078421286835305054208, coefficient := (-1163565969078421286835305054208) }, { argument := 584232470617438077798007701504, coefficient := (-584232470617438077798007701504) }, { argument := 19092564399262682280980643840, coefficient := (-19092564399262682280980643840) }, { argument := 366577236465843499794828361728, coefficient := (-366577236465843499794828361728) }, { argument := 19092564399262682280980643840, coefficient := (-19092564399262682280980643840) }, { argument := 588050983497290614254203830272, coefficient := (-588050983497290614254203830272) }, { argument := 332210620547170671689063202816, coefficient := (-332210620547170671689063202816) }, { argument := 28176117801089793173756051456, coefficient := (-28176117801089793173756051456) }, { argument := 1531731830984323765641060286464, coefficient := (-1531731830984323765641060286464) }, { argument := 266294852832311673506360197120, coefficient := (-266294852832311673506360197120) }, { argument := 44305757911645539484964533305344, coefficient := (-44305757911645539484964533305344) }, { argument := 6589381145616563325274402324480, coefficient := (-6589381145616563325274402324480) }, { argument := 209636373506287913185858027520, coefficient := (-209636373506287913185858027520) }, { argument := 44305779513044292764417587675136, coefficient := (-44305779513044292764417587675136) }, { argument := 215302221438890289217908244480, coefficient := (-215302221438890289217908244480) }, { argument := 215302221438890289217908244480, coefficient := (-215302221438890289217908244480) }, { argument := 3643140220663327788608289505280, coefficient := (-3643140220663327788608289505280) }, { argument := 198304677641083161121757593600, coefficient := (-198304677641083161121757593600) }, { argument := 6589381145616563325274402324480, coefficient := (-6589381145616563325274402324480) }, { argument := 3643140220663327788608289505280, coefficient := (-3643140220663327788608289505280) }, { argument := 1531720991316776730955408736256, coefficient := (-1531720991316776730955408736256) }] }

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
def constantNumerator : ℤ := (-2922986409751021958516651373625344)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    90915284635, 86000944925, 115486983185, 2647945772574085, 13691762425, 4467838265,
    73679936779614615, 45110754095, 21183559383882305, 90365632005, 40498792015, 13691762425,
    4467838265, 325804647, 11807268249, 94458180705, 2606402463, 130363788357,
    220949017531, 130363788357, 81635500097915, 2109810599, 81604049344133, 1065267827,
    4151713005, 7036592915, 4151713005, 875, 875, 12668301,
    1065267827, 532633785, 6334279, 117403869, 8669968527, 90365632005,
    8669968527, 117403869, 325804647, 11807268249, 94458180705, 2606402463,
    52616407, 3885583981, 40498792015, 3885583981, 52616407, 11025915159,
    399582814953, 3196663694385, 88206146511, 127042417953, 215319743199, 127042417953,
    600166455, 21750230985, 174001911825, 4801267695, 72239806287, 122436716721,
    72239806287, 775, 775, 17788465
  ]
def negativeCoefficients : Array ℕ := #[
    209636373506287913185858027520, 198304677641083161121757593600, 266294852832311673506360197120, 5962643797330964676410951598080, 505136874744015738359093657600, 20604267259295378801489346560,
    20739058489084630198428043837440, 416073267881255068701042933760, 5962641884227070164211943342080, 416737921663812984146252267520, 373535425797548480207645573120, 505136874744015738359093657600,
    20604267259295378801489346560, 6010034941234282444779159552, 217805655598939704443623440384, 217805735641668083278581596160, 6009954898505903609821003776, 601196860075203998689397833728,
    2037894989865961038102866690048, 601196860075203998689397833728, 183826803910587041860991057920, 9729784040938212311743594496, 183755983109080473652097449984, 9825361487312850939560329216,
    19146396817681656009216491520, 64901114326941434334486200320, 19146396817681656009216491520, 16924961474604808445886464000, 16924961474604808445886464000, 116844453197859393223262208,
    9825361487312850939560329216, 9825359116906237467882946560, 116846823604472864900644864, 270714890588290317746700288, 39983172636171395162500497408, 416737921663812984146252267520,
    39983172636171395162500497408, 270714890588290317746700288, 6010034941234282444779159552, 217805655598939704443623440384, 217805735641668083278581596160, 6009954898505903609821003776,
    242650348501784941903740928, 35838186637206258502911131648, 373535425797548480207645573120, 35838186637206258502911131648, 242650348501784941903740928, 101696117558253779262973673472,
    3685500961845216577822365057024, 3685502316252436251266525429760, 101694763151034105818813300736, 585879742621058673882024640512, 1985974098404407890635277729792, 585879742621058673882024640512,
    5535558498505260146507120640, 200610472262181306724390010880, 200610545985746918809219891200, 5535484774939648061677240320, 333147304627660814560366952448, 1129279389288780957420059885568,
    333147304627660814560366952448, 14990680163221401766356582400, 14990680163221401766356582400, 328139261319139779086909440
  ]
def negativeScales : Array ℕ := #[
    36, 36, 36, 51, 33, 32,
    56, 35, 54, 36, 35, 33,
    32, 28, 33, 36, 31, 36,
    37, 36, 46, 30, 46, 29,
    31, 32, 31, 9, 9, 23,
    29, 28, 22, 26, 33, 36,
    33, 26, 28, 33, 36, 31,
    25, 31, 35, 31, 25, 33,
    38, 41, 36, 36, 37, 36,
    29, 34, 37, 32, 36, 36,
    36, 9, 9, 24
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36403803808897028, 36323633460213038, 36748939295165432, 51233795000727652, 33672589113414427, 32056929815432888,
    56032121341736498, 35392752351978636, 54233794537841382, 36395055137848057, 35237159825266939, 33672589113414427,
    32056929815432888, 28279431940482414, 33458956167673652, 36458956697858351, 31279412726281931, 36923752232760217,
    37684922559851906, 36923752232760217, 46214261894037842, 30974466361404519, 46213705976709841, 29988569068566109,
    31951059582722450, 32712229905893342, 31951059582722450, 9773139207089529, 9773139207089529, 23594719715669611,
    29988569068566109, 28988568720510175, 22594748983119500, 26806904712541679, 33013379610291107, 36395055137848057,
    33013379610291107, 26806904712541679, 28279431940482414, 33458956167673652, 36458956697858351, 31279412726281931,
    25649009399238140, 31855484299632569, 35237159825266939, 31855484299632569, 25649009399238140, 33360179354366777,
    38539703581558919, 41539704111743619, 36360160140166294, 36886519323338630, 37647689653622455, 36886519323338630,
    29160787443983795, 34340311671174969, 37340312201359668, 32160768229783312, 36072074973071698, 36833245308012083,
    36072074973071698, 9598052500166958, 9598052500166958, 24084438687327386
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
noncomputable def negativeCeiling : ℝ := 122358861 / 3906250000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 209636373506287913185858027520, coefficient := (-209636373506287913185858027520) }, { argument := 198304677641083161121757593600, coefficient := (-198304677641083161121757593600) }, { argument := 266294852832311673506360197120, coefficient := (-266294852832311673506360197120) }, { argument := 5962643797330964676410951598080, coefficient := (-5962643797330964676410951598080) }, { argument := 505136874744015738359093657600, coefficient := (-505136874744015738359093657600) }, { argument := 20604267259295378801489346560, coefficient := (-20604267259295378801489346560) }, { argument := 20739058489084630198428043837440, coefficient := (-20739058489084630198428043837440) }, { argument := 416073267881255068701042933760, coefficient := (-416073267881255068701042933760) }, { argument := 5962641884227070164211943342080, coefficient := (-5962641884227070164211943342080) }, { argument := 416737921663812984146252267520, coefficient := (-416737921663812984146252267520) }, { argument := 373535425797548480207645573120, coefficient := (-373535425797548480207645573120) }, { argument := 505136874744015738359093657600, coefficient := (-505136874744015738359093657600) }, { argument := 20604267259295378801489346560, coefficient := (-20604267259295378801489346560) }, { argument := 6010034941234282444779159552, coefficient := (-6010034941234282444779159552) }, { argument := 217805655598939704443623440384, coefficient := (-217805655598939704443623440384) }, { argument := 217805735641668083278581596160, coefficient := (-217805735641668083278581596160) }, { argument := 6009954898505903609821003776, coefficient := (-6009954898505903609821003776) }, { argument := 601196860075203998689397833728, coefficient := (-601196860075203998689397833728) }, { argument := 2037894989865961038102866690048, coefficient := (-2037894989865961038102866690048) }, { argument := 601196860075203998689397833728, coefficient := (-601196860075203998689397833728) }, { argument := 183826803910587041860991057920, coefficient := (-183826803910587041860991057920) }, { argument := 9729784040938212311743594496, coefficient := (-9729784040938212311743594496) }, { argument := 183755983109080473652097449984, coefficient := (-183755983109080473652097449984) }, { argument := 9825361487312850939560329216, coefficient := (-9825361487312850939560329216) }, { argument := 19146396817681656009216491520, coefficient := (-19146396817681656009216491520) }, { argument := 64901114326941434334486200320, coefficient := (-64901114326941434334486200320) }, { argument := 19146396817681656009216491520, coefficient := (-19146396817681656009216491520) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 116844453197859393223262208, coefficient := (-116844453197859393223262208) }, { argument := 9825361487312850939560329216, coefficient := (-9825361487312850939560329216) }, { argument := 9825359116906237467882946560, coefficient := (-9825359116906237467882946560) }, { argument := 116846823604472864900644864, coefficient := (-116846823604472864900644864) }, { argument := 270714890588290317746700288, coefficient := (-270714890588290317746700288) }, { argument := 39983172636171395162500497408, coefficient := (-39983172636171395162500497408) }, { argument := 416737921663812984146252267520, coefficient := (-416737921663812984146252267520) }, { argument := 39983172636171395162500497408, coefficient := (-39983172636171395162500497408) }, { argument := 270714890588290317746700288, coefficient := (-270714890588290317746700288) }, { argument := 6010034941234282444779159552, coefficient := (-6010034941234282444779159552) }, { argument := 217805655598939704443623440384, coefficient := (-217805655598939704443623440384) }, { argument := 217805735641668083278581596160, coefficient := (-217805735641668083278581596160) }, { argument := 6009954898505903609821003776, coefficient := (-6009954898505903609821003776) }, { argument := 242650348501784941903740928, coefficient := (-242650348501784941903740928) }, { argument := 35838186637206258502911131648, coefficient := (-35838186637206258502911131648) }, { argument := 373535425797548480207645573120, coefficient := (-373535425797548480207645573120) }, { argument := 35838186637206258502911131648, coefficient := (-35838186637206258502911131648) }, { argument := 242650348501784941903740928, coefficient := (-242650348501784941903740928) }, { argument := 101696117558253779262973673472, coefficient := (-101696117558253779262973673472) }, { argument := 3685500961845216577822365057024, coefficient := (-3685500961845216577822365057024) }, { argument := 3685502316252436251266525429760, coefficient := (-3685502316252436251266525429760) }, { argument := 101694763151034105818813300736, coefficient := (-101694763151034105818813300736) }, { argument := 585879742621058673882024640512, coefficient := (-585879742621058673882024640512) }, { argument := 1985974098404407890635277729792, coefficient := (-1985974098404407890635277729792) }, { argument := 585879742621058673882024640512, coefficient := (-585879742621058673882024640512) }, { argument := 5535558498505260146507120640, coefficient := (-5535558498505260146507120640) }, { argument := 200610472262181306724390010880, coefficient := (-200610472262181306724390010880) }, { argument := 200610545985746918809219891200, coefficient := (-200610545985746918809219891200) }, { argument := 5535484774939648061677240320, coefficient := (-5535484774939648061677240320) }, { argument := 333147304627660814560366952448, coefficient := (-333147304627660814560366952448) }, { argument := 1129279389288780957420059885568, coefficient := (-1129279389288780957420059885568) }, { argument := 333147304627660814560366952448, coefficient := (-333147304627660814560366952448) }, { argument := 14990680163221401766356582400, coefficient := (-14990680163221401766356582400) }, { argument := 14990680163221401766356582400, coefficient := (-14990680163221401766356582400) }, { argument := 328139261319139779086909440, coefficient := (-328139261319139779086909440) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
