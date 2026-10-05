import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 1,
parent chunk 8, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent0

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1376169614264928642760712136949760)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1421712901, 14245, 3663, 14245, 1476465, 698034735,
    26496841965, 2792140855, 1476465, 44676720811, 441595, 1717848670037,
    4983715, 441595, 1717848670037, 441595, 441595, 18307267,
    113553, 4983715, 18307267, 44676720811, 441595, 113553,
    441595, 17495063569, 32444011927, 17491679425, 1421712901, 14245,
    54652451323, 160765, 14245, 54652451323, 14245, 14245,
    590557, 3663, 160765, 590557, 1421712901, 14245,
    3663, 14245, 35550824581, 65929610023, 35543937325, 51581542395,
    51581558789, 11320072129, 5837541246921, 46009425, 57419465469949, 1792575,
    2987625, 91421325, 2987625, 1792575, 1464533775, 93811425,
    2918775119129, 91421325, 2987625, 93811425
  ]
def negativeCoefficients : Array ℕ := #[
    6556493507759541114848149504, 134540221096956192138199040, 138384227414012083342147584, 134540221096956192138199040, 1743102207282532680109916160, 206023489777674677267894108160,
    1955121849959529201920649461760, 206023631079734281883059486720, 1743102207282532680109916160, 206035008713272610663006470144, 4170746854005641956284170240, 7922178693383716185142301032448,
    47069857352349387792349921280, 4170746854005641956284170240, 7922178693383716185142301032448, 4170746854005641956284170240, 4170746854005641956284170240, 172907248147491042244809457664,
    4289911049834374583606575104, 47069857352349387792349921280, 172907248147491042244809457664, 206035008713272610663006470144, 4170746854005641956284170240, 4289911049834374583606575104,
    4170746854005641956284170240, 161363480105311313582203338752, 598486384741749259763326124032, 161332266886173023713781350400, 6556493507759541114848149504, 134540221096956192138199040,
    252039945639062498433398996992, 1518382495237077025559674880, 134540221096956192138199040, 252039945639062498433398996992, 134540221096956192138199040, 134540221096956192138199040,
    5577653166048098136929337344, 138384227414012083342147584, 1518382495237077025559674880, 5577653166048098136929337344, 6556493507759541114848149504, 134540221096956192138199040,
    138384227414012083342147584, 134540221096956192138199040, 163949240663762400861145268224, 608093321486878552506534723584, 163917478801561870723239116800, 59469469467985265099821547520,
    59469488368980411624470872064, 203924290487886149306023936, 26289948584393316180286242816, 1697448175907068173719961600, 258594283294275378387777224704, 1058149512253756783617638400,
    55111953763216499146752000, 1686425785154424873890611200, 1763582520422927972696064000, 1058149512253756783617638400, 27015879734728727881737830400, 1730515348164998073208012800,
    26289989077775278942839635968, 1686425785154424873890611200, 55111953763216499146752000, 1730515348164998073208012800
  ]
def negativeScales : Array ℕ := #[
    30, 13, 11, 13, 20, 29,
    34, 31, 20, 35, 18, 40,
    22, 18, 40, 18, 18, 24,
    16, 22, 24, 35, 18, 16,
    18, 34, 34, 34, 30, 13,
    35, 17, 13, 35, 13, 13,
    19, 11, 17, 19, 30, 13,
    11, 13, 35, 35, 35, 35,
    35, 33, 42, 25, 45, 20,
    21, 26, 21, 20, 30, 26,
    41, 26, 21, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30404983012247478, 13798168001833534, 11838809987105390, 13798168001833534, 20493715726727574, 29378723587461350,
    34625101370714141, 31378724576939351, 20493715726727574, 35378804247422635, 18752364311834874, 40643740089809230,
    22248790137717588, 18752364311834874, 40643740089809230, 18752364311834874, 18752364311834874, 24125913098719867,
    16793006296655241, 22248790137717588, 24125913098719867, 35378804247422635, 18752364311834874, 16793006296655241,
    18752364311834874, 34026228855549954, 34917233184633059, 34025949761963991, 30404983012247478, 13798168001833534,
    35669567155367765, 17294593827330713, 13798168001833534, 35669567155367765, 13798168001833534, 13798168001833534,
    19171716788332992, 11838809987105390, 17294593827330713, 19171716788332992, 30404983012247478, 13798168001833534,
    11838809987105390, 13798168001833534, 35049163971590977, 35940207505470913, 35048884451417022, 35586135862220719,
    35586136320747890, 33398164099606948, 42408497977306743, 25455426090771593, 45706605133871962, 20773602051171266,
    21510567644964381, 26446027392769327, 21510567644964381, 20773602051171266, 30447794318943517, 26483260298968415,
    41408500199431908, 26446027392769327, 21510567644964381, 26483260298968415
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
noncomputable def negativeCeiling : ℝ := 2054414567 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6556493507759541114848149504, coefficient := (-6556493507759541114848149504) }, { argument := 134540221096956192138199040, coefficient := (-134540221096956192138199040) }, { argument := 138384227414012083342147584, coefficient := (-138384227414012083342147584) }, { argument := 134540221096956192138199040, coefficient := (-134540221096956192138199040) }, { argument := 1743102207282532680109916160, coefficient := (-1743102207282532680109916160) }, { argument := 206023489777674677267894108160, coefficient := (-206023489777674677267894108160) }, { argument := 1955121849959529201920649461760, coefficient := (-1955121849959529201920649461760) }, { argument := 206023631079734281883059486720, coefficient := (-206023631079734281883059486720) }, { argument := 1743102207282532680109916160, coefficient := (-1743102207282532680109916160) }, { argument := 206035008713272610663006470144, coefficient := (-206035008713272610663006470144) }, { argument := 4170746854005641956284170240, coefficient := (-4170746854005641956284170240) }, { argument := 7922178693383716185142301032448, coefficient := (-7922178693383716185142301032448) }, { argument := 47069857352349387792349921280, coefficient := (-47069857352349387792349921280) }, { argument := 4170746854005641956284170240, coefficient := (-4170746854005641956284170240) }, { argument := 7922178693383716185142301032448, coefficient := (-7922178693383716185142301032448) }, { argument := 4170746854005641956284170240, coefficient := (-4170746854005641956284170240) }, { argument := 4170746854005641956284170240, coefficient := (-4170746854005641956284170240) }, { argument := 172907248147491042244809457664, coefficient := (-172907248147491042244809457664) }, { argument := 4289911049834374583606575104, coefficient := (-4289911049834374583606575104) }, { argument := 47069857352349387792349921280, coefficient := (-47069857352349387792349921280) }, { argument := 172907248147491042244809457664, coefficient := (-172907248147491042244809457664) }, { argument := 206035008713272610663006470144, coefficient := (-206035008713272610663006470144) }, { argument := 4170746854005641956284170240, coefficient := (-4170746854005641956284170240) }, { argument := 4289911049834374583606575104, coefficient := (-4289911049834374583606575104) }, { argument := 4170746854005641956284170240, coefficient := (-4170746854005641956284170240) }, { argument := 161363480105311313582203338752, coefficient := (-161363480105311313582203338752) }, { argument := 598486384741749259763326124032, coefficient := (-598486384741749259763326124032) }, { argument := 161332266886173023713781350400, coefficient := (-161332266886173023713781350400) }, { argument := 6556493507759541114848149504, coefficient := (-6556493507759541114848149504) }, { argument := 134540221096956192138199040, coefficient := (-134540221096956192138199040) }, { argument := 252039945639062498433398996992, coefficient := (-252039945639062498433398996992) }, { argument := 1518382495237077025559674880, coefficient := (-1518382495237077025559674880) }, { argument := 134540221096956192138199040, coefficient := (-134540221096956192138199040) }, { argument := 252039945639062498433398996992, coefficient := (-252039945639062498433398996992) }, { argument := 134540221096956192138199040, coefficient := (-134540221096956192138199040) }, { argument := 134540221096956192138199040, coefficient := (-134540221096956192138199040) }, { argument := 5577653166048098136929337344, coefficient := (-5577653166048098136929337344) }, { argument := 138384227414012083342147584, coefficient := (-138384227414012083342147584) }, { argument := 1518382495237077025559674880, coefficient := (-1518382495237077025559674880) }, { argument := 5577653166048098136929337344, coefficient := (-5577653166048098136929337344) }, { argument := 6556493507759541114848149504, coefficient := (-6556493507759541114848149504) }, { argument := 134540221096956192138199040, coefficient := (-134540221096956192138199040) }, { argument := 138384227414012083342147584, coefficient := (-138384227414012083342147584) }, { argument := 134540221096956192138199040, coefficient := (-134540221096956192138199040) }, { argument := 163949240663762400861145268224, coefficient := (-163949240663762400861145268224) }, { argument := 608093321486878552506534723584, coefficient := (-608093321486878552506534723584) }, { argument := 163917478801561870723239116800, coefficient := (-163917478801561870723239116800) }, { argument := 59469469467985265099821547520, coefficient := (-59469469467985265099821547520) }, { argument := 59469488368980411624470872064, coefficient := (-59469488368980411624470872064) }, { argument := 203924290487886149306023936, coefficient := (-203924290487886149306023936) }, { argument := 26289948584393316180286242816, coefficient := (-26289948584393316180286242816) }, { argument := 1697448175907068173719961600, coefficient := (-1697448175907068173719961600) }, { argument := 258594283294275378387777224704, coefficient := (-258594283294275378387777224704) }, { argument := 1058149512253756783617638400, coefficient := (-1058149512253756783617638400) }, { argument := 55111953763216499146752000, coefficient := (-55111953763216499146752000) }, { argument := 1686425785154424873890611200, coefficient := (-1686425785154424873890611200) }, { argument := 1763582520422927972696064000, coefficient := (-1763582520422927972696064000) }, { argument := 1058149512253756783617638400, coefficient := (-1058149512253756783617638400) }, { argument := 27015879734728727881737830400, coefficient := (-27015879734728727881737830400) }, { argument := 1730515348164998073208012800, coefficient := (-1730515348164998073208012800) }, { argument := 26289989077775278942839635968, coefficient := (-26289989077775278942839635968) }, { argument := 1686425785154424873890611200, coefficient := (-1686425785154424873890611200) }, { argument := 55111953763216499146752000, coefficient := (-55111953763216499146752000) }, { argument := 1730515348164998073208012800, coefficient := (-1730515348164998073208012800) }] }

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

end TermShard10


end Parent0

namespace Parent0

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 110228926613120801648886554694778880
def positiveArguments : Array ℕ := #[
    1755, 1395, 1575, 675, 17775, 1575,
    675, 1575, 1575, 65295, 405, 17775,
    65295, 1395, 1575
  ]
def positiveCoefficients : Array ℕ := #[
    1112363401700271299813357062717440, 26983224293798523179441848320, 30464930654288655202595635200, 26112797703675990173653401600, 343818503098400537286436454400, 30464930654288655202595635200,
    26112797703675990173653401600, 30464930654288655202595635200, 30464930654288655202595635200, 1262988982267795391399036190720, 31335357244411188208384081920, 343818503098400537286436454400,
    1262988982267795391399036190720, 26983224293798523179441848320, 30464930654288655202595635200
  ]
def positiveScales : Array ℕ := #[
    10, 10, 10, 9, 14, 10,
    9, 10, 10, 15, 8, 14,
    15, 10, 10
  ]
def negativeArguments : Array ℕ := #[
    2987625, 91421325, 2987625, 11320072129, 11062732215201, 1155,
    1714558144677803, 13035, 1155, 428639561970455, 1155, 1155,
    47883, 297, 13035, 47883, 44251075435893, 1155,
    297, 1155, 5127020036963, 18598130093953, 1281912908615, 115317667,
    18865, 4431322077, 212905, 18865, 4431322077, 18865,
    18865, 782089, 4851, 212905, 782089, 115317667,
    18865, 4851, 18865, 21198285971, 157251579887, 42388354795,
    25643970575, 25643978737, 1730971087, 3210086611, 1730635915, 51581542395,
    51581558789
  ]
def negativeCoefficients : Array ℕ := #[
    55111953763216499146752000, 1686425785154424873890611200, 1763582520422927972696064000, 203924290487886149306023936, 12455529170519701341207527424, 174538665206862087098204160,
    482605213842250160021876768768, 1969793507334586411536875520, 174538665206862087098204160, 482605242891598441543022673920, 174538665206862087098204160, 174538665206862087098204160,
    7235874377575911096556978176, 179525484212772432443867136, 1969793507334586411536875520, 7235874377575911096556978176, 12455570427739463978537975808, 174538665206862087098204160,
    179525484212772432443867136, 174538665206862087098204160, 23090045527987633428415643648, 83758531760914738562820210688, 23092889990239770766380892160, 8508941961305046111892799488,
    178174887398671713912750080, 326973857050392205447007305728, 2010830872070723628443893760, 178174887398671713912750080, 326973857050392205447007305728, 178174887398671713912750080,
    178174887398671713912750080, 7386621760442075911068581888, 183265598467205191453114368, 2010830872070723628443893760, 7386621760442075911068581888, 8508941961305046111892799488,
    178174887398671713912750080, 183265598467205191453114368, 178174887398671713912750080, 195519678054172288975076589568, 725194912340495343094593486848, 195481783152241026419843399680,
    59130970278845421592143462400, 59130989099136062794313498624, 7982695160219957670757531648, 29607823083779314372667506688, 7981149452193789326298972160, 59469469467985265099821547520,
    59469488368980411624470872064
  ]
def negativeScales : Array ℕ := #[
    21, 26, 21, 33, 43, 10,
    50, 13, 10, 48, 10, 10,
    15, 8, 13, 15, 45, 10,
    8, 10, 42, 44, 40, 26,
    14, 32, 17, 14, 32, 14,
    14, 19, 12, 17, 19, 26,
    14, 12, 14, 34, 37, 35,
    34, 34, 30, 31, 30, 35,
    35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10777255315166917, 10446049406716546, 10621136113274016, 9398743691938192, 14117561939394139, 10621136113274016,
    9398743691938192, 10621136113274016, 10621136113274016, 15994684899055573, 8661778097770205, 14117561939394139,
    15994684899055573, 10446049406716546, 10621136113274016
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    21510567644964381, 26446027392769327, 21510567644964381, 33398164099606948, 43330772972320297, 10173677136303420,
    50606758253584340, 13670102962458164, 10173677136303420, 48606758340424159, 10173677136303420, 10173677136303420,
    15547225923426421, 8214319120800766, 13670102962458164, 15547225923426421, 45330777751040410, 10173677136303420,
    8214319120800766, 10173677136303420, 42221257674606820, 44080222809718824, 40221435389234281, 26781038314509347,
    14203424479697473, 32045090042467562, 17699850305889104, 14203424479697473, 32045090042467562, 14203424479697473,
    14203424479697473, 19576973266822201, 12244066464194818, 17699850305889104, 19576973266822201, 26781038314509347,
    14203424479697473, 12244066464194818, 14203424479697473, 34303228566440026, 37194283555515409, 35302948921514435,
    34577900607298489, 34577901066481477, 30688934481120788, 31579965077061198, 30688655101639455, 35586135862220719,
    35586136320747890
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 49
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
noncomputable def positiveFloor : ℝ := 36235403627 / 250000000000
noncomputable def negativeCeiling : ℝ := 152971353 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 55111953763216499146752000, coefficient := (-55111953763216499146752000) }, { argument := 1686425785154424873890611200, coefficient := (-1686425785154424873890611200) }, { argument := 1763582520422927972696064000, coefficient := (-1763582520422927972696064000) }, { argument := 203924290487886149306023936, coefficient := (-203924290487886149306023936) }, { argument := 12455529170519701341207527424, coefficient := (-12455529170519701341207527424) }, { argument := 174538665206862087098204160, coefficient := (-174538665206862087098204160) }, { argument := 482605213842250160021876768768, coefficient := (-482605213842250160021876768768) }, { argument := 1969793507334586411536875520, coefficient := (-1969793507334586411536875520) }, { argument := 174538665206862087098204160, coefficient := (-174538665206862087098204160) }, { argument := 482605242891598441543022673920, coefficient := (-482605242891598441543022673920) }, { argument := 174538665206862087098204160, coefficient := (-174538665206862087098204160) }, { argument := 174538665206862087098204160, coefficient := (-174538665206862087098204160) }, { argument := 7235874377575911096556978176, coefficient := (-7235874377575911096556978176) }, { argument := 179525484212772432443867136, coefficient := (-179525484212772432443867136) }, { argument := 1969793507334586411536875520, coefficient := (-1969793507334586411536875520) }, { argument := 7235874377575911096556978176, coefficient := (-7235874377575911096556978176) }, { argument := 12455570427739463978537975808, coefficient := (-12455570427739463978537975808) }, { argument := 174538665206862087098204160, coefficient := (-174538665206862087098204160) }, { argument := 179525484212772432443867136, coefficient := (-179525484212772432443867136) }, { argument := 174538665206862087098204160, coefficient := (-174538665206862087098204160) }, { argument := 23090045527987633428415643648, coefficient := (-23090045527987633428415643648) }, { argument := 83758531760914738562820210688, coefficient := (-83758531760914738562820210688) }, { argument := 23092889990239770766380892160, coefficient := (-23092889990239770766380892160) }, { argument := 8508941961305046111892799488, coefficient := (-8508941961305046111892799488) }, { argument := 178174887398671713912750080, coefficient := (-178174887398671713912750080) }, { argument := 326973857050392205447007305728, coefficient := (-326973857050392205447007305728) }, { argument := 2010830872070723628443893760, coefficient := (-2010830872070723628443893760) }, { argument := 178174887398671713912750080, coefficient := (-178174887398671713912750080) }, { argument := 326973857050392205447007305728, coefficient := (-326973857050392205447007305728) }, { argument := 178174887398671713912750080, coefficient := (-178174887398671713912750080) }, { argument := 178174887398671713912750080, coefficient := (-178174887398671713912750080) }, { argument := 7386621760442075911068581888, coefficient := (-7386621760442075911068581888) }, { argument := 183265598467205191453114368, coefficient := (-183265598467205191453114368) }, { argument := 2010830872070723628443893760, coefficient := (-2010830872070723628443893760) }, { argument := 7386621760442075911068581888, coefficient := (-7386621760442075911068581888) }, { argument := 8508941961305046111892799488, coefficient := (-8508941961305046111892799488) }, { argument := 178174887398671713912750080, coefficient := (-178174887398671713912750080) }, { argument := 183265598467205191453114368, coefficient := (-183265598467205191453114368) }, { argument := 178174887398671713912750080, coefficient := (-178174887398671713912750080) }, { argument := 195519678054172288975076589568, coefficient := (-195519678054172288975076589568) }, { argument := 725194912340495343094593486848, coefficient := (-725194912340495343094593486848) }, { argument := 195481783152241026419843399680, coefficient := (-195481783152241026419843399680) }, { argument := 59130970278845421592143462400, coefficient := (-59130970278845421592143462400) }, { argument := 59130989099136062794313498624, coefficient := (-59130989099136062794313498624) }, { argument := 7982695160219957670757531648, coefficient := (-7982695160219957670757531648) }, { argument := 29607823083779314372667506688, coefficient := (-29607823083779314372667506688) }, { argument := 7981149452193789326298972160, coefficient := (-7981149452193789326298972160) }, { argument := 59469469467985265099821547520, coefficient := (-59469469467985265099821547520) }, { argument := 59469488368980411624470872064, coefficient := (-59469488368980411624470872064) }, { argument := 1112363401700271299813357062717440, coefficient := 1112363401700271299813357062717440 }, { argument := 26983224293798523179441848320, coefficient := 26983224293798523179441848320 }, { argument := 30464930654288655202595635200, coefficient := 30464930654288655202595635200 }, { argument := 26112797703675990173653401600, coefficient := 26112797703675990173653401600 }, { argument := 343818503098400537286436454400, coefficient := 343818503098400537286436454400 }, { argument := 30464930654288655202595635200, coefficient := 30464930654288655202595635200 }, { argument := 26112797703675990173653401600, coefficient := 26112797703675990173653401600 }, { argument := 30464930654288655202595635200, coefficient := 30464930654288655202595635200 }, { argument := 30464930654288655202595635200, coefficient := 30464930654288655202595635200 }, { argument := 1262988982267795391399036190720, coefficient := 1262988982267795391399036190720 }, { argument := 31335357244411188208384081920, coefficient := 31335357244411188208384081920 }, { argument := 343818503098400537286436454400, coefficient := 343818503098400537286436454400 }, { argument := 1262988982267795391399036190720, coefficient := 1262988982267795391399036190720 }, { argument := 26983224293798523179441848320, coefficient := 26983224293798523179441848320 }, { argument := 30464930654288655202595635200, coefficient := 30464930654288655202595635200 }] }

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

end TermShard11


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
