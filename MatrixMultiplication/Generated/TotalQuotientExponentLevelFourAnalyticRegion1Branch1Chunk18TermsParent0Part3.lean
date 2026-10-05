import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 18, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 203529352484817104140627025533599744
def positiveArguments : Array ℕ := #[
    26915, 47, 35, 37
  ]
def positiveCoefficients : Array ℕ := #[
    2132425994071424646330235423293440, 1818224432700402278758088704, 1353996917968384675670917120, 1431368170423720942852112384
  ]
def positiveScales : Array ℕ := #[
    14, 5, 5, 5
  ]
def negativeArguments : Array ℕ := #[
    309214431945, 1148654557575, 19321833915, 30199451143, 1273, 30199443961,
    1273, 5984795457, 22232023695, 373970979, 30197452295, 2479,
    30197445113, 2479, 93, 83549349, 13079181999, 3269796699,
    334202193, 157599613701, 585443290635, 9847902447, 58809457489, 2479,
    58809443503, 2479, 157599613701, 585443290635, 9847902447, 1823157145295,
    77921, 1823156711729, 77921, 951, 58809457489, 2479,
    58809443503, 2479, 1899, 13716685542061, 145565, 120611,
    12532110295439, 811005, 13715397568279, 3248179, 3248179, 2324881,
    120611, 89984855547137, 3149, 89984839607039, 3149, 93,
    77878797357, 201, 77878778835, 201, 2253, 93
  ]
def negativeCoefficients : Array ℕ := #[
    712999936248361776482762096640, 2648617081585762275066013286400, 712849850529452948546943713280, 69635193300177049349978587136, 192370321046177867425120256, 69635176739612557177228623872,
    192370321046177867425120256, 27599997532194649412235952128, 102527112835577894518684385280, 27594187762430436717946208256, 69630584270489768576250019840, 187307944176541607756038144,
    69630567709925276403500056576, 187307944176541607756038144, 1798881619586568211962789888, 12329707668224328420789583872, 482536646058043793300697120768, 482536823036106436470135324672,
    12329884646286971590227787776, 726799935014459101188880072704, 2699880638003551222325355479040, 726646944410668166905916817408, 67802688213330284893400203264, 187307944176541607756038144,
    67802672088570121462038396928, 187307944176541607756038144, 726799935014459101188880072704, 2699880638003551222325355479040, 726646944410668166905916817408, 2101957079088235324075063377920,
    5887544299386969995142496256, 2101956579220670257702847381504, 5887544299386969995142496256, 36790030542512395044658348032, 67802688213330284893400203264, 187307944176541607756038144,
    67802672088570121462038396928, 187307944176541607756038144, 36732002103170892844272451584, 61774459895984189537838432256, 171852819269729976382914560, 8899520997896730919829504,
    225758429026820147749087870976, 239366426839981038533345280, 61768659377739511369390096384, 239673306874391270634029056, 239673306874391270634029056, 171545939235319744282230784,
    8899520997896730919829504, 101313940477768525789672767488, 237931712872904204446859264, 101313922530813672527375630336, 237931712872904204446859264, 1798881619586568211962789888,
    89788140225804177598612242432, 242994089742540464115941376, 89788118871392069270592552960, 242994089742540464115941376, 43579357945468152489808232448, 1798881619586568211962789888
  ]
def negativeScales : Array ℕ := #[
    38, 40, 34, 34, 10, 34,
    10, 32, 34, 28, 34, 11,
    34, 11, 6, 26, 33, 31,
    28, 37, 39, 33, 35, 11,
    35, 11, 37, 39, 33, 40,
    16, 40, 16, 9, 35, 11,
    35, 11, 10, 43, 17, 16,
    43, 19, 43, 21, 21, 21,
    16, 46, 11, 46, 11, 6,
    36, 7, 36, 7, 11, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14716122804900257, 5554588851677541, 5129283016944966, 5209453365628949
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    38169816699406632, 40063082130710095, 34169512981686595, 34813803279394722, 10314016703901359, 34813802936294540,
    10314016703901359, 32478654794853681, 34371920226157015, 28478351077133643, 34813707786812049, 11275542556086723,
    34813707443689156, 11275542556086723, 6539158811108986, 26316125251347425, 33606553263195809, 31606553792327283,
    28316145959343734, 37197473042309498, 39090738473612960, 33197169324589461, 35775329131113656, 11275542556086723,
    35775328788013476, 11275542556086723, 37197473042309498, 39090738473612960, 33197169324589461, 40729576057253861,
    16249724571930991, 40729575714165721, 16249724571930991, 9893301534732022, 35775329131113656, 11275542556086723,
    35775328788013476, 11275542556086723, 10891024193864606, 43640997148758011, 17151303986591323, 16880001967812042,
    43510694605611344, 19629351283408454, 43640861675751256, 21631199707801444, 21631199707801444, 21148725442489547,
    16880001967812042, 46354747449805599, 11620678042145331, 46354747194243680, 11620678042145331, 6539158811108986,
    36180511554291761, 7651051691200812, 36180511211173972, 7651051691200812, 11137631598235429, 6539158811108986
  ]

abbrev PositiveTerm := Fin 4
abbrev NegativeTerm := Fin 60
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
noncomputable def positiveFloor : ℝ := 188867928763 / 500000000000
noncomputable def negativeCeiling : ℝ := 1761454483 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 712999936248361776482762096640, coefficient := (-712999936248361776482762096640) }, { argument := 2648617081585762275066013286400, coefficient := (-2648617081585762275066013286400) }, { argument := 712849850529452948546943713280, coefficient := (-712849850529452948546943713280) }, { argument := 69635193300177049349978587136, coefficient := (-69635193300177049349978587136) }, { argument := 192370321046177867425120256, coefficient := (-192370321046177867425120256) }, { argument := 69635176739612557177228623872, coefficient := (-69635176739612557177228623872) }, { argument := 192370321046177867425120256, coefficient := (-192370321046177867425120256) }, { argument := 27599997532194649412235952128, coefficient := (-27599997532194649412235952128) }, { argument := 102527112835577894518684385280, coefficient := (-102527112835577894518684385280) }, { argument := 27594187762430436717946208256, coefficient := (-27594187762430436717946208256) }, { argument := 69630584270489768576250019840, coefficient := (-69630584270489768576250019840) }, { argument := 187307944176541607756038144, coefficient := (-187307944176541607756038144) }, { argument := 69630567709925276403500056576, coefficient := (-69630567709925276403500056576) }, { argument := 187307944176541607756038144, coefficient := (-187307944176541607756038144) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 12329707668224328420789583872, coefficient := (-12329707668224328420789583872) }, { argument := 482536646058043793300697120768, coefficient := (-482536646058043793300697120768) }, { argument := 482536823036106436470135324672, coefficient := (-482536823036106436470135324672) }, { argument := 12329884646286971590227787776, coefficient := (-12329884646286971590227787776) }, { argument := 726799935014459101188880072704, coefficient := (-726799935014459101188880072704) }, { argument := 2699880638003551222325355479040, coefficient := (-2699880638003551222325355479040) }, { argument := 726646944410668166905916817408, coefficient := (-726646944410668166905916817408) }, { argument := 67802688213330284893400203264, coefficient := (-67802688213330284893400203264) }, { argument := 187307944176541607756038144, coefficient := (-187307944176541607756038144) }, { argument := 67802672088570121462038396928, coefficient := (-67802672088570121462038396928) }, { argument := 187307944176541607756038144, coefficient := (-187307944176541607756038144) }, { argument := 726799935014459101188880072704, coefficient := (-726799935014459101188880072704) }, { argument := 2699880638003551222325355479040, coefficient := (-2699880638003551222325355479040) }, { argument := 726646944410668166905916817408, coefficient := (-726646944410668166905916817408) }, { argument := 2101957079088235324075063377920, coefficient := (-2101957079088235324075063377920) }, { argument := 5887544299386969995142496256, coefficient := (-5887544299386969995142496256) }, { argument := 2101956579220670257702847381504, coefficient := (-2101956579220670257702847381504) }, { argument := 5887544299386969995142496256, coefficient := (-5887544299386969995142496256) }, { argument := 36790030542512395044658348032, coefficient := (-36790030542512395044658348032) }, { argument := 67802688213330284893400203264, coefficient := (-67802688213330284893400203264) }, { argument := 187307944176541607756038144, coefficient := (-187307944176541607756038144) }, { argument := 67802672088570121462038396928, coefficient := (-67802672088570121462038396928) }, { argument := 187307944176541607756038144, coefficient := (-187307944176541607756038144) }, { argument := 36732002103170892844272451584, coefficient := (-36732002103170892844272451584) }, { argument := 61774459895984189537838432256, coefficient := (-61774459895984189537838432256) }, { argument := 171852819269729976382914560, coefficient := (-171852819269729976382914560) }, { argument := 8899520997896730919829504, coefficient := (-8899520997896730919829504) }, { argument := 225758429026820147749087870976, coefficient := (-225758429026820147749087870976) }, { argument := 239366426839981038533345280, coefficient := (-239366426839981038533345280) }, { argument := 61768659377739511369390096384, coefficient := (-61768659377739511369390096384) }, { argument := 239673306874391270634029056, coefficient := (-239673306874391270634029056) }, { argument := 239673306874391270634029056, coefficient := (-239673306874391270634029056) }, { argument := 171545939235319744282230784, coefficient := (-171545939235319744282230784) }, { argument := 8899520997896730919829504, coefficient := (-8899520997896730919829504) }, { argument := 101313940477768525789672767488, coefficient := (-101313940477768525789672767488) }, { argument := 237931712872904204446859264, coefficient := (-237931712872904204446859264) }, { argument := 101313922530813672527375630336, coefficient := (-101313922530813672527375630336) }, { argument := 237931712872904204446859264, coefficient := (-237931712872904204446859264) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 89788140225804177598612242432, coefficient := (-89788140225804177598612242432) }, { argument := 242994089742540464115941376, coefficient := (-242994089742540464115941376) }, { argument := 89788118871392069270592552960, coefficient := (-89788118871392069270592552960) }, { argument := 242994089742540464115941376, coefficient := (-242994089742540464115941376) }, { argument := 43579357945468152489808232448, coefficient := (-43579357945468152489808232448) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 2132425994071424646330235423293440, coefficient := 2132425994071424646330235423293440 }, { argument := 1818224432700402278758088704, coefficient := 1818224432700402278758088704 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }] }

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


end Parent0

namespace Parent0

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2531581461437789828944269676642304)
def positiveArguments : Array ℕ := #[
    3, 643, 1163, 35, 643, 19,
    19, 37, 37, 1163, 37, 47,
    3, 93, 2253, 1707, 951, 93,
    951, 1899, 93, 2253, 93, 1143,
    3429, 7239, 18669, 15621, 437007, 13335,
    15621, 14097, 7239, 7239, 14097, 437007,
    14097, 1143, 18669, 8181, 122715, 215433,
    8181, 68175, 8181, 215433, 428139, 68175,
    6607521, 422685, 122715, 215433, 8181, 422685,
    8181, 215433, 215433, 8181, 22347, 101803
  ]
def positiveCoefficients : Array ℕ := #[
    1856910058928070412348686336, 24874857664390609898754277376, 44991383302778039365865046016, 1353996917968384675670917120, 24874857664390609898754277376, 1470053796651389076442710016,
    1470053796651389076442710016, 1431368170423720942852112384, 1431368170423720942852112384, 44991383302778039365865046016, 1431368170423720942852112384, 1818224432700402278758088704,
    1856910058928070412348686336, 3597763239173136423925579776, 87158715890936304979616464896, 66036363970629504039150157824, 73580061085024790089316696064, 3597763239173136423925579776,
    73580061085024790089316696064, 73464004206341785688544903168, 3597763239173136423925579776, 87158715890936304979616464896, 3597763239173136423925579776, 353741366225797413552424747008,
    265306024669348060164318560256, 280045248262089619062336258048, 361110978022168193001433595904, 4834465338419231318549804875776, 8452944730437284028013149683712, 257936412872977280715309711360,
    4834465338419231318549804875776, 272675636465718839613327409152, 280045248262089619062336258048, 280045248262089619062336258048, 272675636465718839613327409152, 8452944730437284028013149683712,
    272675636465718839613327409152, 353741366225797413552424747008, 361110978022168193001433595904, 316487108168553000904679227392, 4747306622528295013570188410880, 8334160515105229023823219654656,
    316487108168553000904679227392, 5274785136142550015077987123200, 316487108168553000904679227392, 8334160515105229023823219654656, 8281412663743803523672439783424, 5274785136142550015077987123200,
    127808043848733986865339627995136, 8175916961020952523370880040960, 4747306622528295013570188410880, 8334160515105229023823219654656, 316487108168553000904679227392, 8175916961020952523370880040960,
    316487108168553000904679227392, 8334160515105229023823219654656, 8334160515105229023823219654656, 316487108168553000904679227392, 1729015378619399562698170564608, 1969156403427649501961805365248
  ]
def positiveScales : Array ℕ := #[
    1, 9, 10, 5, 9, 4,
    4, 5, 5, 10, 5, 5,
    1, 6, 11, 10, 9, 6,
    9, 10, 6, 11, 6, 10,
    11, 12, 14, 13, 18, 13,
    13, 13, 12, 12, 13, 18,
    13, 10, 14, 12, 16, 17,
    12, 16, 12, 17, 18, 16,
    22, 18, 16, 17, 12, 18,
    12, 17, 17, 12, 14, 16
  ]
def negativeArguments : Array ℕ := #[
    1, 3, 381, 2727
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 475368975085586025561263702016, 30185929917934712623140245078016, 216055199176398848617594352566272
  ]
def negativeScales : Array ℕ := #[
    0, 1, 8, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 9328674927327946, 10183635381473218, 5129283016944966, 9328674927327946, 4247927513443585,
    4247927513443585, 5209453365628949, 5209453365628949, 10183635381473218, 5209453365628949, 5554588851677541,
    1584962500720924, 6539158811107971, 11137631598235427, 10737247343017206, 9893301530621223, 6539158811107971,
    9893301530621223, 10891024189919810, 6539158811107971, 11137631598235427, 6539158811107971, 10158609688214478,
    11743572188923520, 12821574700875186, 14188357031608530, 13931199191644376, 18737296863498603, 13702930204433473,
    13931199191644376, 13783100553094012, 12821574700875186, 12821574700875186, 13783100553094012, 18737296863498603,
    13783100553094012, 10158609688214478, 14188357031608530, 12998061484221231, 16904952080950021, 17716879733085716,
    12998061484221231, 16056955174689987, 12998061484221231, 17716879733085716, 18707719733801506, 16056955174689987,
    22655677674365080, 18689223390186018, 16904952080950021, 17716879733085716, 12998061484221231, 18689223390186018,
    12998061484221231, 17716879733085716, 17716879733085716, 12998061484221231, 14447793547619150, 16635420550794014
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 1584962500724866, 8573647187496003, 11413098984915275
  ]

abbrev PositiveTerm := Fin 60
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 60314646657 / 1000000000000
noncomputable def negativeCeiling : ℝ := 131224023 / 4000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1856910058928070412348686336, coefficient := 1856910058928070412348686336 }, { argument := 24874857664390609898754277376, coefficient := 24874857664390609898754277376 }, { argument := 44991383302778039365865046016, coefficient := 44991383302778039365865046016 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 24874857664390609898754277376, coefficient := 24874857664390609898754277376 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 44991383302778039365865046016, coefficient := 44991383302778039365865046016 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 1818224432700402278758088704, coefficient := 1818224432700402278758088704 }, { argument := 1856910058928070412348686336, coefficient := 1856910058928070412348686336 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 87158715890936304979616464896, coefficient := 87158715890936304979616464896 }, { argument := 66036363970629504039150157824, coefficient := 66036363970629504039150157824 }, { argument := 73580061085024790089316696064, coefficient := 73580061085024790089316696064 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 73580061085024790089316696064, coefficient := 73580061085024790089316696064 }, { argument := 73464004206341785688544903168, coefficient := 73464004206341785688544903168 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 87158715890936304979616464896, coefficient := 87158715890936304979616464896 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 353741366225797413552424747008, coefficient := 353741366225797413552424747008 }, { argument := 265306024669348060164318560256, coefficient := 265306024669348060164318560256 }, { argument := 280045248262089619062336258048, coefficient := 280045248262089619062336258048 }, { argument := 361110978022168193001433595904, coefficient := 361110978022168193001433595904 }, { argument := 4834465338419231318549804875776, coefficient := 4834465338419231318549804875776 }, { argument := 8452944730437284028013149683712, coefficient := 8452944730437284028013149683712 }, { argument := 257936412872977280715309711360, coefficient := 257936412872977280715309711360 }, { argument := 4834465338419231318549804875776, coefficient := 4834465338419231318549804875776 }, { argument := 272675636465718839613327409152, coefficient := 272675636465718839613327409152 }, { argument := 280045248262089619062336258048, coefficient := 280045248262089619062336258048 }, { argument := 280045248262089619062336258048, coefficient := 280045248262089619062336258048 }, { argument := 272675636465718839613327409152, coefficient := 272675636465718839613327409152 }, { argument := 8452944730437284028013149683712, coefficient := 8452944730437284028013149683712 }, { argument := 272675636465718839613327409152, coefficient := 272675636465718839613327409152 }, { argument := 353741366225797413552424747008, coefficient := 353741366225797413552424747008 }, { argument := 361110978022168193001433595904, coefficient := 361110978022168193001433595904 }, { argument := 30185929917934712623140245078016, coefficient := (-30185929917934712623140245078016) }, { argument := 316487108168553000904679227392, coefficient := 316487108168553000904679227392 }, { argument := 4747306622528295013570188410880, coefficient := 4747306622528295013570188410880 }, { argument := 8334160515105229023823219654656, coefficient := 8334160515105229023823219654656 }, { argument := 316487108168553000904679227392, coefficient := 316487108168553000904679227392 }, { argument := 5274785136142550015077987123200, coefficient := 5274785136142550015077987123200 }, { argument := 316487108168553000904679227392, coefficient := 316487108168553000904679227392 }, { argument := 8334160515105229023823219654656, coefficient := 8334160515105229023823219654656 }, { argument := 8281412663743803523672439783424, coefficient := 8281412663743803523672439783424 }, { argument := 5274785136142550015077987123200, coefficient := 5274785136142550015077987123200 }, { argument := 127808043848733986865339627995136, coefficient := 127808043848733986865339627995136 }, { argument := 8175916961020952523370880040960, coefficient := 8175916961020952523370880040960 }, { argument := 4747306622528295013570188410880, coefficient := 4747306622528295013570188410880 }, { argument := 8334160515105229023823219654656, coefficient := 8334160515105229023823219654656 }, { argument := 316487108168553000904679227392, coefficient := 316487108168553000904679227392 }, { argument := 8175916961020952523370880040960, coefficient := 8175916961020952523370880040960 }, { argument := 316487108168553000904679227392, coefficient := 316487108168553000904679227392 }, { argument := 8334160515105229023823219654656, coefficient := 8334160515105229023823219654656 }, { argument := 8334160515105229023823219654656, coefficient := 8334160515105229023823219654656 }, { argument := 316487108168553000904679227392, coefficient := 316487108168553000904679227392 }, { argument := 216055199176398848617594352566272, coefficient := (-216055199176398848617594352566272) }, { argument := 1729015378619399562698170564608, coefficient := 1729015378619399562698170564608 }, { argument := 1969156403427649501961805365248, coefficient := 1969156403427649501961805365248 }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18
