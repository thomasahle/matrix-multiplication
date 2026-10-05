import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-10437160367894648861614981762777088)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2479, 2479, 77921, 2479, 3149, 201,
    107189907, 4391590335, 90426245745, 4391590335, 107189907, 75398193,
    11803164243, 2950792143, 301597101, 107189907, 4391590335, 90426245745,
    4391590335, 107189907, 1424414511, 222984102861, 55746046161, 5697739827,
    157599613701, 585443290635, 9847902447, 75398193, 11803164243, 2950792143,
    301597101, 313204295583, 1163475906705, 19571147901, 77878797357, 201,
    77878778835, 201, 76721073, 3143276565, 64722498555, 3143276565,
    76721073, 874211481, 136852904331, 34213238631, 3496896117, 49873295475,
    185266864125, 3116424825, 1424414511, 222984102861, 55746046161, 5697739827,
    4833719797437, 17956064470995, 302043894039, 65163988549, 43081, 65163973051,
    43081, 309214431945, 1148654557575, 19321833915
  ]
def negativeCoefficients : Array ℕ := #[
    187307944176541607756038144, 187307944176541607756038144, 5887544299386969995142496256, 187307944176541607756038144, 237931712872904204446859264, 242994089742540464115941376,
    247163097714215997841342464, 40505271493160697237004615680, 417017453201095577045544468480, 40505271493160697237004615680, 247163097714215997841342464, 11126809359129271989493039104,
    435459900101161472003068133376, 435460059813071662180366024704, 11126969071039462166790930432, 247163097714215997841342464, 40505271493160697237004615680, 417017453201095577045544468480,
    40505271493160697237004615680, 247163097714215997841342464, 420412959028722222738142396416, 16453322711930371293521331093504, 16453328746450653614274370338816, 420418993549004543491181641728,
    726799935014459101188880072704, 2699880638003551222325355479040, 726646944410668166905916817408, 11126809359129271989493039104, 435459900101161472003068133376, 435460059813071662180366024704,
    11126969071039462166790930432, 722199935425759992953507414016, 2682792785864288239905574748160, 722047913116929760786259116032, 89788140225804177598612242432, 242994089742540464115941376,
    89788118871392069270592552960, 242994089742540464115941376, 176906749836423486291050496, 28991609173721933105615339520, 298479841663780316989064478720, 28991609173721933105615339520,
    176906749836423486291050496, 129010843650444802256554426368, 5048981003875628959170708897792, 5048982855670479542577757421568, 129012695445295385663602950144, 459999958869910823537265868800,
    1708785213926298241978073088000, 459903129373840611965770137600, 420412959028722222738142396416, 16453322711930371293521331093504, 16453328746450653614274370338816, 420418993549004543491181641728,
    11145799003417939254307952001024, 41403865733434206403128710922240, 11143452824728158027930610434048, 1202063419585542833456948445184, 3255108327176114967219798016, 1202063133697903179106317500416,
    3255108327176114967219798016, 712999936248361776482762096640, 2648617081585762275066013286400, 712849850529452948546943713280
  ]
def negativeScales : Array ℕ := #[
    11, 11, 16, 11, 11, 7,
    26, 32, 36, 32, 26, 26,
    33, 31, 28, 26, 32, 36,
    32, 26, 30, 37, 35, 32,
    37, 39, 33, 26, 33, 31,
    28, 38, 40, 34, 36, 7,
    36, 7, 26, 31, 35, 31,
    26, 29, 36, 34, 31, 35,
    37, 31, 30, 37, 35, 32,
    42, 44, 38, 35, 15, 35,
    15, 38, 40, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11275542556086723, 11275542556086723, 16249724571930991, 11275542556086723, 11620678042145331, 7651051691200812,
    26675593827187116, 32032096334278942, 36396022516985578, 32032096334278942, 26675593827187116, 26168026612358290,
    33458454624199967, 31458455153331440, 28168047320354600, 26675593827187116, 32032096334278942, 36396022516985578,
    32032096334278942, 26675593827187116, 30407721892104786, 37698149904015690, 35698150433147164, 32407742600101096,
    37197473042309498, 39090738473612960, 33197169324589461, 26168026612358290, 33458454624199967, 31458455153331440,
    28168047320354600, 38188313043024022, 40081578474327484, 34188009325303985, 36180511554291761, 7651051691200812,
    36180511211173972, 7651051691200812, 26193119561848000, 31549622068981467, 35913548257244098, 31549622068981467,
    26193119561848000, 29703407084307298, 36993835117523039, 34993835646654694, 31703427792303646, 35537548483908027,
    37430813915210604, 31537244766187981, 30407721892104786, 37698149904015690, 35698150433147164, 32407742600101096,
    42136270983583741, 44029536414887204, 38135967265863704, 35923355866331352, 15394764117785726, 35923355523214035,
    15394764117785726, 38169816699406632, 40063082130710095, 34169512981686595
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
noncomputable def negativeCeiling : ℝ := 38067037169 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 187307944176541607756038144, coefficient := (-187307944176541607756038144) }, { argument := 187307944176541607756038144, coefficient := (-187307944176541607756038144) }, { argument := 5887544299386969995142496256, coefficient := (-5887544299386969995142496256) }, { argument := 187307944176541607756038144, coefficient := (-187307944176541607756038144) }, { argument := 237931712872904204446859264, coefficient := (-237931712872904204446859264) }, { argument := 242994089742540464115941376, coefficient := (-242994089742540464115941376) }, { argument := 247163097714215997841342464, coefficient := (-247163097714215997841342464) }, { argument := 40505271493160697237004615680, coefficient := (-40505271493160697237004615680) }, { argument := 417017453201095577045544468480, coefficient := (-417017453201095577045544468480) }, { argument := 40505271493160697237004615680, coefficient := (-40505271493160697237004615680) }, { argument := 247163097714215997841342464, coefficient := (-247163097714215997841342464) }, { argument := 11126809359129271989493039104, coefficient := (-11126809359129271989493039104) }, { argument := 435459900101161472003068133376, coefficient := (-435459900101161472003068133376) }, { argument := 435460059813071662180366024704, coefficient := (-435460059813071662180366024704) }, { argument := 11126969071039462166790930432, coefficient := (-11126969071039462166790930432) }, { argument := 247163097714215997841342464, coefficient := (-247163097714215997841342464) }, { argument := 40505271493160697237004615680, coefficient := (-40505271493160697237004615680) }, { argument := 417017453201095577045544468480, coefficient := (-417017453201095577045544468480) }, { argument := 40505271493160697237004615680, coefficient := (-40505271493160697237004615680) }, { argument := 247163097714215997841342464, coefficient := (-247163097714215997841342464) }, { argument := 420412959028722222738142396416, coefficient := (-420412959028722222738142396416) }, { argument := 16453322711930371293521331093504, coefficient := (-16453322711930371293521331093504) }, { argument := 16453328746450653614274370338816, coefficient := (-16453328746450653614274370338816) }, { argument := 420418993549004543491181641728, coefficient := (-420418993549004543491181641728) }, { argument := 726799935014459101188880072704, coefficient := (-726799935014459101188880072704) }, { argument := 2699880638003551222325355479040, coefficient := (-2699880638003551222325355479040) }, { argument := 726646944410668166905916817408, coefficient := (-726646944410668166905916817408) }, { argument := 11126809359129271989493039104, coefficient := (-11126809359129271989493039104) }, { argument := 435459900101161472003068133376, coefficient := (-435459900101161472003068133376) }, { argument := 435460059813071662180366024704, coefficient := (-435460059813071662180366024704) }, { argument := 11126969071039462166790930432, coefficient := (-11126969071039462166790930432) }, { argument := 722199935425759992953507414016, coefficient := (-722199935425759992953507414016) }, { argument := 2682792785864288239905574748160, coefficient := (-2682792785864288239905574748160) }, { argument := 722047913116929760786259116032, coefficient := (-722047913116929760786259116032) }, { argument := 89788140225804177598612242432, coefficient := (-89788140225804177598612242432) }, { argument := 242994089742540464115941376, coefficient := (-242994089742540464115941376) }, { argument := 89788118871392069270592552960, coefficient := (-89788118871392069270592552960) }, { argument := 242994089742540464115941376, coefficient := (-242994089742540464115941376) }, { argument := 176906749836423486291050496, coefficient := (-176906749836423486291050496) }, { argument := 28991609173721933105615339520, coefficient := (-28991609173721933105615339520) }, { argument := 298479841663780316989064478720, coefficient := (-298479841663780316989064478720) }, { argument := 28991609173721933105615339520, coefficient := (-28991609173721933105615339520) }, { argument := 176906749836423486291050496, coefficient := (-176906749836423486291050496) }, { argument := 129010843650444802256554426368, coefficient := (-129010843650444802256554426368) }, { argument := 5048981003875628959170708897792, coefficient := (-5048981003875628959170708897792) }, { argument := 5048982855670479542577757421568, coefficient := (-5048982855670479542577757421568) }, { argument := 129012695445295385663602950144, coefficient := (-129012695445295385663602950144) }, { argument := 459999958869910823537265868800, coefficient := (-459999958869910823537265868800) }, { argument := 1708785213926298241978073088000, coefficient := (-1708785213926298241978073088000) }, { argument := 459903129373840611965770137600, coefficient := (-459903129373840611965770137600) }, { argument := 420412959028722222738142396416, coefficient := (-420412959028722222738142396416) }, { argument := 16453322711930371293521331093504, coefficient := (-16453322711930371293521331093504) }, { argument := 16453328746450653614274370338816, coefficient := (-16453328746450653614274370338816) }, { argument := 420418993549004543491181641728, coefficient := (-420418993549004543491181641728) }, { argument := 11145799003417939254307952001024, coefficient := (-11145799003417939254307952001024) }, { argument := 41403865733434206403128710922240, coefficient := (-41403865733434206403128710922240) }, { argument := 11143452824728158027930610434048, coefficient := (-11143452824728158027930610434048) }, { argument := 1202063419585542833456948445184, coefficient := (-1202063419585542833456948445184) }, { argument := 3255108327176114967219798016, coefficient := (-3255108327176114967219798016) }, { argument := 1202063133697903179106317500416, coefficient := (-1202063133697903179106317500416) }, { argument := 3255108327176114967219798016, coefficient := (-3255108327176114967219798016) }, { argument := 712999936248361776482762096640, coefficient := (-712999936248361776482762096640) }, { argument := 2648617081585762275066013286400, coefficient := (-2648617081585762275066013286400) }, { argument := 712849850529452948546943713280, coefficient := (-712849850529452948546943713280) }] }

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

end TermShard4


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3249859635348665445599715069526016)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1823157145295, 77921, 1823156711729, 77921, 2253, 81874198632339,
    10583069445, 754376933525961, 110735043705, 4904349255, 3017507286754047, 4904349255,
    9550574865, 180428427855, 9550574865, 110735043705, 180428427855, 40937219880741,
    9550574865, 9550574865, 10583069445, 18141546563295675, 5963825, 4941455,
    65706423237717295, 33227025, 9070620029992075, 133078495, 133078495, 95250805,
    4941455, 2156163235544831, 2345, 2156163684925697, 2345, 157599613701,
    585443290635, 9847902447, 65163988549, 43081, 65163973051, 43081,
    1707, 58813455185, 1273, 58813441199, 1273, 951,
    3980163, 163068015, 3357696705, 163068015, 3980163, 75398193,
    11803164243, 2950792143, 301597101, 5984795457, 22232023695, 373970979,
    75398193, 11803164243, 2950792143, 301597101
  ]
def negativeCoefficients : Array ℕ := #[
    2101957079088235324075063377920, 5887544299386969995142496256, 2101956579220670257702847381504, 5887544299386969995142496256, 43579357945468152489808232448, 184364305225929946817020035072,
    12201448347888148969496248320, 6794823353448830781560362893312, 127668813201073558729607086080, 11308659444384138069289205760, 6794822346106641244826848198656, 11308659444384138069289205760,
    11011063143216134435886858240, 416039629032869079496481832960, 11011063143216134435886858240, 127668813201073558729607086080, 416039629032869079496481832960, 184364848200489228300542017536,
    11011063143216134435886858240, 11011063143216134435886858240, 12201448347888148969496248320, 5106391396398931516014251212800, 28163367289700061866570547200, 1458460091788038918090260480,
    18494713950576981817333141995520, 39227547296367943314151833600, 5106305123386458277698496102400, 39277839023670979138913566720, 39277839023670979138913566720, 28113075562397026041808814080,
    1458460091788038918090260480, 2427623986037415971873613676544, 177183190437269088417873920, 2427624491995291138131312508928, 177183190437269088417873920, 726799935014459101188880072704,
    2699880638003551222325355479040, 726646944410668166905916817408, 1202063419585542833456948445184, 3255108327176114967219798016, 1202063133697903179106317500416, 3255108327176114967219798016,
    33018181985314752019575078912, 67807297243017565667128770560, 192370321046177867425120256, 67807281118257402235766964224, 192370321046177867425120256, 36790030542512395044658348032,
    9177631029081003761074176, 1504036969656415134280581120, 15484642948568209647017656320, 1504036969656415134280581120, 9177631029081003761074176, 11126809359129271989493039104,
    435459900101161472003068133376, 435460059813071662180366024704, 11126969071039462166790930432, 27599997532194649412235952128, 102527112835577894518684385280, 27594187762430436717946208256,
    11126809359129271989493039104, 435459900101161472003068133376, 435460059813071662180366024704, 11126969071039462166790930432
  ]
def negativeScales : Array ℕ := #[
    40, 16, 40, 16, 11, 46,
    33, 49, 36, 32, 51, 32,
    33, 37, 33, 36, 37, 45,
    33, 33, 33, 54, 22, 22,
    55, 24, 53, 26, 26, 26,
    22, 50, 11, 50, 11, 37,
    39, 33, 35, 15, 35, 15,
    10, 35, 10, 35, 10, 9,
    21, 27, 31, 27, 21, 26,
    33, 31, 28, 32, 34, 28,
    26, 33, 31, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    40729576057253861, 16249724571930991, 40729575714165721, 16249724571930991, 11137631598235429, 46218474114342677,
    33301039066953526, 49422278892033570, 36688320899889850, 32191414575779028, 51422278678151970, 32191414575779028,
    33152940427964392, 37392635707710883, 33152940427964392, 36688320899889850, 37392635707710883, 45218478363242970,
    33152940427964392, 33152940427964392, 33301039066953526, 54010146968776962, 22507806493723827, 22236504471906082,
    55866883931009890, 24985853809389571, 53010122594088647, 26987702234354710, 26987702234354710, 26505227949622022,
    22236504471906082, 50937387835320552, 11195372207402739, 50937388136002598, 11195372207402739, 37197473042309498,
    39090738473612960, 33197169324589461, 35923355866331352, 15394764117785726, 35923355523214035, 15394764117785726,
    10737247343197484, 35775427197997266, 10314016703901359, 35775426854920408, 10314016703901359, 9893301534732022,
    21924396090852929, 27280898591264535, 31644824773989832, 27280898591264535, 21924396090852929, 26168026612358290,
    33458454624199967, 31458455153331440, 28168047320354600, 32478654794853681, 34371920226157015, 28478351077133643,
    26168026612358290, 33458454624199967, 31458455153331440, 28168047320354600
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
noncomputable def negativeCeiling : ℝ := 18424590069 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2101957079088235324075063377920, coefficient := (-2101957079088235324075063377920) }, { argument := 5887544299386969995142496256, coefficient := (-5887544299386969995142496256) }, { argument := 2101956579220670257702847381504, coefficient := (-2101956579220670257702847381504) }, { argument := 5887544299386969995142496256, coefficient := (-5887544299386969995142496256) }, { argument := 43579357945468152489808232448, coefficient := (-43579357945468152489808232448) }, { argument := 184364305225929946817020035072, coefficient := (-184364305225929946817020035072) }, { argument := 12201448347888148969496248320, coefficient := (-12201448347888148969496248320) }, { argument := 6794823353448830781560362893312, coefficient := (-6794823353448830781560362893312) }, { argument := 127668813201073558729607086080, coefficient := (-127668813201073558729607086080) }, { argument := 11308659444384138069289205760, coefficient := (-11308659444384138069289205760) }, { argument := 6794822346106641244826848198656, coefficient := (-6794822346106641244826848198656) }, { argument := 11308659444384138069289205760, coefficient := (-11308659444384138069289205760) }, { argument := 11011063143216134435886858240, coefficient := (-11011063143216134435886858240) }, { argument := 416039629032869079496481832960, coefficient := (-416039629032869079496481832960) }, { argument := 11011063143216134435886858240, coefficient := (-11011063143216134435886858240) }, { argument := 127668813201073558729607086080, coefficient := (-127668813201073558729607086080) }, { argument := 416039629032869079496481832960, coefficient := (-416039629032869079496481832960) }, { argument := 184364848200489228300542017536, coefficient := (-184364848200489228300542017536) }, { argument := 11011063143216134435886858240, coefficient := (-11011063143216134435886858240) }, { argument := 11011063143216134435886858240, coefficient := (-11011063143216134435886858240) }, { argument := 12201448347888148969496248320, coefficient := (-12201448347888148969496248320) }, { argument := 5106391396398931516014251212800, coefficient := (-5106391396398931516014251212800) }, { argument := 28163367289700061866570547200, coefficient := (-28163367289700061866570547200) }, { argument := 1458460091788038918090260480, coefficient := (-1458460091788038918090260480) }, { argument := 18494713950576981817333141995520, coefficient := (-18494713950576981817333141995520) }, { argument := 39227547296367943314151833600, coefficient := (-39227547296367943314151833600) }, { argument := 5106305123386458277698496102400, coefficient := (-5106305123386458277698496102400) }, { argument := 39277839023670979138913566720, coefficient := (-39277839023670979138913566720) }, { argument := 39277839023670979138913566720, coefficient := (-39277839023670979138913566720) }, { argument := 28113075562397026041808814080, coefficient := (-28113075562397026041808814080) }, { argument := 1458460091788038918090260480, coefficient := (-1458460091788038918090260480) }, { argument := 2427623986037415971873613676544, coefficient := (-2427623986037415971873613676544) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 2427624491995291138131312508928, coefficient := (-2427624491995291138131312508928) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 726799935014459101188880072704, coefficient := (-726799935014459101188880072704) }, { argument := 2699880638003551222325355479040, coefficient := (-2699880638003551222325355479040) }, { argument := 726646944410668166905916817408, coefficient := (-726646944410668166905916817408) }, { argument := 1202063419585542833456948445184, coefficient := (-1202063419585542833456948445184) }, { argument := 3255108327176114967219798016, coefficient := (-3255108327176114967219798016) }, { argument := 1202063133697903179106317500416, coefficient := (-1202063133697903179106317500416) }, { argument := 3255108327176114967219798016, coefficient := (-3255108327176114967219798016) }, { argument := 33018181985314752019575078912, coefficient := (-33018181985314752019575078912) }, { argument := 67807297243017565667128770560, coefficient := (-67807297243017565667128770560) }, { argument := 192370321046177867425120256, coefficient := (-192370321046177867425120256) }, { argument := 67807281118257402235766964224, coefficient := (-67807281118257402235766964224) }, { argument := 192370321046177867425120256, coefficient := (-192370321046177867425120256) }, { argument := 36790030542512395044658348032, coefficient := (-36790030542512395044658348032) }, { argument := 9177631029081003761074176, coefficient := (-9177631029081003761074176) }, { argument := 1504036969656415134280581120, coefficient := (-1504036969656415134280581120) }, { argument := 15484642948568209647017656320, coefficient := (-15484642948568209647017656320) }, { argument := 1504036969656415134280581120, coefficient := (-1504036969656415134280581120) }, { argument := 9177631029081003761074176, coefficient := (-9177631029081003761074176) }, { argument := 11126809359129271989493039104, coefficient := (-11126809359129271989493039104) }, { argument := 435459900101161472003068133376, coefficient := (-435459900101161472003068133376) }, { argument := 435460059813071662180366024704, coefficient := (-435460059813071662180366024704) }, { argument := 11126969071039462166790930432, coefficient := (-11126969071039462166790930432) }, { argument := 27599997532194649412235952128, coefficient := (-27599997532194649412235952128) }, { argument := 102527112835577894518684385280, coefficient := (-102527112835577894518684385280) }, { argument := 27594187762430436717946208256, coefficient := (-27594187762430436717946208256) }, { argument := 11126809359129271989493039104, coefficient := (-11126809359129271989493039104) }, { argument := 435459900101161472003068133376, coefficient := (-435459900101161472003068133376) }, { argument := 435460059813071662180366024704, coefficient := (-435460059813071662180366024704) }, { argument := 11126969071039462166790930432, coefficient := (-11126969071039462166790930432) }] }

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

end TermShard5


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18
