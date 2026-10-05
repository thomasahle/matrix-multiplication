import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 10, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10

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
def constantNumerator : ℤ := (-89035824749887867679093764042784768)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    39592108325, 53166545465, 13010020975536249, 1309342725, 427259205, 177468491070128157,
    4313939715, 52040082866454015, 8641661985, 3872897955, 1309342725, 427259205,
    116818173, 4313939715, 34511509269, 934553835, 1415657769051, 2574526232485,
    1415657769051, 291941122447443, 10689, 291939776063405, 5397, 45038123349,
    81906681515, 45038123349, 302445228415, 46319, 302445084289, 23387,
    3747459, 2968238304806029, 29234750919, 104132314288047721, 723404581251, 23014591149,
    208263749311571817, 11818303563, 11818303563, 399956273211, 21770559195, 723404581251,
    399956273211, 5937376512041643, 23014591149, 21770559195, 29234750919, 104079723828005685,
    10474739235, 3418072803, 354935463811171689, 34511509269, 52039860878390193, 69133278951,
    30983176053, 10474739235, 3418072803, 10769199069121945, 1527, 10769146097185383,
    771, 23127684963, 42060187805, 23127684963
  ]
def negativeCoefficients : Array ℕ := #[
    182586372402465088041962700800, 245187414369024546799207055360, 117183851235014775705462802219008, 193224881222787721371372748800, 7881541207771604424358625280, 399623515126716682387457820327936,
    159156283744033044182209658880, 117183848902846017654171075870720, 159410527008799870131382517760, 142884714798956183435146690560, 193224881222787721371372748800, 7881541207771604424358625280,
    4309829880978654304860635136, 159156283744033044182209658880, 159156244770674502452354482176, 4309868854337196034715811840, 1632142285102651208903505739776, 5936453315212806632512390430720,
    1632142285102651208903505739776, 10518287442147429120048390733824, 403819002683149101513572352, 10518238933550214444978578391040, 407785790528759603493076992, 51925420936197845855055642624,
    188863948979255241103145697280, 51925420936197845855055642624, 1394782431221533233717088092160, 874941172480156386612740096, 1394781766557674141851379040256, 883535879478979140901666816,
    70787499110112791131487993856, 3341939230867816232682149380096, 67410746032679764730616741888, 117242562956219773192066148859904, 1668057396510778008121431293952, 53068034110833006277294030848,
    117242067974297153486231546363904, 54502305303017682122626301952, 54502305303017682122626301952, 922236376574746568548650319872, 50199491726463654586629488640, 1668057396510778008121431293952,
    922236376574746568548650319872, 3342445830898634833934067695616, 53068034110833006277294030848, 50199491726463654586629488640, 67410746032679764730616741888, 117183351362157634119815072317440,
    193224833906889172306372853760, 7881539277781005712496787456, 399621805640141746653385967271936, 159156244770674502452354482176, 117183349030165262925629031972864, 159410487973183567152757604352,
    142884679810094361626554662912, 193224833906889172306372853760, 7881539277781005712496787456, 97000321829552567795655838269440, 28844214477367792965255168, 96999844700765044362149873319936,
    29127556466339971678076928, 53328810691230220067354443776, 193968380032748625997825310720, 53328810691230220067354443776
  ]
def negativeScales : Array ℕ := #[
    35, 35, 53, 30, 28, 57,
    32, 55, 33, 31, 30, 28,
    26, 32, 35, 29, 40, 41,
    40, 48, 13, 48, 12, 35,
    36, 35, 38, 15, 38, 14,
    21, 51, 34, 56, 39, 34,
    57, 33, 33, 38, 34, 39,
    38, 52, 34, 34, 34, 56,
    33, 31, 58, 35, 55, 36,
    34, 33, 31, 53, 10, 53,
    9, 34, 35, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35204493843446343, 35629799678191648, 53530472806255597, 30286195631132324, 28670536333223874, 57300340514817589,
    32006358869733994, 55530472777543379, 33008661655603415, 31850766344779936, 30286195631132324, 28670536333223874,
    26799689486506241, 32006358869733994, 35006358516454333, 29799702532593711, 40364609679092138, 41227444108835461,
    40364609679092138, 48052670769727202, 13383839268854459, 48052664116241603, 12397941971972645, 35390427663247873,
    36253262092991193, 35390427663247873, 38137882943673477, 15499316486274657, 38137882256177377, 14513419189392997,
    21837481264783842, 51398528346590075, 34766965248760066, 56531195447610580, 39396011778231276, 34421829762387018,
    57531189356738336, 33460303910201706, 33460303910201706, 38541051324087011, 34341659413703020, 39396011778231276,
    38541051324087011, 52398747026198393, 34421829762387018, 34341659413703020, 34766965248760066, 56530466652117270,
    33286195277852663, 31670535979944212, 58300334343326208, 35006358516454333, 55530466623407100, 36008661302323754,
    34850765991500263, 33286195277852663, 31670535979944212, 53257760475417579, 10576484346799762, 53257753379018148,
    9590587049919383, 34428901811062525, 35291736240805828, 34428901811062525
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
noncomputable def negativeCeiling : ℝ := 1179361138251 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 182586372402465088041962700800, coefficient := (-182586372402465088041962700800) }, { argument := 245187414369024546799207055360, coefficient := (-245187414369024546799207055360) }, { argument := 117183851235014775705462802219008, coefficient := (-117183851235014775705462802219008) }, { argument := 193224881222787721371372748800, coefficient := (-193224881222787721371372748800) }, { argument := 7881541207771604424358625280, coefficient := (-7881541207771604424358625280) }, { argument := 399623515126716682387457820327936, coefficient := (-399623515126716682387457820327936) }, { argument := 159156283744033044182209658880, coefficient := (-159156283744033044182209658880) }, { argument := 117183848902846017654171075870720, coefficient := (-117183848902846017654171075870720) }, { argument := 159410527008799870131382517760, coefficient := (-159410527008799870131382517760) }, { argument := 142884714798956183435146690560, coefficient := (-142884714798956183435146690560) }, { argument := 193224881222787721371372748800, coefficient := (-193224881222787721371372748800) }, { argument := 7881541207771604424358625280, coefficient := (-7881541207771604424358625280) }, { argument := 4309829880978654304860635136, coefficient := (-4309829880978654304860635136) }, { argument := 159156283744033044182209658880, coefficient := (-159156283744033044182209658880) }, { argument := 159156244770674502452354482176, coefficient := (-159156244770674502452354482176) }, { argument := 4309868854337196034715811840, coefficient := (-4309868854337196034715811840) }, { argument := 1632142285102651208903505739776, coefficient := (-1632142285102651208903505739776) }, { argument := 5936453315212806632512390430720, coefficient := (-5936453315212806632512390430720) }, { argument := 1632142285102651208903505739776, coefficient := (-1632142285102651208903505739776) }, { argument := 10518287442147429120048390733824, coefficient := (-10518287442147429120048390733824) }, { argument := 403819002683149101513572352, coefficient := (-403819002683149101513572352) }, { argument := 10518238933550214444978578391040, coefficient := (-10518238933550214444978578391040) }, { argument := 407785790528759603493076992, coefficient := (-407785790528759603493076992) }, { argument := 51925420936197845855055642624, coefficient := (-51925420936197845855055642624) }, { argument := 188863948979255241103145697280, coefficient := (-188863948979255241103145697280) }, { argument := 51925420936197845855055642624, coefficient := (-51925420936197845855055642624) }, { argument := 1394782431221533233717088092160, coefficient := (-1394782431221533233717088092160) }, { argument := 874941172480156386612740096, coefficient := (-874941172480156386612740096) }, { argument := 1394781766557674141851379040256, coefficient := (-1394781766557674141851379040256) }, { argument := 883535879478979140901666816, coefficient := (-883535879478979140901666816) }, { argument := 70787499110112791131487993856, coefficient := (-70787499110112791131487993856) }, { argument := 3341939230867816232682149380096, coefficient := (-3341939230867816232682149380096) }, { argument := 67410746032679764730616741888, coefficient := (-67410746032679764730616741888) }, { argument := 117242562956219773192066148859904, coefficient := (-117242562956219773192066148859904) }, { argument := 1668057396510778008121431293952, coefficient := (-1668057396510778008121431293952) }, { argument := 53068034110833006277294030848, coefficient := (-53068034110833006277294030848) }, { argument := 117242067974297153486231546363904, coefficient := (-117242067974297153486231546363904) }, { argument := 54502305303017682122626301952, coefficient := (-54502305303017682122626301952) }, { argument := 54502305303017682122626301952, coefficient := (-54502305303017682122626301952) }, { argument := 922236376574746568548650319872, coefficient := (-922236376574746568548650319872) }, { argument := 50199491726463654586629488640, coefficient := (-50199491726463654586629488640) }, { argument := 1668057396510778008121431293952, coefficient := (-1668057396510778008121431293952) }, { argument := 922236376574746568548650319872, coefficient := (-922236376574746568548650319872) }, { argument := 3342445830898634833934067695616, coefficient := (-3342445830898634833934067695616) }, { argument := 53068034110833006277294030848, coefficient := (-53068034110833006277294030848) }, { argument := 50199491726463654586629488640, coefficient := (-50199491726463654586629488640) }, { argument := 67410746032679764730616741888, coefficient := (-67410746032679764730616741888) }, { argument := 117183351362157634119815072317440, coefficient := (-117183351362157634119815072317440) }, { argument := 193224833906889172306372853760, coefficient := (-193224833906889172306372853760) }, { argument := 7881539277781005712496787456, coefficient := (-7881539277781005712496787456) }, { argument := 399621805640141746653385967271936, coefficient := (-399621805640141746653385967271936) }, { argument := 159156244770674502452354482176, coefficient := (-159156244770674502452354482176) }, { argument := 117183349030165262925629031972864, coefficient := (-117183349030165262925629031972864) }, { argument := 159410487973183567152757604352, coefficient := (-159410487973183567152757604352) }, { argument := 142884679810094361626554662912, coefficient := (-142884679810094361626554662912) }, { argument := 193224833906889172306372853760, coefficient := (-193224833906889172306372853760) }, { argument := 7881539277781005712496787456, coefficient := (-7881539277781005712496787456) }, { argument := 97000321829552567795655838269440, coefficient := (-97000321829552567795655838269440) }, { argument := 28844214477367792965255168, coefficient := (-28844214477367792965255168) }, { argument := 96999844700765044362149873319936, coefficient := (-96999844700765044362149873319936) }, { argument := 29127556466339971678076928, coefficient := (-29127556466339971678076928) }, { argument := 53328810691230220067354443776, coefficient := (-53328810691230220067354443776) }, { argument := 193968380032748625997825310720, coefficient := (-193968380032748625997825310720) }, { argument := 53328810691230220067354443776, coefficient := (-53328810691230220067354443776) }] }

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
def constantNumerator : ℤ := (-1679051362258113626705990353158144)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    310257033435, 1527, 310256885541, 771, 114379133, 9884935475,
    3563, 9884930765, 1799, 1175, 1285, 5397,
    23387, 771, 771, 1799, 23387, 23387,
    771, 288611, 11565, 5397, 23387, 1799,
    11565, 1799, 23387, 23387, 771, 234009567,
    8641661985, 69133278951, 1872093465, 23127684963, 42060187805, 23127684963,
    104875101, 3872897955, 30983176053, 839008395, 782689549011, 1423405303085,
    782689549011, 302445228415, 46319, 302445084289, 23387, 42603630195,
    77479293325, 42603630195, 172061063185, 46319, 172060981231, 23387,
    2093, 35455995, 1309342725, 10474739235, 283650525, 1415657769051,
    2574526232485, 1415657769051, 310257033435, 1527
  ]
def negativeCoefficients : Array ℕ := #[
    1430808023210948115051042570240, 461507431637884687444082688, 1430807341170256105750935896064, 466040903461439546849230848, 2160560736075557486240592822272, 45586218723114390403835494400,
    33651583556929091792797696, 45586197002073243610838466560, 33982149210729966957756416, 45455610817510056968952217600, 24272963721949976398397440, 407785790528759603493076992,
    883535879478979140901666816, 29127556466339971678076928, 466040903461439546849230848, 33982149210729966957756416, 883535879478979140901666816, 883535879478979140901666816,
    466040903461439546849230848, 10903415303899929398160130048, 873826693990199150342307840, 407785790528759603493076992, 883535879478979140901666816, 33982149210729966957756416,
    873826693990199150342307840, 33982149210729966957756416, 883535879478979140901666816, 883535879478979140901666816, 29127556466339971678076928, 4316714593248588257424310272,
    159410527008799870131382517760, 159410487973183567152757604352, 4316753628864891236049223680, 53328810691230220067354443776, 193968380032748625997825310720, 53328810691230220067354443776,
    3869208295702881340785426432, 142884714798956183435146690560, 142884679810094361626554662912, 3869243284564703149377454080, 902379612485816618508129140736, 3282149167396246487278991441920,
    902379612485816618508129140736, 1394782431221533233717088092160, 874941172480156386612740096, 1394781766557674141851379040256, 883535879478979140901666816, 49118641426133097430458040320,
    178655086872268471313786470400, 49118641426133097430458040320, 793491599406015864484648714240, 874941172480156386612740096, 793491221459899910286500429824, 883535879478979140901666816,
    40484507847254701802560421888, 5232381325149803948393103360, 193224881222787721371372748800, 193224833906889172306372853760, 5232428641048353013392998400, 1632142285102651208903505739776,
    5936453315212806632512390430720, 1632142285102651208903505739776, 1430808023210948115051042570240, 461507431637884687444082688
  ]
def negativeScales : Array ℕ := #[
    38, 10, 38, 9, 26, 33,
    11, 33, 10, 10, 10, 12,
    14, 9, 9, 10, 14, 14,
    9, 18, 13, 12, 14, 10,
    13, 10, 14, 14, 9, 27,
    33, 36, 30, 34, 35, 34,
    26, 31, 34, 29, 39, 40,
    39, 38, 15, 38, 14, 35,
    36, 35, 37, 15, 37, 14,
    11, 25, 30, 33, 28, 40,
    41, 40, 38, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    38174672959956355, 10576484346799762, 38174672272249169, 9590587049919383, 26769248634428470, 33202584402621439,
    11798876768764696, 33202583715202155, 10812979472091290, 10198445041452363, 10327552644081241, 12397941971972645,
    14513419189392997, 9590587049919383, 9590587049919383, 10812979472091290, 14513419189392997, 14513419189392997,
    9590587049919383, 18138766761594480, 13497477645523802, 12397941971972645, 14513419189392997, 10812979472091290,
    13497477645523802, 10812979472091290, 14513419189392997, 14513419189392997, 9590587049919383, 27801992272406483,
    33008661655603415, 36008661302323754, 30802005318493961, 34428901811062525, 35291736240805828, 34428901811062525,
    26644096959170915, 31850766344779936, 34850765991500263, 29644110005258220, 39509649224947239, 40372483654690192,
    39509649224947239, 38137882943673477, 15499316486274657, 38137882256177377, 14513419189392997, 35310257314563885,
    36173091744307209, 35310257314563885, 37324129701247104, 15499316486274657, 37324129014080261, 14513419189392997,
    11031356596255710, 25079526247262615, 30286195631132324, 33286195277852663, 28079539293349914, 40364609679092138,
    41227444108835461, 40364609679092138, 38174672959956355, 10576484346799762
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
noncomputable def negativeCeiling : ℝ := 12349763337 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1430808023210948115051042570240, coefficient := (-1430808023210948115051042570240) }, { argument := 461507431637884687444082688, coefficient := (-461507431637884687444082688) }, { argument := 1430807341170256105750935896064, coefficient := (-1430807341170256105750935896064) }, { argument := 466040903461439546849230848, coefficient := (-466040903461439546849230848) }, { argument := 2160560736075557486240592822272, coefficient := (-2160560736075557486240592822272) }, { argument := 45586218723114390403835494400, coefficient := (-45586218723114390403835494400) }, { argument := 33651583556929091792797696, coefficient := (-33651583556929091792797696) }, { argument := 45586197002073243610838466560, coefficient := (-45586197002073243610838466560) }, { argument := 33982149210729966957756416, coefficient := (-33982149210729966957756416) }, { argument := 45455610817510056968952217600, coefficient := (-45455610817510056968952217600) }, { argument := 24272963721949976398397440, coefficient := (-24272963721949976398397440) }, { argument := 407785790528759603493076992, coefficient := (-407785790528759603493076992) }, { argument := 883535879478979140901666816, coefficient := (-883535879478979140901666816) }, { argument := 29127556466339971678076928, coefficient := (-29127556466339971678076928) }, { argument := 466040903461439546849230848, coefficient := (-466040903461439546849230848) }, { argument := 33982149210729966957756416, coefficient := (-33982149210729966957756416) }, { argument := 883535879478979140901666816, coefficient := (-883535879478979140901666816) }, { argument := 883535879478979140901666816, coefficient := (-883535879478979140901666816) }, { argument := 466040903461439546849230848, coefficient := (-466040903461439546849230848) }, { argument := 10903415303899929398160130048, coefficient := (-10903415303899929398160130048) }, { argument := 873826693990199150342307840, coefficient := (-873826693990199150342307840) }, { argument := 407785790528759603493076992, coefficient := (-407785790528759603493076992) }, { argument := 883535879478979140901666816, coefficient := (-883535879478979140901666816) }, { argument := 33982149210729966957756416, coefficient := (-33982149210729966957756416) }, { argument := 873826693990199150342307840, coefficient := (-873826693990199150342307840) }, { argument := 33982149210729966957756416, coefficient := (-33982149210729966957756416) }, { argument := 883535879478979140901666816, coefficient := (-883535879478979140901666816) }, { argument := 883535879478979140901666816, coefficient := (-883535879478979140901666816) }, { argument := 29127556466339971678076928, coefficient := (-29127556466339971678076928) }, { argument := 4316714593248588257424310272, coefficient := (-4316714593248588257424310272) }, { argument := 159410527008799870131382517760, coefficient := (-159410527008799870131382517760) }, { argument := 159410487973183567152757604352, coefficient := (-159410487973183567152757604352) }, { argument := 4316753628864891236049223680, coefficient := (-4316753628864891236049223680) }, { argument := 53328810691230220067354443776, coefficient := (-53328810691230220067354443776) }, { argument := 193968380032748625997825310720, coefficient := (-193968380032748625997825310720) }, { argument := 53328810691230220067354443776, coefficient := (-53328810691230220067354443776) }, { argument := 3869208295702881340785426432, coefficient := (-3869208295702881340785426432) }, { argument := 142884714798956183435146690560, coefficient := (-142884714798956183435146690560) }, { argument := 142884679810094361626554662912, coefficient := (-142884679810094361626554662912) }, { argument := 3869243284564703149377454080, coefficient := (-3869243284564703149377454080) }, { argument := 902379612485816618508129140736, coefficient := (-902379612485816618508129140736) }, { argument := 3282149167396246487278991441920, coefficient := (-3282149167396246487278991441920) }, { argument := 902379612485816618508129140736, coefficient := (-902379612485816618508129140736) }, { argument := 1394782431221533233717088092160, coefficient := (-1394782431221533233717088092160) }, { argument := 874941172480156386612740096, coefficient := (-874941172480156386612740096) }, { argument := 1394781766557674141851379040256, coefficient := (-1394781766557674141851379040256) }, { argument := 883535879478979140901666816, coefficient := (-883535879478979140901666816) }, { argument := 49118641426133097430458040320, coefficient := (-49118641426133097430458040320) }, { argument := 178655086872268471313786470400, coefficient := (-178655086872268471313786470400) }, { argument := 49118641426133097430458040320, coefficient := (-49118641426133097430458040320) }, { argument := 793491599406015864484648714240, coefficient := (-793491599406015864484648714240) }, { argument := 874941172480156386612740096, coefficient := (-874941172480156386612740096) }, { argument := 793491221459899910286500429824, coefficient := (-793491221459899910286500429824) }, { argument := 883535879478979140901666816, coefficient := (-883535879478979140901666816) }, { argument := 40484507847254701802560421888, coefficient := (-40484507847254701802560421888) }, { argument := 5232381325149803948393103360, coefficient := (-5232381325149803948393103360) }, { argument := 193224881222787721371372748800, coefficient := (-193224881222787721371372748800) }, { argument := 193224833906889172306372853760, coefficient := (-193224833906889172306372853760) }, { argument := 5232428641048353013392998400, coefficient := (-5232428641048353013392998400) }, { argument := 1632142285102651208903505739776, coefficient := (-1632142285102651208903505739776) }, { argument := 5936453315212806632512390430720, coefficient := (-5936453315212806632512390430720) }, { argument := 1632142285102651208903505739776, coefficient := (-1632142285102651208903505739776) }, { argument := 1430808023210948115051042570240, coefficient := (-1430808023210948115051042570240) }, { argument := 461507431637884687444082688, coefficient := (-461507431637884687444082688) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
