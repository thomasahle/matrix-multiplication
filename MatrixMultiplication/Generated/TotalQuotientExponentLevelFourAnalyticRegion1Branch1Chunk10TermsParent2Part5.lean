import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 1,
parent chunk 10, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-173282409392916122938964684929236992)
def positiveArguments : Array ℕ := #[
    705, 93, 285, 843, 1881, 93,
    939, 1911, 93, 285, 93, 9,
    27, 57, 147, 123, 3441, 105,
    123, 111, 57, 57, 111, 3441,
    111, 9, 147, 21, 315, 553,
    21, 175, 21, 553, 1099, 175,
    16961, 1085, 315, 553, 21, 1085,
    21, 553, 553, 21, 9, 5989465679,
    5989466545, 68772251921, 251183773943, 8596508607, 12794765091, 251552271255,
    251552305743, 12794864913
  ]
def positiveCoefficients : Array ℕ := #[
    436373863848096546901941288960, 7195526478346272847851159552, 176406455598166689173125201920, 130447931639696946467495215104, 145535325868487518567828291584, 7195526478346272847851159552,
    145303212111121509766284705792, 147856463442147606583264149504, 7195526478346272847851159552, 176406455598166689173125201920, 7195526478346272847851159552, 5570730176784211237046059008,
    4178047632588158427784544256, 4410161389954167229328130048, 5686787055467215637817851904, 76133312416050886906296139776, 133117239849406047685246451712, 4061990753905154027012751360,
    76133312416050886906296139776, 4294104511271162828556337152, 4410161389954167229328130048, 4410161389954167229328130048, 4294104511271162828556337152, 133117239849406047685246451712,
    4294104511271162828556337152, 5570730176784211237046059008, 5686787055467215637817851904, 1624796301562061610805100544, 24371944523430924162076508160, 42786302607800955751200980992,
    1624796301562061610805100544, 27079938359367693513418342400, 1624796301562061610805100544, 42786302607800955751200980992, 42515503224207278816066797568, 27079938359367693513418342400,
    656146906447479213830126436352, 41973904457019924945798430720, 24371944523430924162076508160, 42786302607800955751200980992, 1624796301562061610805100544, 41973904457019924945798430720,
    1624796301562061610805100544, 42786302607800955751200980992, 42786302607800955751200980992, 1624796301562061610805100544, 1426106925256758076683791106048, 56568903945615362876677625479168,
    56568912124754111206903135600640, 324767777423197971640193191510016, 1186181835109128945293627991523328, 324766912923177785108592146251776, 60421569821928986083752815886336, 2375844028928690607202537266216960,
    2375844354658641129619185526112256, 60422041217996039097477337448448
  ]
def positiveScales : Array ℕ := #[
    9, 6, 8, 9, 10, 6,
    9, 10, 6, 8, 6, 3,
    4, 5, 7, 6, 11, 6,
    6, 6, 5, 5, 6, 11,
    6, 3, 7, 4, 8, 9,
    4, 7, 4, 9, 10, 7,
    14, 10, 8, 9, 4, 10,
    4, 9, 9, 4, 3, 32,
    32, 36, 37, 33, 33, 37,
    37, 33
  ]
def negativeArguments : Array ℕ := #[
    235, 3, 3, 7, 9, 357,
    11585, 15375
  ]
def negativeCoefficients : Array ℕ := #[
    37237236381704238668965656657920, 950737950171172051122527404032, 475368975085586025561263702016, 1109194275199700726309615304704, 1426106925256758076683791106048, 113137816070369474083580761079808,
    1835716525455504702042413329285120, 4872531994627256762002952945664000
  ]
def negativeScales : Array ℕ := #[
    7, 1, 1, 2, 3, 8,
    13, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9461479447286151, 6539158811107971, 8154818109052103, 9719388820935039, 10877284133344468, 6539158811107971,
    9874981347482478, 10900112062706946, 6539158811107971, 8154818109052103, 6539158811107971, 3169925001442312,
    4754887502147955, 5832890014087662, 7199672344836364, 6942514504772358, 11748612176723449, 6714245517659862,
    6942514504772358, 6794415866314396, 5832890014087662, 5832890014087662, 6794415866314396, 11748612176723449,
    6794415866314396, 3169925001442312, 7199672344836364, 4392317422778759, 8299208018387278, 9111135670234706,
    4392317422778759, 7451211111832325, 4392317422778759, 9111135670234706, 10101975670949231, 7451211111832325,
    14049933611508950, 10083479327331841, 8299208018387278, 9111135670234706, 4392317422778759, 10083479327331841,
    4392317422778759, 9111135670234706, 9111135670234706, 4392317422778759, 3169925001442312, 32479780159731485,
    32479780368326688, 36001107535735632, 37869952315127262, 33001103695417600, 33574834608938545, 37872067259314453,
    37872067457108982, 33574845864490450
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    7876516949414244, 1584962500724866, 1584962500724866, 2807354922807594, 3169925001442313, 8479780264029236,
    13499970423752455, 13908298795065783
  ]

abbrev PositiveTerm := Fin 56
abbrev NegativeTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 3070100798609 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1129236860983 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 436373863848096546901941288960, coefficient := 436373863848096546901941288960 }, { argument := 37237236381704238668965656657920, coefficient := (-37237236381704238668965656657920) }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 130447931639696946467495215104, coefficient := 130447931639696946467495215104 }, { argument := 145535325868487518567828291584, coefficient := 145535325868487518567828291584 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 145303212111121509766284705792, coefficient := 145303212111121509766284705792 }, { argument := 147856463442147606583264149504, coefficient := 147856463442147606583264149504 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 5686787055467215637817851904, coefficient := 5686787055467215637817851904 }, { argument := 76133312416050886906296139776, coefficient := 76133312416050886906296139776 }, { argument := 133117239849406047685246451712, coefficient := 133117239849406047685246451712 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 76133312416050886906296139776, coefficient := 76133312416050886906296139776 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 133117239849406047685246451712, coefficient := 133117239849406047685246451712 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 5686787055467215637817851904, coefficient := 5686787055467215637817851904 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 42786302607800955751200980992, coefficient := 42786302607800955751200980992 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 27079938359367693513418342400, coefficient := 27079938359367693513418342400 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 42786302607800955751200980992, coefficient := 42786302607800955751200980992 }, { argument := 42515503224207278816066797568, coefficient := 42515503224207278816066797568 }, { argument := 27079938359367693513418342400, coefficient := 27079938359367693513418342400 }, { argument := 656146906447479213830126436352, coefficient := 656146906447479213830126436352 }, { argument := 41973904457019924945798430720, coefficient := 41973904457019924945798430720 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 42786302607800955751200980992, coefficient := 42786302607800955751200980992 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 41973904457019924945798430720, coefficient := 41973904457019924945798430720 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 42786302607800955751200980992, coefficient := 42786302607800955751200980992 }, { argument := 42786302607800955751200980992, coefficient := 42786302607800955751200980992 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 1426106925256758076683791106048, coefficient := 1426106925256758076683791106048 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 56568903945615362876677625479168, coefficient := 56568903945615362876677625479168 }, { argument := 56568912124754111206903135600640, coefficient := 56568912124754111206903135600640 }, { argument := 113137816070369474083580761079808, coefficient := (-113137816070369474083580761079808) }, { argument := 324767777423197971640193191510016, coefficient := 324767777423197971640193191510016 }, { argument := 1186181835109128945293627991523328, coefficient := 1186181835109128945293627991523328 }, { argument := 324766912923177785108592146251776, coefficient := 324766912923177785108592146251776 }, { argument := 1835716525455504702042413329285120, coefficient := (-1835716525455504702042413329285120) }, { argument := 60421569821928986083752815886336, coefficient := 60421569821928986083752815886336 }, { argument := 2375844028928690607202537266216960, coefficient := 2375844028928690607202537266216960 }, { argument := 2375844354658641129619185526112256, coefficient := 2375844354658641129619185526112256 }, { argument := 60422041217996039097477337448448, coefficient := 60422041217996039097477337448448 }, { argument := 4872531994627256762002952945664000, coefficient := (-4872531994627256762002952945664000) }] }

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


end Parent2

namespace Parent2

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-40338850401404535525459896196661248)
def positiveArguments : Array ℕ := #[
    34982977, 6900430309, 286687981321, 27601753947, 34982977, 5139253,
    993105099, 993105123, 5139229, 1066269, 48193419, 133995
  ]
def positiveCoefficients : Array ℕ := #[
    660809752223198770035549011968, 130345443234397716514658641248256, 1353845714031849313501975901372416, 130345597707727737663623226458112, 660809752223198770035549011968, 194155488913498182187382472704,
    37518449867876326512339537887232, 37518450774570691223311418916864, 194154582219133471215501443072, 10070625974645867464724840448, 455173973160986268329991733248, 10124375949953889766547128320
  ]
def positiveScales : Array ℕ := #[
    25, 32, 38, 34, 25, 22,
    29, 29, 22, 20, 25, 17
  ]
def negativeArguments : Array ℕ := #[
    20395, 119, 3
  ]
def negativeCoefficients : Array ℕ := #[
    1615858374478421165220328867102720, 75425210713579649389053840719872, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    14, 6, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    25060149729925835, 32684039184758535, 38060690468213717, 34684040894505877, 25060149729925835, 22293127245569376,
    29887371163226351, 29887371198091423, 22293120508255251, 20024140018686312, 25522332818461723, 17031819642210997
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    14315927886679886, 6894817767286876, 1584962500724866
  ]

abbrev PositiveTerm := Fin 12
abbrev NegativeTerm := Fin 3
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
noncomputable def positiveFloor : ℝ := 753590553317 / 1000000000000
noncomputable def negativeCeiling : ℝ := 142358172197 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 660809752223198770035549011968, coefficient := 660809752223198770035549011968 }, { argument := 130345443234397716514658641248256, coefficient := 130345443234397716514658641248256 }, { argument := 1353845714031849313501975901372416, coefficient := 1353845714031849313501975901372416 }, { argument := 130345597707727737663623226458112, coefficient := 130345597707727737663623226458112 }, { argument := 660809752223198770035549011968, coefficient := 660809752223198770035549011968 }, { argument := 1615858374478421165220328867102720, coefficient := (-1615858374478421165220328867102720) }, { argument := 194155488913498182187382472704, coefficient := 194155488913498182187382472704 }, { argument := 37518449867876326512339537887232, coefficient := 37518449867876326512339537887232 }, { argument := 37518450774570691223311418916864, coefficient := 37518450774570691223311418916864 }, { argument := 194154582219133471215501443072, coefficient := 194154582219133471215501443072 }, { argument := 75425210713579649389053840719872, coefficient := (-75425210713579649389053840719872) }, { argument := 10070625974645867464724840448, coefficient := 10070625974645867464724840448 }, { argument := 455173973160986268329991733248, coefficient := 455173973160986268329991733248 }, { argument := 10124375949953889766547128320, coefficient := 10124375949953889766547128320 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
