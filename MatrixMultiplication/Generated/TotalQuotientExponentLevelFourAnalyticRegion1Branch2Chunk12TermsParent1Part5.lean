import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 2,
parent chunk 12, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 485774997430492220797300741505024
def positiveArguments : Array ℕ := #[
    6405, 915, 8601, 101565, 7137, 6405,
    101565, 915, 7137, 7137, 7137, 7137,
    7137, 8235, 8601, 1405, 5901, 25571,
    843, 843, 1967, 25571, 25571, 843,
    315563, 12645, 5901, 25571, 1967, 12645,
    1967, 25571, 25571, 843, 3, 57,
    87, 897, 27, 87, 27, 27,
    2313, 27, 897, 2313, 3, 27,
    27, 57, 1, 1, 26817277, 97360391,
    6704319, 12524341, 467723467, 935400813, 25094803
  ]
def positiveCoefficients : Array ℕ := #[
    495562871976428791295555665920, 566357567973061475766349332480, 665470142368347234025460465664, 7858211255626227976258096988160, 17670356120759518043910099173376, 495562871976428791295555665920,
    7858211255626227976258096988160, 566357567973061475766349332480, 552198628773734938872190599168, 552198628773734938872190599168, 552198628773734938872190599168, 17670356120759518043910099173376,
    552198628773734938872190599168, 637152263969694160237142999040, 665470142368347234025460465664, 27176652424936863847394836480, 456567760738939312636233252864, 989230148267701844045172047872,
    32611982909924236616873803776, 521791726558787785869980860416, 38047313394911609386352771072, 989230148267701844045172047872, 989230148267701844045172047872, 521791726558787785869980860416,
    12207752269281639240249760546816, 978359487297727098506214113280, 456567760738939312636233252864, 989230148267701844045172047872, 38047313394911609386352771072, 978359487297727098506214113280,
    38047313394911609386352771072, 989230148267701844045172047872, 989230148267701844045172047872, 32611982909924236616873803776, 3713820117856140824697372672, 4410161389954167229328130048,
    3365649481807127622381993984, 34701006726218315830766075904, 4178047632588158427784544256, 3365649481807127622381993984, 4178047632588158427784544256, 4178047632588158427784544256,
    178959706929192785990104645632, 4178047632588158427784544256, 34701006726218315830766075904, 178959706929192785990104645632, 3713820117856140824697372672, 4178047632588158427784544256,
    4178047632588158427784544256, 4410161389954167229328130048, 79228162514264337593543950336, 79228162514264337593543950336, 253282020133262061174819651584, 919542894434966920073442230272,
    253282010688529095435529224192, 236578112633720380821386297344, 8835046495249546273639396016128, 8834610894720433411825594269696, 237013713162833242635188043776
  ]
def positiveScales : Array ℕ := #[
    12, 9, 13, 16, 12, 12,
    16, 9, 12, 12, 12, 12,
    12, 13, 13, 10, 12, 14,
    9, 9, 10, 14, 14, 9,
    18, 13, 12, 14, 10, 13,
    10, 14, 14, 9, 1, 5,
    6, 9, 4, 6, 4, 4,
    11, 4, 9, 11, 1, 4,
    4, 5, 0, 0, 24, 26,
    22, 23, 28, 29, 24
  ]
def negativeArguments : Array ℕ := #[
    183, 281, 3, 1, 9
  ]
def negativeCoefficients : Array ℕ := #[
    57995014960441495118474171645952, 22263113666508278863785850044416, 475368975085586025561263702016, 158456325028528675187087900672, 1426106925256758076683791106048
  ]
def negativeScales : Array ℕ := #[
    7, 8, 1, 0, 3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12644982855227843, 9837627933086892, 13070288689961679, 16632043799520677, 12801102057105355, 12644982855227843,
    16632043799520677, 9837627933086892, 12801102057105355, 12801102057105355, 12801102057105355, 12801102057105355,
    12801102057105355, 13007552934613717, 13070288689961679, 10456354415108284, 12526743742999645, 14642220960418536,
    9719388820935039, 9719388820935039, 10941781241718677, 14642220960418536, 14642220960418536, 9719388820935039,
    18267568532621526, 13626279416549884, 12526743742999645, 14642220960418536, 10941781241718677, 13626279416549884,
    10941781241718677, 14642220960418536, 14642220960418536, 9719388820935039, 1584962500720924, 5832890014087662,
    6442943495848725, 9808964174871270, 4754887502147955, 6442943495848725, 4754887502147955, 4754887502147955,
    11175549550636190, 4754887502147955, 9808964174871270, 11175549550636190, 1584962500720924, 4754887502147955,
    4754887502147955, 5832890014087662, 0, 0, 24676659419048834, 26536831626147964,
    22676659365251610, 23578231358566423, 28801080573692945, 29801009441728256, 24580885284863898
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    7515699838284497, 8134426320220927, 1584962500724866, 0, 3169925001442313
  ]

abbrev PositiveTerm := Fin 59
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 20730236881 / 1000000000000
noncomputable def negativeCeiling : ℝ := 7490000251 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 495562871976428791295555665920, coefficient := 495562871976428791295555665920 }, { argument := 566357567973061475766349332480, coefficient := 566357567973061475766349332480 }, { argument := 665470142368347234025460465664, coefficient := 665470142368347234025460465664 }, { argument := 7858211255626227976258096988160, coefficient := 7858211255626227976258096988160 }, { argument := 17670356120759518043910099173376, coefficient := 17670356120759518043910099173376 }, { argument := 495562871976428791295555665920, coefficient := 495562871976428791295555665920 }, { argument := 7858211255626227976258096988160, coefficient := 7858211255626227976258096988160 }, { argument := 566357567973061475766349332480, coefficient := 566357567973061475766349332480 }, { argument := 552198628773734938872190599168, coefficient := 552198628773734938872190599168 }, { argument := 552198628773734938872190599168, coefficient := 552198628773734938872190599168 }, { argument := 552198628773734938872190599168, coefficient := 552198628773734938872190599168 }, { argument := 17670356120759518043910099173376, coefficient := 17670356120759518043910099173376 }, { argument := 552198628773734938872190599168, coefficient := 552198628773734938872190599168 }, { argument := 637152263969694160237142999040, coefficient := 637152263969694160237142999040 }, { argument := 665470142368347234025460465664, coefficient := 665470142368347234025460465664 }, { argument := 57995014960441495118474171645952, coefficient := (-57995014960441495118474171645952) }, { argument := 27176652424936863847394836480, coefficient := 27176652424936863847394836480 }, { argument := 456567760738939312636233252864, coefficient := 456567760738939312636233252864 }, { argument := 989230148267701844045172047872, coefficient := 989230148267701844045172047872 }, { argument := 32611982909924236616873803776, coefficient := 32611982909924236616873803776 }, { argument := 521791726558787785869980860416, coefficient := 521791726558787785869980860416 }, { argument := 38047313394911609386352771072, coefficient := 38047313394911609386352771072 }, { argument := 989230148267701844045172047872, coefficient := 989230148267701844045172047872 }, { argument := 989230148267701844045172047872, coefficient := 989230148267701844045172047872 }, { argument := 521791726558787785869980860416, coefficient := 521791726558787785869980860416 }, { argument := 12207752269281639240249760546816, coefficient := 12207752269281639240249760546816 }, { argument := 978359487297727098506214113280, coefficient := 978359487297727098506214113280 }, { argument := 456567760738939312636233252864, coefficient := 456567760738939312636233252864 }, { argument := 989230148267701844045172047872, coefficient := 989230148267701844045172047872 }, { argument := 38047313394911609386352771072, coefficient := 38047313394911609386352771072 }, { argument := 978359487297727098506214113280, coefficient := 978359487297727098506214113280 }, { argument := 38047313394911609386352771072, coefficient := 38047313394911609386352771072 }, { argument := 989230148267701844045172047872, coefficient := 989230148267701844045172047872 }, { argument := 989230148267701844045172047872, coefficient := 989230148267701844045172047872 }, { argument := 32611982909924236616873803776, coefficient := 32611982909924236616873803776 }, { argument := 22263113666508278863785850044416, coefficient := (-22263113666508278863785850044416) }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 34701006726218315830766075904, coefficient := 34701006726218315830766075904 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 178959706929192785990104645632, coefficient := 178959706929192785990104645632 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 34701006726218315830766075904, coefficient := 34701006726218315830766075904 }, { argument := 178959706929192785990104645632, coefficient := 178959706929192785990104645632 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 253282020133262061174819651584, coefficient := 253282020133262061174819651584 }, { argument := 919542894434966920073442230272, coefficient := 919542894434966920073442230272 }, { argument := 253282010688529095435529224192, coefficient := 253282010688529095435529224192 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 236578112633720380821386297344, coefficient := 236578112633720380821386297344 }, { argument := 8835046495249546273639396016128, coefficient := 8835046495249546273639396016128 }, { argument := 8834610894720433411825594269696, coefficient := 8834610894720433411825594269696 }, { argument := 237013713162833242635188043776, coefficient := 237013713162833242635188043776 }] }

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


end Parent1

namespace Parent1

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-7817314752810972071616914456051712)
def positiveArguments : Array ℕ := #[
    505273, 312672293, 12699388373, 312672293, 8083827, 134490457,
    11299182247, 5649590463, 67245889, 7216695, 1503, 35410633,
    2421, 75, 2421, 1617, 7218231, 1503,
    9, 535, 489, 535, 489
  ]
def positiveCoefficients : Array ℕ := #[
    76354696956767815873914208256, 11812425252681577512502426599424, 119942332011199352202892165513216, 11812425252681577512502426599424, 76349587356233350917792989184, 635113226402621256217837699072,
    53358879527068524813782364454912, 53358873288822400942981037162496, 635119464648745127019164991488, 545278057361487268247261675520, 58144496220185204786668240896, 5351103565324729392076660146176,
    93657901097184551422836867072, 2901421967075110019294822400, 93657901097184551422836867072, 62554657610139372015996370944, 545394114240170272648033468416, 58144496220185204786668240896,
    2785365088392105618523029504, 41393620063604902941939466240, 37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096
  ]
def positiveScales : Array ℕ := #[
    18, 28, 33, 28, 22, 27,
    33, 32, 26, 22, 10, 25,
    11, 6, 11, 10, 22, 10,
    3, 9, 8, 9, 8
  ]
def negativeArguments : Array ℕ := #[
    229, 907, 1363, 43, 1
  ]
def negativeCoefficients : Array ℕ := #[
    18143249215766533308921564626944, 143719886800875508394688725909504, 107987985506942292140000404307968, 6813621976226733033044779728896, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    7, 9, 10, 5, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    18946703563329190, 28220076141705282, 33564039964572649, 28220076141705282, 22946607016001628, 27002928566622680,
    33395499313470874, 32395499144803778, 26002942737076346, 22782906852563785, 10553629293916271, 25077679297768053,
    11241387363998936, 6228818690495880, 11241387363998936, 10659103963471994, 22783213882830495, 10553629293916271,
    3169925001442312, 9063395081288509, 8933690654464738, 9063395081288509, 8933690654464738
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    7839203789504465, 9824958741594111, 10412569846805221, 5426264754702117, 0
  ]

abbrev PositiveTerm := Fin 23
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 101163522909 / 1000000000000
noncomputable def negativeCeiling : ℝ := 32688755317 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 18143249215766533308921564626944, coefficient := (-18143249215766533308921564626944) }, { argument := 76354696956767815873914208256, coefficient := 76354696956767815873914208256 }, { argument := 11812425252681577512502426599424, coefficient := 11812425252681577512502426599424 }, { argument := 119942332011199352202892165513216, coefficient := 119942332011199352202892165513216 }, { argument := 11812425252681577512502426599424, coefficient := 11812425252681577512502426599424 }, { argument := 76349587356233350917792989184, coefficient := 76349587356233350917792989184 }, { argument := 143719886800875508394688725909504, coefficient := (-143719886800875508394688725909504) }, { argument := 635113226402621256217837699072, coefficient := 635113226402621256217837699072 }, { argument := 53358879527068524813782364454912, coefficient := 53358879527068524813782364454912 }, { argument := 53358873288822400942981037162496, coefficient := 53358873288822400942981037162496 }, { argument := 635119464648745127019164991488, coefficient := 635119464648745127019164991488 }, { argument := 107987985506942292140000404307968, coefficient := (-107987985506942292140000404307968) }, { argument := 545278057361487268247261675520, coefficient := 545278057361487268247261675520 }, { argument := 58144496220185204786668240896, coefficient := 58144496220185204786668240896 }, { argument := 5351103565324729392076660146176, coefficient := 5351103565324729392076660146176 }, { argument := 93657901097184551422836867072, coefficient := 93657901097184551422836867072 }, { argument := 2901421967075110019294822400, coefficient := 2901421967075110019294822400 }, { argument := 93657901097184551422836867072, coefficient := 93657901097184551422836867072 }, { argument := 62554657610139372015996370944, coefficient := 62554657610139372015996370944 }, { argument := 545394114240170272648033468416, coefficient := 545394114240170272648033468416 }, { argument := 58144496220185204786668240896, coefficient := 58144496220185204786668240896 }, { argument := 2785365088392105618523029504, coefficient := 2785365088392105618523029504 }, { argument := 6813621976226733033044779728896, coefficient := (-6813621976226733033044779728896) }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
