import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 11, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-45643616445125348662146152529920)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3363, 6549, 6549, 205851, 6549, 8319,
    531, 16312095, 422935035, 84767, 8202812661, 26825,
    3219, 84767, 168461, 26825, 2599879, 166315,
    422935035, 84767, 3219, 166315, 3219, 84767,
    84767, 16312095, 635568169, 24849017417, 24849021137, 635575485,
    219067, 163135, 172457, 13983, 2997023, 5420743,
    163135, 2997023, 88559, 88559, 172457, 172457,
    5420743, 172457, 219067, 13983, 32112633, 824911485,
    84767, 15974071827, 26825, 3219, 84767, 168461,
    26825, 2599879, 166315, 824911485, 84767, 3219,
    166315, 3219, 84767, 84767
  ]
def negativeCoefficients : Array ℕ := #[
    63525273927562467414638592, 61853556192626613008990208, 61853556192626613008990208, 1944207725730398673769070592, 61853556192626613008990208, 78570733541985157065474048,
    80242451276921011471122432, 150452520885518604183797760, 15603548700900783585094533120, 1601203358613644863317475328, 151315185842051427232357810176, 1013419847223825862859161600,
    60805190833429551771549696, 1601203358613644863317475328, 1591069160141406604688883712, 1013419847223825862859161600, 24555162898233300657077485568, 1570800763196930087431700480,
    15603548700900783585094533120, 1601203358613644863317475328, 60805190833429551771549696, 1570800763196930087431700480, 60805190833429551771549696, 1601203358613644863317475328,
    1601203358613644863317475328, 150452520885518604183797760, 732760209683698797399506944, 28648966548409386244077780992, 28648970837277383381548531712, 732768644457426501091983360,
    2069029316605609136057483264, 1540766512365879143872593920, 1628810313072500809236742144, 2113051216958919968739557376, 28306081927178865414573654016, 51197470110900498409252192256,
    1540766512365879143872593920, 28306081927178865414573654016, 1672832213425811641918816256, 1672832213425811641918816256, 1628810313072500809236742144, 1628810313072500809236742144,
    51197470110900498409252192256, 1628810313072500809236742144, 2069029316605609136057483264, 2113051216958919968739557376, 148093380620989944909791232, 15216931047258695682238709760,
    1601203358613644863317475328, 147334807403861479924973961216, 1013419847223825862859161600, 60805190833429551771549696, 1601203358613644863317475328, 1591069160141406604688883712,
    1013419847223825862859161600, 24555162898233300657077485568, 1570800763196930087431700480, 15216931047258695682238709760, 1601203358613644863317475328, 60805190833429551771549696,
    1570800763196930087431700480, 60805190833429551771549696, 1601203358613644863317475328, 1601203358613644863317475328
  ]
def negativeScales : Array ℕ := #[
    11, 12, 12, 17, 12, 13,
    9, 23, 28, 16, 32, 14,
    11, 16, 17, 14, 21, 17,
    28, 16, 11, 17, 11, 16,
    16, 23, 29, 34, 34, 29,
    17, 17, 17, 13, 21, 22,
    17, 21, 16, 16, 17, 17,
    22, 17, 17, 13, 24, 29,
    16, 33, 14, 11, 16, 17,
    14, 21, 17, 29, 16, 11,
    17, 11, 16, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11715533063630459, 12677058915753742, 12677058915753742, 17651240931578205, 12677058915753742, 13022194401760635,
    9052568050804154, 23959438759028386, 28655860834097066, 16371215108933627, 32933471541862067, 14711290550625444,
    11652396861500322, 16371215108933627, 17362055109648151, 14711290550625444, 21310013050207869, 17343558766030761,
    28655860834097066, 16371215108933627, 11652396861500322, 17343558766030761, 11652396861500322, 16371215108933627,
    16371215108933627, 23959438759028386, 29243471631463450, 34532469754559433, 34532469970536791, 29243488238173299,
    17741012649401125, 17315706814483911, 17395877163167900, 13771386298616460, 21515098724867337, 22370059179012165,
    17315706814483911, 21515098724867337, 16434351310982556, 16434351310982556, 17395877163167900, 17395877163167900,
    22370059179012165, 17395877163167900, 17741012649401125, 13771386298616460, 24936637632823640, 29619664082100260,
    16371215108933627, 33895013058718883, 14711290550625444, 11652396861500322, 16371215108933627, 17362055109648151,
    14711290550625444, 21310013050207869, 17343558766030761, 29619664082100260, 16371215108933627, 11652396861500322,
    17343558766030761, 11652396861500322, 16371215108933627, 16371215108933627
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
noncomputable def negativeCeiling : ℝ := 115815773 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 63525273927562467414638592, coefficient := (-63525273927562467414638592) }, { argument := 61853556192626613008990208, coefficient := (-61853556192626613008990208) }, { argument := 61853556192626613008990208, coefficient := (-61853556192626613008990208) }, { argument := 1944207725730398673769070592, coefficient := (-1944207725730398673769070592) }, { argument := 61853556192626613008990208, coefficient := (-61853556192626613008990208) }, { argument := 78570733541985157065474048, coefficient := (-78570733541985157065474048) }, { argument := 80242451276921011471122432, coefficient := (-80242451276921011471122432) }, { argument := 150452520885518604183797760, coefficient := (-150452520885518604183797760) }, { argument := 15603548700900783585094533120, coefficient := (-15603548700900783585094533120) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }, { argument := 151315185842051427232357810176, coefficient := (-151315185842051427232357810176) }, { argument := 1013419847223825862859161600, coefficient := (-1013419847223825862859161600) }, { argument := 60805190833429551771549696, coefficient := (-60805190833429551771549696) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }, { argument := 1591069160141406604688883712, coefficient := (-1591069160141406604688883712) }, { argument := 1013419847223825862859161600, coefficient := (-1013419847223825862859161600) }, { argument := 24555162898233300657077485568, coefficient := (-24555162898233300657077485568) }, { argument := 1570800763196930087431700480, coefficient := (-1570800763196930087431700480) }, { argument := 15603548700900783585094533120, coefficient := (-15603548700900783585094533120) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }, { argument := 60805190833429551771549696, coefficient := (-60805190833429551771549696) }, { argument := 1570800763196930087431700480, coefficient := (-1570800763196930087431700480) }, { argument := 60805190833429551771549696, coefficient := (-60805190833429551771549696) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }, { argument := 150452520885518604183797760, coefficient := (-150452520885518604183797760) }, { argument := 732760209683698797399506944, coefficient := (-732760209683698797399506944) }, { argument := 28648966548409386244077780992, coefficient := (-28648966548409386244077780992) }, { argument := 28648970837277383381548531712, coefficient := (-28648970837277383381548531712) }, { argument := 732768644457426501091983360, coefficient := (-732768644457426501091983360) }, { argument := 2069029316605609136057483264, coefficient := (-2069029316605609136057483264) }, { argument := 1540766512365879143872593920, coefficient := (-1540766512365879143872593920) }, { argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 2113051216958919968739557376, coefficient := (-2113051216958919968739557376) }, { argument := 28306081927178865414573654016, coefficient := (-28306081927178865414573654016) }, { argument := 51197470110900498409252192256, coefficient := (-51197470110900498409252192256) }, { argument := 1540766512365879143872593920, coefficient := (-1540766512365879143872593920) }, { argument := 28306081927178865414573654016, coefficient := (-28306081927178865414573654016) }, { argument := 1672832213425811641918816256, coefficient := (-1672832213425811641918816256) }, { argument := 1672832213425811641918816256, coefficient := (-1672832213425811641918816256) }, { argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 51197470110900498409252192256, coefficient := (-51197470110900498409252192256) }, { argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 2069029316605609136057483264, coefficient := (-2069029316605609136057483264) }, { argument := 2113051216958919968739557376, coefficient := (-2113051216958919968739557376) }, { argument := 148093380620989944909791232, coefficient := (-148093380620989944909791232) }, { argument := 15216931047258695682238709760, coefficient := (-15216931047258695682238709760) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }, { argument := 147334807403861479924973961216, coefficient := (-147334807403861479924973961216) }, { argument := 1013419847223825862859161600, coefficient := (-1013419847223825862859161600) }, { argument := 60805190833429551771549696, coefficient := (-60805190833429551771549696) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }, { argument := 1591069160141406604688883712, coefficient := (-1591069160141406604688883712) }, { argument := 1013419847223825862859161600, coefficient := (-1013419847223825862859161600) }, { argument := 24555162898233300657077485568, coefficient := (-24555162898233300657077485568) }, { argument := 1570800763196930087431700480, coefficient := (-1570800763196930087431700480) }, { argument := 15216931047258695682238709760, coefficient := (-15216931047258695682238709760) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }, { argument := 60805190833429551771549696, coefficient := (-60805190833429551771549696) }, { argument := 1570800763196930087431700480, coefficient := (-1570800763196930087431700480) }, { argument := 60805190833429551771549696, coefficient := (-60805190833429551771549696) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }] }

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


end Parent1

namespace Parent1

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-617122502001374231661804534104064)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    32112633, 219067, 163135, 172457, 13983, 2997023,
    5420743, 163135, 2997023, 88559, 88559, 172457,
    172457, 5420743, 172457, 219067, 13983, 1001193255,
    25593637155, 2664433, 495199077453, 843175, 101181, 2664433,
    5295139, 843175, 81720521, 5227685, 25593637155, 2664433,
    101181, 5227685, 101181, 2664433, 2664433, 1001193255,
    6474873391, 253152487667, 253152526055, 6474948087, 32112633, 824911485,
    84767, 15974071827, 26825, 3219, 84767, 168461,
    26825, 2599879, 166315, 824911485, 84767, 3219,
    166315, 3219, 84767, 84767, 32112633, 13002215659,
    508349658983, 508349734595, 13002365163, 8333592369
  ]
def negativeCoefficients : Array ℕ := #[
    148093380620989944909791232, 2069029316605609136057483264, 1540766512365879143872593920, 1628810313072500809236742144, 2113051216958919968739557376, 28306081927178865414573654016,
    51197470110900498409252192256, 1540766512365879143872593920, 28306081927178865414573654016, 1672832213425811641918816256, 1672832213425811641918816256, 1628810313072500809236742144,
    1628810313072500809236742144, 51197470110900498409252192256, 1628810313072500809236742144, 2069029316605609136057483264, 2113051216958919968739557376, 4617188935827306476753387520,
    472119274513668838917647892480, 50329716380207269622654697472, 4567405323656282495858742657024, 31854250873548904824464998400, 1911255052412934289467899904, 50329716380207269622654697472,
    50011173871471780574410047488, 31854250873548904824464998400, 771828498666089963896786911232, 49374088854000802477920747520, 472119274513668838917647892480, 50329716380207269622654697472,
    1911255052412934289467899904, 49374088854000802477920747520, 1911255052412934289467899904, 50329716380207269622654697472, 50329716380207269622654697472, 4617188935827306476753387520,
    14930041544181114802622431232, 583729893952007825551192489984, 583729982468709263246475919360, 14930213781430531028705869824, 148093380620989944909791232, 15216931047258695682238709760,
    1601203358613644863317475328, 147334807403861479924973961216, 1013419847223825862859161600, 60805190833429551771549696, 1601203358613644863317475328, 1591069160141406604688883712,
    1013419847223825862859161600, 24555162898233300657077485568, 1570800763196930087431700480, 15216931047258695682238709760, 1601203358613644863317475328, 60805190833429551771549696,
    1570800763196930087431700480, 60805190833429551771549696, 1601203358613644863317475328, 1601203358613644863317475328, 148093380620989944909791232, 14990534040796986389963997184,
    586087253701057923736464785408, 586087340875758730069378334720, 14990706407173611132014297088, 76863822822780946434754609152
  ]
def negativeScales : Array ℕ := #[
    24, 17, 17, 17, 13, 21,
    22, 17, 21, 16, 16, 17,
    17, 22, 17, 17, 13, 29,
    34, 21, 38, 19, 16, 21,
    22, 19, 26, 22, 34, 21,
    16, 22, 16, 21, 21, 29,
    32, 37, 37, 32, 24, 29,
    16, 33, 14, 11, 16, 17,
    14, 21, 17, 29, 16, 11,
    17, 11, 16, 16, 24, 33,
    38, 38, 33, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    24936637632823640, 17741012649401125, 17315706814483911, 17395877163167900, 13771386298616460, 21515098724867337,
    22370059179012165, 17315706814483911, 21515098724867337, 16434351310982556, 16434351310982556, 17395877163167900,
    17395877163167900, 22370059179012165, 17395877163167900, 17741012649401125, 13771386298616460, 29899073335073144,
    34575066134652059, 21345397124777895, 38849217672307118, 19685472566426753, 16626578877333553, 21345397124777895,
    22336237125492418, 19685472566426753, 26284195066052138, 22317740781875029, 34575066134652059, 21345397124777895,
    16626578877333553, 22317740781875029, 16626578877333553, 21345397124777895, 21345397124777895, 29899073335073144,
    32592204836757222, 37881215708192959, 37881215926962985, 32592221480005776, 24936637632823640, 29619664082100260,
    16371215108933627, 33895013058718883, 14711290550625444, 11652396861500322, 16371215108933627, 17362055109648151,
    14711290550625444, 21310013050207869, 17343558766030761, 29619664082100260, 16371215108933627, 11652396861500322,
    17343558766030761, 11652396861500322, 16371215108933627, 16371215108933627, 24936637632823640, 33598038437354447,
    38887030216954019, 38887030431540681, 33598055025868671, 32956291399067364
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
noncomputable def negativeCeiling : ℝ := 4159403241 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 148093380620989944909791232, coefficient := (-148093380620989944909791232) }, { argument := 2069029316605609136057483264, coefficient := (-2069029316605609136057483264) }, { argument := 1540766512365879143872593920, coefficient := (-1540766512365879143872593920) }, { argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 2113051216958919968739557376, coefficient := (-2113051216958919968739557376) }, { argument := 28306081927178865414573654016, coefficient := (-28306081927178865414573654016) }, { argument := 51197470110900498409252192256, coefficient := (-51197470110900498409252192256) }, { argument := 1540766512365879143872593920, coefficient := (-1540766512365879143872593920) }, { argument := 28306081927178865414573654016, coefficient := (-28306081927178865414573654016) }, { argument := 1672832213425811641918816256, coefficient := (-1672832213425811641918816256) }, { argument := 1672832213425811641918816256, coefficient := (-1672832213425811641918816256) }, { argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 51197470110900498409252192256, coefficient := (-51197470110900498409252192256) }, { argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 2069029316605609136057483264, coefficient := (-2069029316605609136057483264) }, { argument := 2113051216958919968739557376, coefficient := (-2113051216958919968739557376) }, { argument := 4617188935827306476753387520, coefficient := (-4617188935827306476753387520) }, { argument := 472119274513668838917647892480, coefficient := (-472119274513668838917647892480) }, { argument := 50329716380207269622654697472, coefficient := (-50329716380207269622654697472) }, { argument := 4567405323656282495858742657024, coefficient := (-4567405323656282495858742657024) }, { argument := 31854250873548904824464998400, coefficient := (-31854250873548904824464998400) }, { argument := 1911255052412934289467899904, coefficient := (-1911255052412934289467899904) }, { argument := 50329716380207269622654697472, coefficient := (-50329716380207269622654697472) }, { argument := 50011173871471780574410047488, coefficient := (-50011173871471780574410047488) }, { argument := 31854250873548904824464998400, coefficient := (-31854250873548904824464998400) }, { argument := 771828498666089963896786911232, coefficient := (-771828498666089963896786911232) }, { argument := 49374088854000802477920747520, coefficient := (-49374088854000802477920747520) }, { argument := 472119274513668838917647892480, coefficient := (-472119274513668838917647892480) }, { argument := 50329716380207269622654697472, coefficient := (-50329716380207269622654697472) }, { argument := 1911255052412934289467899904, coefficient := (-1911255052412934289467899904) }, { argument := 49374088854000802477920747520, coefficient := (-49374088854000802477920747520) }, { argument := 1911255052412934289467899904, coefficient := (-1911255052412934289467899904) }, { argument := 50329716380207269622654697472, coefficient := (-50329716380207269622654697472) }, { argument := 50329716380207269622654697472, coefficient := (-50329716380207269622654697472) }, { argument := 4617188935827306476753387520, coefficient := (-4617188935827306476753387520) }, { argument := 14930041544181114802622431232, coefficient := (-14930041544181114802622431232) }, { argument := 583729893952007825551192489984, coefficient := (-583729893952007825551192489984) }, { argument := 583729982468709263246475919360, coefficient := (-583729982468709263246475919360) }, { argument := 14930213781430531028705869824, coefficient := (-14930213781430531028705869824) }, { argument := 148093380620989944909791232, coefficient := (-148093380620989944909791232) }, { argument := 15216931047258695682238709760, coefficient := (-15216931047258695682238709760) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }, { argument := 147334807403861479924973961216, coefficient := (-147334807403861479924973961216) }, { argument := 1013419847223825862859161600, coefficient := (-1013419847223825862859161600) }, { argument := 60805190833429551771549696, coefficient := (-60805190833429551771549696) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }, { argument := 1591069160141406604688883712, coefficient := (-1591069160141406604688883712) }, { argument := 1013419847223825862859161600, coefficient := (-1013419847223825862859161600) }, { argument := 24555162898233300657077485568, coefficient := (-24555162898233300657077485568) }, { argument := 1570800763196930087431700480, coefficient := (-1570800763196930087431700480) }, { argument := 15216931047258695682238709760, coefficient := (-15216931047258695682238709760) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }, { argument := 60805190833429551771549696, coefficient := (-60805190833429551771549696) }, { argument := 1570800763196930087431700480, coefficient := (-1570800763196930087431700480) }, { argument := 60805190833429551771549696, coefficient := (-60805190833429551771549696) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }, { argument := 148093380620989944909791232, coefficient := (-148093380620989944909791232) }, { argument := 14990534040796986389963997184, coefficient := (-14990534040796986389963997184) }, { argument := 586087253701057923736464785408, coefficient := (-586087253701057923736464785408) }, { argument := 586087340875758730069378334720, coefficient := (-586087340875758730069378334720) }, { argument := 14990706407173611132014297088, coefficient := (-14990706407173611132014297088) }, { argument := 76863822822780946434754609152, coefficient := (-76863822822780946434754609152) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
