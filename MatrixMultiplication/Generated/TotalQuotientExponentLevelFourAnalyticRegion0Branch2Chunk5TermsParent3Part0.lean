import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 5, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-17772425989987025483597495664640)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    31077795087, 1563029879931, 3124797676911, 62849146749, 59618000813, 652894340681,
    8653153, 7290434837685, 12395057, 2104821, 33911005, 8653153,
    12395057, 560116255, 12395057, 1304391281077, 33911005, 2104821,
    12395057, 2104821, 8653153, 8653153, 29168316497, 59618000813,
    1155109326815, 2310862545309, 7439828959, 875005640523, 44007625296999, 87979716229419,
    1769538596721, 1155109326815, 6457694439139, 301725269, 295076188819893, 432201061,
    73392633, 1182436865, 301725269, 432201061, 19530595115, 432201061,
    6449309554597, 1182436865, 73392633, 432201061, 73392633, 301725269,
    301725269, 282675290899, 652894340681, 6457694439139, 25836884716065, 326944291333,
    8653153, 301725269, 75466569, 4256147, 31077795087, 875005640523,
    248362391613, 248362391613, 12491164127169, 24972242148189
  ]
def negativeCoefficients : Array ℕ := #[
    139961946373309831317553152, 7039260784826202704131915776, 7036418826672285576150908928, 141523696939675010048458752, 16780975390375045473763328, 367546838675407158453993472,
    39905624705413006923661312, 4104149952295881061139742720, 28581055532255261715595264, 4853386788496176517742592, 39096726907330310837370880, 39905624705413006923661312,
    28581055532255261715595264, 645770075469352375555194880, 28581055532255261715595264, 367153505462731319397056512, 39096726907330310837370880, 4853386788496176517742592,
    28581055532255261715595264, 4853386788496176517742592, 39905624705413006923661312, 39905624705413006923661312, 16420302413364236400984064, 16780975390375045473763328,
    650268741727027310394081280, 650449981122378020583112704, 16753005463726312581496832, 492584384575808121839026176, 24774090611128138720176242688, 24764088576685836735677988864,
    498080835300650374687358976, 650268741727027310394081280, 14541435134889462280038121472, 1391462204453542572301746176, 166113126751897029079115759616, 996587795081591301783683072,
    169231889730836258793455616, 1363256889498403195836170240, 1391462204453542572301746176, 996587795081591301783683072, 22517243105852935545018122240, 996587795081591301783683072,
    14522554053440014364029485056, 1363256889498403195836170240, 169231889730836258793455616, 996587795081591301783683072, 169231889730836258793455616, 1391462204453542572301746176,
    1391462204453542572301746176, 636528167379791479624957952, 367546838675407158453993472, 14541435134889462280038121472, 14544873047460599668439777280, 368106547154552421238177792,
    39905624705413006923661312, 1391462204453542572301746176, 1392112484463942962987925504, 39256027224543343490891776, 139961946373309831317553152, 492584384575808121839026176,
    139815596790144000124256256, 139815596790144000124256256, 7031900263567751913802825728, 7029061277074360934527401984
  ]
def negativeScales : Array ℕ := #[
    34, 40, 41, 35, 35, 39,
    23, 42, 23, 21, 25, 23,
    23, 29, 23, 40, 25, 21,
    23, 21, 23, 23, 34, 35,
    40, 41, 32, 39, 45, 46,
    40, 40, 42, 28, 48, 28,
    26, 30, 28, 28, 34, 28,
    42, 30, 26, 28, 26, 28,
    28, 38, 39, 42, 44, 38,
    23, 28, 26, 22, 34, 39,
    37, 37, 43, 44
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34855165101573603, 40507482496779131, 41506899920434116, 35871174109953181, 35795028947303403, 39248058579928929,
    23044794481105170, 42729142005394615, 23563261570041397, 21005266116918533, 25015250205491155, 23044794481105170,
    23563261570041397, 29061151056099763, 23563261570041397, 40246513841494855, 25015250205491155, 21005266116918533,
    23563261570041397, 21005266116918533, 23044794481105170, 23044794481105170, 34763683070018930, 35795028947303403,
    40071166542488423, 41071568586641375, 32792622308826718, 39670501360773924, 45322818757854487, 46322236181509479,
    40686510368500588, 40071166542488423, 42554156316738918, 28168660284003809, 48068080835579136, 28687127372991373,
    26129131919817172, 30139116008389794, 28168660284003809, 28687127372991373, 34185016858998402, 28687127372991373,
    42552281856476054, 30139116008389794, 26129131919817172, 28687127372991373, 26129131919817172, 28168660284003809,
    28168660284003809, 38040354824151711, 39248058579928929, 42554156316738918, 44554497361013745, 38250253876840679,
    23044794481105170, 28168660284003809, 26169334349454250, 22021116549230146, 34855165101573603, 39670501360773924,
    37853655774968692, 37853655774968692, 43505973170228171, 44505390593883157
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
noncomputable def negativeCeiling : ℝ := 94001119 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 139961946373309831317553152, coefficient := (-139961946373309831317553152) }, { argument := 7039260784826202704131915776, coefficient := (-7039260784826202704131915776) }, { argument := 7036418826672285576150908928, coefficient := (-7036418826672285576150908928) }, { argument := 141523696939675010048458752, coefficient := (-141523696939675010048458752) }, { argument := 16780975390375045473763328, coefficient := (-16780975390375045473763328) }, { argument := 367546838675407158453993472, coefficient := (-367546838675407158453993472) }, { argument := 39905624705413006923661312, coefficient := (-39905624705413006923661312) }, { argument := 4104149952295881061139742720, coefficient := (-4104149952295881061139742720) }, { argument := 28581055532255261715595264, coefficient := (-28581055532255261715595264) }, { argument := 4853386788496176517742592, coefficient := (-4853386788496176517742592) }, { argument := 39096726907330310837370880, coefficient := (-39096726907330310837370880) }, { argument := 39905624705413006923661312, coefficient := (-39905624705413006923661312) }, { argument := 28581055532255261715595264, coefficient := (-28581055532255261715595264) }, { argument := 645770075469352375555194880, coefficient := (-645770075469352375555194880) }, { argument := 28581055532255261715595264, coefficient := (-28581055532255261715595264) }, { argument := 367153505462731319397056512, coefficient := (-367153505462731319397056512) }, { argument := 39096726907330310837370880, coefficient := (-39096726907330310837370880) }, { argument := 4853386788496176517742592, coefficient := (-4853386788496176517742592) }, { argument := 28581055532255261715595264, coefficient := (-28581055532255261715595264) }, { argument := 4853386788496176517742592, coefficient := (-4853386788496176517742592) }, { argument := 39905624705413006923661312, coefficient := (-39905624705413006923661312) }, { argument := 39905624705413006923661312, coefficient := (-39905624705413006923661312) }, { argument := 16420302413364236400984064, coefficient := (-16420302413364236400984064) }, { argument := 16780975390375045473763328, coefficient := (-16780975390375045473763328) }, { argument := 650268741727027310394081280, coefficient := (-650268741727027310394081280) }, { argument := 650449981122378020583112704, coefficient := (-650449981122378020583112704) }, { argument := 16753005463726312581496832, coefficient := (-16753005463726312581496832) }, { argument := 492584384575808121839026176, coefficient := (-492584384575808121839026176) }, { argument := 24774090611128138720176242688, coefficient := (-24774090611128138720176242688) }, { argument := 24764088576685836735677988864, coefficient := (-24764088576685836735677988864) }, { argument := 498080835300650374687358976, coefficient := (-498080835300650374687358976) }, { argument := 650268741727027310394081280, coefficient := (-650268741727027310394081280) }, { argument := 14541435134889462280038121472, coefficient := (-14541435134889462280038121472) }, { argument := 1391462204453542572301746176, coefficient := (-1391462204453542572301746176) }, { argument := 166113126751897029079115759616, coefficient := (-166113126751897029079115759616) }, { argument := 996587795081591301783683072, coefficient := (-996587795081591301783683072) }, { argument := 169231889730836258793455616, coefficient := (-169231889730836258793455616) }, { argument := 1363256889498403195836170240, coefficient := (-1363256889498403195836170240) }, { argument := 1391462204453542572301746176, coefficient := (-1391462204453542572301746176) }, { argument := 996587795081591301783683072, coefficient := (-996587795081591301783683072) }, { argument := 22517243105852935545018122240, coefficient := (-22517243105852935545018122240) }, { argument := 996587795081591301783683072, coefficient := (-996587795081591301783683072) }, { argument := 14522554053440014364029485056, coefficient := (-14522554053440014364029485056) }, { argument := 1363256889498403195836170240, coefficient := (-1363256889498403195836170240) }, { argument := 169231889730836258793455616, coefficient := (-169231889730836258793455616) }, { argument := 996587795081591301783683072, coefficient := (-996587795081591301783683072) }, { argument := 169231889730836258793455616, coefficient := (-169231889730836258793455616) }, { argument := 1391462204453542572301746176, coefficient := (-1391462204453542572301746176) }, { argument := 1391462204453542572301746176, coefficient := (-1391462204453542572301746176) }, { argument := 636528167379791479624957952, coefficient := (-636528167379791479624957952) }, { argument := 367546838675407158453993472, coefficient := (-367546838675407158453993472) }, { argument := 14541435134889462280038121472, coefficient := (-14541435134889462280038121472) }, { argument := 14544873047460599668439777280, coefficient := (-14544873047460599668439777280) }, { argument := 368106547154552421238177792, coefficient := (-368106547154552421238177792) }, { argument := 39905624705413006923661312, coefficient := (-39905624705413006923661312) }, { argument := 1391462204453542572301746176, coefficient := (-1391462204453542572301746176) }, { argument := 1392112484463942962987925504, coefficient := (-1392112484463942962987925504) }, { argument := 39256027224543343490891776, coefficient := (-39256027224543343490891776) }, { argument := 139961946373309831317553152, coefficient := (-139961946373309831317553152) }, { argument := 492584384575808121839026176, coefficient := (-492584384575808121839026176) }, { argument := 139815596790144000124256256, coefficient := (-139815596790144000124256256) }, { argument := 139815596790144000124256256, coefficient := (-139815596790144000124256256) }, { argument := 7031900263567751913802825728, coefficient := (-7031900263567751913802825728) }, { argument := 7029061277074360934527401984, coefficient := (-7029061277074360934527401984) }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-34246456248199108587489157185536)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    502267434151, 2310862545309, 25836884716065, 75466569, 295144683722665, 108100761,
    18356733, 295747365, 75466569, 108100761, 4884930615, 108100761,
    51606652052477, 295747365, 18356733, 108100761, 18356733, 75466569,
    75466569, 1131011005289, 7290434837685, 295076188819893, 295144683722665, 7322311473645,
    12395057, 432201061, 108100761, 6096643, 1563029879931, 44007625296999,
    12491164127169, 2104821, 73392633, 18356733, 1035279, 33911005,
    1182436865, 295747365, 16679495, 8653153, 301725269, 75466569,
    4256147, 12395057, 432201061, 108100761, 6096643, 560116255,
    19530595115, 4884930615, 275499245, 12395057, 432201061, 108100761,
    6096643, 7439828959, 326944291333, 4256147, 7322311473645, 6096643,
    1035279, 16679495, 4256147, 6096643
  ]
def negativeCoefficients : Array ℕ := #[
    141375714330173671060013056, 650449981122378020583112704, 14544873047460599668439777280, 1392112484463942962987925504, 166151685954222123773308436480, 997053536170121311329189888,
    169310977840209279282315264, 1363893988157241416440872960, 1392112484463942962987925504, 997053536170121311329189888, 22527766218183401326730280960, 997053536170121311329189888,
    14525981184585891236557094912, 1363893988157241416440872960, 169310977840209279282315264, 997053536170121311329189888, 169310977840209279282315264, 1392112484463942962987925504,
    1392112484463942962987925504, 636702592746433810077319168, 4104149952295881061139742720, 166113126751897029079115759616, 166151685954222123773308436480, 4122094903024791180269322240,
    28581055532255261715595264, 996587795081591301783683072, 997053536170121311329189888, 28115803282443205473206272, 7039260784826202704131915776, 24774090611128138720176242688,
    7031900263567751913802825728, 4853386788496176517742592, 169231889730836258793455616, 169310977840209279282315264, 4774381689471487721865216, 39096726907330310837370880,
    1363256889498403195836170240, 1363893988157241416440872960, 38460296942964762203914240, 39905624705413006923661312, 1391462204453542572301746176, 1392112484463942962987925504,
    39256027224543343490891776, 28581055532255261715595264, 996587795081591301783683072, 997053536170121311329189888, 28115803282443205473206272, 645770075469352375555194880,
    22517243105852935545018122240, 22527766218183401326730280960, 635258008126900727437066240, 28581055532255261715595264, 996587795081591301783683072, 997053536170121311329189888,
    28115803282443205473206272, 16753005463726312581496832, 368106547154552421238177792, 39256027224543343490891776, 4122094903024791180269322240, 28115803282443205473206272,
    4774381689471487721865216, 38460296942964762203914240, 39256027224543343490891776, 28115803282443205473206272
  ]
def negativeScales : Array ℕ := #[
    38, 41, 44, 26, 48, 26,
    24, 28, 26, 26, 32, 26,
    45, 28, 24, 26, 24, 26,
    26, 40, 42, 48, 48, 42,
    23, 28, 26, 22, 40, 45,
    43, 21, 26, 24, 19, 25,
    30, 28, 23, 23, 28, 26,
    22, 23, 28, 26, 22, 29,
    34, 32, 28, 23, 28, 26,
    22, 32, 38, 22, 42, 22,
    19, 23, 22, 22
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    38869664783330798, 41071568586641375, 44554497361013745, 26169334349454250, 48068415683977747, 26687801438442683,
    24129805985267613, 28139790073840235, 26169334349454250, 26687801438442683, 32185690924448843, 26687801438442683,
    45552622273305424, 28139790073840235, 24129805985267613, 26687801438442683, 24129805985267613, 26169334349454250,
    26169334349454250, 40040750106171146, 42729142005394615, 48068080835579136, 48068415683977747, 42735436282561115,
    23563261570041397, 28687127372991373, 26687801438442683, 22539583638165363, 40507482496779131, 45322818757854487,
    43505973170228171, 21005266116918533, 26129131919817172, 24129805985267613, 19981588202642544, 25015250205491155,
    30139116008389794, 28139790073840235, 23991572294302322, 23044794481105170, 28168660284003809, 26169334349454250,
    22021116549230146, 23563261570041397, 28687127372991373, 26687801438442683, 22539583638165363, 29061151056099763,
    34185016858998402, 32185690924448843, 28037473124224739, 23563261570041397, 28687127372991373, 26687801438442683,
    22539583638165363, 32792622308826718, 38250253876840679, 22021116549230146, 42735436282561115, 22539583638165363,
    19981588202642544, 23991572294302322, 22021116549230146, 22539583638165363
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
noncomputable def negativeCeiling : ℝ := 7347509 / 20000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 141375714330173671060013056, coefficient := (-141375714330173671060013056) }, { argument := 650449981122378020583112704, coefficient := (-650449981122378020583112704) }, { argument := 14544873047460599668439777280, coefficient := (-14544873047460599668439777280) }, { argument := 1392112484463942962987925504, coefficient := (-1392112484463942962987925504) }, { argument := 166151685954222123773308436480, coefficient := (-166151685954222123773308436480) }, { argument := 997053536170121311329189888, coefficient := (-997053536170121311329189888) }, { argument := 169310977840209279282315264, coefficient := (-169310977840209279282315264) }, { argument := 1363893988157241416440872960, coefficient := (-1363893988157241416440872960) }, { argument := 1392112484463942962987925504, coefficient := (-1392112484463942962987925504) }, { argument := 997053536170121311329189888, coefficient := (-997053536170121311329189888) }, { argument := 22527766218183401326730280960, coefficient := (-22527766218183401326730280960) }, { argument := 997053536170121311329189888, coefficient := (-997053536170121311329189888) }, { argument := 14525981184585891236557094912, coefficient := (-14525981184585891236557094912) }, { argument := 1363893988157241416440872960, coefficient := (-1363893988157241416440872960) }, { argument := 169310977840209279282315264, coefficient := (-169310977840209279282315264) }, { argument := 997053536170121311329189888, coefficient := (-997053536170121311329189888) }, { argument := 169310977840209279282315264, coefficient := (-169310977840209279282315264) }, { argument := 1392112484463942962987925504, coefficient := (-1392112484463942962987925504) }, { argument := 1392112484463942962987925504, coefficient := (-1392112484463942962987925504) }, { argument := 636702592746433810077319168, coefficient := (-636702592746433810077319168) }, { argument := 4104149952295881061139742720, coefficient := (-4104149952295881061139742720) }, { argument := 166113126751897029079115759616, coefficient := (-166113126751897029079115759616) }, { argument := 166151685954222123773308436480, coefficient := (-166151685954222123773308436480) }, { argument := 4122094903024791180269322240, coefficient := (-4122094903024791180269322240) }, { argument := 28581055532255261715595264, coefficient := (-28581055532255261715595264) }, { argument := 996587795081591301783683072, coefficient := (-996587795081591301783683072) }, { argument := 997053536170121311329189888, coefficient := (-997053536170121311329189888) }, { argument := 28115803282443205473206272, coefficient := (-28115803282443205473206272) }, { argument := 7039260784826202704131915776, coefficient := (-7039260784826202704131915776) }, { argument := 24774090611128138720176242688, coefficient := (-24774090611128138720176242688) }, { argument := 7031900263567751913802825728, coefficient := (-7031900263567751913802825728) }, { argument := 4853386788496176517742592, coefficient := (-4853386788496176517742592) }, { argument := 169231889730836258793455616, coefficient := (-169231889730836258793455616) }, { argument := 169310977840209279282315264, coefficient := (-169310977840209279282315264) }, { argument := 4774381689471487721865216, coefficient := (-4774381689471487721865216) }, { argument := 39096726907330310837370880, coefficient := (-39096726907330310837370880) }, { argument := 1363256889498403195836170240, coefficient := (-1363256889498403195836170240) }, { argument := 1363893988157241416440872960, coefficient := (-1363893988157241416440872960) }, { argument := 38460296942964762203914240, coefficient := (-38460296942964762203914240) }, { argument := 39905624705413006923661312, coefficient := (-39905624705413006923661312) }, { argument := 1391462204453542572301746176, coefficient := (-1391462204453542572301746176) }, { argument := 1392112484463942962987925504, coefficient := (-1392112484463942962987925504) }, { argument := 39256027224543343490891776, coefficient := (-39256027224543343490891776) }, { argument := 28581055532255261715595264, coefficient := (-28581055532255261715595264) }, { argument := 996587795081591301783683072, coefficient := (-996587795081591301783683072) }, { argument := 997053536170121311329189888, coefficient := (-997053536170121311329189888) }, { argument := 28115803282443205473206272, coefficient := (-28115803282443205473206272) }, { argument := 645770075469352375555194880, coefficient := (-645770075469352375555194880) }, { argument := 22517243105852935545018122240, coefficient := (-22517243105852935545018122240) }, { argument := 22527766218183401326730280960, coefficient := (-22527766218183401326730280960) }, { argument := 635258008126900727437066240, coefficient := (-635258008126900727437066240) }, { argument := 28581055532255261715595264, coefficient := (-28581055532255261715595264) }, { argument := 996587795081591301783683072, coefficient := (-996587795081591301783683072) }, { argument := 997053536170121311329189888, coefficient := (-997053536170121311329189888) }, { argument := 28115803282443205473206272, coefficient := (-28115803282443205473206272) }, { argument := 16753005463726312581496832, coefficient := (-16753005463726312581496832) }, { argument := 368106547154552421238177792, coefficient := (-368106547154552421238177792) }, { argument := 39256027224543343490891776, coefficient := (-39256027224543343490891776) }, { argument := 4122094903024791180269322240, coefficient := (-4122094903024791180269322240) }, { argument := 28115803282443205473206272, coefficient := (-28115803282443205473206272) }, { argument := 4774381689471487721865216, coefficient := (-4774381689471487721865216) }, { argument := 38460296942964762203914240, coefficient := (-38460296942964762203914240) }, { argument := 39256027224543343490891776, coefficient := (-39256027224543343490891776) }, { argument := 28115803282443205473206272, coefficient := (-28115803282443205473206272) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5
