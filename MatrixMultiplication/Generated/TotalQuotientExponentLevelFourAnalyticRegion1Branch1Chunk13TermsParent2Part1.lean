import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 13, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-6245615840426188216831766400335872)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    153109513750351, 86229, 2500641, 2213211, 143715, 86229,
    143715, 4397679, 143715, 86229, 70449093, 4512651,
    2500641, 4397679, 143715, 4512651, 143715, 4397679,
    143715, 86229, 20224719703801, 117711, 50606990782728815, 1231659,
    54549, 6325874191379479, 54549, 106227, 2006829, 106227,
    1231659, 2006829, 1294389103646361, 106227, 106227, 117711,
    3819, 110751, 98021, 6365, 3819, 6365,
    194769, 6365, 3819, 3120123, 199861, 110751,
    194769, 6365, 199861, 6365, 194769, 6365,
    3819, 13217504601, 104181, 124784940069, 1090089, 48279,
    249569819229, 48279, 94017, 1776159
  ]
def negativeCoefficients : Array ℕ := #[
    344771974536479298562763522048, 814409878902733274263584768, 11808943244089632476821979136, 20903186891836820706098675712, 678674899085611061886320640, 13030558062443732388217356288,
    678674899085611061886320640, 20767451912019698493721411584, 21717596770739553980362260480, 13030558062443732388217356288, 332686435531766542536674377728, 21310391831288187343230468096,
    11808943244089632476821979136, 20767451912019698493721411584, 678674899085611061886320640, 21310391831288187343230468096, 678674899085611061886320640, 20767451912019698493721411584,
    21717596770739553980362260480, 814409878902733274263584768, 1457344641947374589337703284736, 1111748962130137615498739712, 56978406207859904233297475010560, 11632690359849488708511203328,
    1030401477096225107047612416, 56978409302178518648527328903168, 1030401477096225107047612416, 1003285648751587604230569984, 37907928025803228938225319936, 1003285648751587604230569984,
    11632690359849488708511203328, 37907928025803228938225319936, 1457352571213545431212977291264, 1003285648751587604230569984, 1003285648751587604230569984, 1111748962130137615498739712,
    72138870392316700284420096, 1046013620688592154124091392, 1851564340069461973966782464, 60115725326930583570350080, 1154221926277067204550721536, 60115725326930583570350080,
    1839541195004075857252712448, 1923703210461778674251202560, 1154221926277067204550721536, 29468728555261372066185609216, 1887633775265620324108992512, 1046013620688592154124091392,
    1839541195004075857252712448, 60115725326930583570350080, 1887633775265620324108992512, 60115725326930583570350080, 1839541195004075857252712448, 1923703210461778674251202560,
    72138870392316700284420096, 30477490583465685202765873152, 1967923450207370032032251904, 1150937926853013658457711050752, 20591199027779554725410635776, 1823929051411708810176233472,
    1150937645959829962063941206016, 1823929051411708810176233472, 1775930918479821736224227328, 67101389838778129384904589312
  ]
def negativeScales : Array ℕ := #[
    47, 16, 21, 21, 17, 16,
    17, 22, 17, 16, 26, 22,
    21, 22, 17, 22, 17, 22,
    17, 16, 44, 16, 55, 20,
    15, 52, 15, 16, 20, 16,
    20, 20, 50, 16, 16, 16,
    11, 16, 16, 12, 11, 12,
    17, 12, 11, 21, 17, 16,
    17, 12, 17, 12, 17, 12,
    11, 33, 16, 36, 20, 15,
    37, 15, 16, 20
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    47121557258641667, 16395885528678480, 21253866523806047, 21077709568652220, 17132851122844681, 16395885528678480,
    17132851122844681, 22068310870649970, 17132851122844681, 16395885528678480, 26070077796824158, 22105543776848946,
    21253866523806047, 22068310870649970, 17132851122844681, 22105543776848946, 17132851122844681, 22068310870649970,
    17132851122844681, 16395885528678480, 44201184941889928, 16844889621395901, 55490186208867365, 20232171452706728,
    15735265128813176, 52490186287215608, 15735265128813176, 16696790980903244, 20936486268864749, 16696790980903244,
    20232171452706728, 20936486268864749, 50201192791427733, 16696790980903244, 16696790980903244, 16844889621395901,
    11898979208910875, 16756960200011716, 16580803244599554, 12635944798803559, 11898979208910875, 12635944798803559,
    17571404546596521, 12635944798803559, 11898979208910875, 21573171472770842, 17608637452800154, 16756960200011716,
    17571404546596521, 12635944798803559, 17608637452800154, 12635944798803559, 17571404546596521, 12635944798803559,
    11898979208910875, 33621730777803456, 16668732664705512, 36860652875923916, 20056014497552901, 15559108173498689,
    37860652523825632, 15559108173498689, 16520634025682838, 20760329305710158
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
noncomputable def negativeCeiling : ℝ := 77177314499 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 344771974536479298562763522048, coefficient := (-344771974536479298562763522048) }, { argument := 814409878902733274263584768, coefficient := (-814409878902733274263584768) }, { argument := 11808943244089632476821979136, coefficient := (-11808943244089632476821979136) }, { argument := 20903186891836820706098675712, coefficient := (-20903186891836820706098675712) }, { argument := 678674899085611061886320640, coefficient := (-678674899085611061886320640) }, { argument := 13030558062443732388217356288, coefficient := (-13030558062443732388217356288) }, { argument := 678674899085611061886320640, coefficient := (-678674899085611061886320640) }, { argument := 20767451912019698493721411584, coefficient := (-20767451912019698493721411584) }, { argument := 21717596770739553980362260480, coefficient := (-21717596770739553980362260480) }, { argument := 13030558062443732388217356288, coefficient := (-13030558062443732388217356288) }, { argument := 332686435531766542536674377728, coefficient := (-332686435531766542536674377728) }, { argument := 21310391831288187343230468096, coefficient := (-21310391831288187343230468096) }, { argument := 11808943244089632476821979136, coefficient := (-11808943244089632476821979136) }, { argument := 20767451912019698493721411584, coefficient := (-20767451912019698493721411584) }, { argument := 678674899085611061886320640, coefficient := (-678674899085611061886320640) }, { argument := 21310391831288187343230468096, coefficient := (-21310391831288187343230468096) }, { argument := 678674899085611061886320640, coefficient := (-678674899085611061886320640) }, { argument := 20767451912019698493721411584, coefficient := (-20767451912019698493721411584) }, { argument := 21717596770739553980362260480, coefficient := (-21717596770739553980362260480) }, { argument := 814409878902733274263584768, coefficient := (-814409878902733274263584768) }, { argument := 1457344641947374589337703284736, coefficient := (-1457344641947374589337703284736) }, { argument := 1111748962130137615498739712, coefficient := (-1111748962130137615498739712) }, { argument := 56978406207859904233297475010560, coefficient := (-56978406207859904233297475010560) }, { argument := 11632690359849488708511203328, coefficient := (-11632690359849488708511203328) }, { argument := 1030401477096225107047612416, coefficient := (-1030401477096225107047612416) }, { argument := 56978409302178518648527328903168, coefficient := (-56978409302178518648527328903168) }, { argument := 1030401477096225107047612416, coefficient := (-1030401477096225107047612416) }, { argument := 1003285648751587604230569984, coefficient := (-1003285648751587604230569984) }, { argument := 37907928025803228938225319936, coefficient := (-37907928025803228938225319936) }, { argument := 1003285648751587604230569984, coefficient := (-1003285648751587604230569984) }, { argument := 11632690359849488708511203328, coefficient := (-11632690359849488708511203328) }, { argument := 37907928025803228938225319936, coefficient := (-37907928025803228938225319936) }, { argument := 1457352571213545431212977291264, coefficient := (-1457352571213545431212977291264) }, { argument := 1003285648751587604230569984, coefficient := (-1003285648751587604230569984) }, { argument := 1003285648751587604230569984, coefficient := (-1003285648751587604230569984) }, { argument := 1111748962130137615498739712, coefficient := (-1111748962130137615498739712) }, { argument := 72138870392316700284420096, coefficient := (-72138870392316700284420096) }, { argument := 1046013620688592154124091392, coefficient := (-1046013620688592154124091392) }, { argument := 1851564340069461973966782464, coefficient := (-1851564340069461973966782464) }, { argument := 60115725326930583570350080, coefficient := (-60115725326930583570350080) }, { argument := 1154221926277067204550721536, coefficient := (-1154221926277067204550721536) }, { argument := 60115725326930583570350080, coefficient := (-60115725326930583570350080) }, { argument := 1839541195004075857252712448, coefficient := (-1839541195004075857252712448) }, { argument := 1923703210461778674251202560, coefficient := (-1923703210461778674251202560) }, { argument := 1154221926277067204550721536, coefficient := (-1154221926277067204550721536) }, { argument := 29468728555261372066185609216, coefficient := (-29468728555261372066185609216) }, { argument := 1887633775265620324108992512, coefficient := (-1887633775265620324108992512) }, { argument := 1046013620688592154124091392, coefficient := (-1046013620688592154124091392) }, { argument := 1839541195004075857252712448, coefficient := (-1839541195004075857252712448) }, { argument := 60115725326930583570350080, coefficient := (-60115725326930583570350080) }, { argument := 1887633775265620324108992512, coefficient := (-1887633775265620324108992512) }, { argument := 60115725326930583570350080, coefficient := (-60115725326930583570350080) }, { argument := 1839541195004075857252712448, coefficient := (-1839541195004075857252712448) }, { argument := 1923703210461778674251202560, coefficient := (-1923703210461778674251202560) }, { argument := 72138870392316700284420096, coefficient := (-72138870392316700284420096) }, { argument := 30477490583465685202765873152, coefficient := (-30477490583465685202765873152) }, { argument := 1967923450207370032032251904, coefficient := (-1967923450207370032032251904) }, { argument := 1150937926853013658457711050752, coefficient := (-1150937926853013658457711050752) }, { argument := 20591199027779554725410635776, coefficient := (-20591199027779554725410635776) }, { argument := 1823929051411708810176233472, coefficient := (-1823929051411708810176233472) }, { argument := 1150937645959829962063941206016, coefficient := (-1150937645959829962063941206016) }, { argument := 1823929051411708810176233472, coefficient := (-1823929051411708810176233472) }, { argument := 1775930918479821736224227328, coefficient := (-1775930918479821736224227328) }, { argument := 67101389838778129384904589312, coefficient := (-67101389838778129384904589312) }] }

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


end Parent2

namespace Parent2

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-95528536004107656508628412854697984)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    94017, 1090089, 1776159, 13217504601, 94017, 94017,
    104181, 430162893460299, 1561221517605651, 215095028783313, 107363420865491, 10048422426868781,
    1287701755, 13295688805, 89007769075, 312865194685, 10047478391233317, 89007769075,
    10112532085, 5171583685, 1287701755, 10070978755, 312865194685, 10070978755,
    107362774373595, 13295688805, 306219050141087, 12647967142018585, 243109579761, 510429274567153389,
    76931799463, 9230147389, 243107384305, 483172448291, 76931799463, 7456778516681,
    477013162149, 50591955691025777, 243107384305, 9230147389, 477013162149, 9230147389,
    243107384305, 243122752497, 306219050141087, 13050147454391545, 6765, 2041720230352835061,
    70785, 3135, 510430082499514443, 3135, 6105, 115335,
    6105, 70785, 115335, 52200860494108923, 6105, 6105,
    6765, 3819, 110751, 98021
  ]
def negativeCoefficients : Array ℕ := #[
    1775930918479821736224227328, 20591199027779554725410635776, 67101389838778129384904589312, 30477490583465685202765873152, 1775930918479821736224227328, 1775930918479821736224227328,
    1967923450207370032032251904, 121080090418526059192746246144, 439444790308225631504937517056, 121087736434721817301044166656, 120880465550761750687209488384, 11313517874326894301252465721344,
    47507809435503277952372572160, 61315542167380045060605214720, 820951768349182274429360537600, 1442836043981377214120974090240, 11312454984692869266302784503808, 820951768349182274429360537600,
    46635822827292861421940899840, 47699440346483377282985492480, 47507809435503277952372572160, 46444191916312762091327979520, 1442836043981377214120974090240, 46444191916312762091327979520,
    120879737665596269775846113280, 61315542167380045060605214720, 344772000027286660943905292288, 56961380107789176667317112668160, 1121145049929561575434374610944, 574692272684906148415554491252736,
    709570607911953457714879791104, 42566541661875360348195782656, 1121134925175822302915036446720, 1114119812136467377591819436032, 709570607911953457714879791104, 17194160613943742203547260813312,
    1099917465244189894116636622848, 56961478199512083440071866318848, 1121134925175822302915036446720, 42566541661875360348195782656, 1099917465244189894116636622848, 42566541661875360348195782656,
    1121134925175822302915036446720, 1121205798451997210550403596288, 344772000027286660943905292288, 14693159803181947251303991214080, 63893618513226299741306880, 574693154288239452348557889110016,
    668545422979855672902942720, 59218475695185350979747840, 574693182335876194255413216018432, 59218475695185350979747840, 57660094755838368059228160, 2178616553207082122886512640,
    57660094755838368059228160, 668545422979855672902942720, 2178616553207082122886512640, 14693235991855511958112318783488, 57660094755838368059228160, 57660094755838368059228160,
    63893618513226299741306880, 72138870392316700284420096, 1046013620688592154124091392, 1851564340069461973966782464
  ]
def negativeScales : Array ℕ := #[
    16, 20, 20, 33, 16, 16,
    16, 48, 50, 47, 46, 53,
    30, 33, 36, 38, 53, 36,
    33, 32, 30, 33, 38, 33,
    46, 33, 48, 53, 37, 58,
    36, 33, 37, 38, 36, 42,
    38, 55, 37, 33, 38, 33,
    37, 37, 48, 53, 12, 60,
    16, 11, 58, 11, 12, 16,
    12, 16, 16, 55, 12, 12,
    12, 11, 16, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16520634025682838, 20056014497552901, 20760329305710158, 33621730777803456, 16520634025682838, 16520634025682838,
    16668732664705512, 48611876409375781, 50471596675346232, 47611967510409287, 46609495873663986, 53157818538449463,
    30262151343085632, 33630239469204674, 36373212216602051, 38186750215768100, 53157682992843119, 36373212216602051,
    33235425228913001, 32267958996156815, 30262151343085632, 33229484848342179, 38186750215768100, 33229484848342179,
    46609487186408558, 33630239469204674, 48121557365307703, 53489755043054000, 37822815788833479, 58824488688270549,
    36162861002779071, 33103706539309278, 37822802760190787, 38813747235520161, 36162861002779071, 42761689629767395,
    38795238119183948, 55489757527479765, 37822802760190787, 33103706539309278, 38795238119183948, 33103706539309278,
    37822802760190787, 37822893958218894, 48121557365307703, 53534915626182882, 12723874218989575, 60824490901426821,
    16111156051745362, 11614249727697750, 58824490971836893, 11614249727697750, 12575775579877617, 16815470860503971,
    12575775579877617, 16111156051745362, 16815470860503971, 55534923106992866, 12575775579877617, 12575775579877617,
    12723874218989575, 11898979208910875, 16756960200011716, 16580803244599554
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
noncomputable def negativeCeiling : ℝ := 339975610901 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1775930918479821736224227328, coefficient := (-1775930918479821736224227328) }, { argument := 20591199027779554725410635776, coefficient := (-20591199027779554725410635776) }, { argument := 67101389838778129384904589312, coefficient := (-67101389838778129384904589312) }, { argument := 30477490583465685202765873152, coefficient := (-30477490583465685202765873152) }, { argument := 1775930918479821736224227328, coefficient := (-1775930918479821736224227328) }, { argument := 1775930918479821736224227328, coefficient := (-1775930918479821736224227328) }, { argument := 1967923450207370032032251904, coefficient := (-1967923450207370032032251904) }, { argument := 121080090418526059192746246144, coefficient := (-121080090418526059192746246144) }, { argument := 439444790308225631504937517056, coefficient := (-439444790308225631504937517056) }, { argument := 121087736434721817301044166656, coefficient := (-121087736434721817301044166656) }, { argument := 120880465550761750687209488384, coefficient := (-120880465550761750687209488384) }, { argument := 11313517874326894301252465721344, coefficient := (-11313517874326894301252465721344) }, { argument := 47507809435503277952372572160, coefficient := (-47507809435503277952372572160) }, { argument := 61315542167380045060605214720, coefficient := (-61315542167380045060605214720) }, { argument := 820951768349182274429360537600, coefficient := (-820951768349182274429360537600) }, { argument := 1442836043981377214120974090240, coefficient := (-1442836043981377214120974090240) }, { argument := 11312454984692869266302784503808, coefficient := (-11312454984692869266302784503808) }, { argument := 820951768349182274429360537600, coefficient := (-820951768349182274429360537600) }, { argument := 46635822827292861421940899840, coefficient := (-46635822827292861421940899840) }, { argument := 47699440346483377282985492480, coefficient := (-47699440346483377282985492480) }, { argument := 47507809435503277952372572160, coefficient := (-47507809435503277952372572160) }, { argument := 46444191916312762091327979520, coefficient := (-46444191916312762091327979520) }, { argument := 1442836043981377214120974090240, coefficient := (-1442836043981377214120974090240) }, { argument := 46444191916312762091327979520, coefficient := (-46444191916312762091327979520) }, { argument := 120879737665596269775846113280, coefficient := (-120879737665596269775846113280) }, { argument := 61315542167380045060605214720, coefficient := (-61315542167380045060605214720) }, { argument := 344772000027286660943905292288, coefficient := (-344772000027286660943905292288) }, { argument := 56961380107789176667317112668160, coefficient := (-56961380107789176667317112668160) }, { argument := 1121145049929561575434374610944, coefficient := (-1121145049929561575434374610944) }, { argument := 574692272684906148415554491252736, coefficient := (-574692272684906148415554491252736) }, { argument := 709570607911953457714879791104, coefficient := (-709570607911953457714879791104) }, { argument := 42566541661875360348195782656, coefficient := (-42566541661875360348195782656) }, { argument := 1121134925175822302915036446720, coefficient := (-1121134925175822302915036446720) }, { argument := 1114119812136467377591819436032, coefficient := (-1114119812136467377591819436032) }, { argument := 709570607911953457714879791104, coefficient := (-709570607911953457714879791104) }, { argument := 17194160613943742203547260813312, coefficient := (-17194160613943742203547260813312) }, { argument := 1099917465244189894116636622848, coefficient := (-1099917465244189894116636622848) }, { argument := 56961478199512083440071866318848, coefficient := (-56961478199512083440071866318848) }, { argument := 1121134925175822302915036446720, coefficient := (-1121134925175822302915036446720) }, { argument := 42566541661875360348195782656, coefficient := (-42566541661875360348195782656) }, { argument := 1099917465244189894116636622848, coefficient := (-1099917465244189894116636622848) }, { argument := 42566541661875360348195782656, coefficient := (-42566541661875360348195782656) }, { argument := 1121134925175822302915036446720, coefficient := (-1121134925175822302915036446720) }, { argument := 1121205798451997210550403596288, coefficient := (-1121205798451997210550403596288) }, { argument := 344772000027286660943905292288, coefficient := (-344772000027286660943905292288) }, { argument := 14693159803181947251303991214080, coefficient := (-14693159803181947251303991214080) }, { argument := 63893618513226299741306880, coefficient := (-63893618513226299741306880) }, { argument := 574693154288239452348557889110016, coefficient := (-574693154288239452348557889110016) }, { argument := 668545422979855672902942720, coefficient := (-668545422979855672902942720) }, { argument := 59218475695185350979747840, coefficient := (-59218475695185350979747840) }, { argument := 574693182335876194255413216018432, coefficient := (-574693182335876194255413216018432) }, { argument := 59218475695185350979747840, coefficient := (-59218475695185350979747840) }, { argument := 57660094755838368059228160, coefficient := (-57660094755838368059228160) }, { argument := 2178616553207082122886512640, coefficient := (-2178616553207082122886512640) }, { argument := 57660094755838368059228160, coefficient := (-57660094755838368059228160) }, { argument := 668545422979855672902942720, coefficient := (-668545422979855672902942720) }, { argument := 2178616553207082122886512640, coefficient := (-2178616553207082122886512640) }, { argument := 14693235991855511958112318783488, coefficient := (-14693235991855511958112318783488) }, { argument := 57660094755838368059228160, coefficient := (-57660094755838368059228160) }, { argument := 57660094755838368059228160, coefficient := (-57660094755838368059228160) }, { argument := 63893618513226299741306880, coefficient := (-63893618513226299741306880) }, { argument := 72138870392316700284420096, coefficient := (-72138870392316700284420096) }, { argument := 1046013620688592154124091392, coefficient := (-1046013620688592154124091392) }, { argument := 1851564340069461973966782464, coefficient := (-1851564340069461973966782464) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
