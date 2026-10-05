import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 15, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 522112758428717085000449325682130944
def positiveArguments : Array ℕ := #[
    33981, 1935, 1505, 215, 2021, 23865,
    1677, 1505, 23865, 215, 1677, 1677,
    1677, 1677, 1677, 1935, 2021, 565,
    2373
  ]
def positiveCoefficients : Array ℕ := #[
    5384504380794432911532433952735232, 37428343375268919248903208960, 29110933736320270526924718080, 33269638555794594887913963520, 39091825303058648993298907136, 461616234961650004069806243840,
    1038012722940791360502915661824, 29110933736320270526924718080, 461616234961650004069806243840, 33269638555794594887913963520, 32437897591899730015716114432, 32437897591899730015716114432,
    32437897591899730015716114432, 1038012722940791360502915661824, 32437897591899730015716114432, 37428343375268919248903208960, 39091825303058648993298907136, 21857378818632495478687662080,
    367203964153025924041952722944
  ]
def positiveScales : Array ℕ := #[
    15, 10, 10, 7, 10, 14,
    10, 10, 14, 7, 10, 10,
    10, 10, 10, 10, 10, 9,
    11
  ]
def negativeArguments : Array ℕ := #[
    1535909625, 90021, 90021, 29637, 1665, 827,
    827, 191965725, 28035, 1575, 5290794015, 85155,
    1535725305, 85155, 85155, 28035, 1575, 5235,
    5235, 231, 827, 827, 909, 405492655,
    37647, 2115, 11198800165, 114351, 3243940195, 114351,
    114351, 37647, 2115, 10871, 10871, 231,
    1317, 1317, 27393, 909, 122558228487485, 122558193312451,
    165495, 135, 43
  ]
def negativeCoefficients : Array ℕ := #[
    7083132943180552445362176000, 425112153154408331782127616, 425112153154408331782127616, 279913550905615350396616704, 15725480387955918561607680, 7998253222570386619856060416,
    7998253222570386619856060416, 7082285199998215030780723200, 264783088694501007131934720, 14875454421039382423142400, 24399480785354803634566594560, 402133117848764638172282880,
    7082282917213635909223710720, 402133117848764638172282880, 402133117848764638172282880, 264783088694501007131934720, 14875454421039382423142400, 202519253301842679346778603520,
    202519253301842679346778603520, 17872759317182677718856105984, 7998253222570386619856060416, 7998253222570386619856060416, 17582617120475166716926623744, 7480019230554001783631380480,
    355565861961187066720026624, 19975610222538599253934080, 25822675072046412349917102080, 540007329682626799831351296, 7480016820948057155321200640, 540007329682626799831351296,
    540007329682626799831351296, 355565861961187066720026624, 19975610222538599253934080, 210275721360490140131693428736, 210275721360490140131693428736, 17872759317182677718856105984,
    203795878967355727755268325376, 203795878967355727755268325376, 529857679627256591723620466688, 17582617120475166716926623744, 137988298036856388397448560640, 137988258433288884611316711424,
    100035589258561527633999298560, 20890238162940792138922721280, 3406810988113366516522389864448
  ]
def negativeScales : Array ℕ := #[
    30, 16, 16, 14, 10, 9,
    9, 27, 14, 10, 32, 16,
    30, 16, 16, 14, 10, 12,
    12, 7, 9, 9, 9, 28,
    15, 11, 33, 16, 31, 16,
    16, 15, 11, 13, 13, 7,
    10, 10, 14, 9, 46, 46,
    17, 7, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    15052440688628755, 10918117850659694, 10555547771646966, 7748192849576052, 10980853605307137, 14542608715939499,
    10711666973558447, 10555547771646966, 14542608715939499, 7748192849576052, 10711666973558447, 10711666973558447,
    10711666973558447, 10711666973558447, 10711666973558447, 10918117850659694, 10980853605307137, 9142107057302549,
    11212496385193947
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    30516446182415446, 16457973970567442, 16457973970567442, 14855111799946705, 10701306462033270, 9691743519230811,
    9691743519230811, 27516273503448370, 14774941449737867, 10621136113284685, 32300837104783336, 16377803621883399,
    30516273038434263, 16377803621883399, 16377803621883399, 14774941449737867, 10621136113284685, 12353973821818172,
    12353973821818172, 7851749043206919, 9691743519230811, 9691743519230811, 9828136485328458, 28595100541139362,
    15200247284086348, 11046441948007313, 33382625119662740, 16803109457304290, 31595100076390943, 16803109457304290,
    16803109457304290, 15200247284086348, 11046441948007313, 13408197036444915, 13408197036444915, 7851749043206919,
    10363039630256516, 10363039630256516, 14741519654107753, 9828136485328458, 46800460678229501, 46800460264166279,
    17336428104857997, 7076815597050831, 5426264754702117
  ]

abbrev PositiveTerm := Fin 19
abbrev NegativeTerm := Fin 45
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
noncomputable def positiveFloor : ℝ := 976134837727 / 1000000000000
noncomputable def negativeCeiling : ℝ := 35936779 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7083132943180552445362176000, coefficient := (-7083132943180552445362176000) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 279913550905615350396616704, coefficient := (-279913550905615350396616704) }, { argument := 15725480387955918561607680, coefficient := (-15725480387955918561607680) }, { argument := 7998253222570386619856060416, coefficient := (-7998253222570386619856060416) }, { argument := 7998253222570386619856060416, coefficient := (-7998253222570386619856060416) }, { argument := 7082285199998215030780723200, coefficient := (-7082285199998215030780723200) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 24399480785354803634566594560, coefficient := (-24399480785354803634566594560) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 7082282917213635909223710720, coefficient := (-7082282917213635909223710720) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 202519253301842679346778603520, coefficient := (-202519253301842679346778603520) }, { argument := 202519253301842679346778603520, coefficient := (-202519253301842679346778603520) }, { argument := 17872759317182677718856105984, coefficient := (-17872759317182677718856105984) }, { argument := 7998253222570386619856060416, coefficient := (-7998253222570386619856060416) }, { argument := 7998253222570386619856060416, coefficient := (-7998253222570386619856060416) }, { argument := 17582617120475166716926623744, coefficient := (-17582617120475166716926623744) }, { argument := 7480019230554001783631380480, coefficient := (-7480019230554001783631380480) }, { argument := 355565861961187066720026624, coefficient := (-355565861961187066720026624) }, { argument := 19975610222538599253934080, coefficient := (-19975610222538599253934080) }, { argument := 25822675072046412349917102080, coefficient := (-25822675072046412349917102080) }, { argument := 540007329682626799831351296, coefficient := (-540007329682626799831351296) }, { argument := 7480016820948057155321200640, coefficient := (-7480016820948057155321200640) }, { argument := 540007329682626799831351296, coefficient := (-540007329682626799831351296) }, { argument := 540007329682626799831351296, coefficient := (-540007329682626799831351296) }, { argument := 355565861961187066720026624, coefficient := (-355565861961187066720026624) }, { argument := 19975610222538599253934080, coefficient := (-19975610222538599253934080) }, { argument := 210275721360490140131693428736, coefficient := (-210275721360490140131693428736) }, { argument := 210275721360490140131693428736, coefficient := (-210275721360490140131693428736) }, { argument := 17872759317182677718856105984, coefficient := (-17872759317182677718856105984) }, { argument := 203795878967355727755268325376, coefficient := (-203795878967355727755268325376) }, { argument := 203795878967355727755268325376, coefficient := (-203795878967355727755268325376) }, { argument := 529857679627256591723620466688, coefficient := (-529857679627256591723620466688) }, { argument := 17582617120475166716926623744, coefficient := (-17582617120475166716926623744) }, { argument := 137988298036856388397448560640, coefficient := (-137988298036856388397448560640) }, { argument := 137988258433288884611316711424, coefficient := (-137988258433288884611316711424) }, { argument := 100035589258561527633999298560, coefficient := (-100035589258561527633999298560) }, { argument := 20890238162940792138922721280, coefficient := (-20890238162940792138922721280) }, { argument := 5384504380794432911532433952735232, coefficient := 5384504380794432911532433952735232 }, { argument := 37428343375268919248903208960, coefficient := 37428343375268919248903208960 }, { argument := 29110933736320270526924718080, coefficient := 29110933736320270526924718080 }, { argument := 33269638555794594887913963520, coefficient := 33269638555794594887913963520 }, { argument := 39091825303058648993298907136, coefficient := 39091825303058648993298907136 }, { argument := 461616234961650004069806243840, coefficient := 461616234961650004069806243840 }, { argument := 1038012722940791360502915661824, coefficient := 1038012722940791360502915661824 }, { argument := 29110933736320270526924718080, coefficient := 29110933736320270526924718080 }, { argument := 461616234961650004069806243840, coefficient := 461616234961650004069806243840 }, { argument := 33269638555794594887913963520, coefficient := 33269638555794594887913963520 }, { argument := 32437897591899730015716114432, coefficient := 32437897591899730015716114432 }, { argument := 32437897591899730015716114432, coefficient := 32437897591899730015716114432 }, { argument := 32437897591899730015716114432, coefficient := 32437897591899730015716114432 }, { argument := 1038012722940791360502915661824, coefficient := 1038012722940791360502915661824 }, { argument := 32437897591899730015716114432, coefficient := 32437897591899730015716114432 }, { argument := 37428343375268919248903208960, coefficient := 37428343375268919248903208960 }, { argument := 39091825303058648993298907136, coefficient := 39091825303058648993298907136 }, { argument := 3406810988113366516522389864448, coefficient := (-3406810988113366516522389864448) }, { argument := 21857378818632495478687662080, coefficient := 21857378818632495478687662080 }, { argument := 367203964153025924041952722944, coefficient := 367203964153025924041952722944 }] }

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


end Parent2

namespace Parent2

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 181845832459393746755183543591108608
def positiveArguments : Array ℕ := #[
    10283, 339, 339, 791, 10283, 10283,
    339, 126899, 5085, 2373, 10283, 791,
    5085, 791, 10283, 10283, 339, 7,
    133, 203, 2093, 63, 203, 63,
    63, 5397, 63, 2093, 5397, 7,
    63, 63, 133, 45, 801, 45,
    1425, 2433, 45, 2433, 2433, 801,
    45, 199, 50247769615, 50247754225, 42339229341, 593730277371,
    169356916113, 12259696107, 141, 226512461521, 3489, 111,
    453007157681, 57, 57, 1929
  ]
def positiveCoefficients : Array ℕ := #[
    795608588998222835424230899712, 26228854582358994574425194496, 419661673317743913190803111936, 30600330346085493670162726912, 795608588998222835424230899712, 795608588998222835424230899712,
    419661673317743913190803111936, 9818334565329716969026497806336, 786865637470769837232755834880, 367203964153025924041952722944, 795608588998222835424230899712, 30600330346085493670162726912,
    786865637470769837232755834880, 30600330346085493670162726912, 795608588998222835424230899712, 795608588998222835424230899712, 26228854582358994574425194496, 69324642199981295394350956544,
    82323012612477788280791760896, 62825456993733048951130554368, 647752125556075228840966750208, 77990222474978957318644826112, 62825456993733048951130554368, 77990222474978957318644826112,
    77990222474978957318644826112, 3340581196011598671815286718464, 77990222474978957318644826112, 647752125556075228840966750208, 3340581196011598671815286718464, 69324642199981295394350956544,
    77990222474978957318644826112, 77990222474978957318644826112, 82323012612477788280791760896, 3481706360490132023153786880, 61974373216724350012137406464, 3481706360490132023153786880,
    55127017374427090366601625600, 94122128611916569025924038656, 3481706360490132023153786880, 94122128611916569025924038656, 94122128611916569025924038656, 61974373216724350012137406464,
    3481706360490132023153786880, 31532808680677206362230492233728, 474576766137663553549168101294080, 474576620783223210821488423731200, 799765430201877826039911593017344, 2803811961721708172764088648073216,
    799765424294197355969985430683648, 57894777985864271614820034281472, 5454673298101206836274266112, 2139349712478141234252474044383232, 134974149908334118097595138048, 4294104511271162828556337152,
    2139265817932798754689310812798976, 4410161389954167229328130048, 4410161389954167229328130048, 74624572993171829696262832128
  ]
def positiveScales : Array ℕ := #[
    13, 8, 8, 9, 13, 13,
    8, 16, 12, 11, 13, 9,
    12, 9, 13, 13, 8, 2,
    7, 7, 11, 5, 7, 5,
    5, 12, 5, 11, 12, 2,
    5, 5, 7, 5, 9, 5,
    10, 11, 5, 11, 11, 9,
    5, 7, 35, 35, 35, 39,
    37, 33, 7, 37, 11, 6,
    38, 5, 5, 10
  ]
def negativeArguments : Array ℕ := #[
    113, 7, 3, 199, 2995, 27789
  ]
def negativeCoefficients : Array ℕ := #[
    17905564728223740296140932775936, 8873554201597605810476922437632, 475368975085586025561263702016, 31532808680677206362230492233728, 949153386920886764370656525025280, 4403342816217783354773985671774208
  ]
def negativeScales : Array ℕ := #[
    6, 2, 1, 7, 11, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13327973602613883, 8405141463136342, 8405141463136342, 9627533884472051, 13327973602613883, 13327973602613883,
    8405141463136342, 16953321174135312, 12312032058744862, 11212496385193947, 13327973602613883, 9627533884472051,
    12312032058744862, 9627533884472051, 13327973602613883, 13327973602613883, 8405141463136342, 2807354922011143,
    7055282435501189, 7665335917183229, 11031356596255709, 5977279922488012, 7665335917183229, 5977279922488012,
    5977279922488012, 12397941971972637, 5977279922488012, 11031356596255709, 12397941971972637, 2807354922011143,
    5977279922488012, 5977279922488012, 7055282435501189, 5491853096329661, 9645658432407524, 5491853096329661,
    10476746203939458, 11248520604938428, 5491853096329661, 11248520604938428, 11248520604938428, 9645658432407524,
    5491853096329661, 7636624620542709, 35548340508612028, 35548340066740075, 35301275958511138, 39111016729209176,
    37301275947854286, 33513204166861683, 7139551352398793, 37720799465680884, 11768597882173550, 6794415866314396,
    38720742889321705, 5832890014087662, 5832890014087662, 10913637427705176
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6820178963384638, 2807354922807594, 1584962500724866, 7636624620558753, 11548340287677413, 14762226299267708
  ]

abbrev PositiveTerm := Fin 58
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 4424230548709 / 1000000000000
noncomputable def negativeCeiling : ℝ := 919064331511 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 795608588998222835424230899712, coefficient := 795608588998222835424230899712 }, { argument := 26228854582358994574425194496, coefficient := 26228854582358994574425194496 }, { argument := 419661673317743913190803111936, coefficient := 419661673317743913190803111936 }, { argument := 30600330346085493670162726912, coefficient := 30600330346085493670162726912 }, { argument := 795608588998222835424230899712, coefficient := 795608588998222835424230899712 }, { argument := 795608588998222835424230899712, coefficient := 795608588998222835424230899712 }, { argument := 419661673317743913190803111936, coefficient := 419661673317743913190803111936 }, { argument := 9818334565329716969026497806336, coefficient := 9818334565329716969026497806336 }, { argument := 786865637470769837232755834880, coefficient := 786865637470769837232755834880 }, { argument := 367203964153025924041952722944, coefficient := 367203964153025924041952722944 }, { argument := 795608588998222835424230899712, coefficient := 795608588998222835424230899712 }, { argument := 30600330346085493670162726912, coefficient := 30600330346085493670162726912 }, { argument := 786865637470769837232755834880, coefficient := 786865637470769837232755834880 }, { argument := 30600330346085493670162726912, coefficient := 30600330346085493670162726912 }, { argument := 795608588998222835424230899712, coefficient := 795608588998222835424230899712 }, { argument := 795608588998222835424230899712, coefficient := 795608588998222835424230899712 }, { argument := 26228854582358994574425194496, coefficient := 26228854582358994574425194496 }, { argument := 17905564728223740296140932775936, coefficient := (-17905564728223740296140932775936) }, { argument := 69324642199981295394350956544, coefficient := 69324642199981295394350956544 }, { argument := 82323012612477788280791760896, coefficient := 82323012612477788280791760896 }, { argument := 62825456993733048951130554368, coefficient := 62825456993733048951130554368 }, { argument := 647752125556075228840966750208, coefficient := 647752125556075228840966750208 }, { argument := 77990222474978957318644826112, coefficient := 77990222474978957318644826112 }, { argument := 62825456993733048951130554368, coefficient := 62825456993733048951130554368 }, { argument := 77990222474978957318644826112, coefficient := 77990222474978957318644826112 }, { argument := 77990222474978957318644826112, coefficient := 77990222474978957318644826112 }, { argument := 3340581196011598671815286718464, coefficient := 3340581196011598671815286718464 }, { argument := 77990222474978957318644826112, coefficient := 77990222474978957318644826112 }, { argument := 647752125556075228840966750208, coefficient := 647752125556075228840966750208 }, { argument := 3340581196011598671815286718464, coefficient := 3340581196011598671815286718464 }, { argument := 69324642199981295394350956544, coefficient := 69324642199981295394350956544 }, { argument := 77990222474978957318644826112, coefficient := 77990222474978957318644826112 }, { argument := 77990222474978957318644826112, coefficient := 77990222474978957318644826112 }, { argument := 82323012612477788280791760896, coefficient := 82323012612477788280791760896 }, { argument := 8873554201597605810476922437632, coefficient := (-8873554201597605810476922437632) }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 61974373216724350012137406464, coefficient := 61974373216724350012137406464 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 55127017374427090366601625600, coefficient := 55127017374427090366601625600 }, { argument := 94122128611916569025924038656, coefficient := 94122128611916569025924038656 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 94122128611916569025924038656, coefficient := 94122128611916569025924038656 }, { argument := 94122128611916569025924038656, coefficient := 94122128611916569025924038656 }, { argument := 61974373216724350012137406464, coefficient := 61974373216724350012137406464 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 31532808680677206362230492233728, coefficient := 31532808680677206362230492233728 }, { argument := 31532808680677206362230492233728, coefficient := (-31532808680677206362230492233728) }, { argument := 474576766137663553549168101294080, coefficient := 474576766137663553549168101294080 }, { argument := 474576620783223210821488423731200, coefficient := 474576620783223210821488423731200 }, { argument := 949153386920886764370656525025280, coefficient := (-949153386920886764370656525025280) }, { argument := 799765430201877826039911593017344, coefficient := 799765430201877826039911593017344 }, { argument := 2803811961721708172764088648073216, coefficient := 2803811961721708172764088648073216 }, { argument := 799765424294197355969985430683648, coefficient := 799765424294197355969985430683648 }, { argument := 4403342816217783354773985671774208, coefficient := (-4403342816217783354773985671774208) }, { argument := 57894777985864271614820034281472, coefficient := 57894777985864271614820034281472 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 2139349712478141234252474044383232, coefficient := 2139349712478141234252474044383232 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 2139265817932798754689310812798976, coefficient := 2139265817932798754689310812798976 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15
