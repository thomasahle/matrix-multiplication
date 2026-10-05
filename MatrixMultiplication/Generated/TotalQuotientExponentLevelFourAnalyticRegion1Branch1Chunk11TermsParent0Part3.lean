import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 11, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent0

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-974835627009310168960392469938176)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    17092736547, 337018185177, 674036159923, 2136597775, 569062438813601, 2104765187957807,
    35560555665859, 494937999, 9755947233, 19511888347, 123734837, 160811452749,
    577428049521, 80417362977, 21516779525, 21516779515, 1401, 82503,
    18187, 5085, 22831, 5085, 144977, 148195,
    22831, 1138807, 9113, 82503, 144977, 5085,
    9113, 5085, 144977, 74305, 1401, 158631,
    4678485, 4123653, 290447, 647555, 290447, 8220491,
    4191067, 647555, 128871791, 8249565, 4678485, 8220491,
    290447, 8249565, 290447, 8220491, 2102049, 158631,
    500669627, 9870521945, 19741037715, 977873, 1401, 82503,
    18187, 5085, 22831, 5085
  ]
def negativeCoefficients : Array ℕ := #[
    78826334150462728692446527488, 3108444105073086501917363798016, 3108443134631385958223699771392, 78826544687764527957986508800, 1281414693695739571728755458048, 4739509858094585790007802331136,
    1281204041966802981332568768512, 4564997299953456992005128192, 179965461803765848133785878528, 179965405365952354619412709376, 4565009742282334709097693184, 185402982061389958302897537024,
    665729215655948265293397098496, 185429814239915581896973615104, 99228631297027192752019865600, 99228631250910332567745986560, 52928283540002983555104768, 779218803872388678131122176,
    1374170867583203800023826432, 48026467130784291823288320, 862530793363174958991147008, 48026467130784291823288320, 1369269051173985108292009984, 1399662201857734144887357440,
    862530793363174958991147008, 21511456029029328227494002688, 1377117624268514458637172736, 779218803872388678131122176, 1369269051173985108292009984, 48026467130784291823288320,
    1377117624268514458637172736, 48026467130784291823288320, 1369269051173985108292009984, 1403581766038515950414725120, 52928283540002983555104768, 1498227435088189379787620352,
    22093520754608392087598530560, 38946801428369722188786302976, 1371597177850039843382362112, 24463936222517224850839306240, 1371597177850039843382362112, 38820171171131572652381044736,
    39583508656522070713658507264, 24463936222517224850839306240, 608579826405781998223581249536, 38957469254254524717324042240, 22093520754608392087598530560, 38820171171131572652381044736,
    1371597177850039843382362112, 38957469254254524717324042240, 1371597177850039843382362112, 38820171171131572652381044736, 39706582971798619407217852416, 1498227435088189379787620352,
    4617862237374310856959983616, 182078992193348826781838213120, 182078935239026499203597598720, 4617874679703188574052548608, 52928283540002983555104768, 779218803872388678131122176,
    1374170867583203800023826432, 48026467130784291823288320, 862530793363174958991147008, 48026467130784291823288320
  ]
def negativeScales : Array ℕ := #[
    33, 38, 39, 30, 49, 50,
    45, 28, 33, 34, 26, 37,
    39, 36, 34, 34, 10, 16,
    14, 12, 14, 12, 17, 17,
    14, 20, 13, 16, 17, 12,
    13, 12, 17, 16, 10, 17,
    22, 21, 18, 19, 18, 22,
    21, 19, 26, 22, 22, 22,
    18, 22, 18, 22, 21, 17,
    28, 33, 34, 19, 10, 16,
    14, 12, 14, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33992664360897859, 38294035483704729, 39294035033302020, 30992668214189043, 49015580285391945, 50902580720052877,
    45015343101294953, 28882672572052293, 33183634809035580, 34183634356601177, 26882676504247994, 37226579200500512,
    39070850234330996, 36226787977347376, 34324743110829666, 34324743110159168, 10452241240430869, 16332158959591929,
    14150619965305846, 12312032058744863, 14478706430677913, 12312032058744863, 17145464515243274, 17177137247337698,
    14478706430677913, 20119091835478221, 13153710352151716, 16332158959591929, 17145464515243274, 12312032058744863,
    13153710352151716, 12312032058744863, 17145464515243274, 16181171672850345, 10452241240430869, 17275315207496350,
    22157609997244880, 21975491522169910, 18147915402909608, 19304643207556371, 18147915402909608, 22970793150983731,
    21998886177711138, 19304643207556371, 26941361272001058, 22975886633336321, 22157609997244880, 22970793150983731,
    18147915402909608, 22975886633336321, 18147915402909608, 22970793150983731, 21003364869087187, 17275315207496350,
    28899283700746579, 33200479229200210, 34200478777925024, 19899287587926935, 10452241240430869, 16332158959591929,
    14150619965305846, 12312032058744863, 14478706430677913, 12312032058744863
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
noncomputable def negativeCeiling : ℝ := 169856911 / 20000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 78826334150462728692446527488, coefficient := (-78826334150462728692446527488) }, { argument := 3108444105073086501917363798016, coefficient := (-3108444105073086501917363798016) }, { argument := 3108443134631385958223699771392, coefficient := (-3108443134631385958223699771392) }, { argument := 78826544687764527957986508800, coefficient := (-78826544687764527957986508800) }, { argument := 1281414693695739571728755458048, coefficient := (-1281414693695739571728755458048) }, { argument := 4739509858094585790007802331136, coefficient := (-4739509858094585790007802331136) }, { argument := 1281204041966802981332568768512, coefficient := (-1281204041966802981332568768512) }, { argument := 4564997299953456992005128192, coefficient := (-4564997299953456992005128192) }, { argument := 179965461803765848133785878528, coefficient := (-179965461803765848133785878528) }, { argument := 179965405365952354619412709376, coefficient := (-179965405365952354619412709376) }, { argument := 4565009742282334709097693184, coefficient := (-4565009742282334709097693184) }, { argument := 185402982061389958302897537024, coefficient := (-185402982061389958302897537024) }, { argument := 665729215655948265293397098496, coefficient := (-665729215655948265293397098496) }, { argument := 185429814239915581896973615104, coefficient := (-185429814239915581896973615104) }, { argument := 99228631297027192752019865600, coefficient := (-99228631297027192752019865600) }, { argument := 99228631250910332567745986560, coefficient := (-99228631250910332567745986560) }, { argument := 52928283540002983555104768, coefficient := (-52928283540002983555104768) }, { argument := 779218803872388678131122176, coefficient := (-779218803872388678131122176) }, { argument := 1374170867583203800023826432, coefficient := (-1374170867583203800023826432) }, { argument := 48026467130784291823288320, coefficient := (-48026467130784291823288320) }, { argument := 862530793363174958991147008, coefficient := (-862530793363174958991147008) }, { argument := 48026467130784291823288320, coefficient := (-48026467130784291823288320) }, { argument := 1369269051173985108292009984, coefficient := (-1369269051173985108292009984) }, { argument := 1399662201857734144887357440, coefficient := (-1399662201857734144887357440) }, { argument := 862530793363174958991147008, coefficient := (-862530793363174958991147008) }, { argument := 21511456029029328227494002688, coefficient := (-21511456029029328227494002688) }, { argument := 1377117624268514458637172736, coefficient := (-1377117624268514458637172736) }, { argument := 779218803872388678131122176, coefficient := (-779218803872388678131122176) }, { argument := 1369269051173985108292009984, coefficient := (-1369269051173985108292009984) }, { argument := 48026467130784291823288320, coefficient := (-48026467130784291823288320) }, { argument := 1377117624268514458637172736, coefficient := (-1377117624268514458637172736) }, { argument := 48026467130784291823288320, coefficient := (-48026467130784291823288320) }, { argument := 1369269051173985108292009984, coefficient := (-1369269051173985108292009984) }, { argument := 1403581766038515950414725120, coefficient := (-1403581766038515950414725120) }, { argument := 52928283540002983555104768, coefficient := (-52928283540002983555104768) }, { argument := 1498227435088189379787620352, coefficient := (-1498227435088189379787620352) }, { argument := 22093520754608392087598530560, coefficient := (-22093520754608392087598530560) }, { argument := 38946801428369722188786302976, coefficient := (-38946801428369722188786302976) }, { argument := 1371597177850039843382362112, coefficient := (-1371597177850039843382362112) }, { argument := 24463936222517224850839306240, coefficient := (-24463936222517224850839306240) }, { argument := 1371597177850039843382362112, coefficient := (-1371597177850039843382362112) }, { argument := 38820171171131572652381044736, coefficient := (-38820171171131572652381044736) }, { argument := 39583508656522070713658507264, coefficient := (-39583508656522070713658507264) }, { argument := 24463936222517224850839306240, coefficient := (-24463936222517224850839306240) }, { argument := 608579826405781998223581249536, coefficient := (-608579826405781998223581249536) }, { argument := 38957469254254524717324042240, coefficient := (-38957469254254524717324042240) }, { argument := 22093520754608392087598530560, coefficient := (-22093520754608392087598530560) }, { argument := 38820171171131572652381044736, coefficient := (-38820171171131572652381044736) }, { argument := 1371597177850039843382362112, coefficient := (-1371597177850039843382362112) }, { argument := 38957469254254524717324042240, coefficient := (-38957469254254524717324042240) }, { argument := 1371597177850039843382362112, coefficient := (-1371597177850039843382362112) }, { argument := 38820171171131572652381044736, coefficient := (-38820171171131572652381044736) }, { argument := 39706582971798619407217852416, coefficient := (-39706582971798619407217852416) }, { argument := 1498227435088189379787620352, coefficient := (-1498227435088189379787620352) }, { argument := 4617862237374310856959983616, coefficient := (-4617862237374310856959983616) }, { argument := 182078992193348826781838213120, coefficient := (-182078992193348826781838213120) }, { argument := 182078935239026499203597598720, coefficient := (-182078935239026499203597598720) }, { argument := 4617874679703188574052548608, coefficient := (-4617874679703188574052548608) }, { argument := 52928283540002983555104768, coefficient := (-52928283540002983555104768) }, { argument := 779218803872388678131122176, coefficient := (-779218803872388678131122176) }, { argument := 1374170867583203800023826432, coefficient := (-1374170867583203800023826432) }, { argument := 48026467130784291823288320, coefficient := (-48026467130784291823288320) }, { argument := 862530793363174958991147008, coefficient := (-862530793363174958991147008) }, { argument := 48026467130784291823288320, coefficient := (-48026467130784291823288320) }] }

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
def constantNumerator : ℤ := (-561395880538913281908495678963712)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    144977, 148195, 22831, 1138807, 9113, 82503,
    144977, 5085, 9113, 5085, 144977, 74305,
    1401, 986451477, 19450692159, 38901372181, 123306763, 7907137543,
    28392551095, 3954137761, 39549, 2331939, 513895, 144529,
    645483, 144529, 4097493, 4180463, 645483, 32133747,
    257129, 2331939, 4097493, 144529, 257129, 144529,
    4097493, 2096581, 39549, 974988221, 19221542735, 38443073445,
    1904279, 80841, 2384229, 2101479, 148015, 82501,
    148015, 4189291, 66745, 82501, 65675257, 4204119,
    2384229, 4189291, 148015, 4204119, 148015, 4189291,
    133905, 80841, 30462839283, 600513452481
  ]
def negativeCoefficients : Array ℕ := #[
    1369269051173985108292009984, 1399662201857734144887357440, 862530793363174958991147008, 21511456029029328227494002688, 1377117624268514458637172736, 779218803872388678131122176,
    1369269051173985108292009984, 48026467130784291823288320, 1377117624268514458637172736, 48026467130784291823288320, 1369269051173985108292009984, 1403581766038515950414725120,
    52928283540002983555104768, 4549204484337946015152734208, 179400970156791046830368489472, 179400914184757841177161498624, 4549216599237116423900758016, 9116308913208847178785619968,
    32734382728074180652926238720, 9117620913669738173900521472, 1494118976248092788451704832, 22024541147393115179962073088, 38828808379428741233476894720, 1365037810805333906180538368,
    24385658275697177611777081344, 1365037810805333906180538368, 38699727213985982351205728256, 39483356708153371277966442496, 24385658275697177611777081344, 606989319207252053106672795648,
    38856235883961248132878041088, 22024541147393115179962073088, 38699727213985982351205728256, 1365037810805333906180538368, 38856235883961248132878041088, 1365037810805333906180538368,
    38699727213985982351205728256, 39603295372085294527103893504, 1494118976248092788451704832, 4496339546917092150197878784, 177287439767208068182316154880, 177287384311683696592976609280,
    4496351661816262558945902592, 1527043315366659954881593344, 22518406234171622676410400768, 39695815976217676616130625536, 1397962149923901072610426880, 24934397261006630385608556544,
    1397962149923901072610426880, 39566734810774917733859459072, 40344876915089212132881858560, 24934397261006630385608556544, 620285264821300093816609439744, 39706781311190899932316827648,
    22518406234171622676410400768, 39566734810774917733859459072, 1397962149923901072610426880, 39706781311190899932316827648, 1397962149923901072610426880, 39566734810774917733859459072,
    40470302968874229909757624320, 1527043315366659954881593344, 140485050003011694125050232832, 5538758985368374592875316379648
  ]
def negativeScales : Array ℕ := #[
    17, 17, 14, 20, 13, 16,
    17, 12, 13, 12, 17, 16,
    10, 29, 34, 35, 26, 32,
    34, 31, 15, 21, 18, 17,
    19, 17, 21, 21, 19, 24,
    17, 21, 21, 17, 17, 17,
    21, 20, 15, 29, 34, 35,
    20, 16, 21, 21, 17, 16,
    17, 21, 16, 16, 25, 22,
    21, 21, 17, 22, 17, 21,
    17, 16, 34, 39
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    17145464515243274, 17177137247337698, 14478706430677913, 20119091835478221, 13153710352151716, 16332158959591929,
    17145464515243274, 12312032058744863, 13153710352151716, 12312032058744863, 17145464515243274, 16181171672850345,
    10452241240430869, 29877672849336307, 34179102443755493, 35179101993643170, 26877676691344878, 32880508377298916,
    34724793431271525, 31880715992079339, 15271353596035632, 21153098619634233, 18971114104607005, 17140999475525776,
    19300019574402030, 17140999475525776, 21966310067699619, 21995231325629272, 19300019574402030, 24937585890719630,
    17972132821569416, 21153098619634233, 21966310067699619, 17140999475525776, 17972132821569416, 17140999475525776,
    21966310067699619, 20999607161668485, 15271353596035632, 29860809550746122, 34162005081385575, 35162004630110388,
    20860813437926332, 16302799547458561, 21185091379494154, 21002973609089230, 17175383861973769, 16332123986014538,
    17175383861973769, 21998274693720106, 16026372145257723, 16332123986014538, 25968846619406991, 22003372075512963,
    21185091379494154, 21998274693720106, 17175383861973769, 22003372075512963, 17175383861973769, 21998274693720106,
    17030850306200810, 16302799547458561, 34826331364170652, 39127405608776394
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
noncomputable def negativeCeiling : ℝ := 715610539 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1369269051173985108292009984, coefficient := (-1369269051173985108292009984) }, { argument := 1399662201857734144887357440, coefficient := (-1399662201857734144887357440) }, { argument := 862530793363174958991147008, coefficient := (-862530793363174958991147008) }, { argument := 21511456029029328227494002688, coefficient := (-21511456029029328227494002688) }, { argument := 1377117624268514458637172736, coefficient := (-1377117624268514458637172736) }, { argument := 779218803872388678131122176, coefficient := (-779218803872388678131122176) }, { argument := 1369269051173985108292009984, coefficient := (-1369269051173985108292009984) }, { argument := 48026467130784291823288320, coefficient := (-48026467130784291823288320) }, { argument := 1377117624268514458637172736, coefficient := (-1377117624268514458637172736) }, { argument := 48026467130784291823288320, coefficient := (-48026467130784291823288320) }, { argument := 1369269051173985108292009984, coefficient := (-1369269051173985108292009984) }, { argument := 1403581766038515950414725120, coefficient := (-1403581766038515950414725120) }, { argument := 52928283540002983555104768, coefficient := (-52928283540002983555104768) }, { argument := 4549204484337946015152734208, coefficient := (-4549204484337946015152734208) }, { argument := 179400970156791046830368489472, coefficient := (-179400970156791046830368489472) }, { argument := 179400914184757841177161498624, coefficient := (-179400914184757841177161498624) }, { argument := 4549216599237116423900758016, coefficient := (-4549216599237116423900758016) }, { argument := 9116308913208847178785619968, coefficient := (-9116308913208847178785619968) }, { argument := 32734382728074180652926238720, coefficient := (-32734382728074180652926238720) }, { argument := 9117620913669738173900521472, coefficient := (-9117620913669738173900521472) }, { argument := 1494118976248092788451704832, coefficient := (-1494118976248092788451704832) }, { argument := 22024541147393115179962073088, coefficient := (-22024541147393115179962073088) }, { argument := 38828808379428741233476894720, coefficient := (-38828808379428741233476894720) }, { argument := 1365037810805333906180538368, coefficient := (-1365037810805333906180538368) }, { argument := 24385658275697177611777081344, coefficient := (-24385658275697177611777081344) }, { argument := 1365037810805333906180538368, coefficient := (-1365037810805333906180538368) }, { argument := 38699727213985982351205728256, coefficient := (-38699727213985982351205728256) }, { argument := 39483356708153371277966442496, coefficient := (-39483356708153371277966442496) }, { argument := 24385658275697177611777081344, coefficient := (-24385658275697177611777081344) }, { argument := 606989319207252053106672795648, coefficient := (-606989319207252053106672795648) }, { argument := 38856235883961248132878041088, coefficient := (-38856235883961248132878041088) }, { argument := 22024541147393115179962073088, coefficient := (-22024541147393115179962073088) }, { argument := 38699727213985982351205728256, coefficient := (-38699727213985982351205728256) }, { argument := 1365037810805333906180538368, coefficient := (-1365037810805333906180538368) }, { argument := 38856235883961248132878041088, coefficient := (-38856235883961248132878041088) }, { argument := 1365037810805333906180538368, coefficient := (-1365037810805333906180538368) }, { argument := 38699727213985982351205728256, coefficient := (-38699727213985982351205728256) }, { argument := 39603295372085294527103893504, coefficient := (-39603295372085294527103893504) }, { argument := 1494118976248092788451704832, coefficient := (-1494118976248092788451704832) }, { argument := 4496339546917092150197878784, coefficient := (-4496339546917092150197878784) }, { argument := 177287439767208068182316154880, coefficient := (-177287439767208068182316154880) }, { argument := 177287384311683696592976609280, coefficient := (-177287384311683696592976609280) }, { argument := 4496351661816262558945902592, coefficient := (-4496351661816262558945902592) }, { argument := 1527043315366659954881593344, coefficient := (-1527043315366659954881593344) }, { argument := 22518406234171622676410400768, coefficient := (-22518406234171622676410400768) }, { argument := 39695815976217676616130625536, coefficient := (-39695815976217676616130625536) }, { argument := 1397962149923901072610426880, coefficient := (-1397962149923901072610426880) }, { argument := 24934397261006630385608556544, coefficient := (-24934397261006630385608556544) }, { argument := 1397962149923901072610426880, coefficient := (-1397962149923901072610426880) }, { argument := 39566734810774917733859459072, coefficient := (-39566734810774917733859459072) }, { argument := 40344876915089212132881858560, coefficient := (-40344876915089212132881858560) }, { argument := 24934397261006630385608556544, coefficient := (-24934397261006630385608556544) }, { argument := 620285264821300093816609439744, coefficient := (-620285264821300093816609439744) }, { argument := 39706781311190899932316827648, coefficient := (-39706781311190899932316827648) }, { argument := 22518406234171622676410400768, coefficient := (-22518406234171622676410400768) }, { argument := 39566734810774917733859459072, coefficient := (-39566734810774917733859459072) }, { argument := 1397962149923901072610426880, coefficient := (-1397962149923901072610426880) }, { argument := 39706781311190899932316827648, coefficient := (-39706781311190899932316827648) }, { argument := 1397962149923901072610426880, coefficient := (-1397962149923901072610426880) }, { argument := 39566734810774917733859459072, coefficient := (-39566734810774917733859459072) }, { argument := 40470302968874229909757624320, coefficient := (-40470302968874229909757624320) }, { argument := 1527043315366659954881593344, coefficient := (-1527043315366659954881593344) }, { argument := 140485050003011694125050232832, coefficient := (-140485050003011694125050232832) }, { argument := 5538758985368374592875316379648, coefficient := (-5538758985368374592875316379648) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
