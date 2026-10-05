import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 17, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17

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
def constantNumerator : ℤ := (-86392596446938975104984579196321792)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    6469444845, 13657716895, 98753253405758879, 33751842999, 1896170955, 176165907481268525,
    102519642967, 98753250132254727, 102519642967, 102519642967, 33751842999, 1896170955,
    2834846445, 49606278855, 49606303185, 2834822115, 127742800653, 216506797299,
    127742800653, 4492572662833941, 2705, 4492571353930987, 2705, 3845101023,
    6516927009, 3845101023, 85057707, 82773, 85057707, 82773,
    16113319, 1351266343073949, 8058292065, 49301118845532003, 126812069865, 3817085715,
    24649465677984657, 3817085715, 3817085715, 326997009585, 3817085715, 126812069865,
    326997009585, 676726916779119, 3817085715, 3817085715, 8058292065, 197497757749144831,
    33751859553, 1896171885, 88078976308591955, 102519693249, 197497751202134121, 102519693249,
    102519693249, 33751859553, 1896171885, 175673654669641119, 2705, 175673602426108513,
    2705, 3845101023, 6516927009, 3845101023
  ]
def negativeCoefficients : Array ℕ := #[
    238680386709389117458785239040, 251940408193244068428717752320, 111186278809949963122539543658496, 155652902454644617417479684096, 8744545081721607720083128320, 396690357644013101367510119219200,
    236394202042540795366247235584, 111186275124311943336796669083648, 236394202042540795366247235584, 236394202042540795366247235584, 155652902454644617417479684096, 8744545081721607720083128320,
    6536710857397542545145200640, 228768582621813672935077969920, 228768694824134501273425674240, 6536654756237128375971348480, 589109687726197097576175501312, 1996922739996581703362744942592,
    589109687726197097576175501312, 10116374285136906825914665402368, 817536085514392979395051520, 10116371337749478876643931979776, 817536085514392979395051520, 70929594508839784323552903168,
    240432169364136927495179993088, 70929594508839784323552903168, 803347329293093603561013510144, 781768881773138286546518016, 803347329293093603561013510144, 781768881773138286546518016,
    76092997573386628745106817024, 3042781299573064762430274404352, 74324625697129727450960363520, 111016250230843233327578552991744, 584817449564257592311503912960, 70412803292017636532488765440,
    111011324442253531812753542479872, 70412803292017636532488765440, 70412803292017636532488765440, 3016015074341422098141602119680, 70412803292017636532488765440, 584817449564257592311503912960,
    3016015074341422098141602119680, 3047707090238024985547609473024, 70412803292017636532488765440, 70412803292017636532488765440, 74324625697129727450960363520, 111181353525694643714450650038272,
    155652978796494966464459046912, 8744549370589604857553879040, 396672444882549473839628869959680, 236394317984938984649206530048, 111181349840055269471119843786752, 236394317984938984649206530048,
    236394317984938984649206530048, 155652978796494966464459046912, 8744549370589604857553879040, 98895475713626117264093246128128, 25548002672324780606095360, 98895446303131870151598518829056,
    25548002672324780606095360, 70929594508839784323552903168, 240432169364136927495179993088, 70929594508839784323552903168
  ]
def negativeScales : Array ℕ := #[
    32, 33, 56, 34, 30, 57,
    36, 56, 36, 36, 34, 30,
    31, 35, 35, 31, 36, 37,
    36, 51, 11, 51, 11, 31,
    32, 31, 26, 16, 26, 16,
    23, 50, 32, 55, 36, 31,
    54, 31, 31, 38, 31, 36,
    38, 49, 31, 31, 32, 57,
    34, 30, 56, 36, 57, 36,
    36, 34, 30, 57, 11, 57,
    11, 31, 32, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32590994771196291, 33668997283227462, 56454677796451285, 34974247246287961, 30820441895574738, 57289712366704021,
    36577109403211935, 56454677748628372, 36577109403211935, 36577109403211935, 34974247246287961, 30820441895574738,
    31400623444872721, 35529803688431328, 35529804396018403, 31400611062924827, 36894451033554533, 37655621363313161,
    36894451033554533, 51996463283748007, 11401412878714185, 51996462863421193, 11401412878714185, 31840374358285807,
    32601544690538703, 31840374358285807, 26341938627283391, 16336872626519468, 26341938627283391, 16336872626519468,
    23941750362331626, 50263233490246609, 32907826954528630, 55452469905867659, 36883901113524165, 31829824438677684,
    54452405892100158, 31829824438677684, 31829824438677684, 38250486485977868, 31829824438677684, 36883901113524165,
    38250486485977868, 49265567101234566, 31829824438677684, 31829824438677684, 32907826954528630, 57454613887121526,
    34974247953875217, 30820442603161826, 56289647219580777, 36577110110799009, 57454613839296477, 36577110110799009,
    36577110110799009, 34974247953875217, 30820442603161826, 57285675463353936, 11401412878714185, 57285675034311250,
    11401412878714185, 31840374358285807, 32601544690538703, 31840374358285807
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
noncomputable def negativeCeiling : ℝ := 115385666351 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 238680386709389117458785239040, coefficient := (-238680386709389117458785239040) }, { argument := 251940408193244068428717752320, coefficient := (-251940408193244068428717752320) }, { argument := 111186278809949963122539543658496, coefficient := (-111186278809949963122539543658496) }, { argument := 155652902454644617417479684096, coefficient := (-155652902454644617417479684096) }, { argument := 8744545081721607720083128320, coefficient := (-8744545081721607720083128320) }, { argument := 396690357644013101367510119219200, coefficient := (-396690357644013101367510119219200) }, { argument := 236394202042540795366247235584, coefficient := (-236394202042540795366247235584) }, { argument := 111186275124311943336796669083648, coefficient := (-111186275124311943336796669083648) }, { argument := 236394202042540795366247235584, coefficient := (-236394202042540795366247235584) }, { argument := 236394202042540795366247235584, coefficient := (-236394202042540795366247235584) }, { argument := 155652902454644617417479684096, coefficient := (-155652902454644617417479684096) }, { argument := 8744545081721607720083128320, coefficient := (-8744545081721607720083128320) }, { argument := 6536710857397542545145200640, coefficient := (-6536710857397542545145200640) }, { argument := 228768582621813672935077969920, coefficient := (-228768582621813672935077969920) }, { argument := 228768694824134501273425674240, coefficient := (-228768694824134501273425674240) }, { argument := 6536654756237128375971348480, coefficient := (-6536654756237128375971348480) }, { argument := 589109687726197097576175501312, coefficient := (-589109687726197097576175501312) }, { argument := 1996922739996581703362744942592, coefficient := (-1996922739996581703362744942592) }, { argument := 589109687726197097576175501312, coefficient := (-589109687726197097576175501312) }, { argument := 10116374285136906825914665402368, coefficient := (-10116374285136906825914665402368) }, { argument := 817536085514392979395051520, coefficient := (-817536085514392979395051520) }, { argument := 10116371337749478876643931979776, coefficient := (-10116371337749478876643931979776) }, { argument := 817536085514392979395051520, coefficient := (-817536085514392979395051520) }, { argument := 70929594508839784323552903168, coefficient := (-70929594508839784323552903168) }, { argument := 240432169364136927495179993088, coefficient := (-240432169364136927495179993088) }, { argument := 70929594508839784323552903168, coefficient := (-70929594508839784323552903168) }, { argument := 803347329293093603561013510144, coefficient := (-803347329293093603561013510144) }, { argument := 781768881773138286546518016, coefficient := (-781768881773138286546518016) }, { argument := 803347329293093603561013510144, coefficient := (-803347329293093603561013510144) }, { argument := 781768881773138286546518016, coefficient := (-781768881773138286546518016) }, { argument := 76092997573386628745106817024, coefficient := (-76092997573386628745106817024) }, { argument := 3042781299573064762430274404352, coefficient := (-3042781299573064762430274404352) }, { argument := 74324625697129727450960363520, coefficient := (-74324625697129727450960363520) }, { argument := 111016250230843233327578552991744, coefficient := (-111016250230843233327578552991744) }, { argument := 584817449564257592311503912960, coefficient := (-584817449564257592311503912960) }, { argument := 70412803292017636532488765440, coefficient := (-70412803292017636532488765440) }, { argument := 111011324442253531812753542479872, coefficient := (-111011324442253531812753542479872) }, { argument := 70412803292017636532488765440, coefficient := (-70412803292017636532488765440) }, { argument := 70412803292017636532488765440, coefficient := (-70412803292017636532488765440) }, { argument := 3016015074341422098141602119680, coefficient := (-3016015074341422098141602119680) }, { argument := 70412803292017636532488765440, coefficient := (-70412803292017636532488765440) }, { argument := 584817449564257592311503912960, coefficient := (-584817449564257592311503912960) }, { argument := 3016015074341422098141602119680, coefficient := (-3016015074341422098141602119680) }, { argument := 3047707090238024985547609473024, coefficient := (-3047707090238024985547609473024) }, { argument := 70412803292017636532488765440, coefficient := (-70412803292017636532488765440) }, { argument := 70412803292017636532488765440, coefficient := (-70412803292017636532488765440) }, { argument := 74324625697129727450960363520, coefficient := (-74324625697129727450960363520) }, { argument := 111181353525694643714450650038272, coefficient := (-111181353525694643714450650038272) }, { argument := 155652978796494966464459046912, coefficient := (-155652978796494966464459046912) }, { argument := 8744549370589604857553879040, coefficient := (-8744549370589604857553879040) }, { argument := 396672444882549473839628869959680, coefficient := (-396672444882549473839628869959680) }, { argument := 236394317984938984649206530048, coefficient := (-236394317984938984649206530048) }, { argument := 111181349840055269471119843786752, coefficient := (-111181349840055269471119843786752) }, { argument := 236394317984938984649206530048, coefficient := (-236394317984938984649206530048) }, { argument := 236394317984938984649206530048, coefficient := (-236394317984938984649206530048) }, { argument := 155652978796494966464459046912, coefficient := (-155652978796494966464459046912) }, { argument := 8744549370589604857553879040, coefficient := (-8744549370589604857553879040) }, { argument := 98895475713626117264093246128128, coefficient := (-98895475713626117264093246128128) }, { argument := 25548002672324780606095360, coefficient := (-25548002672324780606095360) }, { argument := 98895446303131870151598518829056, coefficient := (-98895446303131870151598518829056) }, { argument := 25548002672324780606095360, coefficient := (-25548002672324780606095360) }, { argument := 70929594508839784323552903168, coefficient := (-70929594508839784323552903168) }, { argument := 240432169364136927495179993088, coefficient := (-240432169364136927495179993088) }, { argument := 70929594508839784323552903168, coefficient := (-70929594508839784323552903168) }] }

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
def constantNumerator : ℤ := (-1884206927409345922390574036418560)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    44902455, 84937, 44902455, 84937, 513577305, 3271023,
    2705, 3271023, 2705, 2195, 1623, 2705,
    82773, 2705, 84937, 2705, 82773, 47067,
    84937, 1325991, 1623, 2705, 82773, 2705,
    1623, 2705, 41657, 47067, 1623, 2834846445,
    49606278855, 49606303185, 2834822115, 3845101023, 6516927009, 3845101023,
    2834846445, 49606278855, 49606303185, 2834822115, 329396987637, 558283413771,
    329396987637, 85057707, 82773, 85057707, 82773, 3845101023,
    6516927009, 3845101023, 85025829, 47067, 85025829, 47067,
    2569, 933297165, 16331536935, 16331544945, 933289155, 127742800653,
    216506797299, 127742800653, 44902455, 84937
  ]
def negativeCoefficients : Array ℕ := #[
    424091696981125030147900047360, 802207283910998111031394304, 424091696981125030147900047360, 802207283910998111031394304, 2425300251494521055156140769280, 30893938759791430991679062016,
    25548002672324780606095360, 30893938759791430991679062016, 25548002672324780606095360, 42457474784865776615680901120, 30657603206789736727314432, 817536085514392979395051520,
    781768881773138286546518016, 25548002672324780606095360, 802207283910998111031394304, 25548002672324780606095360, 781768881773138286546518016, 444535246498451182546059264,
    802207283910998111031394304, 12523630909973607453107945472, 490521651308635787637030912, 817536085514392979395051520, 781768881773138286546518016, 25548002672324780606095360,
    490521651308635787637030912, 25548002672324780606095360, 786878482307603242667737088, 444535246498451182546059264, 30657603206789736727314432, 6536710857397542545145200640,
    228768582621813672935077969920, 228768694824134501273425674240, 6536654756237128375971348480, 70929594508839784323552903168, 240432169364136927495179993088, 70929594508839784323552903168,
    6536710857397542545145200640, 228768582621813672935077969920, 228768694824134501273425674240, 6536654756237128375971348480, 3038150964795304095192182685696, 10298511254430531727710209703936,
    3038150964795304095192182685696, 803347329293093603561013510144, 781768881773138286546518016, 803347329293093603561013510144, 781768881773138286546518016, 70929594508839784323552903168,
    240432169364136927495179993088, 70929594508839784323552903168, 803046250095611766460769107968, 444535246498451182546059264, 803046250095611766460769107968, 444535246498451182546059264,
    49691686889439717597122658304, 4304073486868418889158492160, 150631841085139952339496468480, 150631914964349967546250690560, 4304036547263411285781381120, 589109687726197097576175501312,
    1996922739996581703362744942592, 589109687726197097576175501312, 424091696981125030147900047360, 802207283910998111031394304
  ]
def negativeScales : Array ℕ := #[
    25, 16, 25, 16, 28, 21,
    11, 21, 11, 11, 10, 11,
    16, 11, 16, 11, 16, 15,
    16, 20, 10, 11, 16, 11,
    10, 11, 15, 15, 10, 31,
    35, 35, 31, 31, 32, 31,
    31, 35, 35, 31, 38, 39,
    38, 26, 16, 26, 16, 31,
    32, 31, 26, 15, 26, 15,
    11, 29, 33, 33, 29, 36,
    37, 36, 25, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    25420290989345031, 16374105532718445, 25420290989345031, 16374105532718445, 28936006218434943, 21641310473020336,
    11401412878714185, 21641310473020336, 11401412878714185, 11100005224422721, 10664447284578613, 11401412878714185,
    16336872626519468, 11401412878714185, 16374105532718445, 11401412878714185, 16336872626519468, 15522428279676108,
    16374105532718445, 20338639552693656, 10664447284578613, 11401412878714185, 16336872626519468, 11401412878714185,
    10664447284578613, 11401412878714185, 15346271324521718, 15522428279676108, 10664447284578613, 31400623444872721,
    35529803688431328, 35529804396018403, 31400611062924827, 31840374358285807, 32601544690538703, 31840374358285807,
    31400623444872721, 35529803688431328, 35529804396018403, 31400611062924827, 38261036405318778, 39022206739005524,
    38261036405318778, 26341938627283391, 16336872626519468, 26341938627283391, 16336872626519468, 31840374358285807,
    32601544690538703, 31840374358285807, 26341397831458779, 15522428279676108, 26341397831458779, 15522428279676108,
    11326991174900818, 29797761272960163, 33926941522925424, 33926942230512585, 29797748891012112, 36894451033554533,
    37655621363313161, 36894451033554533, 25420290989345031, 16374105532718445
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
noncomputable def negativeCeiling : ℝ := 12175728013 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 424091696981125030147900047360, coefficient := (-424091696981125030147900047360) }, { argument := 802207283910998111031394304, coefficient := (-802207283910998111031394304) }, { argument := 424091696981125030147900047360, coefficient := (-424091696981125030147900047360) }, { argument := 802207283910998111031394304, coefficient := (-802207283910998111031394304) }, { argument := 2425300251494521055156140769280, coefficient := (-2425300251494521055156140769280) }, { argument := 30893938759791430991679062016, coefficient := (-30893938759791430991679062016) }, { argument := 25548002672324780606095360, coefficient := (-25548002672324780606095360) }, { argument := 30893938759791430991679062016, coefficient := (-30893938759791430991679062016) }, { argument := 25548002672324780606095360, coefficient := (-25548002672324780606095360) }, { argument := 42457474784865776615680901120, coefficient := (-42457474784865776615680901120) }, { argument := 30657603206789736727314432, coefficient := (-30657603206789736727314432) }, { argument := 817536085514392979395051520, coefficient := (-817536085514392979395051520) }, { argument := 781768881773138286546518016, coefficient := (-781768881773138286546518016) }, { argument := 25548002672324780606095360, coefficient := (-25548002672324780606095360) }, { argument := 802207283910998111031394304, coefficient := (-802207283910998111031394304) }, { argument := 25548002672324780606095360, coefficient := (-25548002672324780606095360) }, { argument := 781768881773138286546518016, coefficient := (-781768881773138286546518016) }, { argument := 444535246498451182546059264, coefficient := (-444535246498451182546059264) }, { argument := 802207283910998111031394304, coefficient := (-802207283910998111031394304) }, { argument := 12523630909973607453107945472, coefficient := (-12523630909973607453107945472) }, { argument := 490521651308635787637030912, coefficient := (-490521651308635787637030912) }, { argument := 817536085514392979395051520, coefficient := (-817536085514392979395051520) }, { argument := 781768881773138286546518016, coefficient := (-781768881773138286546518016) }, { argument := 25548002672324780606095360, coefficient := (-25548002672324780606095360) }, { argument := 490521651308635787637030912, coefficient := (-490521651308635787637030912) }, { argument := 25548002672324780606095360, coefficient := (-25548002672324780606095360) }, { argument := 786878482307603242667737088, coefficient := (-786878482307603242667737088) }, { argument := 444535246498451182546059264, coefficient := (-444535246498451182546059264) }, { argument := 30657603206789736727314432, coefficient := (-30657603206789736727314432) }, { argument := 6536710857397542545145200640, coefficient := (-6536710857397542545145200640) }, { argument := 228768582621813672935077969920, coefficient := (-228768582621813672935077969920) }, { argument := 228768694824134501273425674240, coefficient := (-228768694824134501273425674240) }, { argument := 6536654756237128375971348480, coefficient := (-6536654756237128375971348480) }, { argument := 70929594508839784323552903168, coefficient := (-70929594508839784323552903168) }, { argument := 240432169364136927495179993088, coefficient := (-240432169364136927495179993088) }, { argument := 70929594508839784323552903168, coefficient := (-70929594508839784323552903168) }, { argument := 6536710857397542545145200640, coefficient := (-6536710857397542545145200640) }, { argument := 228768582621813672935077969920, coefficient := (-228768582621813672935077969920) }, { argument := 228768694824134501273425674240, coefficient := (-228768694824134501273425674240) }, { argument := 6536654756237128375971348480, coefficient := (-6536654756237128375971348480) }, { argument := 3038150964795304095192182685696, coefficient := (-3038150964795304095192182685696) }, { argument := 10298511254430531727710209703936, coefficient := (-10298511254430531727710209703936) }, { argument := 3038150964795304095192182685696, coefficient := (-3038150964795304095192182685696) }, { argument := 803347329293093603561013510144, coefficient := (-803347329293093603561013510144) }, { argument := 781768881773138286546518016, coefficient := (-781768881773138286546518016) }, { argument := 803347329293093603561013510144, coefficient := (-803347329293093603561013510144) }, { argument := 781768881773138286546518016, coefficient := (-781768881773138286546518016) }, { argument := 70929594508839784323552903168, coefficient := (-70929594508839784323552903168) }, { argument := 240432169364136927495179993088, coefficient := (-240432169364136927495179993088) }, { argument := 70929594508839784323552903168, coefficient := (-70929594508839784323552903168) }, { argument := 803046250095611766460769107968, coefficient := (-803046250095611766460769107968) }, { argument := 444535246498451182546059264, coefficient := (-444535246498451182546059264) }, { argument := 803046250095611766460769107968, coefficient := (-803046250095611766460769107968) }, { argument := 444535246498451182546059264, coefficient := (-444535246498451182546059264) }, { argument := 49691686889439717597122658304, coefficient := (-49691686889439717597122658304) }, { argument := 4304073486868418889158492160, coefficient := (-4304073486868418889158492160) }, { argument := 150631841085139952339496468480, coefficient := (-150631841085139952339496468480) }, { argument := 150631914964349967546250690560, coefficient := (-150631914964349967546250690560) }, { argument := 4304036547263411285781381120, coefficient := (-4304036547263411285781381120) }, { argument := 589109687726197097576175501312, coefficient := (-589109687726197097576175501312) }, { argument := 1996922739996581703362744942592, coefficient := (-1996922739996581703362744942592) }, { argument := 589109687726197097576175501312, coefficient := (-589109687726197097576175501312) }, { argument := 424091696981125030147900047360, coefficient := (-424091696981125030147900047360) }, { argument := 802207283910998111031394304, coefficient := (-802207283910998111031394304) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17
