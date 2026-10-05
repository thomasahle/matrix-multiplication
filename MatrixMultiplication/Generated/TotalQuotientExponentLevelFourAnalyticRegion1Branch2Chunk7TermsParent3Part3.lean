import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 7, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 204232869219246321834615417746751488
def positiveArguments : Array ℕ := #[
    27027, 45, 35, 5
  ]
def positiveCoefficients : Array ℕ := #[
    2141299548273022252140712345731072, 1740853180245066011576893440, 1353996917968384675670917120, 1547425049106725343623905280
  ]
def positiveScales : Array ℕ := #[
    14, 5, 5, 2
  ]
def negativeArguments : Array ℕ := #[
    2643816735, 4537880289, 2643816735, 22762535, 19851, 22762535,
    10023, 4406361225, 7563133815, 4406361225, 19516455, 19851,
    19516455, 10023, 75, 774268929, 29091272703, 58178144937,
    1552938327, 67857962865, 116472260751, 67857962865, 22762535, 19851,
    22762535, 10023, 76670685315, 131598528381, 76670685315, 8053735,
    19851, 8053735, 10023, 2421, 19516455, 19851,
    19516455, 10023, 1617, 81360498554569, 10822305, 3531489,
    69477798463241, 35656647, 81360497120531, 71427213, 32011239, 10822305,
    3531489, 14895143808543, 22905, 14895050297825, 11565, 39,
    20173871, 23923, 20173871, 12079, 1503, 9
  ]
def negativeCoefficients : Array ℕ := #[
    780316971013366177467633500160, 2678691722506052396456783904768, 780316971013366177467633500160, 107493032349147199614337679360, 187487394102890654274158592, 107493032349147199614337679360,
    189329117031209815907500032, 40641508906946155076439244800, 139515193880523562315457495040, 40641508906946155076439244800, 92163852956433701679063367680, 187487394102890654274158592,
    92163852956433701679063367680, 189329117031209815907500032, 1450710983537555009647411200, 7141370388744095793395269632, 268319631165366849438455169024, 268299337584005026289232642048,
    7161663970105918942617796608, 1251758474333941576354328739840, 4297067971520125719316090847232, 1251758474333941576354328739840, 107493032349147199614337679360, 187487394102890654274158592,
    107493032349147199614337679360, 189329117031209815907500032, 707162254980863098330042859520, 2427564373521109984288960413696, 707162254980863098330042859520, 1217046023229253187044030545920,
    5999596611292500936773074944, 1217046023229253187044030545920, 6058531744998714109040001024, 46828950548592275711418433536, 92163852956433701679063367680, 187487394102890654274158592,
    92163852956433701679063367680, 189329117031209815907500032, 31277328805069686007998185472, 91603777743258681704559149056, 199636290622627249001594880, 8143059222765058840854528,
    312900187269574587230543937536, 164437260433900865624997888, 91603776128675431095776313344, 164699939763667480426315776, 147625783328837518340653056, 199636290622627249001594880,
    8143059222765058840854528, 134163528211568410827901894656, 216331608580258447239413760, 134162685941898930932835942400, 218456673497549787585576960, 1508739422879057210033307648,
    95268412240135932356870537216, 225946346739381044894498816, 95268412240135932356870537216, 228165858986329778144935936, 29072248110092602393334120448, 1392682544196052809261514752
  ]
def negativeScales : Array ℕ := #[
    31, 32, 31, 24, 14, 24,
    13, 32, 32, 32, 24, 14,
    24, 13, 6, 29, 34, 35,
    30, 35, 36, 35, 24, 14,
    24, 13, 36, 36, 36, 22,
    14, 22, 13, 11, 24, 14,
    24, 13, 10, 46, 23, 21,
    45, 25, 46, 26, 24, 23,
    21, 43, 14, 43, 13, 5,
    24, 14, 24, 13, 10, 3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14722113760991968, 5491853096329661, 5129283016944966, 2321928094887362
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    31299975029065533, 32079371404657144, 31299975029065533, 24440157899723957, 14276924064937944, 24440157899723957,
    13291026768056127, 32036940623231739, 32816336999721460, 32036940623231739, 24218187687482135, 14276924064937944,
    24218187687482135, 13291026768056127, 6228818690495881, 29528259507830139, 34759867362886475, 35759758244681241,
    30532353390023899, 35981799086698831, 36761195444917550, 35981799086698831, 24440157899723957, 14276924064937944,
    24440157899723957, 13291026768056127, 36157956024193105, 36937352408190777, 36157956024193105, 22941226580950274,
    14276924064937944, 22941226580950274, 13291026768056127, 11241387363998937, 24218187687482135, 14276924064937944,
    24218187687482135, 13291026768056127, 10659103963500476, 46209393753193275, 23367504470022377, 21751845172312424,
    45981617291367480, 25087667708624046, 46209393727764725, 26089970494493467, 24932075189589290, 23367504470022377,
    21751845172312424, 43759907286295581, 14483374942405524, 43759898229123986, 13497477645523802, 5285402218862249,
    24265984601740514, 14546110697754515, 24265984601740514, 13560213400873323, 10553629293917849, 3169925001442313
  ]

abbrev PositiveTerm := Fin 4
abbrev NegativeTerm := Fin 60
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
noncomputable def positiveFloor : ℝ := 23716379541 / 62500000000
noncomputable def negativeCeiling : ℝ := 8017538077 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 780316971013366177467633500160, coefficient := (-780316971013366177467633500160) }, { argument := 2678691722506052396456783904768, coefficient := (-2678691722506052396456783904768) }, { argument := 780316971013366177467633500160, coefficient := (-780316971013366177467633500160) }, { argument := 107493032349147199614337679360, coefficient := (-107493032349147199614337679360) }, { argument := 187487394102890654274158592, coefficient := (-187487394102890654274158592) }, { argument := 107493032349147199614337679360, coefficient := (-107493032349147199614337679360) }, { argument := 189329117031209815907500032, coefficient := (-189329117031209815907500032) }, { argument := 40641508906946155076439244800, coefficient := (-40641508906946155076439244800) }, { argument := 139515193880523562315457495040, coefficient := (-139515193880523562315457495040) }, { argument := 40641508906946155076439244800, coefficient := (-40641508906946155076439244800) }, { argument := 92163852956433701679063367680, coefficient := (-92163852956433701679063367680) }, { argument := 187487394102890654274158592, coefficient := (-187487394102890654274158592) }, { argument := 92163852956433701679063367680, coefficient := (-92163852956433701679063367680) }, { argument := 189329117031209815907500032, coefficient := (-189329117031209815907500032) }, { argument := 1450710983537555009647411200, coefficient := (-1450710983537555009647411200) }, { argument := 7141370388744095793395269632, coefficient := (-7141370388744095793395269632) }, { argument := 268319631165366849438455169024, coefficient := (-268319631165366849438455169024) }, { argument := 268299337584005026289232642048, coefficient := (-268299337584005026289232642048) }, { argument := 7161663970105918942617796608, coefficient := (-7161663970105918942617796608) }, { argument := 1251758474333941576354328739840, coefficient := (-1251758474333941576354328739840) }, { argument := 4297067971520125719316090847232, coefficient := (-4297067971520125719316090847232) }, { argument := 1251758474333941576354328739840, coefficient := (-1251758474333941576354328739840) }, { argument := 107493032349147199614337679360, coefficient := (-107493032349147199614337679360) }, { argument := 187487394102890654274158592, coefficient := (-187487394102890654274158592) }, { argument := 107493032349147199614337679360, coefficient := (-107493032349147199614337679360) }, { argument := 189329117031209815907500032, coefficient := (-189329117031209815907500032) }, { argument := 707162254980863098330042859520, coefficient := (-707162254980863098330042859520) }, { argument := 2427564373521109984288960413696, coefficient := (-2427564373521109984288960413696) }, { argument := 707162254980863098330042859520, coefficient := (-707162254980863098330042859520) }, { argument := 1217046023229253187044030545920, coefficient := (-1217046023229253187044030545920) }, { argument := 5999596611292500936773074944, coefficient := (-5999596611292500936773074944) }, { argument := 1217046023229253187044030545920, coefficient := (-1217046023229253187044030545920) }, { argument := 6058531744998714109040001024, coefficient := (-6058531744998714109040001024) }, { argument := 46828950548592275711418433536, coefficient := (-46828950548592275711418433536) }, { argument := 92163852956433701679063367680, coefficient := (-92163852956433701679063367680) }, { argument := 187487394102890654274158592, coefficient := (-187487394102890654274158592) }, { argument := 92163852956433701679063367680, coefficient := (-92163852956433701679063367680) }, { argument := 189329117031209815907500032, coefficient := (-189329117031209815907500032) }, { argument := 31277328805069686007998185472, coefficient := (-31277328805069686007998185472) }, { argument := 91603777743258681704559149056, coefficient := (-91603777743258681704559149056) }, { argument := 199636290622627249001594880, coefficient := (-199636290622627249001594880) }, { argument := 8143059222765058840854528, coefficient := (-8143059222765058840854528) }, { argument := 312900187269574587230543937536, coefficient := (-312900187269574587230543937536) }, { argument := 164437260433900865624997888, coefficient := (-164437260433900865624997888) }, { argument := 91603776128675431095776313344, coefficient := (-91603776128675431095776313344) }, { argument := 164699939763667480426315776, coefficient := (-164699939763667480426315776) }, { argument := 147625783328837518340653056, coefficient := (-147625783328837518340653056) }, { argument := 199636290622627249001594880, coefficient := (-199636290622627249001594880) }, { argument := 8143059222765058840854528, coefficient := (-8143059222765058840854528) }, { argument := 134163528211568410827901894656, coefficient := (-134163528211568410827901894656) }, { argument := 216331608580258447239413760, coefficient := (-216331608580258447239413760) }, { argument := 134162685941898930932835942400, coefficient := (-134162685941898930932835942400) }, { argument := 218456673497549787585576960, coefficient := (-218456673497549787585576960) }, { argument := 1508739422879057210033307648, coefficient := (-1508739422879057210033307648) }, { argument := 95268412240135932356870537216, coefficient := (-95268412240135932356870537216) }, { argument := 225946346739381044894498816, coefficient := (-225946346739381044894498816) }, { argument := 95268412240135932356870537216, coefficient := (-95268412240135932356870537216) }, { argument := 228165858986329778144935936, coefficient := (-228165858986329778144935936) }, { argument := 29072248110092602393334120448, coefficient := (-29072248110092602393334120448) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 2141299548273022252140712345731072, coefficient := 2141299548273022252140712345731072 }, { argument := 1740853180245066011576893440, coefficient := 1740853180245066011576893440 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1547425049106725343623905280, coefficient := 1547425049106725343623905280 }] }

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


end Parent3

namespace Parent3

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 2307199807297788980463122325176320
def positiveArguments : Array ℕ := #[
    47, 555, 39, 35, 555, 5,
    39, 39, 39, 39, 39, 45,
    47, 3, 454035817, 509, 454032023, 257,
    617747367, 5035, 1643, 134855369071, 16589, 39535830225,
    33231, 14893, 5035, 1643, 1517231829, 56729,
    52088267085, 1403741, 44659, 104176203739, 22933, 22933,
    776101, 42245, 1403741, 776101, 3034806241, 44659,
    42245, 56729, 105402469, 3456054539, 700587, 116092185429,
    718903, 22895, 700587, 398373, 718903, 11223129,
    13737, 432007033, 700587, 22895, 13737
  ]
def positiveCoefficients : Array ℕ := #[
    1818224432700402278758088704, 21470522556355814142781685760, 48279661532129830721065844736, 1353996917968384675670917120, 21470522556355814142781685760, 1547425049106725343623905280,
    1508739422879057210033307648, 1508739422879057210033307648, 1508739422879057210033307648, 48279661532129830721065844736, 1508739422879057210033307648, 1740853180245066011576893440,
    1818224432700402278758088704, 475368975085586025561263702016, 34305976387570173905609647194112, 39381967499766159995228389376, 34305689721035197786666594992128, 39768823762042841331134365696,
    186702685491313531839030805659648, 779128512225236210514636308480, 31780241946029371744675954688, 636836474935906204475802743996416, 641755853490786668134424117248, 186702679526964663974668900761600,
    642781022585819873674574954496, 576145031408661513564770533376, 779128512225236210514636308480, 31780241946029371744675954688, 28659698944050435904628311719936, 1097298445134692775230506532864,
    983919546531864628520756591984640, 27152299823226546757299555270656, 863830690850715589011249823744, 983916425699306026321281378418688, 887177466279113307633175494656, 887177466279113307633175494656,
    15011976600459733073898206396416, 817137139993920151767398481920, 27152299823226546757299555270656, 15011976600459733073898206396416, 28662934549004037767960798953472, 863830690850715589011249823744,
    817137139993920151767398481920, 1097298445134692775230506532864, 995498173634613621355182030848, 65283024471772412344454743064576, 13551323410981667353918011604992, 548229845392997404183838362435584,
    13905606375974652121340704718848, 442853706241230959278366392320, 13551323410981667353918011604992, 7705654488597418691443575226368, 13905606375974652121340704718848, 217086886799451416238255205515264,
    8502791159831634418144634732544, 65283057056101144145006717566976, 13551323410981667353918011604992, 442853706241230959278366392320, 8502791159831634418144634732544
  ]
def positiveScales : Array ℕ := #[
    5, 9, 5, 5, 9, 2,
    5, 5, 5, 5, 5, 5,
    5, 1, 28, 8, 28, 8,
    29, 12, 10, 36, 14, 35,
    15, 13, 12, 10, 30, 15,
    35, 20, 15, 36, 14, 14,
    19, 15, 20, 19, 31, 15,
    15, 15, 26, 31, 19, 36,
    19, 14, 19, 18, 19, 23,
    13, 28, 19, 14, 13
  ]
def negativeArguments : Array ℕ := #[
    1, 3, 867, 12795, 13359
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 475368975085586025561263702016, 68690816899867180693602604941312, 1013724339370012199509394844549120, 2116818046056114571824307265077248
  ]
def negativeScales : Array ℕ := #[
    0, 1, 9, 13, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5554588851677541, 9116343961237468, 5285402218862248, 5129283016944966, 9116343961237468, 2321928094887362,
    5285402218862248, 5285402218862248, 5285402218862248, 5285402218862248, 5285402218862248, 5491853096329661,
    5554588851677541, 1584962500720924, 28758230869307864, 8991521844801183, 28758218813853983, 8005624549193878,
    29202441715524446, 12297776062894146, 10682116764947138, 36972622004351737, 14017939301495817, 35202441669436536,
    15020242087365238, 13862346774648731, 12297776062894146, 10682116764947138, 30498794396390665, 15791798812398820,
    35600239390003668, 20420845342228238, 15446663326383968, 36600234814002701, 14485137474198596, 14485137474198596,
    19565884888082835, 15366492977699987, 20420845342228238, 19565884888082835, 31498957263689020, 15446663326383968,
    15366492977699987, 15791798812398820, 26651333420876607, 31686478838418408, 19418204692366197, 36756479906368153,
    19455437598565170, 14482744944560899, 19418204692366197, 18603760345521884, 19455437598565170, 23419971618540385,
    13745779350381986, 28686479558502045, 19418204692366197, 14482744944560899, 13745779350381986
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 1584962500724866, 9759888183500541, 13643292526944756, 13705524397246449
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
noncomputable def positiveFloor : ℝ := 86149501919 / 50000000000
noncomputable def negativeCeiling : ℝ := 523778401907 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1818224432700402278758088704, coefficient := 1818224432700402278758088704 }, { argument := 21470522556355814142781685760, coefficient := 21470522556355814142781685760 }, { argument := 48279661532129830721065844736, coefficient := 48279661532129830721065844736 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 21470522556355814142781685760, coefficient := 21470522556355814142781685760 }, { argument := 1547425049106725343623905280, coefficient := 1547425049106725343623905280 }, { argument := 1508739422879057210033307648, coefficient := 1508739422879057210033307648 }, { argument := 1508739422879057210033307648, coefficient := 1508739422879057210033307648 }, { argument := 1508739422879057210033307648, coefficient := 1508739422879057210033307648 }, { argument := 48279661532129830721065844736, coefficient := 48279661532129830721065844736 }, { argument := 1508739422879057210033307648, coefficient := 1508739422879057210033307648 }, { argument := 1740853180245066011576893440, coefficient := 1740853180245066011576893440 }, { argument := 1818224432700402278758088704, coefficient := 1818224432700402278758088704 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 34305976387570173905609647194112, coefficient := 34305976387570173905609647194112 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 34305689721035197786666594992128, coefficient := 34305689721035197786666594992128 }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 68690816899867180693602604941312, coefficient := (-68690816899867180693602604941312) }, { argument := 186702685491313531839030805659648, coefficient := 186702685491313531839030805659648 }, { argument := 779128512225236210514636308480, coefficient := 779128512225236210514636308480 }, { argument := 31780241946029371744675954688, coefficient := 31780241946029371744675954688 }, { argument := 636836474935906204475802743996416, coefficient := 636836474935906204475802743996416 }, { argument := 641755853490786668134424117248, coefficient := 641755853490786668134424117248 }, { argument := 186702679526964663974668900761600, coefficient := 186702679526964663974668900761600 }, { argument := 642781022585819873674574954496, coefficient := 642781022585819873674574954496 }, { argument := 576145031408661513564770533376, coefficient := 576145031408661513564770533376 }, { argument := 779128512225236210514636308480, coefficient := 779128512225236210514636308480 }, { argument := 31780241946029371744675954688, coefficient := 31780241946029371744675954688 }, { argument := 1013724339370012199509394844549120, coefficient := (-1013724339370012199509394844549120) }, { argument := 28659698944050435904628311719936, coefficient := 28659698944050435904628311719936 }, { argument := 1097298445134692775230506532864, coefficient := 1097298445134692775230506532864 }, { argument := 983919546531864628520756591984640, coefficient := 983919546531864628520756591984640 }, { argument := 27152299823226546757299555270656, coefficient := 27152299823226546757299555270656 }, { argument := 863830690850715589011249823744, coefficient := 863830690850715589011249823744 }, { argument := 983916425699306026321281378418688, coefficient := 983916425699306026321281378418688 }, { argument := 887177466279113307633175494656, coefficient := 887177466279113307633175494656 }, { argument := 887177466279113307633175494656, coefficient := 887177466279113307633175494656 }, { argument := 15011976600459733073898206396416, coefficient := 15011976600459733073898206396416 }, { argument := 817137139993920151767398481920, coefficient := 817137139993920151767398481920 }, { argument := 27152299823226546757299555270656, coefficient := 27152299823226546757299555270656 }, { argument := 15011976600459733073898206396416, coefficient := 15011976600459733073898206396416 }, { argument := 28662934549004037767960798953472, coefficient := 28662934549004037767960798953472 }, { argument := 863830690850715589011249823744, coefficient := 863830690850715589011249823744 }, { argument := 817137139993920151767398481920, coefficient := 817137139993920151767398481920 }, { argument := 1097298445134692775230506532864, coefficient := 1097298445134692775230506532864 }, { argument := 2116818046056114571824307265077248, coefficient := (-2116818046056114571824307265077248) }, { argument := 995498173634613621355182030848, coefficient := 995498173634613621355182030848 }, { argument := 65283024471772412344454743064576, coefficient := 65283024471772412344454743064576 }, { argument := 13551323410981667353918011604992, coefficient := 13551323410981667353918011604992 }, { argument := 548229845392997404183838362435584, coefficient := 548229845392997404183838362435584 }, { argument := 13905606375974652121340704718848, coefficient := 13905606375974652121340704718848 }, { argument := 442853706241230959278366392320, coefficient := 442853706241230959278366392320 }, { argument := 13551323410981667353918011604992, coefficient := 13551323410981667353918011604992 }, { argument := 7705654488597418691443575226368, coefficient := 7705654488597418691443575226368 }, { argument := 13905606375974652121340704718848, coefficient := 13905606375974652121340704718848 }, { argument := 217086886799451416238255205515264, coefficient := 217086886799451416238255205515264 }, { argument := 8502791159831634418144634732544, coefficient := 8502791159831634418144634732544 }, { argument := 65283057056101144145006717566976, coefficient := 65283057056101144145006717566976 }, { argument := 13551323410981667353918011604992, coefficient := 13551323410981667353918011604992 }, { argument := 442853706241230959278366392320, coefficient := 442853706241230959278366392320 }, { argument := 8502791159831634418144634732544, coefficient := 8502791159831634418144634732544 }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
