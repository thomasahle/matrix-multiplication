import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 21, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21

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
def constantNumerator : ℤ := (-904809336626636600333637741707264)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    37373584079, 41413971547, 2255175, 1066188825, 40471677675, 4264758225,
    2255175, 22039152135, 429822798405, 859645281495, 2754907155, 1048353615,
    191367225, 158561415, 70423932465, 1066188825, 16773652395, 4270222935,
    4270222935, 3056407965, 158561415, 976092985, 19036440955, 38072867945,
    122012205, 886625927, 103629357975, 28372020105, 78398449, 3186319,
    78398449, 3186319, 134211915, 2080011015, 3517192575, 1719958005,
    1113035625, 133564275, 3517192575, 6989863725, 1113035625, 107875412775,
    6900820875, 4160022135, 3517192575, 133564275, 6900820875, 133564275,
    3517192575, 3517192575, 134211915, 18592723457, 82827912713, 4024028883,
    866662793997, 38383666867, 1006007037, 38383666867, 74747140741, 1412114902107,
    74747140741, 866662793997, 1412114902107, 18592725417
  ]
def negativeCoefficients : Array ℕ := #[
    86177617577822362593245790208, 95494116775424780170893983744, 332805088531423504524902400, 39335424778048200457479782400, 373285340152194707285763686400, 39335451756411408257699020800,
    332805088531423504524902400, 25409412439743403866728693760, 991103894902836133095863746560, 991103531369391907987909509120, 25409533617558145569380106240, 38677421669306469793325383680,
    28240817789367938789985484800, 1462470921235125401624248320, 162386532355757555628826951680, 39335424778048200457479782400, 38677409113991284624761815040, 39385854809814928919604756480,
    39385854809814928919604756480, 28190387757601210327860510720, 1462470921235125401624248320, 2250717185804777032484126720, 87790088592792011789377208320, 87790056391694388120141168640,
    2250727919503984922229473280, 65421446257937950121161392128, 238953030635957113823900467200, 65421424216384625047460904960, 1446196124478770523179843584, 58777211130198144795541504,
    1446196124478770523179843584, 58777211130198144795541504, 2475772847647460076174704640, 38369430864201839271991050240, 64880751288976487650374451200, 15863812567881526673449943040,
    41063766638592713702768640000, 2463825998315562822166118400, 64880751288976487650374451200, 64470113622590560513346764800, 41063766638592713702768640000, 994975065653101453018084147200,
    63648838289818706239291392000, 38369431832655903141742510080, 64880751288976487650374451200, 2463825998315562822166118400, 63648838289818706239291392000, 2463825998315562822166118400,
    64880751288976487650374451200, 64880751288976487650374451200, 2475772847647460076174704640, 85743802811133829333938864128, 95494081748516548710276005888, 148460461899832633311526649856,
    999194172441795107236790403072, 88506709913259240268060688384, 148460434783118844958485774336, 88506709913259240268060688384, 86177585968173470787322249216, 3256115275229905734072337956864,
    86177585968173470787322249216, 999194172441795107236790403072, 3256115275229905734072337956864, 85743811850038425451619155968
  ]
def negativeScales : Array ℕ := #[
    35, 35, 21, 29, 35, 31,
    21, 34, 38, 39, 31, 29,
    27, 27, 36, 29, 33, 31,
    31, 31, 27, 29, 34, 35,
    26, 29, 36, 34, 26, 21,
    26, 21, 26, 30, 31, 30,
    30, 26, 31, 32, 30, 36,
    32, 31, 31, 26, 32, 26,
    31, 31, 26, 34, 36, 31,
    39, 35, 29, 35, 36, 40,
    36, 39, 40, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35121299871839222, 35269398510828356, 21104807959273164, 29989815840116120, 35236193603248791, 31989816829594442,
    21104807959273164, 34359349672140249, 38644951051146439, 39644950521970843, 31359356552355049, 29965478294823423,
    27511768523202913, 27240466501385119, 36035346738263698, 29989815840116120, 33965477826501152, 31991664265116361,
    31991664265116361, 31509189979101104, 27240466501385119, 29862443350276665, 34148044727071751, 35148044197896156,
    26862450230491748, 29723750310095794, 36592641817107550, 34723749824028198, 26224321777198165, 21603459279595911,
    26224321777198165, 21603459279595911, 26999937538852851, 30953944033513892, 31711777182332063, 30679726194122254,
    30051852623834423, 26992958955933587, 31711777182332063, 32702617183028300, 30051852623834423, 36650575123532664,
    32684120839383532, 31953944069927883, 31711777182332063, 26992958955933587, 32684120839383532, 26992958955933587,
    31711777182332063, 31711777182332063, 26999937538852851, 34114019060181361, 36269397981652761, 31905993519162658,
    39656679814559453, 35159773490478263, 29905993255650373, 35159773490478263, 36121299342663627, 40360994622410115,
    36121299342663627, 39656679814559453, 40360994622410115, 34114019212266780
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
noncomputable def negativeCeiling : ℝ := 6813406099 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 86177617577822362593245790208, coefficient := (-86177617577822362593245790208) }, { argument := 95494116775424780170893983744, coefficient := (-95494116775424780170893983744) }, { argument := 332805088531423504524902400, coefficient := (-332805088531423504524902400) }, { argument := 39335424778048200457479782400, coefficient := (-39335424778048200457479782400) }, { argument := 373285340152194707285763686400, coefficient := (-373285340152194707285763686400) }, { argument := 39335451756411408257699020800, coefficient := (-39335451756411408257699020800) }, { argument := 332805088531423504524902400, coefficient := (-332805088531423504524902400) }, { argument := 25409412439743403866728693760, coefficient := (-25409412439743403866728693760) }, { argument := 991103894902836133095863746560, coefficient := (-991103894902836133095863746560) }, { argument := 991103531369391907987909509120, coefficient := (-991103531369391907987909509120) }, { argument := 25409533617558145569380106240, coefficient := (-25409533617558145569380106240) }, { argument := 38677421669306469793325383680, coefficient := (-38677421669306469793325383680) }, { argument := 28240817789367938789985484800, coefficient := (-28240817789367938789985484800) }, { argument := 1462470921235125401624248320, coefficient := (-1462470921235125401624248320) }, { argument := 162386532355757555628826951680, coefficient := (-162386532355757555628826951680) }, { argument := 39335424778048200457479782400, coefficient := (-39335424778048200457479782400) }, { argument := 38677409113991284624761815040, coefficient := (-38677409113991284624761815040) }, { argument := 39385854809814928919604756480, coefficient := (-39385854809814928919604756480) }, { argument := 39385854809814928919604756480, coefficient := (-39385854809814928919604756480) }, { argument := 28190387757601210327860510720, coefficient := (-28190387757601210327860510720) }, { argument := 1462470921235125401624248320, coefficient := (-1462470921235125401624248320) }, { argument := 2250717185804777032484126720, coefficient := (-2250717185804777032484126720) }, { argument := 87790088592792011789377208320, coefficient := (-87790088592792011789377208320) }, { argument := 87790056391694388120141168640, coefficient := (-87790056391694388120141168640) }, { argument := 2250727919503984922229473280, coefficient := (-2250727919503984922229473280) }, { argument := 65421446257937950121161392128, coefficient := (-65421446257937950121161392128) }, { argument := 238953030635957113823900467200, coefficient := (-238953030635957113823900467200) }, { argument := 65421424216384625047460904960, coefficient := (-65421424216384625047460904960) }, { argument := 1446196124478770523179843584, coefficient := (-1446196124478770523179843584) }, { argument := 58777211130198144795541504, coefficient := (-58777211130198144795541504) }, { argument := 1446196124478770523179843584, coefficient := (-1446196124478770523179843584) }, { argument := 58777211130198144795541504, coefficient := (-58777211130198144795541504) }, { argument := 2475772847647460076174704640, coefficient := (-2475772847647460076174704640) }, { argument := 38369430864201839271991050240, coefficient := (-38369430864201839271991050240) }, { argument := 64880751288976487650374451200, coefficient := (-64880751288976487650374451200) }, { argument := 15863812567881526673449943040, coefficient := (-15863812567881526673449943040) }, { argument := 41063766638592713702768640000, coefficient := (-41063766638592713702768640000) }, { argument := 2463825998315562822166118400, coefficient := (-2463825998315562822166118400) }, { argument := 64880751288976487650374451200, coefficient := (-64880751288976487650374451200) }, { argument := 64470113622590560513346764800, coefficient := (-64470113622590560513346764800) }, { argument := 41063766638592713702768640000, coefficient := (-41063766638592713702768640000) }, { argument := 994975065653101453018084147200, coefficient := (-994975065653101453018084147200) }, { argument := 63648838289818706239291392000, coefficient := (-63648838289818706239291392000) }, { argument := 38369431832655903141742510080, coefficient := (-38369431832655903141742510080) }, { argument := 64880751288976487650374451200, coefficient := (-64880751288976487650374451200) }, { argument := 2463825998315562822166118400, coefficient := (-2463825998315562822166118400) }, { argument := 63648838289818706239291392000, coefficient := (-63648838289818706239291392000) }, { argument := 2463825998315562822166118400, coefficient := (-2463825998315562822166118400) }, { argument := 64880751288976487650374451200, coefficient := (-64880751288976487650374451200) }, { argument := 64880751288976487650374451200, coefficient := (-64880751288976487650374451200) }, { argument := 2475772847647460076174704640, coefficient := (-2475772847647460076174704640) }, { argument := 85743802811133829333938864128, coefficient := (-85743802811133829333938864128) }, { argument := 95494081748516548710276005888, coefficient := (-95494081748516548710276005888) }, { argument := 148460461899832633311526649856, coefficient := (-148460461899832633311526649856) }, { argument := 999194172441795107236790403072, coefficient := (-999194172441795107236790403072) }, { argument := 88506709913259240268060688384, coefficient := (-88506709913259240268060688384) }, { argument := 148460434783118844958485774336, coefficient := (-148460434783118844958485774336) }, { argument := 88506709913259240268060688384, coefficient := (-88506709913259240268060688384) }, { argument := 86177585968173470787322249216, coefficient := (-86177585968173470787322249216) }, { argument := 3256115275229905734072337956864, coefficient := (-3256115275229905734072337956864) }, { argument := 86177585968173470787322249216, coefficient := (-86177585968173470787322249216) }, { argument := 999194172441795107236790403072, coefficient := (-999194172441795107236790403072) }, { argument := 3256115275229905734072337956864, coefficient := (-3256115275229905734072337956864) }, { argument := 85743811850038425451619155968, coefficient := (-85743811850038425451619155968) }] }

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
def constantNumerator : ℤ := (-699519736471787907714339160719360)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    74747140741, 74747140741, 82827912713, 1722184167, 7264147275, 6018864885,
    28016828235, 40471677675, 6888736305, 162094257765, 162094257765, 116018809335,
    6018864885, 976092985, 19036440955, 38072867945, 122012205, 280577825,
    32794100625, 8978487375, 565427215, 558850417, 565427215, 558850417,
    33669339, 3935292075, 1077418485, 57, 57, 3186319,
    558850417, 139712621, 796563, 9032265, 4270222935, 162094257765,
    17080903455, 9032265, 1900812655, 37070963965, 74141900735, 237602715,
    9032265, 4270222935, 162094257765, 17080903455, 9032265, 35909947185,
    700340643555, 1400680773345, 4488764805, 886625927, 103629357975, 28372020105,
    1900812655, 37070963965, 74141900735, 237602715, 1762028741, 205946951925,
    56384900715, 147, 147, 6464835
  ]
def negativeCoefficients : Array ℕ := #[
    86177585968173470787322249216, 86177585968173470787322249216, 95494081748516548710276005888, 15884345288221835374872231936, 267999731391319277025676492800, 13878557518479033988829675520,
    258409630104062343452169338880, 373285340152194707285763686400, 15884344451200823030301327360, 373763911101107777423309537280, 373763911101107777423309537280, 267521160442406206888130641920,
    13878557518479033988829675520, 2250717185804777032484126720, 87790088592792011789377208320, 87790056391694388120141168640, 2250727919503984922229473280, 41405978644264525393140121600,
    151236095339213363179683840000, 41405964693914319650291712000, 10430291127415346489133629440, 10308970617884861657484623872, 10430291127415346489133629440, 10308970617884861657484623872,
    2484358718655871523588407296, 9074165720352801790781030400, 2484357881634859179017502720, 1102540347488541807332032512, 1102540347488541807332032512, 58777211130198144795541504,
    10308970617884861657484623872, 10308971853816714596024582144, 58775975198345206255583232, 333231761721848406453780480, 39385854809814928919604756480, 373763911101107777423309537280,
    39385881822765781858029404160, 333231761721848406453780480, 2191487786178335531629281280, 85479823103508011479130439680, 85479791749807693695926927360, 2191498237411774792697118720,
    333231761721848406453780480, 39385854809814928919604756480, 373763911101107777423309537280, 39385881822765781858029404160, 333231761721848406453780480, 82802700677765218195073925120,
    3229751154019032433724982558720, 3229749969357598805051509309440, 82803095564909761086231674880, 65421446257937950121161392128, 238953030635957113823900467200, 65421424216384625047460904960,
    2191487786178335531629281280, 85479823103508011479130439680, 85479791749807693695926927360, 2191498237411774792697118720, 65007386471495304867229990912, 237440669682564980192103628800,
    65007364569445481850957987840, 1421696763866803909454462976, 1421696763866803909454462976, 238510313447520178242846720
  ]
def negativeScales : Array ℕ := #[
    36, 36, 36, 30, 32, 32,
    34, 35, 32, 37, 37, 36,
    32, 29, 34, 35, 26, 28,
    34, 33, 29, 29, 29, 29,
    25, 31, 30, 5, 5, 21,
    29, 27, 19, 23, 31, 37,
    33, 23, 30, 35, 36, 27,
    23, 31, 37, 33, 23, 35,
    39, 40, 32, 29, 36, 34,
    30, 35, 36, 27, 30, 37,
    35, 7, 7, 22
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36121299342663627, 36121299342663627, 36269397981652761, 30681592283997956, 32758146306712572, 32486844284626926,
    34705574587499887, 35236193603248791, 32681592207975553, 37238042027641160, 37238042027641160, 36755567762596226,
    32486844284626926, 29862443350276665, 34148044727071751, 35148044197896156, 26862450230491748, 28063825751568094,
    34932717266462956, 33063825265500499, 29074766083372737, 29057886939250002, 29074766083372737, 29057886939250002,
    25004932062514525, 31873823572357836, 30004931576446930, 5832890015409720, 5832890015409720, 21603459279595911,
    29057886939250002, 27057887112213212, 19603428943153129, 23106656383665533, 31991664265116361, 37238042027641160,
    33991665254594692, 23106656383665533, 30823969201314635, 35109570579257115, 36109570050081520, 27823976081529577,
    23106656383665533, 31991664265116361, 37238042027641160, 33991665254594692, 23106656383665533, 35063664480016139,
    39349265859003603, 40349265329828008, 32063671360230939, 29723750310095794, 36592641817107550, 34723749824028198,
    30823969201314635, 35109570579257115, 36109570050081520, 27823976081529577, 30714590310786643, 37583481817821024,
    35714589824719047, 7199672344836365, 7199672344836365, 22624182118377635
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
noncomputable def negativeCeiling : ℝ := 5189280127 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 86177585968173470787322249216, coefficient := (-86177585968173470787322249216) }, { argument := 86177585968173470787322249216, coefficient := (-86177585968173470787322249216) }, { argument := 95494081748516548710276005888, coefficient := (-95494081748516548710276005888) }, { argument := 15884345288221835374872231936, coefficient := (-15884345288221835374872231936) }, { argument := 267999731391319277025676492800, coefficient := (-267999731391319277025676492800) }, { argument := 13878557518479033988829675520, coefficient := (-13878557518479033988829675520) }, { argument := 258409630104062343452169338880, coefficient := (-258409630104062343452169338880) }, { argument := 373285340152194707285763686400, coefficient := (-373285340152194707285763686400) }, { argument := 15884344451200823030301327360, coefficient := (-15884344451200823030301327360) }, { argument := 373763911101107777423309537280, coefficient := (-373763911101107777423309537280) }, { argument := 373763911101107777423309537280, coefficient := (-373763911101107777423309537280) }, { argument := 267521160442406206888130641920, coefficient := (-267521160442406206888130641920) }, { argument := 13878557518479033988829675520, coefficient := (-13878557518479033988829675520) }, { argument := 2250717185804777032484126720, coefficient := (-2250717185804777032484126720) }, { argument := 87790088592792011789377208320, coefficient := (-87790088592792011789377208320) }, { argument := 87790056391694388120141168640, coefficient := (-87790056391694388120141168640) }, { argument := 2250727919503984922229473280, coefficient := (-2250727919503984922229473280) }, { argument := 41405978644264525393140121600, coefficient := (-41405978644264525393140121600) }, { argument := 151236095339213363179683840000, coefficient := (-151236095339213363179683840000) }, { argument := 41405964693914319650291712000, coefficient := (-41405964693914319650291712000) }, { argument := 10430291127415346489133629440, coefficient := (-10430291127415346489133629440) }, { argument := 10308970617884861657484623872, coefficient := (-10308970617884861657484623872) }, { argument := 10430291127415346489133629440, coefficient := (-10430291127415346489133629440) }, { argument := 10308970617884861657484623872, coefficient := (-10308970617884861657484623872) }, { argument := 2484358718655871523588407296, coefficient := (-2484358718655871523588407296) }, { argument := 9074165720352801790781030400, coefficient := (-9074165720352801790781030400) }, { argument := 2484357881634859179017502720, coefficient := (-2484357881634859179017502720) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 58777211130198144795541504, coefficient := (-58777211130198144795541504) }, { argument := 10308970617884861657484623872, coefficient := (-10308970617884861657484623872) }, { argument := 10308971853816714596024582144, coefficient := (-10308971853816714596024582144) }, { argument := 58775975198345206255583232, coefficient := (-58775975198345206255583232) }, { argument := 333231761721848406453780480, coefficient := (-333231761721848406453780480) }, { argument := 39385854809814928919604756480, coefficient := (-39385854809814928919604756480) }, { argument := 373763911101107777423309537280, coefficient := (-373763911101107777423309537280) }, { argument := 39385881822765781858029404160, coefficient := (-39385881822765781858029404160) }, { argument := 333231761721848406453780480, coefficient := (-333231761721848406453780480) }, { argument := 2191487786178335531629281280, coefficient := (-2191487786178335531629281280) }, { argument := 85479823103508011479130439680, coefficient := (-85479823103508011479130439680) }, { argument := 85479791749807693695926927360, coefficient := (-85479791749807693695926927360) }, { argument := 2191498237411774792697118720, coefficient := (-2191498237411774792697118720) }, { argument := 333231761721848406453780480, coefficient := (-333231761721848406453780480) }, { argument := 39385854809814928919604756480, coefficient := (-39385854809814928919604756480) }, { argument := 373763911101107777423309537280, coefficient := (-373763911101107777423309537280) }, { argument := 39385881822765781858029404160, coefficient := (-39385881822765781858029404160) }, { argument := 333231761721848406453780480, coefficient := (-333231761721848406453780480) }, { argument := 82802700677765218195073925120, coefficient := (-82802700677765218195073925120) }, { argument := 3229751154019032433724982558720, coefficient := (-3229751154019032433724982558720) }, { argument := 3229749969357598805051509309440, coefficient := (-3229749969357598805051509309440) }, { argument := 82803095564909761086231674880, coefficient := (-82803095564909761086231674880) }, { argument := 65421446257937950121161392128, coefficient := (-65421446257937950121161392128) }, { argument := 238953030635957113823900467200, coefficient := (-238953030635957113823900467200) }, { argument := 65421424216384625047460904960, coefficient := (-65421424216384625047460904960) }, { argument := 2191487786178335531629281280, coefficient := (-2191487786178335531629281280) }, { argument := 85479823103508011479130439680, coefficient := (-85479823103508011479130439680) }, { argument := 85479791749807693695926927360, coefficient := (-85479791749807693695926927360) }, { argument := 2191498237411774792697118720, coefficient := (-2191498237411774792697118720) }, { argument := 65007386471495304867229990912, coefficient := (-65007386471495304867229990912) }, { argument := 237440669682564980192103628800, coefficient := (-237440669682564980192103628800) }, { argument := 65007364569445481850957987840, coefficient := (-65007364569445481850957987840) }, { argument := 1421696763866803909454462976, coefficient := (-1421696763866803909454462976) }, { argument := 1421696763866803909454462976, coefficient := (-1421696763866803909454462976) }, { argument := 238510313447520178242846720, coefficient := (-238510313447520178242846720) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21
