import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 7, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-7307053716829818907468479313477632)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1171437, 13342739, 851, 69, 14789, 26749,
    53370957, 14789, 437, 437, 851, 851,
    26749, 851, 4685747, 69, 19196323478407, 230849527962755,
    379156647793, 3642653149140333, 14772336927, 24620561545, 753389183277, 24620561545,
    14772336927, 12068999269359, 773085632513, 230849587183747, 753389183277, 24620561545,
    773085632513, 24620561545, 753389183277, 24620561545, 19196323478407, 3470081474492377,
    46291519435, 3904242861129849, 522432862195, 46291519435, 62467880376940293, 46291519435,
    46291519435, 1919114134291, 11903533569, 522432862195, 1919114134291, 3470093257394941,
    46291519435, 11903533569, 46291519435, 412485, 195012315, 7402511985,
    780049795, 412485, 4345631415, 170066111817, 170066111817, 4345631415,
    1734135047313003, 1099497105, 28529865, 6277996340640381
  ]
def negativeCoefficients : Array ℕ := #[
    22127819302373474320785604608, 252037213773110588435779813376, 16460733959872790842799292416, 21354465677672809742009892864, 286060863140492013835674189824, 517400907981947452707448029184,
    252037218495477071305425027072, 286060863140492013835674189824, 16905618661490974379091165184, 16905618661490974379091165184, 16460733959872790842799292416, 16460733959872790842799292416,
    517400907981947452707448029184, 16460733959872790842799292416, 22127814580006991451140390912, 21354465677672809742009892864, 43226277632118634408822439936, 2079307696223436629208947752960,
    874275705710387811630958247936, 16405051365108367490599687815168, 545003037325956038419298648064, 28385574860726877001005137920, 868598590738242436230757220352, 908338395543260064032164413440,
    545003037325956038419298648064, 13914608796728315105892718608384, 891307050626823937831561330688, 2079308229638711636631197057024, 868598590738242436230757220352, 28385574860726877001005137920,
    891307050626823937831561330688, 28385574860726877001005137920, 868598590738242436230757220352, 908338395543260064032164413440, 43226277632118634408822439936, 976741102216820648594806669312,
    106740976475074597647149957120, 35166293389096614236086975070208, 1204648163075841887732120944640, 106740976475074597647149957120, 35166290348526627845525697724416, 106740976475074597647149957120,
    106740976475074597647149957120, 4425175910438092605314702508032, 109790718660076729008497098752, 1204648163075841887732120944640, 4425175910438092605314702508032, 976744418809045434423675191296,
    106740976475074597647149957120, 109790718660076729008497098752, 106740976475074597647149957120, 60872041833952675186606080, 7194684532053260596496302080, 68276122044931339623208058880,
    7194689466557300313801359360, 60872041833952675186606080, 10020343818897162886006702080, 392145755037383836888448630784, 392145755037383836888448630784, 10020343818897162886006702080,
    976231244111119720192394919936, 10141070852859779306320035840, 526283118112483556815011840, 3534197747542669668119973199872
  ]
def negativeScales : Array ℕ := #[
    20, 23, 9, 6, 13, 14,
    25, 13, 8, 8, 9, 9,
    14, 9, 22, 6, 44, 47,
    38, 51, 33, 34, 39, 34,
    33, 43, 39, 47, 39, 34,
    39, 34, 39, 34, 44, 51,
    35, 51, 38, 35, 55, 35,
    35, 40, 33, 38, 40, 51,
    35, 33, 35, 18, 27, 32,
    29, 18, 32, 37, 37, 32,
    50, 30, 24, 52
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    20159847937326706, 23669551517882943, 9733015321840403, 6108524456778170, 13852236885192533, 14707197337615895,
    25669551544914406, 13852236885192533, 8771489469857739, 8771489469857739, 9733015321840403, 9733015321840403,
    14707197337615895, 9733015321840403, 22159847629436654, 6108524456778170, 44125895262848609, 47713946110914884,
    38464003061822371, 51693911052590988, 33782179022295783, 34519144616015261, 39454604363820099, 34519144616015261,
    33782179022295783, 43456371289994290, 39491837270019224, 47713946481016662, 39454604363820099, 34519144616015261,
    39491837270019224, 34519144616015261, 39454604363820099, 34519144616015261, 44125895262848609, 51623890959746162,
    35430028866123530, 51793964221569580, 38926454699208425, 35430028866123530, 55793964096830375, 35430028866123530,
    35430028866123530, 40803577653940080, 33470670850620953, 38926454699208425, 40803577653940080, 51623895858509020,
    35430028866123530, 33470670850620953, 35430028866123530, 18653982131227114, 27538989991938486, 32785367775657142,
    29538990981416487, 18653982131227114, 32016918668104613, 37307304735119171, 37307304735119171, 32016918668104613,
    50623137677418376, 30034196659536449, 24765969584799886, 52479225611303309
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
noncomputable def negativeCeiling : ℝ := 15982839699 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 22127819302373474320785604608, coefficient := (-22127819302373474320785604608) }, { argument := 252037213773110588435779813376, coefficient := (-252037213773110588435779813376) }, { argument := 16460733959872790842799292416, coefficient := (-16460733959872790842799292416) }, { argument := 21354465677672809742009892864, coefficient := (-21354465677672809742009892864) }, { argument := 286060863140492013835674189824, coefficient := (-286060863140492013835674189824) }, { argument := 517400907981947452707448029184, coefficient := (-517400907981947452707448029184) }, { argument := 252037218495477071305425027072, coefficient := (-252037218495477071305425027072) }, { argument := 286060863140492013835674189824, coefficient := (-286060863140492013835674189824) }, { argument := 16905618661490974379091165184, coefficient := (-16905618661490974379091165184) }, { argument := 16905618661490974379091165184, coefficient := (-16905618661490974379091165184) }, { argument := 16460733959872790842799292416, coefficient := (-16460733959872790842799292416) }, { argument := 16460733959872790842799292416, coefficient := (-16460733959872790842799292416) }, { argument := 517400907981947452707448029184, coefficient := (-517400907981947452707448029184) }, { argument := 16460733959872790842799292416, coefficient := (-16460733959872790842799292416) }, { argument := 22127814580006991451140390912, coefficient := (-22127814580006991451140390912) }, { argument := 21354465677672809742009892864, coefficient := (-21354465677672809742009892864) }, { argument := 43226277632118634408822439936, coefficient := (-43226277632118634408822439936) }, { argument := 2079307696223436629208947752960, coefficient := (-2079307696223436629208947752960) }, { argument := 874275705710387811630958247936, coefficient := (-874275705710387811630958247936) }, { argument := 16405051365108367490599687815168, coefficient := (-16405051365108367490599687815168) }, { argument := 545003037325956038419298648064, coefficient := (-545003037325956038419298648064) }, { argument := 28385574860726877001005137920, coefficient := (-28385574860726877001005137920) }, { argument := 868598590738242436230757220352, coefficient := (-868598590738242436230757220352) }, { argument := 908338395543260064032164413440, coefficient := (-908338395543260064032164413440) }, { argument := 545003037325956038419298648064, coefficient := (-545003037325956038419298648064) }, { argument := 13914608796728315105892718608384, coefficient := (-13914608796728315105892718608384) }, { argument := 891307050626823937831561330688, coefficient := (-891307050626823937831561330688) }, { argument := 2079308229638711636631197057024, coefficient := (-2079308229638711636631197057024) }, { argument := 868598590738242436230757220352, coefficient := (-868598590738242436230757220352) }, { argument := 28385574860726877001005137920, coefficient := (-28385574860726877001005137920) }, { argument := 891307050626823937831561330688, coefficient := (-891307050626823937831561330688) }, { argument := 28385574860726877001005137920, coefficient := (-28385574860726877001005137920) }, { argument := 868598590738242436230757220352, coefficient := (-868598590738242436230757220352) }, { argument := 908338395543260064032164413440, coefficient := (-908338395543260064032164413440) }, { argument := 43226277632118634408822439936, coefficient := (-43226277632118634408822439936) }, { argument := 976741102216820648594806669312, coefficient := (-976741102216820648594806669312) }, { argument := 106740976475074597647149957120, coefficient := (-106740976475074597647149957120) }, { argument := 35166293389096614236086975070208, coefficient := (-35166293389096614236086975070208) }, { argument := 1204648163075841887732120944640, coefficient := (-1204648163075841887732120944640) }, { argument := 106740976475074597647149957120, coefficient := (-106740976475074597647149957120) }, { argument := 35166290348526627845525697724416, coefficient := (-35166290348526627845525697724416) }, { argument := 106740976475074597647149957120, coefficient := (-106740976475074597647149957120) }, { argument := 106740976475074597647149957120, coefficient := (-106740976475074597647149957120) }, { argument := 4425175910438092605314702508032, coefficient := (-4425175910438092605314702508032) }, { argument := 109790718660076729008497098752, coefficient := (-109790718660076729008497098752) }, { argument := 1204648163075841887732120944640, coefficient := (-1204648163075841887732120944640) }, { argument := 4425175910438092605314702508032, coefficient := (-4425175910438092605314702508032) }, { argument := 976744418809045434423675191296, coefficient := (-976744418809045434423675191296) }, { argument := 106740976475074597647149957120, coefficient := (-106740976475074597647149957120) }, { argument := 109790718660076729008497098752, coefficient := (-109790718660076729008497098752) }, { argument := 106740976475074597647149957120, coefficient := (-106740976475074597647149957120) }, { argument := 60872041833952675186606080, coefficient := (-60872041833952675186606080) }, { argument := 7194684532053260596496302080, coefficient := (-7194684532053260596496302080) }, { argument := 68276122044931339623208058880, coefficient := (-68276122044931339623208058880) }, { argument := 7194689466557300313801359360, coefficient := (-7194689466557300313801359360) }, { argument := 60872041833952675186606080, coefficient := (-60872041833952675186606080) }, { argument := 10020343818897162886006702080, coefficient := (-10020343818897162886006702080) }, { argument := 392145755037383836888448630784, coefficient := (-392145755037383836888448630784) }, { argument := 392145755037383836888448630784, coefficient := (-392145755037383836888448630784) }, { argument := 10020343818897162886006702080, coefficient := (-10020343818897162886006702080) }, { argument := 976231244111119720192394919936, coefficient := (-976231244111119720192394919936) }, { argument := 10141070852859779306320035840, coefficient := (-10141070852859779306320035840) }, { argument := 526283118112483556815011840, coefficient := (-526283118112483556815011840) }, { argument := 3534197747542669668119973199872, coefficient := (-3534197747542669668119973199872) }] }

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


end Parent1

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-27961720797773838113108882200985600)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1771046235, 216808919541219, 1771046235, 1845662805, 1099497105, 54865125,
    112760895, 4412893121, 4412893121, 112760895, 46291519435, 171961458725,
    2892610945, 77000465525733, 2062425, 77000490931227, 2062425, 19196329804921,
    230849652474749, 379156738191, 3642655445244563, 14772340449, 24620567415, 753389362899,
    24620567415, 14772340449, 12069002146833, 773085816831, 230849711695741, 753389362899,
    24620567415, 773085816831, 24620567415, 753389362899, 24620567415, 19196329804921,
    12562025049209003, 171961458725, 225498113564766921, 1940707891325, 171961458725, 225498094548817707,
    171961458725, 171961458725, 7129030760285, 44218660815, 1940707891325, 7129030760285,
    12562067971502957, 171961458725, 44218660815, 171961458725, 31215571741867159, 43028775279,
    1116515127, 225375422267049205, 69309823653, 62445937570562525, 69309823653, 72229940139,
    43028775279, 2147144475, 6999849405, 273938826819
  ]
def negativeCoefficients : Array ℕ := #[
    16335018319875931936527482880, 976420569256433736979656474624, 16335018319875931936527482880, 17023234705099948895439421440, 10141070852859779306320035840, 506041459723541881552896000,
    520017842896858752567214080, 20350877506930099319560208384, 20350877506930099319560208384, 520017842896858752567214080, 106740976475074597647149957120, 396516127455230427231630131200,
    106718507614452271510968074240, 43347408481130732772126621696, 76090052292440843983257600, 43347422783152396717548109824, 76090052292440843983257600, 43226291878161680885935505408,
    2079308817727776192323815211008, 874275914153984158530464120832, 16405061705842522122419330613248, 545003167264821293629380231168, 28385581628376109043196887040, 868598797828308936721824743424,
    908338612108035489382300385280, 545003167264821293629380231168, 13914612114229968652975114027008, 891307263131009823956382253056, 2079309351143051199746064515072, 868598797828308936721824743424,
    28385581628376109043196887040, 891307263131009823956382253056, 28385581628376109043196887040, 868598797828308936721824743424, 908338612108035489382300385280, 43226291878161680885935505408,
    3535895708164781411779601235968, 396516127455230427231630131200, 126944152527879261855103794020352, 4474967724137600535899825766400, 396516127455230427231630131200, 126944141822851537571769256771584,
    396516127455230427231630131200, 396516127455230427231630131200, 16438425741072552854659866296320, 407845159668237010866819563520, 4474967724137600535899825766400, 16438425741072552854659866296320,
    3535907789716472481860437409792, 396516127455230427231630131200, 407845159668237010866819563520, 396516127455230427231630131200, 35145609316207480506006126985216, 396870402688436654200357650432,
    20596068802194317383651295232, 126875083467543873309612399656960, 639270289360415928023330586624, 35153937646698330482040163532800, 639270289360415928023330586624, 666203610101746958448105357312,
    396870402688436654200357650432, 19803912309802228253510860800, 16140553816067885127759298560, 631659928772791928880195698688
  ]
def negativeScales : Array ℕ := #[
    30, 47, 30, 30, 30, 25,
    26, 32, 32, 26, 35, 37,
    31, 46, 20, 46, 20, 44,
    47, 38, 51, 33, 34, 39,
    34, 33, 43, 39, 47, 39,
    34, 39, 34, 39, 34, 44,
    53, 37, 57, 40, 37, 57,
    37, 37, 42, 35, 40, 42,
    53, 37, 35, 37, 54, 35,
    30, 57, 36, 55, 36, 36,
    35, 30, 32, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30721954729739330, 47623417438968616, 30721954729739330, 30781491857037243, 30034196659536449, 25709386056206097,
    26748691593269032, 32039077660065054, 32039077660065054, 26748691593269032, 35430028866123530, 37323294297426971,
    31429725148403493, 46129932401546318, 20975910242131222, 46129932877548299, 20975910242131222, 44125895738316158,
    47713946889052877, 38464003405787672, 51693911961976816, 33782179366261088, 34519144959980563, 39454604707785400,
    34519144959980563, 33782179366261088, 43456371633959592, 39491837613984526, 47713947259154455, 39454604707785400,
    34519144959980563, 39491837613984526, 34519144959980563, 39454604707785400, 34519144959980563, 44125895738316158,
    53479918569446394, 37323294297426971, 57645892977573297, 40819720124507129, 37323294297426971, 57645892855912781,
    37323294297426971, 37323294297426971, 42696843084615943, 35363936281924318, 40819720124507129, 42696843084615943,
    53479923498880510, 37323294297426971, 35363936281924318, 37323294297426971, 54793115409080014, 35324582726551007,
    30056355651496890, 57645107807820957, 36012340796633578, 55793457238915696, 36012340796633578, 36071877923610942,
    35324582726551007, 30999772146721039, 32704676738267960, 37995062827081033
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
noncomputable def negativeCeiling : ℝ := 364303054521 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 16335018319875931936527482880, coefficient := (-16335018319875931936527482880) }, { argument := 976420569256433736979656474624, coefficient := (-976420569256433736979656474624) }, { argument := 16335018319875931936527482880, coefficient := (-16335018319875931936527482880) }, { argument := 17023234705099948895439421440, coefficient := (-17023234705099948895439421440) }, { argument := 10141070852859779306320035840, coefficient := (-10141070852859779306320035840) }, { argument := 506041459723541881552896000, coefficient := (-506041459723541881552896000) }, { argument := 520017842896858752567214080, coefficient := (-520017842896858752567214080) }, { argument := 20350877506930099319560208384, coefficient := (-20350877506930099319560208384) }, { argument := 20350877506930099319560208384, coefficient := (-20350877506930099319560208384) }, { argument := 520017842896858752567214080, coefficient := (-520017842896858752567214080) }, { argument := 106740976475074597647149957120, coefficient := (-106740976475074597647149957120) }, { argument := 396516127455230427231630131200, coefficient := (-396516127455230427231630131200) }, { argument := 106718507614452271510968074240, coefficient := (-106718507614452271510968074240) }, { argument := 43347408481130732772126621696, coefficient := (-43347408481130732772126621696) }, { argument := 76090052292440843983257600, coefficient := (-76090052292440843983257600) }, { argument := 43347422783152396717548109824, coefficient := (-43347422783152396717548109824) }, { argument := 76090052292440843983257600, coefficient := (-76090052292440843983257600) }, { argument := 43226291878161680885935505408, coefficient := (-43226291878161680885935505408) }, { argument := 2079308817727776192323815211008, coefficient := (-2079308817727776192323815211008) }, { argument := 874275914153984158530464120832, coefficient := (-874275914153984158530464120832) }, { argument := 16405061705842522122419330613248, coefficient := (-16405061705842522122419330613248) }, { argument := 545003167264821293629380231168, coefficient := (-545003167264821293629380231168) }, { argument := 28385581628376109043196887040, coefficient := (-28385581628376109043196887040) }, { argument := 868598797828308936721824743424, coefficient := (-868598797828308936721824743424) }, { argument := 908338612108035489382300385280, coefficient := (-908338612108035489382300385280) }, { argument := 545003167264821293629380231168, coefficient := (-545003167264821293629380231168) }, { argument := 13914612114229968652975114027008, coefficient := (-13914612114229968652975114027008) }, { argument := 891307263131009823956382253056, coefficient := (-891307263131009823956382253056) }, { argument := 2079309351143051199746064515072, coefficient := (-2079309351143051199746064515072) }, { argument := 868598797828308936721824743424, coefficient := (-868598797828308936721824743424) }, { argument := 28385581628376109043196887040, coefficient := (-28385581628376109043196887040) }, { argument := 891307263131009823956382253056, coefficient := (-891307263131009823956382253056) }, { argument := 28385581628376109043196887040, coefficient := (-28385581628376109043196887040) }, { argument := 868598797828308936721824743424, coefficient := (-868598797828308936721824743424) }, { argument := 908338612108035489382300385280, coefficient := (-908338612108035489382300385280) }, { argument := 43226291878161680885935505408, coefficient := (-43226291878161680885935505408) }, { argument := 3535895708164781411779601235968, coefficient := (-3535895708164781411779601235968) }, { argument := 396516127455230427231630131200, coefficient := (-396516127455230427231630131200) }, { argument := 126944152527879261855103794020352, coefficient := (-126944152527879261855103794020352) }, { argument := 4474967724137600535899825766400, coefficient := (-4474967724137600535899825766400) }, { argument := 396516127455230427231630131200, coefficient := (-396516127455230427231630131200) }, { argument := 126944141822851537571769256771584, coefficient := (-126944141822851537571769256771584) }, { argument := 396516127455230427231630131200, coefficient := (-396516127455230427231630131200) }, { argument := 396516127455230427231630131200, coefficient := (-396516127455230427231630131200) }, { argument := 16438425741072552854659866296320, coefficient := (-16438425741072552854659866296320) }, { argument := 407845159668237010866819563520, coefficient := (-407845159668237010866819563520) }, { argument := 4474967724137600535899825766400, coefficient := (-4474967724137600535899825766400) }, { argument := 16438425741072552854659866296320, coefficient := (-16438425741072552854659866296320) }, { argument := 3535907789716472481860437409792, coefficient := (-3535907789716472481860437409792) }, { argument := 396516127455230427231630131200, coefficient := (-396516127455230427231630131200) }, { argument := 407845159668237010866819563520, coefficient := (-407845159668237010866819563520) }, { argument := 396516127455230427231630131200, coefficient := (-396516127455230427231630131200) }, { argument := 35145609316207480506006126985216, coefficient := (-35145609316207480506006126985216) }, { argument := 396870402688436654200357650432, coefficient := (-396870402688436654200357650432) }, { argument := 20596068802194317383651295232, coefficient := (-20596068802194317383651295232) }, { argument := 126875083467543873309612399656960, coefficient := (-126875083467543873309612399656960) }, { argument := 639270289360415928023330586624, coefficient := (-639270289360415928023330586624) }, { argument := 35153937646698330482040163532800, coefficient := (-35153937646698330482040163532800) }, { argument := 639270289360415928023330586624, coefficient := (-639270289360415928023330586624) }, { argument := 666203610101746958448105357312, coefficient := (-666203610101746958448105357312) }, { argument := 396870402688436654200357650432, coefficient := (-396870402688436654200357650432) }, { argument := 19803912309802228253510860800, coefficient := (-19803912309802228253510860800) }, { argument := 16140553816067885127759298560, coefficient := (-16140553816067885127759298560) }, { argument := 631659928772791928880195698688, coefficient := (-631659928772791928880195698688) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7
