import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 9, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 3236230705531362505879075285893120
def positiveArguments : Array ℕ := #[
    441, 5, 3, 3, 3, 3,
    2635, 31535, 47175, 13685, 2635, 54655,
    27455, 2635, 31535, 2635, 4725, 3675,
    525, 4935, 58275, 4095, 3675, 58275,
    525, 4095, 4095, 4095, 4095, 4095,
    4725, 4935, 5, 21, 91, 3,
    3, 7, 91, 91, 3, 1123
  ]
def positiveCoefficients : Array ℕ := #[
    34939619668790572878752882098176, 792281625142643375935439503360, 475368975085586025561263702016, 475368975085586025561263702016, 475368975085586025561263702016, 475368975085586025561263702016,
    50968312554952766005612380160, 1219951223089514592779496325120, 912497208645122101068221644800, 1058825589851276816374657187840, 50968312554952766005612380160, 1057181450736600920697056788480,
    1062113868080628607729857986560, 50968312554952766005612380160, 1219951223089514592779496325120, 50968312554952766005612380160, 91394791962865965607786905600, 71084838193340195472723148800,
    81239815078103080540255027200, 95456782716771119634799656960, 1127202434208680242496038502400, 2534682230436816112855956848640, 71084838193340195472723148800, 1127202434208680242496038502400,
    81239815078103080540255027200, 79208819701150503526748651520, 79208819701150503526748651520, 79208819701150503526748651520, 2534682230436816112855956848640, 79208819701150503526748651520,
    91394791962865965607786905600, 95456782716771119634799656960, 1547425049106725343623905280, 25996740824992985772881608704, 56326271787484802507910152192, 1856910058928070412348686336,
    29710560942849126597578981376, 2166395068749415481073467392, 56326271787484802507910152192, 56326271787484802507910152192, 29710560942849126597578981376, 695103332058741024355858251776
  ]
def positiveScales : Array ℕ := #[
    8, 2, 1, 1, 1, 1,
    11, 14, 15, 13, 11, 15,
    14, 11, 14, 11, 12, 11,
    9, 12, 15, 11, 11, 15,
    9, 11, 11, 11, 11, 11,
    12, 12, 2, 4, 6, 1,
    1, 2, 6, 6, 1, 10
  ]
def negativeArguments : Array ℕ := #[
    9, 3369, 135, 227814447, 273, 21,
    135, 21, 273, 273, 4152765, 117308019,
    4385801613, 35084511963, 940365093, 14880765, 27062275, 14880765,
    5, 3, 85, 105
  ]
def negativeCoefficients : Array ℕ := #[
    87042659012253300578844672, 2036435543140842844792553472, 163204985647974938585333760, 2101217400051334370008498176, 165018374377396882347393024, 6346860552976803167207424,
    163204985647974938585333760, 6346860552976803167207424, 165018374377396882347393024, 165018374377396882347393024, 19151248288314611529154560, 4327902008573714962902417408,
    161807519826147084741919113216, 161798753283115529364729495552, 4336668551605270340092035072, 70272425875459716058384957440, 255595960820402255850949836800, 70272425875459716058384957440,
    792281625142643375935439503360, 1901475900342344102245054808064, 6734393813712468695451235778560, 8318957063997755447322114785280
  ]
def negativeScales : Array ℕ := #[
    3, 11, 7, 27, 8, 4,
    7, 4, 8, 8, 21, 26,
    32, 35, 29, 23, 24, 23,
    2, 1, 6, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8784634845528344, 2321928094887362, 1584962500720924, 1584962500720924, 1584962500720924, 1584962500720924,
    11363587246524576, 14944666312170518, 15525734897375130, 13740307814241047, 11363587246524576, 15738065863454924,
    14744781290819185, 11363587246524576, 14944666312170518, 11363587246524576, 12206098613995797, 11843528534516384,
    9036173612553484, 12268834369343759, 15830589478829897, 11999647735076951, 11843528534516384, 15830589478829897,
    9036173612553484, 11999647735076951, 11999647735076951, 11999647735076951, 11999647735076951, 11999647735076951,
    12206098613995797, 12268834369343759, 2321928094887362, 4392317422778759, 6507794640198673, 1584962500720924,
    1584962500720924, 2807354922011143, 6507794640198673, 6507794640198673, 1584962500720924, 10133142212400601
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3169925001442313, 11718104713231945, 7076815597050831, 27763283998781733, 8092757140919853, 4392317422778766,
    7076815597050831, 4392317422778766, 8092757140919853, 8092757140919853, 21985640821807945, 26805726397028242,
    32030193408721383, 35030115243066318, 29808645746019874, 23826945360672637, 24689779789364667, 23826945360672637,
    2321928094887363, 1584962500724866, 6409390936137712, 6714245517766967
  ]

abbrev PositiveTerm := Fin 42
abbrev NegativeTerm := Fin 22
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
noncomputable def positiveFloor : ℝ := 1588863849 / 250000000000
noncomputable def negativeCeiling : ℝ := 300244633 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 87042659012253300578844672, coefficient := (-87042659012253300578844672) }, { argument := 2036435543140842844792553472, coefficient := (-2036435543140842844792553472) }, { argument := 163204985647974938585333760, coefficient := (-163204985647974938585333760) }, { argument := 2101217400051334370008498176, coefficient := (-2101217400051334370008498176) }, { argument := 165018374377396882347393024, coefficient := (-165018374377396882347393024) }, { argument := 6346860552976803167207424, coefficient := (-6346860552976803167207424) }, { argument := 163204985647974938585333760, coefficient := (-163204985647974938585333760) }, { argument := 6346860552976803167207424, coefficient := (-6346860552976803167207424) }, { argument := 165018374377396882347393024, coefficient := (-165018374377396882347393024) }, { argument := 165018374377396882347393024, coefficient := (-165018374377396882347393024) }, { argument := 19151248288314611529154560, coefficient := (-19151248288314611529154560) }, { argument := 4327902008573714962902417408, coefficient := (-4327902008573714962902417408) }, { argument := 161807519826147084741919113216, coefficient := (-161807519826147084741919113216) }, { argument := 161798753283115529364729495552, coefficient := (-161798753283115529364729495552) }, { argument := 4336668551605270340092035072, coefficient := (-4336668551605270340092035072) }, { argument := 70272425875459716058384957440, coefficient := (-70272425875459716058384957440) }, { argument := 255595960820402255850949836800, coefficient := (-255595960820402255850949836800) }, { argument := 70272425875459716058384957440, coefficient := (-70272425875459716058384957440) }, { argument := 34939619668790572878752882098176, coefficient := 34939619668790572878752882098176 }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 1901475900342344102245054808064, coefficient := (-1901475900342344102245054808064) }, { argument := 50968312554952766005612380160, coefficient := 50968312554952766005612380160 }, { argument := 1219951223089514592779496325120, coefficient := 1219951223089514592779496325120 }, { argument := 912497208645122101068221644800, coefficient := 912497208645122101068221644800 }, { argument := 1058825589851276816374657187840, coefficient := 1058825589851276816374657187840 }, { argument := 50968312554952766005612380160, coefficient := 50968312554952766005612380160 }, { argument := 1057181450736600920697056788480, coefficient := 1057181450736600920697056788480 }, { argument := 1062113868080628607729857986560, coefficient := 1062113868080628607729857986560 }, { argument := 50968312554952766005612380160, coefficient := 50968312554952766005612380160 }, { argument := 1219951223089514592779496325120, coefficient := 1219951223089514592779496325120 }, { argument := 50968312554952766005612380160, coefficient := 50968312554952766005612380160 }, { argument := 6734393813712468695451235778560, coefficient := (-6734393813712468695451235778560) }, { argument := 91394791962865965607786905600, coefficient := 91394791962865965607786905600 }, { argument := 71084838193340195472723148800, coefficient := 71084838193340195472723148800 }, { argument := 81239815078103080540255027200, coefficient := 81239815078103080540255027200 }, { argument := 95456782716771119634799656960, coefficient := 95456782716771119634799656960 }, { argument := 1127202434208680242496038502400, coefficient := 1127202434208680242496038502400 }, { argument := 2534682230436816112855956848640, coefficient := 2534682230436816112855956848640 }, { argument := 71084838193340195472723148800, coefficient := 71084838193340195472723148800 }, { argument := 1127202434208680242496038502400, coefficient := 1127202434208680242496038502400 }, { argument := 81239815078103080540255027200, coefficient := 81239815078103080540255027200 }, { argument := 79208819701150503526748651520, coefficient := 79208819701150503526748651520 }, { argument := 79208819701150503526748651520, coefficient := 79208819701150503526748651520 }, { argument := 79208819701150503526748651520, coefficient := 79208819701150503526748651520 }, { argument := 2534682230436816112855956848640, coefficient := 2534682230436816112855956848640 }, { argument := 79208819701150503526748651520, coefficient := 79208819701150503526748651520 }, { argument := 91394791962865965607786905600, coefficient := 91394791962865965607786905600 }, { argument := 95456782716771119634799656960, coefficient := 95456782716771119634799656960 }, { argument := 8318957063997755447322114785280, coefficient := (-8318957063997755447322114785280) }, { argument := 1547425049106725343623905280, coefficient := 1547425049106725343623905280 }, { argument := 25996740824992985772881608704, coefficient := 25996740824992985772881608704 }, { argument := 56326271787484802507910152192, coefficient := 56326271787484802507910152192 }, { argument := 1856910058928070412348686336, coefficient := 1856910058928070412348686336 }, { argument := 29710560942849126597578981376, coefficient := 29710560942849126597578981376 }, { argument := 2166395068749415481073467392, coefficient := 2166395068749415481073467392 }, { argument := 56326271787484802507910152192, coefficient := 56326271787484802507910152192 }, { argument := 56326271787484802507910152192, coefficient := 56326271787484802507910152192 }, { argument := 29710560942849126597578981376, coefficient := 29710560942849126597578981376 }, { argument := 695103332058741024355858251776, coefficient := 695103332058741024355858251776 }] }

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


end Parent2

namespace Parent2

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1266496674186546684972642993176576)
def positiveArguments : Array ℕ := #[
    45, 21, 91, 7, 45, 7,
    91, 91, 3, 14880765, 27062275, 14880765,
    116111, 4340337, 69441679, 1861489, 725609, 3475049,
    2270200361, 3475049, 1451141, 32873133, 2760533331, 1380266595,
    16436637, 112184143, 501, 562934961, 807, 25,
    807, 539, 112249679, 501, 3, 2675,
    2445, 2675, 2445
  ]
def positiveCoefficients : Array ℕ := #[
    55707301767842112370460590080, 25996740824992985772881608704, 56326271787484802507910152192, 2166395068749415481073467392, 55707301767842112370460590080, 2166395068749415481073467392,
    56326271787484802507910152192, 56326271787484802507910152192, 1856910058928070412348686336, 140544851750919432116769914880, 511191921640804511701899673600, 140544851750919432116769914880,
    35092396460318552026077200384, 1311786366282175187064169955328, 1311716229695171607093456142336, 35162533047322131996791013376, 6853183242537120787729481728, 1050269115131499374733380550656,
    10720718094184968880074581344256, 1050269115131499374733380550656, 6852819620317939825048027136, 155238981466116068772642029568, 13036250077158896140552425701376, 13036249411305222055932450570240,
    155239647319790153392617160704, 529774636812655329012537622528, 155051989920493879431115309056, 5316770383723861792911588851712, 249754402925825470460898312192, 7737125245533626718119526400,
    249754402925825470460898312192, 166812420293704992042656989184, 530084121822476674081262403584, 155051989920493879431115309056, 7427640235712281649394745344, 206968100318024514709697331200,
    189172712253297173258022420480, 206968100318024514709697331200, 189172712253297173258022420480
  ]
def positiveScales : Array ℕ := #[
    5, 4, 6, 2, 5, 2,
    6, 6, 1, 23, 24, 23,
    16, 22, 26, 20, 19, 21,
    31, 21, 20, 24, 31, 30,
    23, 26, 8, 29, 9, 4,
    9, 9, 26, 8, 1, 11,
    11, 11, 11
  ]
def negativeArguments : Array ℕ := #[
    1, 5, 17, 81, 333, 93,
    5
  ]
def negativeCoefficients : Array ℕ := #[
    1267650600228229401496703205376, 792281625142643375935439503360, 2693757525484987478180494311424, 12834962327310822690154119954432, 26382978117250024418650135461888, 7368219113826583396199587381248,
    792281625142643375935439503360
  ]
def negativeScales : Array ℕ := #[
    0, 2, 4, 6, 8, 6,
    2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5491853096329661, 4392317422778759, 6507794640198673, 2807354922011143, 5491853096329661, 2807354922011143,
    6507794640198673, 6507794640198673, 1584962500720924, 23826945359495917, 24689779789304327, 23826945359495917,
    16825145129551714, 22049375632582305, 26049298494708354, 20828025660226035, 19468832824700764, 21728601890046202,
    31080172485011235, 21728601890046202, 20468756274888577, 24970405623472819, 31362299874488728, 30362299800800067,
    23970411811491512, 26741293527440654, 8968666792316714, 29068393008468365, 9656424863276222, 4643856189773592,
    9656424863276222, 9074141462752505, 26742136078389706, 8968666792316714, 1584962500720924, 11385323176175871,
    11255618749839595, 11385323176175871, 11255618749839595
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 2321928094887363, 4087462841250340, 6339850002884626, 8379378367071265, 6539158811108986,
    2321928094887363
  ]

abbrev PositiveTerm := Fin 39
abbrev NegativeTerm := Fin 7
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
noncomputable def positiveFloor : ℝ := 711620317 / 40000000000
noncomputable def negativeCeiling : ℝ := 439733769 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 55707301767842112370460590080, coefficient := 55707301767842112370460590080 }, { argument := 25996740824992985772881608704, coefficient := 25996740824992985772881608704 }, { argument := 56326271787484802507910152192, coefficient := 56326271787484802507910152192 }, { argument := 2166395068749415481073467392, coefficient := 2166395068749415481073467392 }, { argument := 55707301767842112370460590080, coefficient := 55707301767842112370460590080 }, { argument := 2166395068749415481073467392, coefficient := 2166395068749415481073467392 }, { argument := 56326271787484802507910152192, coefficient := 56326271787484802507910152192 }, { argument := 56326271787484802507910152192, coefficient := 56326271787484802507910152192 }, { argument := 1856910058928070412348686336, coefficient := 1856910058928070412348686336 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 140544851750919432116769914880, coefficient := 140544851750919432116769914880 }, { argument := 511191921640804511701899673600, coefficient := 511191921640804511701899673600 }, { argument := 140544851750919432116769914880, coefficient := 140544851750919432116769914880 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 35092396460318552026077200384, coefficient := 35092396460318552026077200384 }, { argument := 1311786366282175187064169955328, coefficient := 1311786366282175187064169955328 }, { argument := 1311716229695171607093456142336, coefficient := 1311716229695171607093456142336 }, { argument := 35162533047322131996791013376, coefficient := 35162533047322131996791013376 }, { argument := 2693757525484987478180494311424, coefficient := (-2693757525484987478180494311424) }, { argument := 6853183242537120787729481728, coefficient := 6853183242537120787729481728 }, { argument := 1050269115131499374733380550656, coefficient := 1050269115131499374733380550656 }, { argument := 10720718094184968880074581344256, coefficient := 10720718094184968880074581344256 }, { argument := 1050269115131499374733380550656, coefficient := 1050269115131499374733380550656 }, { argument := 6852819620317939825048027136, coefficient := 6852819620317939825048027136 }, { argument := 12834962327310822690154119954432, coefficient := (-12834962327310822690154119954432) }, { argument := 155238981466116068772642029568, coefficient := 155238981466116068772642029568 }, { argument := 13036250077158896140552425701376, coefficient := 13036250077158896140552425701376 }, { argument := 13036249411305222055932450570240, coefficient := 13036249411305222055932450570240 }, { argument := 155239647319790153392617160704, coefficient := 155239647319790153392617160704 }, { argument := 26382978117250024418650135461888, coefficient := (-26382978117250024418650135461888) }, { argument := 529774636812655329012537622528, coefficient := 529774636812655329012537622528 }, { argument := 155051989920493879431115309056, coefficient := 155051989920493879431115309056 }, { argument := 5316770383723861792911588851712, coefficient := 5316770383723861792911588851712 }, { argument := 249754402925825470460898312192, coefficient := 249754402925825470460898312192 }, { argument := 7737125245533626718119526400, coefficient := 7737125245533626718119526400 }, { argument := 249754402925825470460898312192, coefficient := 249754402925825470460898312192 }, { argument := 166812420293704992042656989184, coefficient := 166812420293704992042656989184 }, { argument := 530084121822476674081262403584, coefficient := 530084121822476674081262403584 }, { argument := 155051989920493879431115309056, coefficient := 155051989920493879431115309056 }, { argument := 7427640235712281649394745344, coefficient := 7427640235712281649394745344 }, { argument := 7368219113826583396199587381248, coefficient := (-7368219113826583396199587381248) }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9
