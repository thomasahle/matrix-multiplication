import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 19, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-5115313802691403353501512929116160)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4232288289, 44112433035, 4232288289, 57311283, 6518788731, 244927638917,
    489818229043, 13074626253, 7026697233, 12778806255, 7026697233, 16809318099,
    631569262893, 1263042991947, 33714170037, 2630326997553, 4783533141455, 2630326997553,
    29415, 29415, 105400458495, 191682093825, 105400458495, 2067,
    2067, 2655682920627, 1663730079, 85380852643789, 26181857559, 788082669,
    683038560317723, 788082669, 788082669, 67512415311, 788082669, 26181857559,
    67512415311, 21253724197605, 788082669, 788082669, 1663730079, 816795501758369,
    2071119801, 116355045, 2957440311507451, 6290929433, 204198824458137, 6290929433,
    6290929433, 2071119801, 116355045, 44092568969, 2242338423, 44092568969,
    2242338423, 213143149401, 387623789735, 213143149401, 29415, 29415,
    265, 265, 3219735, 237769005
  ]
def negativeCoefficients : Array ℕ := #[
    39035969456670544045918912512, 406865381332647849850338017280, 39035969456670544045918912512, 264301642509235243116920832, 60125213695669429220721819648, 2259058735839921345468810919936,
    2258887878448467007025679695872, 60296071087123767663853043712, 259239371081188108771635757056, 942909474214015196975144632320, 259239371081188108771635757056, 310077189025826956048003497984,
    11650396557408557574290656985088, 11649515413269351588072234418176, 310958333165032942266426064896, 6065121119253630128136394899456, 22060152907132063879230987960320, 6065121119253630128136394899456,
    284484423871714537391857336320, 284484423871714537391857336320, 486073820777227703946817044480, 1767955264151278494328396185600, 486073820777227703946817044480, 639705515300720257054122442752,
    639705515300720257054122442752, 47840530446999790821958483968, 7672600743761393533285564416, 1538084704604573474591264997376, 60371253220648859643483783168, 7268779651984478084165271552,
    1538066102863288679366398050304, 7268779651984478084165271552, 7268779651984478084165271552, 311346061760001811271745798144, 7268779651984478084165271552, 60371253220648859643483783168,
    311346061760001811271745798144, 47859132188284586046825431040, 7268779651984478084165271552, 7268779651984478084165271552, 7672600743761393533285564416, 919629979339221984686957920256,
    38205416915039255874729148416, 2146371736799958195209502720, 3329781771218859984243260391424, 58023582618158869877163556864, 919629749739159117981340925952, 58023582618158869877163556864,
    58023582618158869877163556864, 38205416915039255874729148416, 2146371736799958195209502720, 203341083830882606075636350976, 10340960753931617932664635392, 203341083830882606075636350976,
    10340960753931617932664635392, 491474641008085789546226122752, 1787599211530737144265378365440, 491474641008085789546226122752, 284484423871714537391857336320, 284484423871714537391857336320,
    20503381900664110803016744960, 20503381900664110803016744960, 14848406882541305793085440, 2193031991947783373366231040
  ]
def negativeScales : Array ℕ := #[
    31, 35, 31, 25, 32, 37,
    38, 33, 32, 33, 32, 33,
    39, 40, 34, 41, 42, 41,
    14, 14, 36, 37, 36, 11,
    11, 41, 30, 46, 34, 29,
    49, 29, 29, 35, 29, 34,
    35, 44, 29, 29, 30, 49,
    30, 26, 51, 32, 47, 32,
    32, 30, 26, 35, 31, 35,
    31, 37, 38, 37, 14, 14,
    8, 8, 21, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31978790773050458, 35360466283793122, 31978790773050458, 25772315858106994, 32601956773337866, 37833564629371802,
    38833455511164541, 33606050655532244, 32710199590997660, 33573034020651769, 32710199590997660, 33968542163257568,
    39200150003827261, 40200040885622682, 34972636046443361, 41258379302585257, 42121213732328581, 41258379302585257,
    14844264417352541, 14844264417352541, 36617090186523343, 37479924616257791, 36617090186523343, 11013322673425448,
    11013322673425448, 41272220042808030, 30631774245846746, 46278977803462840, 34607848406594975, 29553771733833656,
    49278960355267622, 29553771733833656, 29553771733833656, 35974433797961469, 29553771733833656, 34607848406594975,
    35974433797961469, 44272780894111002, 29553771733833656, 29553771733833656, 30631774245846746, 49536968249477138,
    30947763870652839, 26793958525107394, 51393270474999368, 32550626033146626, 47536967889285626, 32550626033146626,
    32550626033146626, 30947763870652839, 26793958525107394, 35359816484136788, 31062356886071742, 35359816484136788,
    31062356886071742, 37633031730397105, 38495866160126912, 37633031730397105, 14844264417352541, 14844264417352541,
    8049848549450562, 8049848549450562, 21618510521673872, 27824985421223289
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
noncomputable def negativeCeiling : ℝ := 39972541891 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 39035969456670544045918912512, coefficient := (-39035969456670544045918912512) }, { argument := 406865381332647849850338017280, coefficient := (-406865381332647849850338017280) }, { argument := 39035969456670544045918912512, coefficient := (-39035969456670544045918912512) }, { argument := 264301642509235243116920832, coefficient := (-264301642509235243116920832) }, { argument := 60125213695669429220721819648, coefficient := (-60125213695669429220721819648) }, { argument := 2259058735839921345468810919936, coefficient := (-2259058735839921345468810919936) }, { argument := 2258887878448467007025679695872, coefficient := (-2258887878448467007025679695872) }, { argument := 60296071087123767663853043712, coefficient := (-60296071087123767663853043712) }, { argument := 259239371081188108771635757056, coefficient := (-259239371081188108771635757056) }, { argument := 942909474214015196975144632320, coefficient := (-942909474214015196975144632320) }, { argument := 259239371081188108771635757056, coefficient := (-259239371081188108771635757056) }, { argument := 310077189025826956048003497984, coefficient := (-310077189025826956048003497984) }, { argument := 11650396557408557574290656985088, coefficient := (-11650396557408557574290656985088) }, { argument := 11649515413269351588072234418176, coefficient := (-11649515413269351588072234418176) }, { argument := 310958333165032942266426064896, coefficient := (-310958333165032942266426064896) }, { argument := 6065121119253630128136394899456, coefficient := (-6065121119253630128136394899456) }, { argument := 22060152907132063879230987960320, coefficient := (-22060152907132063879230987960320) }, { argument := 6065121119253630128136394899456, coefficient := (-6065121119253630128136394899456) }, { argument := 284484423871714537391857336320, coefficient := (-284484423871714537391857336320) }, { argument := 284484423871714537391857336320, coefficient := (-284484423871714537391857336320) }, { argument := 486073820777227703946817044480, coefficient := (-486073820777227703946817044480) }, { argument := 1767955264151278494328396185600, coefficient := (-1767955264151278494328396185600) }, { argument := 486073820777227703946817044480, coefficient := (-486073820777227703946817044480) }, { argument := 639705515300720257054122442752, coefficient := (-639705515300720257054122442752) }, { argument := 639705515300720257054122442752, coefficient := (-639705515300720257054122442752) }, { argument := 47840530446999790821958483968, coefficient := (-47840530446999790821958483968) }, { argument := 7672600743761393533285564416, coefficient := (-7672600743761393533285564416) }, { argument := 1538084704604573474591264997376, coefficient := (-1538084704604573474591264997376) }, { argument := 60371253220648859643483783168, coefficient := (-60371253220648859643483783168) }, { argument := 7268779651984478084165271552, coefficient := (-7268779651984478084165271552) }, { argument := 1538066102863288679366398050304, coefficient := (-1538066102863288679366398050304) }, { argument := 7268779651984478084165271552, coefficient := (-7268779651984478084165271552) }, { argument := 7268779651984478084165271552, coefficient := (-7268779651984478084165271552) }, { argument := 311346061760001811271745798144, coefficient := (-311346061760001811271745798144) }, { argument := 7268779651984478084165271552, coefficient := (-7268779651984478084165271552) }, { argument := 60371253220648859643483783168, coefficient := (-60371253220648859643483783168) }, { argument := 311346061760001811271745798144, coefficient := (-311346061760001811271745798144) }, { argument := 47859132188284586046825431040, coefficient := (-47859132188284586046825431040) }, { argument := 7268779651984478084165271552, coefficient := (-7268779651984478084165271552) }, { argument := 7268779651984478084165271552, coefficient := (-7268779651984478084165271552) }, { argument := 7672600743761393533285564416, coefficient := (-7672600743761393533285564416) }, { argument := 919629979339221984686957920256, coefficient := (-919629979339221984686957920256) }, { argument := 38205416915039255874729148416, coefficient := (-38205416915039255874729148416) }, { argument := 2146371736799958195209502720, coefficient := (-2146371736799958195209502720) }, { argument := 3329781771218859984243260391424, coefficient := (-3329781771218859984243260391424) }, { argument := 58023582618158869877163556864, coefficient := (-58023582618158869877163556864) }, { argument := 919629749739159117981340925952, coefficient := (-919629749739159117981340925952) }, { argument := 58023582618158869877163556864, coefficient := (-58023582618158869877163556864) }, { argument := 58023582618158869877163556864, coefficient := (-58023582618158869877163556864) }, { argument := 38205416915039255874729148416, coefficient := (-38205416915039255874729148416) }, { argument := 2146371736799958195209502720, coefficient := (-2146371736799958195209502720) }, { argument := 203341083830882606075636350976, coefficient := (-203341083830882606075636350976) }, { argument := 10340960753931617932664635392, coefficient := (-10340960753931617932664635392) }, { argument := 203341083830882606075636350976, coefficient := (-203341083830882606075636350976) }, { argument := 10340960753931617932664635392, coefficient := (-10340960753931617932664635392) }, { argument := 491474641008085789546226122752, coefficient := (-491474641008085789546226122752) }, { argument := 1787599211530737144265378365440, coefficient := (-1787599211530737144265378365440) }, { argument := 491474641008085789546226122752, coefficient := (-491474641008085789546226122752) }, { argument := 284484423871714537391857336320, coefficient := (-284484423871714537391857336320) }, { argument := 284484423871714537391857336320, coefficient := (-284484423871714537391857336320) }, { argument := 20503381900664110803016744960, coefficient := (-20503381900664110803016744960) }, { argument := 20503381900664110803016744960, coefficient := (-20503381900664110803016744960) }, { argument := 14848406882541305793085440, coefficient := (-14848406882541305793085440) }, { argument := 2193031991947783373366231040, coefficient := (-2193031991947783373366231040) }] }

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

end TermShard4


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 53549696428541020581012190485544960
def positiveArguments : Array ℕ := #[
    7095, 4815, 3745, 535, 5029, 59385,
    4173, 3745
  ]
def positiveCoefficients : Array ℕ := #[
    562123813038705475226194327633920, 93135645143111031619363799040, 72438835111308580148394065920, 82787240127209805883878932480, 97275007149471521913557745664, 1148672956765036056638820188160,
    2582961891968945943577022693376, 72438835111308580148394065920
  ]
def positiveScales : Array ℕ := #[
    12, 12, 11, 9, 12, 15,
    12, 11
  ]
def negativeArguments : Array ℕ := #[
    2478226575, 237769005, 3219735, 196217721, 7372403847, 14743692513,
    393550623, 16395626877, 29817214595, 16395626877, 196217721, 7372403847,
    14743692513, 393550623, 105400458495, 191682093825, 105400458495, 2067,
    2067, 16395626877, 29817214595, 16395626877, 2067, 2067,
    414237411, 15563963677, 31125573083, 830829093, 213143149401, 387623789735,
    213143149401, 2067, 2067, 213143149401, 387623789735, 213143149401,
    2067, 2067, 2067, 2067, 72981961884993, 28045947,
    1575615, 265162108709339, 85188251, 18245489194041, 85188251, 85188251,
    28045947, 1575615, 5479910007, 26780041, 5479910007, 26780041,
    2491, 2491
  ]
def negativeCoefficients : Array ℕ := #[
    22857605692845384823052697600, 2193031991947783373366231040, 14848406882541305793085440, 7239156164027088468046774272, 271993693947281499788886933504, 271973122488778636297406251008,
    7259727622529951959527456768, 18902870808003299597931773952, 68753815828105274779437629440, 18902870808003299597931773952, 7239156164027088468046774272, 271993693947281499788886933504,
    271973122488778636297406251008, 7259727622529951959527456768, 486073820777227703946817044480, 1767955264151278494328396185600, 486073820777227703946817044480, 19990797353147508032941326336,
    19990797353147508032941326336, 18902870808003299597931773952, 68753815828105274779437629440, 18902870808003299597931773952, 19990797353147508032941326336, 19990797353147508032941326336,
    7641331506473037827382706176, 287104454722130471999380652032, 287082740404821893869484376064, 7663045823781615957278982144, 491474641008085789546226122752, 1787599211530737144265378365440,
    491474641008085789546226122752, 19990797353147508032941326336, 19990797353147508032941326336, 491474641008085789546226122752, 1787599211530737144265378365440, 491474641008085789546226122752,
    639705515300720257054122442752, 639705515300720257054122442752, 19990797353147508032941326336, 19990797353147508032941326336, 20542596021876388540509585408, 258678203306911089008050176,
    14532483331848937584721920, 74636498373509629527808016384, 392861466070982946040315904, 20542594583868864746785603584, 392861466070982946040315904, 392861466070982946040315904,
    258678203306911089008050176, 14532483331848937584721920, 25271624361522229378000355328, 123501140652612203592024064, 25271624361522229378000355328, 123501140652612203592024064,
    24091473733280330193544675328, 24091473733280330193544675328
  ]
def negativeScales : Array ℕ := #[
    31, 27, 21, 27, 32, 33,
    28, 33, 34, 33, 27, 32,
    33, 28, 36, 37, 36, 11,
    11, 33, 34, 33, 11, 11,
    28, 33, 34, 29, 37, 38,
    37, 11, 11, 37, 38, 37,
    11, 11, 11, 11, 46, 24,
    20, 47, 26, 44, 26, 26,
    24, 20, 32, 24, 32, 24,
    11, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12792586968913521, 12233320082730821, 11870750003187727, 9063395081288509, 12296055838078784, 15857810947514299,
    12026869205263395, 11870750003187727
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    31206660947714085, 27824985421223289, 21618510521673872, 27547880100577351, 32779487955777283, 33779378837571737,
    28551973982771183, 33932592019987913, 34795426442573932, 33932592019987913, 27547880100577351, 32779487955777283,
    33779378837571737, 28551973982771183, 36617090186523343, 37479924616257791, 36617090186523343, 11013322673425448,
    11013322673425448, 33932592019987913, 34795426442573932, 33932592019987913, 11013322673425448, 11013322673425448,
    28625882612588771, 33857490469352804, 34857381351144109, 29629976494783738, 37633031730397105, 38495866160126912,
    37633031730397105, 11013322673425448, 11013322673425448, 37633031730397105, 38495866160126912, 37633031730397105,
    11013322673425448, 11013322673425448, 11013322673425448, 11013322673425448, 46052605167189083, 24741288962308597,
    20587483626047870, 47913867965108004, 26344151134652641, 44052605066198614, 26344151134652641, 26344151134652641,
    24741288962308597, 20587483626047870, 32351505054923728, 24674654833667892, 32351505054923728, 24674654833667892,
    11282509306240837, 11282509306240837
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 56
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
noncomputable def positiveFloor : ℝ := 87209764093 / 1000000000000
noncomputable def negativeCeiling : ℝ := 4842498307 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 22857605692845384823052697600, coefficient := (-22857605692845384823052697600) }, { argument := 2193031991947783373366231040, coefficient := (-2193031991947783373366231040) }, { argument := 14848406882541305793085440, coefficient := (-14848406882541305793085440) }, { argument := 7239156164027088468046774272, coefficient := (-7239156164027088468046774272) }, { argument := 271993693947281499788886933504, coefficient := (-271993693947281499788886933504) }, { argument := 271973122488778636297406251008, coefficient := (-271973122488778636297406251008) }, { argument := 7259727622529951959527456768, coefficient := (-7259727622529951959527456768) }, { argument := 18902870808003299597931773952, coefficient := (-18902870808003299597931773952) }, { argument := 68753815828105274779437629440, coefficient := (-68753815828105274779437629440) }, { argument := 18902870808003299597931773952, coefficient := (-18902870808003299597931773952) }, { argument := 7239156164027088468046774272, coefficient := (-7239156164027088468046774272) }, { argument := 271993693947281499788886933504, coefficient := (-271993693947281499788886933504) }, { argument := 271973122488778636297406251008, coefficient := (-271973122488778636297406251008) }, { argument := 7259727622529951959527456768, coefficient := (-7259727622529951959527456768) }, { argument := 486073820777227703946817044480, coefficient := (-486073820777227703946817044480) }, { argument := 1767955264151278494328396185600, coefficient := (-1767955264151278494328396185600) }, { argument := 486073820777227703946817044480, coefficient := (-486073820777227703946817044480) }, { argument := 19990797353147508032941326336, coefficient := (-19990797353147508032941326336) }, { argument := 19990797353147508032941326336, coefficient := (-19990797353147508032941326336) }, { argument := 18902870808003299597931773952, coefficient := (-18902870808003299597931773952) }, { argument := 68753815828105274779437629440, coefficient := (-68753815828105274779437629440) }, { argument := 18902870808003299597931773952, coefficient := (-18902870808003299597931773952) }, { argument := 19990797353147508032941326336, coefficient := (-19990797353147508032941326336) }, { argument := 19990797353147508032941326336, coefficient := (-19990797353147508032941326336) }, { argument := 7641331506473037827382706176, coefficient := (-7641331506473037827382706176) }, { argument := 287104454722130471999380652032, coefficient := (-287104454722130471999380652032) }, { argument := 287082740404821893869484376064, coefficient := (-287082740404821893869484376064) }, { argument := 7663045823781615957278982144, coefficient := (-7663045823781615957278982144) }, { argument := 491474641008085789546226122752, coefficient := (-491474641008085789546226122752) }, { argument := 1787599211530737144265378365440, coefficient := (-1787599211530737144265378365440) }, { argument := 491474641008085789546226122752, coefficient := (-491474641008085789546226122752) }, { argument := 19990797353147508032941326336, coefficient := (-19990797353147508032941326336) }, { argument := 19990797353147508032941326336, coefficient := (-19990797353147508032941326336) }, { argument := 491474641008085789546226122752, coefficient := (-491474641008085789546226122752) }, { argument := 1787599211530737144265378365440, coefficient := (-1787599211530737144265378365440) }, { argument := 491474641008085789546226122752, coefficient := (-491474641008085789546226122752) }, { argument := 639705515300720257054122442752, coefficient := (-639705515300720257054122442752) }, { argument := 639705515300720257054122442752, coefficient := (-639705515300720257054122442752) }, { argument := 19990797353147508032941326336, coefficient := (-19990797353147508032941326336) }, { argument := 19990797353147508032941326336, coefficient := (-19990797353147508032941326336) }, { argument := 20542596021876388540509585408, coefficient := (-20542596021876388540509585408) }, { argument := 258678203306911089008050176, coefficient := (-258678203306911089008050176) }, { argument := 14532483331848937584721920, coefficient := (-14532483331848937584721920) }, { argument := 74636498373509629527808016384, coefficient := (-74636498373509629527808016384) }, { argument := 392861466070982946040315904, coefficient := (-392861466070982946040315904) }, { argument := 20542594583868864746785603584, coefficient := (-20542594583868864746785603584) }, { argument := 392861466070982946040315904, coefficient := (-392861466070982946040315904) }, { argument := 392861466070982946040315904, coefficient := (-392861466070982946040315904) }, { argument := 258678203306911089008050176, coefficient := (-258678203306911089008050176) }, { argument := 14532483331848937584721920, coefficient := (-14532483331848937584721920) }, { argument := 25271624361522229378000355328, coefficient := (-25271624361522229378000355328) }, { argument := 123501140652612203592024064, coefficient := (-123501140652612203592024064) }, { argument := 25271624361522229378000355328, coefficient := (-25271624361522229378000355328) }, { argument := 123501140652612203592024064, coefficient := (-123501140652612203592024064) }, { argument := 24091473733280330193544675328, coefficient := (-24091473733280330193544675328) }, { argument := 24091473733280330193544675328, coefficient := (-24091473733280330193544675328) }, { argument := 562123813038705475226194327633920, coefficient := 562123813038705475226194327633920 }, { argument := 93135645143111031619363799040, coefficient := 93135645143111031619363799040 }, { argument := 72438835111308580148394065920, coefficient := 72438835111308580148394065920 }, { argument := 82787240127209805883878932480, coefficient := 82787240127209805883878932480 }, { argument := 97275007149471521913557745664, coefficient := 97275007149471521913557745664 }, { argument := 1148672956765036056638820188160, coefficient := 1148672956765036056638820188160 }, { argument := 2582961891968945943577022693376, coefficient := 2582961891968945943577022693376 }, { argument := 72438835111308580148394065920, coefficient := 72438835111308580148394065920 }] }

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

end TermShard5


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19
