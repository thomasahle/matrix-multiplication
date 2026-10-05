import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 5, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-288209593352277103112021872738304)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    8388605, 6165606821, 24599340197, 12226068497, 24599340197, 2216412605299,
    45792093, 73667150987365, 302399529, 14947053, 150964635, 307090215,
    277876750981, 45792093, 14947053, 3255, 78855, 59745,
    33285, 3255, 33285, 66465, 3255, 78855,
    3255, 156060784989, 15382739379875, 895585, 72615, 15563815,
    28150415, 15382740147875, 15563815, 459895, 459895, 895585,
    895585, 28150415, 895585, 156060016989, 72615, 8388611,
    22144394199, 88351447767, 43911906683, 88351447767, 21715552018871, 6997884615,
    728317053761345, 46186703163, 2283537159, 23056543377, 46922821173, 2722691591393,
    6997884615, 2283537159, 36735, 889935, 674265, 375645,
    36735, 375645, 750105, 36735
  ]
def negativeCoefficients : Array ℕ := #[
    39614067090032720187836334080, 28433842771526234554115293184, 28361108312260931498144694272, 28191394573975224367546630144, 28361108312260931498144694272, 1247729372915480828510732288,
    13515440322728106281410756608, 41470919217017885060633722880, 11156573438946619382959177728, 551448922694345149221175296, 11139223944103902222892400640, 11329629207290884106622074880,
    1251445632172955708818456576, 13515440322728106281410756608, 551448922694345149221175296, 15371302901740695170580480, 372382209006685873325998080, 282137785519046953292267520,
    314367936764632281875742720, 15371302901740695170580480, 314367936764632281875742720, 313872088283930969128304640, 15371302901740695170580480, 372382209006685873325998080,
    15371302901740695170580480, 175708823280901873924571136, 17319424834785626178977792000, 66082509165012675136061440, 85728660538394821798133760, 1148406848462247300337500160,
    2077134004294857869817282560, 17319425699476754634113024000, 1148406848462247300337500160, 67868522926229233923522560, 67868522926229233923522560, 66082509165012675136061440,
    66082509165012675136061440, 2077134004294857869817282560, 66082509165012675136061440, 175707958589773418789339136, 85728660538394821798133760, 39614095424231617405707616256,
    102122993114072855804060368896, 101862284093722890470625902592, 101253963046239638025945481216, 101862284093722890470625902592, 48899075990166028860950315008, 516352746201017988928619151360,
    1640024205963585422084339138560, 425997146428126226383009480704, 21061912777439398044182249472, 425318154899901962133524447232, 432786636697385410609790582784, 49047651345769190217022963712,
    516352746201017988928619151360, 21061912777439398044182249472, 173476132748216416925122560, 4202599215932597713250549760, 3184126436572101330012733440, 3547866714915135752597667840,
    173476132748216416925122560, 3547866714915135752597667840, 3542270710632935223019438080, 173476132748216416925122560
  ]
def negativeScales : Array ℕ := #[
    22, 32, 34, 33, 34, 41,
    25, 46, 28, 23, 27, 28,
    38, 25, 23, 11, 16, 15,
    15, 11, 15, 16, 11, 16,
    11, 37, 43, 19, 16, 23,
    24, 43, 23, 18, 18, 19,
    19, 24, 19, 37, 16, 23,
    34, 36, 35, 36, 44, 32,
    49, 35, 31, 34, 35, 41,
    32, 31, 15, 19, 19, 18,
    15, 18, 19, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    22999999507728155, 32521595746111208, 34517900569020668, 33509241503864245, 34517900569020668, 41011363615797370,
    25448595171387545, 46066086682270291, 28171880651601359, 23833357732407132, 27169635382253639, 28194087302686284,
    38015654177876577, 25448595171387545, 23833357732407132, 11668441828086828, 16266914615180395, 15866530362339582,
    15022584547805530, 11668441828086828, 15022584547805530, 16020307207094464, 11668441828086828, 16266914615180395,
    11668441828086828, 37183317105680049, 43806377677612589, 19772470839741812, 16147979974469375, 23891692404836528,
    24746652855430418, 43806377749640708, 23891692404836528, 18810944987998023, 18810944987998023, 19772470839741812,
    19772470839741812, 24746652855430418, 19772470839741812, 37183310005930309, 16147979974469375, 23000000515947861,
    34366222479036430, 36362534724501203, 35353893127437097, 36362534724501203, 44303793860735310, 32704271730884725,
    49371559955101981, 35426758518222718, 31088623120238042, 34424457190109006, 35449570704992428, 41308170711273595,
    32704271730884725, 31088623120238042, 15164867654172497, 19763340441600069, 19362956186092205, 18519010373925535,
    15164867654172497, 18519010373925535, 19516733033214433, 15164867654172497
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
noncomputable def negativeCeiling : ℝ := 2301628071 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 39614067090032720187836334080, coefficient := (-39614067090032720187836334080) }, { argument := 28433842771526234554115293184, coefficient := (-28433842771526234554115293184) }, { argument := 28361108312260931498144694272, coefficient := (-28361108312260931498144694272) }, { argument := 28191394573975224367546630144, coefficient := (-28191394573975224367546630144) }, { argument := 28361108312260931498144694272, coefficient := (-28361108312260931498144694272) }, { argument := 1247729372915480828510732288, coefficient := (-1247729372915480828510732288) }, { argument := 13515440322728106281410756608, coefficient := (-13515440322728106281410756608) }, { argument := 41470919217017885060633722880, coefficient := (-41470919217017885060633722880) }, { argument := 11156573438946619382959177728, coefficient := (-11156573438946619382959177728) }, { argument := 551448922694345149221175296, coefficient := (-551448922694345149221175296) }, { argument := 11139223944103902222892400640, coefficient := (-11139223944103902222892400640) }, { argument := 11329629207290884106622074880, coefficient := (-11329629207290884106622074880) }, { argument := 1251445632172955708818456576, coefficient := (-1251445632172955708818456576) }, { argument := 13515440322728106281410756608, coefficient := (-13515440322728106281410756608) }, { argument := 551448922694345149221175296, coefficient := (-551448922694345149221175296) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 282137785519046953292267520, coefficient := (-282137785519046953292267520) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 313872088283930969128304640, coefficient := (-313872088283930969128304640) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 175708823280901873924571136, coefficient := (-175708823280901873924571136) }, { argument := 17319424834785626178977792000, coefficient := (-17319424834785626178977792000) }, { argument := 66082509165012675136061440, coefficient := (-66082509165012675136061440) }, { argument := 85728660538394821798133760, coefficient := (-85728660538394821798133760) }, { argument := 1148406848462247300337500160, coefficient := (-1148406848462247300337500160) }, { argument := 2077134004294857869817282560, coefficient := (-2077134004294857869817282560) }, { argument := 17319425699476754634113024000, coefficient := (-17319425699476754634113024000) }, { argument := 1148406848462247300337500160, coefficient := (-1148406848462247300337500160) }, { argument := 67868522926229233923522560, coefficient := (-67868522926229233923522560) }, { argument := 67868522926229233923522560, coefficient := (-67868522926229233923522560) }, { argument := 66082509165012675136061440, coefficient := (-66082509165012675136061440) }, { argument := 66082509165012675136061440, coefficient := (-66082509165012675136061440) }, { argument := 2077134004294857869817282560, coefficient := (-2077134004294857869817282560) }, { argument := 66082509165012675136061440, coefficient := (-66082509165012675136061440) }, { argument := 175707958589773418789339136, coefficient := (-175707958589773418789339136) }, { argument := 85728660538394821798133760, coefficient := (-85728660538394821798133760) }, { argument := 39614095424231617405707616256, coefficient := (-39614095424231617405707616256) }, { argument := 102122993114072855804060368896, coefficient := (-102122993114072855804060368896) }, { argument := 101862284093722890470625902592, coefficient := (-101862284093722890470625902592) }, { argument := 101253963046239638025945481216, coefficient := (-101253963046239638025945481216) }, { argument := 101862284093722890470625902592, coefficient := (-101862284093722890470625902592) }, { argument := 48899075990166028860950315008, coefficient := (-48899075990166028860950315008) }, { argument := 516352746201017988928619151360, coefficient := (-516352746201017988928619151360) }, { argument := 1640024205963585422084339138560, coefficient := (-1640024205963585422084339138560) }, { argument := 425997146428126226383009480704, coefficient := (-425997146428126226383009480704) }, { argument := 21061912777439398044182249472, coefficient := (-21061912777439398044182249472) }, { argument := 425318154899901962133524447232, coefficient := (-425318154899901962133524447232) }, { argument := 432786636697385410609790582784, coefficient := (-432786636697385410609790582784) }, { argument := 49047651345769190217022963712, coefficient := (-49047651345769190217022963712) }, { argument := 516352746201017988928619151360, coefficient := (-516352746201017988928619151360) }, { argument := 21061912777439398044182249472, coefficient := (-21061912777439398044182249472) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 4202599215932597713250549760, coefficient := (-4202599215932597713250549760) }, { argument := 3184126436572101330012733440, coefficient := (-3184126436572101330012733440) }, { argument := 3547866714915135752597667840, coefficient := (-3547866714915135752597667840) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 3547866714915135752597667840, coefficient := (-3547866714915135752597667840) }, { argument := 3542270710632935223019438080, coefficient := (-3542270710632935223019438080) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-633260456535067157196199386152960)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    889935, 36735, 7979300842225, 393199542293775, 576974115, 46781685,
    10026874485, 18135699885, 393199545077775, 10026874485, 296284005, 296284005,
    576974115, 576974115, 18135699885, 576974115, 7979298058225, 46781685,
    3255, 78855, 59745, 33285, 3255, 33285,
    66465, 3255, 78855, 3255, 457736125, 80282615875,
    20070656375, 114431625, 158126233577, 8128385923373, 465059903, 168818001765731,
    18119217, 30198695, 924080067, 30198695, 18119217, 14803400289,
    948239023, 8128404548909, 924080067, 30198695, 948239023, 30198695,
    924080067, 30198695, 158126233577, 1541794465, 6151401505, 3057295005,
    6151401505, 43431104852255, 1749471795, 1456633958732057, 11546680023, 570884499,
    5764137957, 11730709593, 5445383280569, 1749471795
  ]
def negativeCoefficients : Array ℕ := #[
    4202599215932597713250549760, 173476132748216416925122560, 35935576299721594894915993600, 1770813312156494672043599462400, 21286587673120126621376839680, 27615032657020704806110494720,
    369926374968006524798521835520, 669089228752397493531385528320, 1770813324694516034643060326400, 369926374968006524798521835520, 21861900853474724638170808320, 21861900853474724638170808320,
    21286587673120126621376839680, 21286587673120126621376839680, 669089228752397493531385528320, 21286587673120126621376839680, 35935563761700232295455129600, 27615032657020704806110494720,
    15371302901740695170580480, 372382209006685873325998080, 282137785519046953292267520, 314367936764632281875742720, 15371302901740695170580480, 314367936764632281875742720,
    313872088283930969128304640, 15371302901740695170580480, 372382209006685873325998080, 15371302901740695170580480, 1055467643895815566524416000, 185119108576757077338226688000,
    185119130770496041020030976000, 1055445450156851884720128000, 178034311653719303203586048, 36606995815626227852937003008, 1072355126198148615588806656, 380144344922788933682266636288,
    668481117630014721406009344, 34816724876563266739896320, 1065391781222835962240827392, 1114135196050024535676682240, 668481117630014721406009344, 17067158534491313355897176064,
    1093245161124086575632744448, 36607079697583217028695588864, 1065391781222835962240827392, 34816724876563266739896320, 1093245161124086575632744448, 34816724876563266739896320,
    1065391781222835962240827392, 1114135196050024535676682240, 178034311653719303203586048, 28441087910116938699180605440, 28368332314341691685884395520, 28198569257532781988193239040,
    28368332314341691685884395520, 48899076907226139683056517120, 516352935464612185188618731520, 1640024038440225588329282797568, 425997302570591438297509134336, 21061920497401792891629600768,
    425318310793336129052945154048, 432786795330161072475079704576, 49047652226520154943361384448, 516352935464612185188618731520
  ]
def negativeScales : Array ℕ := #[
    19, 15, 42, 48, 29, 25,
    33, 34, 48, 33, 28, 28,
    29, 29, 34, 29, 42, 25,
    11, 16, 15, 15, 11, 15,
    16, 11, 16, 11, 28, 36,
    34, 26, 37, 42, 28, 47,
    24, 24, 29, 24, 24, 33,
    29, 42, 29, 24, 29, 24,
    29, 24, 37, 30, 32, 31,
    32, 45, 30, 50, 33, 29,
    32, 33, 42, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19763340441600069, 15164867654172497, 42859399481697074, 48482254970725099, 29103931355268074, 25479440490360415,
    33223152916967072, 34078113371112343, 48482254980939920, 33223152916967072, 28142405503082710, 28142405503082710,
    29103931355268074, 29103931355268074, 34078113371112343, 29103931355268074, 42859398978336701, 25479440490360415,
    11668441828086828, 16266914615180395, 15866530362339582, 15022584547805530, 11668441828086828, 15022584547805530,
    16020307207094464, 11668441828086828, 16266914615180395, 11668441828086828, 28769940914834499, 36224368574149218,
    34224368747112428, 26769910578391499, 37202285778388352, 42886106042743201, 28792841317156893, 47262462081244221,
    24111017276625240, 24847982872458062, 29783442619055923, 24847982872458062, 24111017276625240, 33785209545247324,
    29820675525774757, 42886109348558101, 29783442619055923, 24847982872458062, 29820675525774757, 24847982872458062,
    29783442619055923, 24847982872458062, 37202285778388352, 30521963307897985, 32518267998416010, 31509608621689514,
    32518267998416010, 45303793887791814, 30704272259689115, 50371559807735173, 33426759047019497, 29088623649038514,
    32424457718905251, 33449571233794978, 42308170737180136, 30704272259689115
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
noncomputable def negativeCeiling : ℝ := 5424032571 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4202599215932597713250549760, coefficient := (-4202599215932597713250549760) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 35935576299721594894915993600, coefficient := (-35935576299721594894915993600) }, { argument := 1770813312156494672043599462400, coefficient := (-1770813312156494672043599462400) }, { argument := 21286587673120126621376839680, coefficient := (-21286587673120126621376839680) }, { argument := 27615032657020704806110494720, coefficient := (-27615032657020704806110494720) }, { argument := 369926374968006524798521835520, coefficient := (-369926374968006524798521835520) }, { argument := 669089228752397493531385528320, coefficient := (-669089228752397493531385528320) }, { argument := 1770813324694516034643060326400, coefficient := (-1770813324694516034643060326400) }, { argument := 369926374968006524798521835520, coefficient := (-369926374968006524798521835520) }, { argument := 21861900853474724638170808320, coefficient := (-21861900853474724638170808320) }, { argument := 21861900853474724638170808320, coefficient := (-21861900853474724638170808320) }, { argument := 21286587673120126621376839680, coefficient := (-21286587673120126621376839680) }, { argument := 21286587673120126621376839680, coefficient := (-21286587673120126621376839680) }, { argument := 669089228752397493531385528320, coefficient := (-669089228752397493531385528320) }, { argument := 21286587673120126621376839680, coefficient := (-21286587673120126621376839680) }, { argument := 35935563761700232295455129600, coefficient := (-35935563761700232295455129600) }, { argument := 27615032657020704806110494720, coefficient := (-27615032657020704806110494720) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 282137785519046953292267520, coefficient := (-282137785519046953292267520) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 313872088283930969128304640, coefficient := (-313872088283930969128304640) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 1055467643895815566524416000, coefficient := (-1055467643895815566524416000) }, { argument := 185119108576757077338226688000, coefficient := (-185119108576757077338226688000) }, { argument := 185119130770496041020030976000, coefficient := (-185119130770496041020030976000) }, { argument := 1055445450156851884720128000, coefficient := (-1055445450156851884720128000) }, { argument := 178034311653719303203586048, coefficient := (-178034311653719303203586048) }, { argument := 36606995815626227852937003008, coefficient := (-36606995815626227852937003008) }, { argument := 1072355126198148615588806656, coefficient := (-1072355126198148615588806656) }, { argument := 380144344922788933682266636288, coefficient := (-380144344922788933682266636288) }, { argument := 668481117630014721406009344, coefficient := (-668481117630014721406009344) }, { argument := 34816724876563266739896320, coefficient := (-34816724876563266739896320) }, { argument := 1065391781222835962240827392, coefficient := (-1065391781222835962240827392) }, { argument := 1114135196050024535676682240, coefficient := (-1114135196050024535676682240) }, { argument := 668481117630014721406009344, coefficient := (-668481117630014721406009344) }, { argument := 17067158534491313355897176064, coefficient := (-17067158534491313355897176064) }, { argument := 1093245161124086575632744448, coefficient := (-1093245161124086575632744448) }, { argument := 36607079697583217028695588864, coefficient := (-36607079697583217028695588864) }, { argument := 1065391781222835962240827392, coefficient := (-1065391781222835962240827392) }, { argument := 34816724876563266739896320, coefficient := (-34816724876563266739896320) }, { argument := 1093245161124086575632744448, coefficient := (-1093245161124086575632744448) }, { argument := 34816724876563266739896320, coefficient := (-34816724876563266739896320) }, { argument := 1065391781222835962240827392, coefficient := (-1065391781222835962240827392) }, { argument := 1114135196050024535676682240, coefficient := (-1114135196050024535676682240) }, { argument := 178034311653719303203586048, coefficient := (-178034311653719303203586048) }, { argument := 28441087910116938699180605440, coefficient := (-28441087910116938699180605440) }, { argument := 28368332314341691685884395520, coefficient := (-28368332314341691685884395520) }, { argument := 28198569257532781988193239040, coefficient := (-28198569257532781988193239040) }, { argument := 28368332314341691685884395520, coefficient := (-28368332314341691685884395520) }, { argument := 48899076907226139683056517120, coefficient := (-48899076907226139683056517120) }, { argument := 516352935464612185188618731520, coefficient := (-516352935464612185188618731520) }, { argument := 1640024038440225588329282797568, coefficient := (-1640024038440225588329282797568) }, { argument := 425997302570591438297509134336, coefficient := (-425997302570591438297509134336) }, { argument := 21061920497401792891629600768, coefficient := (-21061920497401792891629600768) }, { argument := 425318310793336129052945154048, coefficient := (-425318310793336129052945154048) }, { argument := 432786795330161072475079704576, coefficient := (-432786795330161072475079704576) }, { argument := 49047652226520154943361384448, coefficient := (-49047652226520154943361384448) }, { argument := 516352935464612185188618731520, coefficient := (-516352935464612185188618731520) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5
