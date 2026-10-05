import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
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

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-101631912793112589062665215672320)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    44904567165, 33285, 33285, 1379901, 8559, 375645,
    1379901, 4707412791, 33285, 8559, 33285, 6165606821,
    22144394199, 1541794465, 3255, 78855, 59745, 33285,
    3255, 33285, 66465, 3255, 78855, 3255,
    29723125, 5213156875, 1303289375, 7430625, 837, 20277,
    15363, 8559, 837, 8559, 17091, 837,
    20277, 837, 933306125, 163693125875, 40923286375, 233321625,
    3786795, 2439615105, 25946332569, 1219811229, 3786795, 29723125,
    5213156875, 1303289375, 7430625, 7374285, 4750829415, 50527068687,
    2375421867, 7374285, 58168431, 3255, 8880581005, 36735,
    3255, 2220146065, 3255, 3255
  ]
def negativeCoefficients : Array ℕ := #[
    414171529116728135621353144320, 314367936764632281875742720, 314367936764632281875742720, 13032796464156612600048648192, 323349877815050347072192512, 3547866714915135752597667840,
    13032796464156612600048648192, 10854554875610473762004140032, 314367936764632281875742720, 323349877815050347072192512, 314367936764632281875742720, 28433842771526234554115293184,
    102122993114072855804060368896, 28441087910116938699180605440, 15371302901740695170580480, 372382209006685873325998080, 282137785519046953292267520, 314367936764632281875742720,
    15371302901740695170580480, 314367936764632281875742720, 313872088283930969128304640, 15371302901740695170580480, 372382209006685873325998080, 15371302901740695170580480,
    34268429996617388523520000, 6010360668076528485007360000, 6010361388652468864286720000, 34267709420677009244160000, 15810482984647572175454208, 383021700692591183992455168,
    290198865105305437672046592, 323349877815050347072192512, 15810482984647572175454208, 323349877815050347072192512, 322839862234900425389113344, 15810482984647572175454208,
    383021700692591183992455168, 15810482984647572175454208, 1076028701893785999638528000, 188725324977602994429231104000, 188725347603687522338603008000, 1076006075809258090266624000,
    69854038224602961511710720, 22501477740145527752585379840, 239312678275848937870303690752, 22501545559600114745751896064, 69854038224602961511710720, 34268429996617388523520000,
    6010360668076528485007360000, 6010361388652468864286720000, 34267709420677009244160000, 68015774060797620419297280, 21909333589089066495938396160, 233014976215958176347400962048,
    21909399623821164357705793536, 68015774060797620419297280, 536509079913116483608117248, 15371302901740695170580480, 20477225628135170496014581760, 173476132748216416925122560,
    15371302901740695170580480, 20477233133654165486588395520, 15371302901740695170580480, 15371302901740695170580480
  ]
def negativeScales : Array ℕ := #[
    35, 15, 15, 20, 13, 18,
    20, 32, 15, 13, 15, 32,
    34, 30, 11, 16, 15, 15,
    11, 15, 16, 11, 16, 11,
    24, 32, 30, 22, 9, 14,
    13, 13, 9, 13, 14, 9,
    14, 9, 29, 37, 35, 27,
    21, 31, 34, 30, 21, 24,
    32, 30, 22, 22, 32, 35,
    31, 22, 25, 11, 33, 15,
    11, 31, 11, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35386143135292297, 15022584547805530, 15022584547805530, 20396133334927314, 13063226532302876, 18519010373925535,
    20396133334927314, 32132287221867244, 15022584547805530, 13063226532302876, 15022584547805530, 32521595746111208,
    34366222479036430, 30521963307897985, 11668441828086828, 16266914615180395, 15866530362339582, 15022584547805530,
    11668441828086828, 15022584547805530, 16020307207094464, 11668441828086828, 16266914615180395, 11668441828086828,
    24825082469749558, 32279510128341679, 30279510301304889, 22825052133306142, 9709083812639846, 14307556599677741,
    13907172349434197, 13063226532302876, 9709083812639846, 13063226532302876, 14060949191591810, 9709083812639846,
    14307556599677741, 9709083812639846, 29797775123302974, 37252202782345944, 35252202955309154, 27797744786859814,
    21852545893476809, 31184006407549483, 34594811581549123, 30184010755825827, 21852545893476809, 24825082469749558,
    32279510128341679, 30279510301304889, 22825052133306142, 22814071744702316, 32145532259734847, 35556337433731201,
    31145536608011191, 22814071744702316, 25793733055088885, 11668441828086828, 33048006920833256, 15164867654172497,
    11668441828086828, 31048007449624277, 11668441828086828, 11668441828086828
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
noncomputable def negativeCeiling : ℝ := 169001369 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 414171529116728135621353144320, coefficient := (-414171529116728135621353144320) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 13032796464156612600048648192, coefficient := (-13032796464156612600048648192) }, { argument := 323349877815050347072192512, coefficient := (-323349877815050347072192512) }, { argument := 3547866714915135752597667840, coefficient := (-3547866714915135752597667840) }, { argument := 13032796464156612600048648192, coefficient := (-13032796464156612600048648192) }, { argument := 10854554875610473762004140032, coefficient := (-10854554875610473762004140032) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 323349877815050347072192512, coefficient := (-323349877815050347072192512) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 28433842771526234554115293184, coefficient := (-28433842771526234554115293184) }, { argument := 102122993114072855804060368896, coefficient := (-102122993114072855804060368896) }, { argument := 28441087910116938699180605440, coefficient := (-28441087910116938699180605440) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 282137785519046953292267520, coefficient := (-282137785519046953292267520) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 313872088283930969128304640, coefficient := (-313872088283930969128304640) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 34268429996617388523520000, coefficient := (-34268429996617388523520000) }, { argument := 6010360668076528485007360000, coefficient := (-6010360668076528485007360000) }, { argument := 6010361388652468864286720000, coefficient := (-6010361388652468864286720000) }, { argument := 34267709420677009244160000, coefficient := (-34267709420677009244160000) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 383021700692591183992455168, coefficient := (-383021700692591183992455168) }, { argument := 290198865105305437672046592, coefficient := (-290198865105305437672046592) }, { argument := 323349877815050347072192512, coefficient := (-323349877815050347072192512) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 323349877815050347072192512, coefficient := (-323349877815050347072192512) }, { argument := 322839862234900425389113344, coefficient := (-322839862234900425389113344) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 383021700692591183992455168, coefficient := (-383021700692591183992455168) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 1076028701893785999638528000, coefficient := (-1076028701893785999638528000) }, { argument := 188725324977602994429231104000, coefficient := (-188725324977602994429231104000) }, { argument := 188725347603687522338603008000, coefficient := (-188725347603687522338603008000) }, { argument := 1076006075809258090266624000, coefficient := (-1076006075809258090266624000) }, { argument := 69854038224602961511710720, coefficient := (-69854038224602961511710720) }, { argument := 22501477740145527752585379840, coefficient := (-22501477740145527752585379840) }, { argument := 239312678275848937870303690752, coefficient := (-239312678275848937870303690752) }, { argument := 22501545559600114745751896064, coefficient := (-22501545559600114745751896064) }, { argument := 69854038224602961511710720, coefficient := (-69854038224602961511710720) }, { argument := 34268429996617388523520000, coefficient := (-34268429996617388523520000) }, { argument := 6010360668076528485007360000, coefficient := (-6010360668076528485007360000) }, { argument := 6010361388652468864286720000, coefficient := (-6010361388652468864286720000) }, { argument := 34267709420677009244160000, coefficient := (-34267709420677009244160000) }, { argument := 68015774060797620419297280, coefficient := (-68015774060797620419297280) }, { argument := 21909333589089066495938396160, coefficient := (-21909333589089066495938396160) }, { argument := 233014976215958176347400962048, coefficient := (-233014976215958176347400962048) }, { argument := 21909399623821164357705793536, coefficient := (-21909399623821164357705793536) }, { argument := 68015774060797620419297280, coefficient := (-68015774060797620419297280) }, { argument := 536509079913116483608117248, coefficient := (-536509079913116483608117248) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 20477225628135170496014581760, coefficient := (-20477225628135170496014581760) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 20477233133654165486588395520, coefficient := (-20477233133654165486588395520) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }] }

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
def constantNumerator : ℤ := (-732497598145582914586256850550784)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    134943, 837, 36735, 134943, 232676979, 3255,
    837, 3255, 3255, 78855, 59745, 33285,
    3255, 33285, 66465, 3255, 78855, 3255,
    909527625, 159522600375, 39880654875, 227377125, 7374285, 4750829415,
    50527068687, 2375421867, 7374285, 29723125, 5213156875, 1303289375,
    7430625, 231791715, 149330124585, 1588188672513, 74665287333, 231791715,
    587503977, 33285, 89665958395, 375645, 33285, 22416497815,
    33285, 33285, 1379901, 8559, 375645, 1379901,
    2350048773, 33285, 8559, 33285, 7374285, 4750829415,
    50527068687, 2375421867, 7374285, 1195076973, 66465, 182480878855,
    750105, 66465, 45620236435, 66465
  ]
def negativeCoefficients : Array ℕ := #[
    637250300297878534071779328, 15810482984647572175454208, 173476132748216416925122560, 637250300297878534071779328, 536516585432111474181931008, 15371302901740695170580480,
    15810482984647572175454208, 15371302901740695170580480, 15371302901740695170580480, 372382209006685873325998080, 282137785519046953292267520, 314367936764632281875742720,
    15371302901740695170580480, 314367936764632281875742720, 313872088283930969128304640, 15371302901740695170580480, 372382209006685873325998080, 15371302901740695170580480,
    1048613957896492088819712000, 183917036443141771641225216000, 183917058492765547247173632000, 1048591908272716482871296000, 68015774060797620419297280, 21909333589089066495938396160,
    233014976215958176347400962048, 21909399623821164357705793536, 68015774060797620419297280, 1096589759891756432752640000, 192331541378448911520235520000, 192331564436879003657175040000,
    1096566701461664295813120000, 2137901222505611690476830720, 688663647678664441480442019840, 7324227495652955651135873482752, 688665723310919301297617240064, 2137901222505611690476830720,
    10837535506005542717286776832, 314367936764632281875742720, 413511246659113367128590254080, 3547866714915135752597667840, 314367936764632281875742720, 413511398222174362744693719040,
    314367936764632281875742720, 314367936764632281875742720, 13032796464156612600048648192, 323349877815050347072192512, 3547866714915135752597667840, 13032796464156612600048648192,
    10837687069066538333390241792, 314367936764632281875742720, 323349877815050347072192512, 314367936764632281875742720, 68015774060797620419297280, 21909333589089066495938396160,
    233014976215958176347400962048, 21909399623821164357705793536, 68015774060797620419297280, 11022639534657249913218269184, 313872088283930969128304640, 420772258822972734861958184960,
    3542270710632935223019438080, 313872088283930969128304640, 420772413049282406119878164480, 313872088283930969128304640
  ]
def negativeScales : Array ℕ := #[
    17, 9, 15, 17, 27, 11,
    9, 11, 11, 16, 15, 15,
    11, 15, 16, 11, 16, 11,
    29, 37, 35, 27, 22, 32,
    35, 31, 22, 24, 32, 30,
    22, 27, 37, 40, 36, 27,
    29, 15, 36, 18, 15, 34,
    15, 15, 20, 13, 18, 20,
    31, 15, 13, 15, 22, 32,
    35, 31, 22, 30, 16, 37,
    19, 16, 35, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    17041990615174776, 9709083812639846, 15164867654172497, 17041990615174776, 27793753237598046, 11668441828086828,
    9709083812639846, 11668441828086828, 11668441828086828, 16266914615180395, 15866530362339582, 15022584547805530,
    11668441828086828, 15022584547805530, 16020307207094464, 11668441828086828, 16266914615180395, 11668441828086828,
    29760542216769316, 37214969876146969, 35214970049110178, 27760511880326354, 22814071744702316, 32145532259734847,
    35556337433731201, 31145536608011191, 22814071744702316, 24825082469749558, 32279510128341679, 30279510301304889,
    22825052133306142, 27788253760195689, 37119714275579116, 40530519449574589, 36119718623855460, 27788253760195689,
    29130023376868039, 15022584547805530, 36383841320014408, 18519010373925535, 15022584547805530, 34383841848801081,
    15022584547805530, 15022584547805530, 20396133334927314, 13063226532302876, 18519010373925535, 20396133334927314,
    31130043552834005, 15022584547805530, 13063226532302876, 15022584547805530, 22814071744702316, 32145532259734847,
    35556337433731201, 31145536608011191, 22814071744702316, 30154456396869336, 16020307207094464, 37408954343773886,
    19516733033214433, 16020307207094464, 35408954872567044, 16020307207094464
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
noncomputable def negativeCeiling : ℝ := 1366118647 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 536516585432111474181931008, coefficient := (-536516585432111474181931008) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 282137785519046953292267520, coefficient := (-282137785519046953292267520) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 313872088283930969128304640, coefficient := (-313872088283930969128304640) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 1048613957896492088819712000, coefficient := (-1048613957896492088819712000) }, { argument := 183917036443141771641225216000, coefficient := (-183917036443141771641225216000) }, { argument := 183917058492765547247173632000, coefficient := (-183917058492765547247173632000) }, { argument := 1048591908272716482871296000, coefficient := (-1048591908272716482871296000) }, { argument := 68015774060797620419297280, coefficient := (-68015774060797620419297280) }, { argument := 21909333589089066495938396160, coefficient := (-21909333589089066495938396160) }, { argument := 233014976215958176347400962048, coefficient := (-233014976215958176347400962048) }, { argument := 21909399623821164357705793536, coefficient := (-21909399623821164357705793536) }, { argument := 68015774060797620419297280, coefficient := (-68015774060797620419297280) }, { argument := 1096589759891756432752640000, coefficient := (-1096589759891756432752640000) }, { argument := 192331541378448911520235520000, coefficient := (-192331541378448911520235520000) }, { argument := 192331564436879003657175040000, coefficient := (-192331564436879003657175040000) }, { argument := 1096566701461664295813120000, coefficient := (-1096566701461664295813120000) }, { argument := 2137901222505611690476830720, coefficient := (-2137901222505611690476830720) }, { argument := 688663647678664441480442019840, coefficient := (-688663647678664441480442019840) }, { argument := 7324227495652955651135873482752, coefficient := (-7324227495652955651135873482752) }, { argument := 688665723310919301297617240064, coefficient := (-688665723310919301297617240064) }, { argument := 2137901222505611690476830720, coefficient := (-2137901222505611690476830720) }, { argument := 10837535506005542717286776832, coefficient := (-10837535506005542717286776832) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 413511246659113367128590254080, coefficient := (-413511246659113367128590254080) }, { argument := 3547866714915135752597667840, coefficient := (-3547866714915135752597667840) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 413511398222174362744693719040, coefficient := (-413511398222174362744693719040) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 13032796464156612600048648192, coefficient := (-13032796464156612600048648192) }, { argument := 323349877815050347072192512, coefficient := (-323349877815050347072192512) }, { argument := 3547866714915135752597667840, coefficient := (-3547866714915135752597667840) }, { argument := 13032796464156612600048648192, coefficient := (-13032796464156612600048648192) }, { argument := 10837687069066538333390241792, coefficient := (-10837687069066538333390241792) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 323349877815050347072192512, coefficient := (-323349877815050347072192512) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 68015774060797620419297280, coefficient := (-68015774060797620419297280) }, { argument := 21909333589089066495938396160, coefficient := (-21909333589089066495938396160) }, { argument := 233014976215958176347400962048, coefficient := (-233014976215958176347400962048) }, { argument := 21909399623821164357705793536, coefficient := (-21909399623821164357705793536) }, { argument := 68015774060797620419297280, coefficient := (-68015774060797620419297280) }, { argument := 11022639534657249913218269184, coefficient := (-11022639534657249913218269184) }, { argument := 313872088283930969128304640, coefficient := (-313872088283930969128304640) }, { argument := 420772258822972734861958184960, coefficient := (-420772258822972734861958184960) }, { argument := 3542270710632935223019438080, coefficient := (-3542270710632935223019438080) }, { argument := 313872088283930969128304640, coefficient := (-313872088283930969128304640) }, { argument := 420772413049282406119878164480, coefficient := (-420772413049282406119878164480) }, { argument := 313872088283930969128304640, coefficient := (-313872088283930969128304640) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5
