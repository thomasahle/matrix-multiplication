import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 18, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-8575212026104255982680415278202880)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    62849700765, 668432997717, 31424945097, 97555935, 12738845985, 498534228703,
    498534228703, 12738845985, 5163905, 3326808195, 35382004171, 1663409111,
    5163905, 25316440755, 990757897549, 990757897549, 25316440755, 23353935423,
    84003411219, 11676971607, 164670779, 32659952325, 32659952325, 164670779,
    59873385, 38572992315, 410239994307, 19286554287, 59873385, 4031280375,
    157763996425, 157763996425, 4031280375, 97555935, 62849700765, 668432997717,
    31424945097, 97555935, 390711693945, 15290486533511, 15290486533511, 390711693945,
    19541048007, 70288568571, 9770527263, 24993938325, 978136777835, 978136777835,
    24993938325, 546672733269, 1966365564657, 273336457821, 18899531571, 18899536077,
    56616265233, 14928650090127, 3211543155, 503666055509517, 1016311125, 121957335,
    3211543155, 6382433865, 1016311125, 98500874235
  ]
def negativeCoefficients : Array ℕ := #[
    1159372345121182422587922186240, 12330412439307979995058821660672, 1159375839469465561314575253504, 3599178731632888452659281920, 58747557919924366414907965440, 2299083332217106873731631808512,
    2299083332217106873731631808512, 58747557919924366414907965440, 95257233955949122137620480, 30684389677742310182942146560, 326341387878680443359925895168, 30684482160493723725779173376,
    95257233955949122137620480, 58375737933089402070509813760, 2284532171886618855543456923648, 2284532171886618855543456923648, 58375737933089402070509813760, 53850508732752602562293661696,
    193698678509434338895869247488, 53850526697575487346183241728, 189852482289461580271714304, 37654361374926890104730419200, 37654361374926890104730419200, 189852482289461580271714304,
    1104469009921680362082140160, 355773058695985164013031915520, 3783796091890646221659681325056, 355774130995994796712412577792, 1104469009921680362082140160, 37181998683496434439815168000,
    1455116033048801818817488486400, 1455116033048801818817488486400, 37181998683496434439815168000, 3599178731632888452659281920, 1159372345121182422587922186240, 12330412439307979995058821660672,
    1159375839469465561314575253504, 3599178731632888452659281920, 900919828101118606476721520640, 35257461480772468069947746025472, 35257461480772468069947746025472, 900919828101118606476721520640,
    720937423034402189405400858624, 2593190471473243394197759721472, 720937663543051422430534828032, 57632097959419473381713510400, 2255429851225642819167107153920, 2255429851225642819167107153920,
    57632097959419473381713510400, 1260541500336066023243894489088, 4534130290822881361501265854464, 1260541920859573142572901597184, 43579352750403852731355758592, 43579363140532452248260706304,
    4079631856103167486316249088, 268930651932161914905682771968, 59242514661958725950483988480, 2268310259911828315052213010432, 37495262444277674652205056000, 2249715746656660479132303360,
    59242514661958725950483988480, 58867562037515949203961937920, 37495262444277674652205056000, 908510209024848056822928506880
  ]
def negativeScales : Array ℕ := #[
    35, 39, 34, 26, 33, 38,
    38, 33, 22, 31, 35, 30,
    22, 34, 39, 39, 34, 34,
    36, 33, 27, 34, 34, 27,
    25, 35, 38, 34, 25, 31,
    37, 37, 31, 26, 35, 39,
    34, 26, 38, 43, 43, 38,
    34, 36, 33, 34, 39, 39,
    34, 38, 40, 37, 34, 34,
    35, 43, 31, 48, 29, 26,
    31, 32, 29, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35871186827272233, 39281991998685540, 34871191175548785, 26539726308800860, 33568515538312626, 38858901607375813,
    38858901607375813, 33568515538312626, 22300031029053403, 31631491544957517, 35042296718939053, 30631495893233862,
    22300031029053403, 34559355539026603, 39849741607762999, 39849741607762999, 34559355539026603, 34442946631007540,
    36289728863060379, 33442947112298379, 27295009329148173, 34926803640824563, 34926803640824563, 27295009329148173,
    25835411502231667, 35166872016814904, 38577677190812660, 34166876365091248, 25835411502231667, 31908590984998721,
    37198977046922497, 37198977046922497, 31908590984998721, 26539726308800860, 35871186827272233, 39281991998685540,
    34871191175548785, 26539726308800860, 38507313479584907, 43797699547215507, 43797699547215507, 38507313479584907,
    34185788791510380, 36032571023563255, 33185789272801219, 34540859195408458, 39831245263627619, 39831245263627619,
    34540859195408458, 38991886483699174, 40838668696354009, 37991886964990175, 34137631426252767, 34137631770218069,
    35720497532081360, 43763148950792200, 31580619536729052, 48839460833916375, 29920694984623743, 26861801291435908,
    31580619536729052, 32571459537442814, 29920694984623743, 36519417478000530
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
noncomputable def negativeCeiling : ℝ := 69119776757 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1159372345121182422587922186240, coefficient := (-1159372345121182422587922186240) }, { argument := 12330412439307979995058821660672, coefficient := (-12330412439307979995058821660672) }, { argument := 1159375839469465561314575253504, coefficient := (-1159375839469465561314575253504) }, { argument := 3599178731632888452659281920, coefficient := (-3599178731632888452659281920) }, { argument := 58747557919924366414907965440, coefficient := (-58747557919924366414907965440) }, { argument := 2299083332217106873731631808512, coefficient := (-2299083332217106873731631808512) }, { argument := 2299083332217106873731631808512, coefficient := (-2299083332217106873731631808512) }, { argument := 58747557919924366414907965440, coefficient := (-58747557919924366414907965440) }, { argument := 95257233955949122137620480, coefficient := (-95257233955949122137620480) }, { argument := 30684389677742310182942146560, coefficient := (-30684389677742310182942146560) }, { argument := 326341387878680443359925895168, coefficient := (-326341387878680443359925895168) }, { argument := 30684482160493723725779173376, coefficient := (-30684482160493723725779173376) }, { argument := 95257233955949122137620480, coefficient := (-95257233955949122137620480) }, { argument := 58375737933089402070509813760, coefficient := (-58375737933089402070509813760) }, { argument := 2284532171886618855543456923648, coefficient := (-2284532171886618855543456923648) }, { argument := 2284532171886618855543456923648, coefficient := (-2284532171886618855543456923648) }, { argument := 58375737933089402070509813760, coefficient := (-58375737933089402070509813760) }, { argument := 53850508732752602562293661696, coefficient := (-53850508732752602562293661696) }, { argument := 193698678509434338895869247488, coefficient := (-193698678509434338895869247488) }, { argument := 53850526697575487346183241728, coefficient := (-53850526697575487346183241728) }, { argument := 189852482289461580271714304, coefficient := (-189852482289461580271714304) }, { argument := 37654361374926890104730419200, coefficient := (-37654361374926890104730419200) }, { argument := 37654361374926890104730419200, coefficient := (-37654361374926890104730419200) }, { argument := 189852482289461580271714304, coefficient := (-189852482289461580271714304) }, { argument := 1104469009921680362082140160, coefficient := (-1104469009921680362082140160) }, { argument := 355773058695985164013031915520, coefficient := (-355773058695985164013031915520) }, { argument := 3783796091890646221659681325056, coefficient := (-3783796091890646221659681325056) }, { argument := 355774130995994796712412577792, coefficient := (-355774130995994796712412577792) }, { argument := 1104469009921680362082140160, coefficient := (-1104469009921680362082140160) }, { argument := 37181998683496434439815168000, coefficient := (-37181998683496434439815168000) }, { argument := 1455116033048801818817488486400, coefficient := (-1455116033048801818817488486400) }, { argument := 1455116033048801818817488486400, coefficient := (-1455116033048801818817488486400) }, { argument := 37181998683496434439815168000, coefficient := (-37181998683496434439815168000) }, { argument := 3599178731632888452659281920, coefficient := (-3599178731632888452659281920) }, { argument := 1159372345121182422587922186240, coefficient := (-1159372345121182422587922186240) }, { argument := 12330412439307979995058821660672, coefficient := (-12330412439307979995058821660672) }, { argument := 1159375839469465561314575253504, coefficient := (-1159375839469465561314575253504) }, { argument := 3599178731632888452659281920, coefficient := (-3599178731632888452659281920) }, { argument := 900919828101118606476721520640, coefficient := (-900919828101118606476721520640) }, { argument := 35257461480772468069947746025472, coefficient := (-35257461480772468069947746025472) }, { argument := 35257461480772468069947746025472, coefficient := (-35257461480772468069947746025472) }, { argument := 900919828101118606476721520640, coefficient := (-900919828101118606476721520640) }, { argument := 720937423034402189405400858624, coefficient := (-720937423034402189405400858624) }, { argument := 2593190471473243394197759721472, coefficient := (-2593190471473243394197759721472) }, { argument := 720937663543051422430534828032, coefficient := (-720937663543051422430534828032) }, { argument := 57632097959419473381713510400, coefficient := (-57632097959419473381713510400) }, { argument := 2255429851225642819167107153920, coefficient := (-2255429851225642819167107153920) }, { argument := 2255429851225642819167107153920, coefficient := (-2255429851225642819167107153920) }, { argument := 57632097959419473381713510400, coefficient := (-57632097959419473381713510400) }, { argument := 1260541500336066023243894489088, coefficient := (-1260541500336066023243894489088) }, { argument := 4534130290822881361501265854464, coefficient := (-4534130290822881361501265854464) }, { argument := 1260541920859573142572901597184, coefficient := (-1260541920859573142572901597184) }, { argument := 43579352750403852731355758592, coefficient := (-43579352750403852731355758592) }, { argument := 43579363140532452248260706304, coefficient := (-43579363140532452248260706304) }, { argument := 4079631856103167486316249088, coefficient := (-4079631856103167486316249088) }, { argument := 268930651932161914905682771968, coefficient := (-268930651932161914905682771968) }, { argument := 59242514661958725950483988480, coefficient := (-59242514661958725950483988480) }, { argument := 2268310259911828315052213010432, coefficient := (-2268310259911828315052213010432) }, { argument := 37495262444277674652205056000, coefficient := (-37495262444277674652205056000) }, { argument := 2249715746656660479132303360, coefficient := (-2249715746656660479132303360) }, { argument := 59242514661958725950483988480, coefficient := (-59242514661958725950483988480) }, { argument := 58867562037515949203961937920, coefficient := (-58867562037515949203961937920) }, { argument := 37495262444277674652205056000, coefficient := (-37495262444277674652205056000) }, { argument := 908510209024848056822928506880, coefficient := (-908510209024848056822928506880) }] }

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


end Parent1

namespace Parent1

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2169980534538643738522575001616384)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    6301128975, 59714651610519, 3211543155, 121957335, 6301128975, 121957335,
    3211543155, 3211543155, 56616265233, 14762758383599, 3543640373, 257672522987005,
    37078578537, 1642174807, 515344884131903, 1642174807, 3197919361, 60414746847,
    3197919361, 37078578537, 60414746847, 1845351541371, 3197919361, 3197919361,
    3543640373, 24909928963077, 2044898625, 1694344575, 2934641084134005, 11393006625,
    797117481728235, 45630452175, 45630452175, 32659952325, 1694344575, 12738845985,
    498534228703, 498534228703, 12738845985, 19541048007, 70288568571, 9770527263,
    30769372501, 30769375915, 17634604299, 63431147247, 8817305091, 7977565257,
    7977567159, 8542849, 1694344575, 1694344575, 8542849, 5163905,
    3326808195, 35382004171, 1663409111, 5163905, 483753645, 18931679571,
    18931679571, 483753645, 5163905, 3326808195
  ]
def negativeCoefficients : Array ℕ := #[
    58117656788630395710917836800, 268930882741692357239503847424, 59242514661958725950483988480, 2249715746656660479132303360, 58117656788630395710917836800, 2249715746656660479132303360,
    59242514661958725950483988480, 59242514661958725950483988480, 4079631856103167486316249088, 265942212621348488990651580416, 32684313524997827491092496384, 9283631028063130263389827235840,
    341989524444489463260455632896, 30292778389022376699061338112, 9283628112574919151166058135552, 30292778389022376699061338112, 29495600010363893101717618688, 1114455373364560069086519754752,
    29495600010363893101717618688, 341989524444489463260455632896, 1114455373364560069086519754752, 265943184450752193065241280512, 29495600010363893101717618688, 29495600010363893101717618688,
    32684313524997827491092496384, 897474774367512824107065409536, 37721721592055560748924928000, 1953446296731448681640755200, 3304112123243013329780861829120, 52540969360363102471716864000,
    897474498420446824969682288640, 52608329577491773115911372800, 52608329577491773115911372800, 37654361374926890104730419200, 1953446296731448681640755200, 58747557919924366414907965440,
    2299083332217106873731631808512, 2299083332217106873731631808512, 58747557919924366414907965440, 720937423034402189405400858624, 2593190471473243394197759721472, 720937663543051422430534828032,
    70949342479322924319298813952, 70949350351470957774849966080, 40662629043098903975609499648, 146262267445899398758105350144, 40662642608373327179771019264, 36790026156798991520212451328,
    36790034928225798569104244736, 9849234322709098082074624, 1953446296731448681640755200, 1953446296731448681640755200, 9849234322709098082074624, 95257233955949122137620480,
    30684389677742310182942146560, 326341387878680443359925895168, 30684482160493723725779173376, 95257233955949122137620480, 2230919921009786066388910080, 87306961982928109129049309184,
    87306961982928109129049309184, 2230919921009786066388910080, 95257233955949122137620480, 30684389677742310182942146560
  ]
def negativeScales : Array ℕ := #[
    32, 45, 31, 26, 32, 26,
    31, 31, 35, 43, 31, 47,
    35, 30, 48, 30, 31, 35,
    31, 35, 35, 40, 31, 31,
    31, 44, 30, 30, 51, 33,
    49, 35, 35, 34, 30, 33,
    38, 38, 33, 34, 36, 33,
    34, 34, 34, 35, 33, 32,
    32, 23, 30, 30, 23, 22,
    31, 35, 30, 22, 28, 34,
    34, 28, 22, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32552963193824364, 45763150188983614, 31580619536729052, 26861801291435908, 32552963193824364, 26861801291435908,
    31580619536729052, 31580619536729052, 35720497532081360, 43747027544205412, 31722585053256470, 47872532034104051,
    35109866886015885, 30612960561967987, 48872531581031192, 30612960561967987, 31574486414148035, 35814181694752041,
    31574486414148035, 35109866886015885, 35814181694752041, 40747032816218802, 31574486414148035, 31574486414148035,
    31722585053256470, 44501786140913116, 30929382185246576, 30658080156127340, 51382105491278360, 33407429474723254,
    49501785697326804, 35409277899115623, 35409277899115623, 34926803640824563, 30658080156127340, 33568515538312626,
    38858901607375813, 38858901607375813, 33568515538312626, 34185788791510380, 36032571023563255, 33185789272801219,
    34840775972516475, 34840776132589962, 34037690152521246, 35884472387871606, 33037690633812085, 32893301362749349,
    32893301706714675, 23026285851432555, 30658080156127340, 30658080156127340, 23026285851432555, 22300031029053403,
    31631491544957517, 35042296718939053, 30631495893233862, 22300031029053403, 28849697292576513, 34140083357868929,
    34140083357868929, 28849697292576513, 22300031029053403, 31631491544957517
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
noncomputable def negativeCeiling : ℝ := 20183853263 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 58117656788630395710917836800, coefficient := (-58117656788630395710917836800) }, { argument := 268930882741692357239503847424, coefficient := (-268930882741692357239503847424) }, { argument := 59242514661958725950483988480, coefficient := (-59242514661958725950483988480) }, { argument := 2249715746656660479132303360, coefficient := (-2249715746656660479132303360) }, { argument := 58117656788630395710917836800, coefficient := (-58117656788630395710917836800) }, { argument := 2249715746656660479132303360, coefficient := (-2249715746656660479132303360) }, { argument := 59242514661958725950483988480, coefficient := (-59242514661958725950483988480) }, { argument := 59242514661958725950483988480, coefficient := (-59242514661958725950483988480) }, { argument := 4079631856103167486316249088, coefficient := (-4079631856103167486316249088) }, { argument := 265942212621348488990651580416, coefficient := (-265942212621348488990651580416) }, { argument := 32684313524997827491092496384, coefficient := (-32684313524997827491092496384) }, { argument := 9283631028063130263389827235840, coefficient := (-9283631028063130263389827235840) }, { argument := 341989524444489463260455632896, coefficient := (-341989524444489463260455632896) }, { argument := 30292778389022376699061338112, coefficient := (-30292778389022376699061338112) }, { argument := 9283628112574919151166058135552, coefficient := (-9283628112574919151166058135552) }, { argument := 30292778389022376699061338112, coefficient := (-30292778389022376699061338112) }, { argument := 29495600010363893101717618688, coefficient := (-29495600010363893101717618688) }, { argument := 1114455373364560069086519754752, coefficient := (-1114455373364560069086519754752) }, { argument := 29495600010363893101717618688, coefficient := (-29495600010363893101717618688) }, { argument := 341989524444489463260455632896, coefficient := (-341989524444489463260455632896) }, { argument := 1114455373364560069086519754752, coefficient := (-1114455373364560069086519754752) }, { argument := 265943184450752193065241280512, coefficient := (-265943184450752193065241280512) }, { argument := 29495600010363893101717618688, coefficient := (-29495600010363893101717618688) }, { argument := 29495600010363893101717618688, coefficient := (-29495600010363893101717618688) }, { argument := 32684313524997827491092496384, coefficient := (-32684313524997827491092496384) }, { argument := 897474774367512824107065409536, coefficient := (-897474774367512824107065409536) }, { argument := 37721721592055560748924928000, coefficient := (-37721721592055560748924928000) }, { argument := 1953446296731448681640755200, coefficient := (-1953446296731448681640755200) }, { argument := 3304112123243013329780861829120, coefficient := (-3304112123243013329780861829120) }, { argument := 52540969360363102471716864000, coefficient := (-52540969360363102471716864000) }, { argument := 897474498420446824969682288640, coefficient := (-897474498420446824969682288640) }, { argument := 52608329577491773115911372800, coefficient := (-52608329577491773115911372800) }, { argument := 52608329577491773115911372800, coefficient := (-52608329577491773115911372800) }, { argument := 37654361374926890104730419200, coefficient := (-37654361374926890104730419200) }, { argument := 1953446296731448681640755200, coefficient := (-1953446296731448681640755200) }, { argument := 58747557919924366414907965440, coefficient := (-58747557919924366414907965440) }, { argument := 2299083332217106873731631808512, coefficient := (-2299083332217106873731631808512) }, { argument := 2299083332217106873731631808512, coefficient := (-2299083332217106873731631808512) }, { argument := 58747557919924366414907965440, coefficient := (-58747557919924366414907965440) }, { argument := 720937423034402189405400858624, coefficient := (-720937423034402189405400858624) }, { argument := 2593190471473243394197759721472, coefficient := (-2593190471473243394197759721472) }, { argument := 720937663543051422430534828032, coefficient := (-720937663543051422430534828032) }, { argument := 70949342479322924319298813952, coefficient := (-70949342479322924319298813952) }, { argument := 70949350351470957774849966080, coefficient := (-70949350351470957774849966080) }, { argument := 40662629043098903975609499648, coefficient := (-40662629043098903975609499648) }, { argument := 146262267445899398758105350144, coefficient := (-146262267445899398758105350144) }, { argument := 40662642608373327179771019264, coefficient := (-40662642608373327179771019264) }, { argument := 36790026156798991520212451328, coefficient := (-36790026156798991520212451328) }, { argument := 36790034928225798569104244736, coefficient := (-36790034928225798569104244736) }, { argument := 9849234322709098082074624, coefficient := (-9849234322709098082074624) }, { argument := 1953446296731448681640755200, coefficient := (-1953446296731448681640755200) }, { argument := 1953446296731448681640755200, coefficient := (-1953446296731448681640755200) }, { argument := 9849234322709098082074624, coefficient := (-9849234322709098082074624) }, { argument := 95257233955949122137620480, coefficient := (-95257233955949122137620480) }, { argument := 30684389677742310182942146560, coefficient := (-30684389677742310182942146560) }, { argument := 326341387878680443359925895168, coefficient := (-326341387878680443359925895168) }, { argument := 30684482160493723725779173376, coefficient := (-30684482160493723725779173376) }, { argument := 95257233955949122137620480, coefficient := (-95257233955949122137620480) }, { argument := 2230919921009786066388910080, coefficient := (-2230919921009786066388910080) }, { argument := 87306961982928109129049309184, coefficient := (-87306961982928109129049309184) }, { argument := 87306961982928109129049309184, coefficient := (-87306961982928109129049309184) }, { argument := 2230919921009786066388910080, coefficient := (-2230919921009786066388910080) }, { argument := 95257233955949122137620480, coefficient := (-95257233955949122137620480) }, { argument := 30684389677742310182942146560, coefficient := (-30684389677742310182942146560) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18
