import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 21, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 28066552199374017634694692337614848
def positiveArguments : Array ℕ := #[
    471, 81, 1215, 2133, 81, 675,
    81, 2133, 4239, 675, 65421, 4185,
    1215, 2133, 81, 4185, 81, 2133,
    2133, 81, 1035, 4715
  ]
def positiveCoefficients : Array ℕ := #[
    298531716353748024052473604866048, 12534142897764475283353632768, 188012143466467129250304491520, 330065762974464515794978996224, 12534142897764475283353632768, 208902381629407921389227212800,
    12534142897764475283353632768, 330065762974464515794978996224, 327976739158170436581086724096, 208902381629407921389227212800, 5061704706880553935260975366144, 323798691525582278153302179840,
    188012143466467129250304491520, 330065762974464515794978996224, 12534142897764475283353632768, 323798691525582278153302179840, 12534142897764475283353632768, 330065762974464515794978996224,
    330065762974464515794978996224, 12534142897764475283353632768, 320316985165092146130148392960, 364805455326910499759335669760
  ]
def positiveScales : Array ℕ := #[
    8, 6, 10, 11, 6, 9,
    6, 11, 12, 9, 15, 12,
    10, 11, 6, 12, 6, 11,
    11, 6, 10, 12
  ]
def negativeArguments : Array ℕ := #[
    35072765867, 49297862603, 183129274405, 3080467841, 662591059083, 662590901109,
    4187, 35072774229, 35072765867, 8321, 35284897817, 131074602295,
    2204841899, 406654598493, 406654501539, 1325, 662591059083, 662590901109,
    128419, 8215, 335068777989, 98024283, 335068814139, 98024283,
    18767397, 4187, 1830522427, 6799934645, 114383569, 35072774229,
    35072765867, 159, 35072774229, 35072765867, 8215, 159,
    38864425497, 38864416231, 4187, 4187, 852925, 27
  ]
def negativeCoefficients : Array ℕ := #[
    80872291988210611748689936384, 227346263704609495023576154112, 844534714338291006038993797120, 227298407560878429310470324224, 3055661923108066405444623532032, 3055661194581579330396446785536,
    161976717015246475343832285184, 80872311269669854793598763008, 80872291988210611748689936384, 160951547920213269803681447936, 162722869924297961226861805568, 604474910774781910852493639680,
    162688616935379055037839835136, 937681663099685613687942414336, 937681439538982498383458992128, 102516909503320554015083724800, 3055661923108066405444623532032, 3055661194581579330396446785536,
    2483984717265457023785478651904, 158901209730146858723379773440, 386307999665855450130640011264, 3616457723019755894819782656, 386308041343967841668158193664, 3616457723019755894819782656,
    354506106254033323898330677248, 161976717015246475343832285184, 8441794683013668829300523008, 31359163528566503425263534080, 8440017694321990332911190016, 80872311269669854793598763008,
    80872291988210611748689936384, 6151014570199233240905023488, 80872311269669854793598763008, 80872291988210611748689936384, 158901209730146858723379773440, 6151014570199233240905023488,
    89615263839363893149663494144, 89615242473422569775575334912, 161976717015246475343832285184, 161976717015246475343832285184, 8055648864803184287783321600, 8556641551540548460102746636288
  ]
def negativeScales : Array ℕ := #[
    35, 35, 37, 31, 39, 39,
    12, 35, 35, 13, 35, 36,
    31, 38, 38, 10, 39, 39,
    16, 13, 38, 26, 38, 26,
    24, 12, 30, 32, 26, 35,
    35, 7, 35, 35, 13, 7,
    35, 35, 12, 12, 19, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8879583249426338, 6339850002884624, 10246740598493143, 11058668250340571, 6339850002884624, 9398743691938192,
    6339850002884624, 11058668250340571, 12049508251055095, 9398743691938192, 15997466190213005, 12031011907437706,
    10246740598493143, 11058668250340571, 6339850002884624, 12031011907437706, 6339850002884624, 11058668250340571,
    11058668250340571, 6339850002884624, 10015415052386687, 12203042055562458
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    35029632156061477, 35520806046209616, 37414071477512555, 31520502328489574, 39269327779773265, 39269327435807964,
    12031701202740303, 35029632500026779, 35029632156061477, 13022541203454827, 35038331780910291, 36931597219827647,
    31038028063190254, 38565012971899457, 38565012627934155, 10371776644337926, 39269327779773265, 39269327435807964,
    16970499158689786, 13004044859837437, 38285666304940840, 26546635848379979, 38285666460590743, 26546635848379979,
    24161725229371902, 12031701202740303, 30769608303537831, 32662873734527600, 26769304585815586, 35029632500026779,
    35029632156061477, 7312882955284356, 35029632500026779, 35029632156061477, 13004044859837437, 7312882955284356,
    35177731139015913, 35177730795050611, 12031701202740303, 12031701202740303, 19702059361560245, 4754887502413606
  ]

abbrev PositiveTerm := Fin 22
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 1044862819 / 31250000000
noncomputable def negativeCeiling : ℝ := 9585964457 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 80872291988210611748689936384, coefficient := (-80872291988210611748689936384) }, { argument := 227346263704609495023576154112, coefficient := (-227346263704609495023576154112) }, { argument := 844534714338291006038993797120, coefficient := (-844534714338291006038993797120) }, { argument := 227298407560878429310470324224, coefficient := (-227298407560878429310470324224) }, { argument := 3055661923108066405444623532032, coefficient := (-3055661923108066405444623532032) }, { argument := 3055661194581579330396446785536, coefficient := (-3055661194581579330396446785536) }, { argument := 161976717015246475343832285184, coefficient := (-161976717015246475343832285184) }, { argument := 80872311269669854793598763008, coefficient := (-80872311269669854793598763008) }, { argument := 80872291988210611748689936384, coefficient := (-80872291988210611748689936384) }, { argument := 160951547920213269803681447936, coefficient := (-160951547920213269803681447936) }, { argument := 162722869924297961226861805568, coefficient := (-162722869924297961226861805568) }, { argument := 604474910774781910852493639680, coefficient := (-604474910774781910852493639680) }, { argument := 162688616935379055037839835136, coefficient := (-162688616935379055037839835136) }, { argument := 937681663099685613687942414336, coefficient := (-937681663099685613687942414336) }, { argument := 937681439538982498383458992128, coefficient := (-937681439538982498383458992128) }, { argument := 102516909503320554015083724800, coefficient := (-102516909503320554015083724800) }, { argument := 3055661923108066405444623532032, coefficient := (-3055661923108066405444623532032) }, { argument := 3055661194581579330396446785536, coefficient := (-3055661194581579330396446785536) }, { argument := 2483984717265457023785478651904, coefficient := (-2483984717265457023785478651904) }, { argument := 158901209730146858723379773440, coefficient := (-158901209730146858723379773440) }, { argument := 386307999665855450130640011264, coefficient := (-386307999665855450130640011264) }, { argument := 3616457723019755894819782656, coefficient := (-3616457723019755894819782656) }, { argument := 386308041343967841668158193664, coefficient := (-386308041343967841668158193664) }, { argument := 3616457723019755894819782656, coefficient := (-3616457723019755894819782656) }, { argument := 354506106254033323898330677248, coefficient := (-354506106254033323898330677248) }, { argument := 161976717015246475343832285184, coefficient := (-161976717015246475343832285184) }, { argument := 8441794683013668829300523008, coefficient := (-8441794683013668829300523008) }, { argument := 31359163528566503425263534080, coefficient := (-31359163528566503425263534080) }, { argument := 8440017694321990332911190016, coefficient := (-8440017694321990332911190016) }, { argument := 80872311269669854793598763008, coefficient := (-80872311269669854793598763008) }, { argument := 80872291988210611748689936384, coefficient := (-80872291988210611748689936384) }, { argument := 6151014570199233240905023488, coefficient := (-6151014570199233240905023488) }, { argument := 80872311269669854793598763008, coefficient := (-80872311269669854793598763008) }, { argument := 80872291988210611748689936384, coefficient := (-80872291988210611748689936384) }, { argument := 158901209730146858723379773440, coefficient := (-158901209730146858723379773440) }, { argument := 6151014570199233240905023488, coefficient := (-6151014570199233240905023488) }, { argument := 89615263839363893149663494144, coefficient := (-89615263839363893149663494144) }, { argument := 89615242473422569775575334912, coefficient := (-89615242473422569775575334912) }, { argument := 161976717015246475343832285184, coefficient := (-161976717015246475343832285184) }, { argument := 161976717015246475343832285184, coefficient := (-161976717015246475343832285184) }, { argument := 8055648864803184287783321600, coefficient := (-8055648864803184287783321600) }, { argument := 298531716353748024052473604866048, coefficient := 298531716353748024052473604866048 }, { argument := 12534142897764475283353632768, coefficient := 12534142897764475283353632768 }, { argument := 188012143466467129250304491520, coefficient := 188012143466467129250304491520 }, { argument := 330065762974464515794978996224, coefficient := 330065762974464515794978996224 }, { argument := 12534142897764475283353632768, coefficient := 12534142897764475283353632768 }, { argument := 208902381629407921389227212800, coefficient := 208902381629407921389227212800 }, { argument := 12534142897764475283353632768, coefficient := 12534142897764475283353632768 }, { argument := 330065762974464515794978996224, coefficient := 330065762974464515794978996224 }, { argument := 327976739158170436581086724096, coefficient := 327976739158170436581086724096 }, { argument := 208902381629407921389227212800, coefficient := 208902381629407921389227212800 }, { argument := 5061704706880553935260975366144, coefficient := 5061704706880553935260975366144 }, { argument := 323798691525582278153302179840, coefficient := 323798691525582278153302179840 }, { argument := 188012143466467129250304491520, coefficient := 188012143466467129250304491520 }, { argument := 330065762974464515794978996224, coefficient := 330065762974464515794978996224 }, { argument := 12534142897764475283353632768, coefficient := 12534142897764475283353632768 }, { argument := 323798691525582278153302179840, coefficient := 323798691525582278153302179840 }, { argument := 12534142897764475283353632768, coefficient := 12534142897764475283353632768 }, { argument := 330065762974464515794978996224, coefficient := 330065762974464515794978996224 }, { argument := 330065762974464515794978996224, coefficient := 330065762974464515794978996224 }, { argument := 12534142897764475283353632768, coefficient := 12534142897764475283353632768 }, { argument := 8556641551540548460102746636288, coefficient := (-8556641551540548460102746636288) }, { argument := 320316985165092146130148392960, coefficient := 320316985165092146130148392960 }, { argument := 364805455326910499759335669760, coefficient := 364805455326910499759335669760 }] }

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


end Parent1

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-12888974935708527172091466869637120)
def positiveArguments : Array ℕ := #[
    115, 49335, 2185, 115, 2185, 4255,
    80385, 4255, 49335, 80385, 1035, 4255,
    4255, 4715, 595, 2975, 2465, 44285,
    16575, 595, 66385, 66385, 47515, 2465,
    1769, 1943, 1769, 1943, 3, 45,
    14201912779, 14201913909, 5290523375, 4799641045, 5290470845, 264464371,
    10321959863, 10321956875, 264465483, 203715, 27147, 1084604787,
    111194229, 203715
  ]
def positiveCoefficients : Array ℕ := #[
    284726209035637463226798571520, 3817110739884014741384268349440, 338112373229819487581823303680, 284726209035637463226798571520, 338112373229819487581823303680, 329214679197455816855985848320,
    12438976257244411674720762593280, 329214679197455816855985848320, 3817110739884014741384268349440, 12438976257244411674720762593280, 320316985165092146130148392960, 329214679197455816855985848320,
    329214679197455816855985848320, 364805455326910499759335669760, 92071790421850157945622364160, 1841435808437003158912447283200, 95360068651201949300823162880, 1713192957492283296059616133120,
    2564857018894397257056623001600, 92071790421850157945622364160, 2568145297123749048411823800320, 2568145297123749048411823800320, 1838147530207651367557246484480, 95360068651201949300823162880,
    547478982373959426574137688064, 601329374082873468532249591808, 547478982373959426574137688064, 601329374082873468532249591808, 475368975085586025561263702016, 14261069252567580766837911060480,
    67066636900187698951585408221184, 67066642236461824594284499697664, 49967580525876790162031116288000, 181325312005707508417944942018560, 49967084394054099877104965386240, 1248897681523602996433273225216,
    48744077294556954956820169883648, 48744063184125904142320271360000, 1248902932795131947478750855168, 3848067552231159098832322560, 525099347601253411291976957952, 5121901293288770695766319562752,
    525099900118131907040466960384, 3848067552231159098832322560
  ]
def positiveScales : Array ℕ := #[
    6, 15, 11, 6, 11, 12,
    16, 12, 15, 16, 10, 12,
    12, 12, 9, 11, 11, 15,
    14, 9, 16, 16, 15, 11,
    10, 10, 10, 10, 1, 5,
    33, 33, 32, 32, 32, 27,
    33, 33, 27, 17, 14, 30,
    26, 17
  ]
def negativeArguments : Array ℕ := #[
    115, 85, 29, 3, 45, 1693,
    1775, 631, 39
  ]
def negativeCoefficients : Array ℕ := #[
    36444954756561595293030217154560, 13468787627424937390902471557120, 2297616712913665790212774559744, 475368975085586025561263702016, 14261069252567580766837911060480, 134133279136649523545869907918848,
    281259976925638398457081023692800, 99985941093001594043052465324032, 6179796676112618332296428126208
  ]
def negativeScales : Array ℕ := #[
    6, 6, 4, 1, 5, 10,
    10, 9, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6845490050846035, 15590323888443651, 11093417564387960, 6845490050846035, 11093417564387960, 12054943416573324,
    16294638696319811, 12054943416573324, 15590323888443651, 16294638696319811, 10015415052386687, 12054943416573324,
    12054943416573324, 12203042055562458, 9216745858195305, 11538673953082609, 11267371931265273, 15434530498416207,
    14016721249887312, 9216745858195305, 16018569674279681, 16018569674279681, 15536095408980837, 11267371931265273,
    10788718332658703, 10924070185172542, 10788718332658703, 10924070185172542, 1584962500720924, 5491853096329661,
    33725366200492299, 33725366315282846, 32300763304712595, 32160279367744462, 32300748980015138, 27978498131657712,
    33264997874691207, 33264997457059918, 27978504197781022, 17636192687576585, 14728505154945711, 30014522296929357,
    26728506672968814, 17636192687576585
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6845490052533228, 6409390936137712, 4857980997143165, 1584962500724866, 5491853096329881, 10725366258025642,
    10793603309846131, 9301496194982550, 5285402218862249
  ]

abbrev PositiveTerm := Fin 44
abbrev NegativeTerm := Fin 9
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
noncomputable def positiveFloor : ℝ := 13491494461 / 62500000000
noncomputable def negativeCeiling : ℝ := 17643817201 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 284726209035637463226798571520, coefficient := 284726209035637463226798571520 }, { argument := 3817110739884014741384268349440, coefficient := 3817110739884014741384268349440 }, { argument := 338112373229819487581823303680, coefficient := 338112373229819487581823303680 }, { argument := 284726209035637463226798571520, coefficient := 284726209035637463226798571520 }, { argument := 338112373229819487581823303680, coefficient := 338112373229819487581823303680 }, { argument := 329214679197455816855985848320, coefficient := 329214679197455816855985848320 }, { argument := 12438976257244411674720762593280, coefficient := 12438976257244411674720762593280 }, { argument := 329214679197455816855985848320, coefficient := 329214679197455816855985848320 }, { argument := 3817110739884014741384268349440, coefficient := 3817110739884014741384268349440 }, { argument := 12438976257244411674720762593280, coefficient := 12438976257244411674720762593280 }, { argument := 320316985165092146130148392960, coefficient := 320316985165092146130148392960 }, { argument := 329214679197455816855985848320, coefficient := 329214679197455816855985848320 }, { argument := 329214679197455816855985848320, coefficient := 329214679197455816855985848320 }, { argument := 364805455326910499759335669760, coefficient := 364805455326910499759335669760 }, { argument := 36444954756561595293030217154560, coefficient := (-36444954756561595293030217154560) }, { argument := 92071790421850157945622364160, coefficient := 92071790421850157945622364160 }, { argument := 1841435808437003158912447283200, coefficient := 1841435808437003158912447283200 }, { argument := 95360068651201949300823162880, coefficient := 95360068651201949300823162880 }, { argument := 1713192957492283296059616133120, coefficient := 1713192957492283296059616133120 }, { argument := 2564857018894397257056623001600, coefficient := 2564857018894397257056623001600 }, { argument := 92071790421850157945622364160, coefficient := 92071790421850157945622364160 }, { argument := 2568145297123749048411823800320, coefficient := 2568145297123749048411823800320 }, { argument := 2568145297123749048411823800320, coefficient := 2568145297123749048411823800320 }, { argument := 1838147530207651367557246484480, coefficient := 1838147530207651367557246484480 }, { argument := 95360068651201949300823162880, coefficient := 95360068651201949300823162880 }, { argument := 13468787627424937390902471557120, coefficient := (-13468787627424937390902471557120) }, { argument := 547478982373959426574137688064, coefficient := 547478982373959426574137688064 }, { argument := 601329374082873468532249591808, coefficient := 601329374082873468532249591808 }, { argument := 547478982373959426574137688064, coefficient := 547478982373959426574137688064 }, { argument := 601329374082873468532249591808, coefficient := 601329374082873468532249591808 }, { argument := 2297616712913665790212774559744, coefficient := (-2297616712913665790212774559744) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 14261069252567580766837911060480, coefficient := 14261069252567580766837911060480 }, { argument := 14261069252567580766837911060480, coefficient := (-14261069252567580766837911060480) }, { argument := 67066636900187698951585408221184, coefficient := 67066636900187698951585408221184 }, { argument := 67066642236461824594284499697664, coefficient := 67066642236461824594284499697664 }, { argument := 134133279136649523545869907918848, coefficient := (-134133279136649523545869907918848) }, { argument := 49967580525876790162031116288000, coefficient := 49967580525876790162031116288000 }, { argument := 181325312005707508417944942018560, coefficient := 181325312005707508417944942018560 }, { argument := 49967084394054099877104965386240, coefficient := 49967084394054099877104965386240 }, { argument := 281259976925638398457081023692800, coefficient := (-281259976925638398457081023692800) }, { argument := 1248897681523602996433273225216, coefficient := 1248897681523602996433273225216 }, { argument := 48744077294556954956820169883648, coefficient := 48744077294556954956820169883648 }, { argument := 48744063184125904142320271360000, coefficient := 48744063184125904142320271360000 }, { argument := 1248902932795131947478750855168, coefficient := 1248902932795131947478750855168 }, { argument := 99985941093001594043052465324032, coefficient := (-99985941093001594043052465324032) }, { argument := 3848067552231159098832322560, coefficient := 3848067552231159098832322560 }, { argument := 525099347601253411291976957952, coefficient := 525099347601253411291976957952 }, { argument := 5121901293288770695766319562752, coefficient := 5121901293288770695766319562752 }, { argument := 525099900118131907040466960384, coefficient := 525099900118131907040466960384 }, { argument := 3848067552231159098832322560, coefficient := 3848067552231159098832322560 }, { argument := 6179796676112618332296428126208, coefficient := (-6179796676112618332296428126208) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21
