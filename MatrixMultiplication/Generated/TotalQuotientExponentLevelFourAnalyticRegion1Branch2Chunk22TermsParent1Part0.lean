import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 22, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22

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
def constantNumerator : ℤ := (-573083620284657683400189705977856)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    126665, 515421, 91, 140307873, 3, 7,
    91, 91, 3, 1123, 45, 515421,
    91, 7, 45, 7, 91, 91,
    286093, 1038714121, 247, 22695803639, 3887, 117,
    45391150065, 117, 117, 10023, 117, 3887,
    10023, 2077885455, 117, 117, 247, 1072746479739355,
    34169212593, 1919618685, 4031393869329945, 103787383569, 268186533453315, 103787383569,
    103787383569, 34169212593, 1919618685, 88240887, 3315436809, 6630372111,
    176983281, 35758478295, 65030646825, 35758478295, 1038714121, 88240887,
    1038714121, 88240887, 2008903275, 3653407125, 2008903275, 247,
    247, 126665, 1038714121, 247
  ]
def negativeCoefficients : Array ℕ := #[
    1196317101105367221985607680, 77888219358948972982028992512, 28163135893742401253955076096, 662585196737930856198316228608, 14855280471424563298789490688, 1083197534374707740536733696,
    28163135893742401253955076096, 28163135893742401253955076096, 14855280471424563298789490688, 347551666029370512177929125888, 27853650883921056185230295040, 77888219358948972982028992512,
    28163135893742401253955076096, 1083197534374707740536733696, 27853650883921056185230295040, 1083197534374707740536733696, 28163135893742401253955076096, 28163135893742401253955076096,
    1351035994183625408121929728, 38321787111670352232235139072, 19110699356468057993755230208, 837327362551597851590942261248, 150371029146946035266652995584, 18104873074548686520399691776,
    837318928460399678625719255040, 18104873074548686520399691776, 18104873074548686520399691776, 775492063359835405957120131072, 18104873074548686520399691776, 150371029146946035266652995584,
    775492063359835405957120131072, 38330221202868525197458145280, 18104873074548686520399691776, 18104873074548686520399691776, 19110699356468057993755230208, 301951290401073157186131066880,
    78788839987905566412726337536, 4426339325163234068130693120, 1134736495481127646558861393920, 119658706423579427641799737344, 301951193031533623452956098560, 119658706423579427641799737344,
    119658706423579427641799737344, 78788839987905566412726337536, 4426339325163234068130693120, 3255514118652248429936246784, 122318028616358513205143666688, 122308777445078339349041381376,
    3264765289932422286038532096, 82453437196645360199364771840, 299900924732141904692301004800, 82453437196645360199364771840, 38321787111670352232235139072, 3255514118652248429936246784,
    38321787111670352232235139072, 3255514118652248429936246784, 4632215572845244955020492800, 16848366557985500263612416000, 4632215572845244955020492800, 19110699356468057993755230208,
    19110699356468057993755230208, 1196317101105367221985607680, 38321787111670352232235139072, 19110699356468057993755230208
  ]
def negativeScales : Array ℕ := #[
    16, 18, 6, 27, 1, 2,
    6, 6, 1, 10, 5, 18,
    6, 2, 5, 2, 6, 6,
    18, 29, 7, 34, 11, 6,
    35, 6, 6, 13, 6, 11,
    13, 30, 6, 6, 7, 49,
    34, 30, 51, 36, 47, 36,
    36, 34, 30, 26, 31, 32,
    27, 35, 35, 35, 29, 26,
    29, 26, 30, 31, 30, 7,
    7, 16, 29, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16950658419858052, 18975391809026432, 6507794640199048, 27064020723291064, 1584962500724866, 2807354922807594,
    6507794640199048, 6507794640199048, 1584962500724866, 10133142212400602, 5491853096329881, 18975391809026432,
    6507794640199048, 2807354922807594, 5491853096329881, 2807354922807594, 6507794640199048, 6507794640199048,
    18126124673290384, 29952151509445169, 7948367241724988, 34401706522651660, 11924441399065046, 6870364722125690,
    35401691990840839, 6870364722125690, 6870364722125690, 13291026768056127, 6870364722125690, 11924441399065046,
    13291026768056127, 30952468991637313, 6870364722125690, 6870364722125690, 7948367241724988, 49930230597579087,
    34991977971888503, 30838172616367474, 51840200166894850, 36594840123601440, 47930230132356394, 36594840123601440,
    36594840123601440, 34991977971888503, 30838172616367474, 26394943957226849, 31626551812016875, 32626442693812262,
    27399037839420517, 35057566292694398, 35920400728705733, 35057566292694398, 29952151509445169, 26394943957226849,
    29952151509445169, 26394943957226849, 30903760961286902, 31766595386680513, 30903760961286902, 7948367241724988,
    7948367241724988, 16950658419858052, 29952151509445169, 7948367241724988
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
noncomputable def negativeCeiling : ℝ := 2994193943 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1196317101105367221985607680, coefficient := (-1196317101105367221985607680) }, { argument := 77888219358948972982028992512, coefficient := (-77888219358948972982028992512) }, { argument := 28163135893742401253955076096, coefficient := (-28163135893742401253955076096) }, { argument := 662585196737930856198316228608, coefficient := (-662585196737930856198316228608) }, { argument := 14855280471424563298789490688, coefficient := (-14855280471424563298789490688) }, { argument := 1083197534374707740536733696, coefficient := (-1083197534374707740536733696) }, { argument := 28163135893742401253955076096, coefficient := (-28163135893742401253955076096) }, { argument := 28163135893742401253955076096, coefficient := (-28163135893742401253955076096) }, { argument := 14855280471424563298789490688, coefficient := (-14855280471424563298789490688) }, { argument := 347551666029370512177929125888, coefficient := (-347551666029370512177929125888) }, { argument := 27853650883921056185230295040, coefficient := (-27853650883921056185230295040) }, { argument := 77888219358948972982028992512, coefficient := (-77888219358948972982028992512) }, { argument := 28163135893742401253955076096, coefficient := (-28163135893742401253955076096) }, { argument := 1083197534374707740536733696, coefficient := (-1083197534374707740536733696) }, { argument := 27853650883921056185230295040, coefficient := (-27853650883921056185230295040) }, { argument := 1083197534374707740536733696, coefficient := (-1083197534374707740536733696) }, { argument := 28163135893742401253955076096, coefficient := (-28163135893742401253955076096) }, { argument := 28163135893742401253955076096, coefficient := (-28163135893742401253955076096) }, { argument := 1351035994183625408121929728, coefficient := (-1351035994183625408121929728) }, { argument := 38321787111670352232235139072, coefficient := (-38321787111670352232235139072) }, { argument := 19110699356468057993755230208, coefficient := (-19110699356468057993755230208) }, { argument := 837327362551597851590942261248, coefficient := (-837327362551597851590942261248) }, { argument := 150371029146946035266652995584, coefficient := (-150371029146946035266652995584) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 837318928460399678625719255040, coefficient := (-837318928460399678625719255040) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 775492063359835405957120131072, coefficient := (-775492063359835405957120131072) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 150371029146946035266652995584, coefficient := (-150371029146946035266652995584) }, { argument := 775492063359835405957120131072, coefficient := (-775492063359835405957120131072) }, { argument := 38330221202868525197458145280, coefficient := (-38330221202868525197458145280) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 19110699356468057993755230208, coefficient := (-19110699356468057993755230208) }, { argument := 301951290401073157186131066880, coefficient := (-301951290401073157186131066880) }, { argument := 78788839987905566412726337536, coefficient := (-78788839987905566412726337536) }, { argument := 4426339325163234068130693120, coefficient := (-4426339325163234068130693120) }, { argument := 1134736495481127646558861393920, coefficient := (-1134736495481127646558861393920) }, { argument := 119658706423579427641799737344, coefficient := (-119658706423579427641799737344) }, { argument := 301951193031533623452956098560, coefficient := (-301951193031533623452956098560) }, { argument := 119658706423579427641799737344, coefficient := (-119658706423579427641799737344) }, { argument := 119658706423579427641799737344, coefficient := (-119658706423579427641799737344) }, { argument := 78788839987905566412726337536, coefficient := (-78788839987905566412726337536) }, { argument := 4426339325163234068130693120, coefficient := (-4426339325163234068130693120) }, { argument := 3255514118652248429936246784, coefficient := (-3255514118652248429936246784) }, { argument := 122318028616358513205143666688, coefficient := (-122318028616358513205143666688) }, { argument := 122308777445078339349041381376, coefficient := (-122308777445078339349041381376) }, { argument := 3264765289932422286038532096, coefficient := (-3264765289932422286038532096) }, { argument := 82453437196645360199364771840, coefficient := (-82453437196645360199364771840) }, { argument := 299900924732141904692301004800, coefficient := (-299900924732141904692301004800) }, { argument := 82453437196645360199364771840, coefficient := (-82453437196645360199364771840) }, { argument := 38321787111670352232235139072, coefficient := (-38321787111670352232235139072) }, { argument := 3255514118652248429936246784, coefficient := (-3255514118652248429936246784) }, { argument := 38321787111670352232235139072, coefficient := (-38321787111670352232235139072) }, { argument := 3255514118652248429936246784, coefficient := (-3255514118652248429936246784) }, { argument := 4632215572845244955020492800, coefficient := (-4632215572845244955020492800) }, { argument := 16848366557985500263612416000, coefficient := (-16848366557985500263612416000) }, { argument := 4632215572845244955020492800, coefficient := (-4632215572845244955020492800) }, { argument := 19110699356468057993755230208, coefficient := (-19110699356468057993755230208) }, { argument := 19110699356468057993755230208, coefficient := (-19110699356468057993755230208) }, { argument := 1196317101105367221985607680, coefficient := (-1196317101105367221985607680) }, { argument := 38321787111670352232235139072, coefficient := (-38321787111670352232235139072) }, { argument := 19110699356468057993755230208, coefficient := (-19110699356468057993755230208) }] }

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
def constantNumerator : ℤ := (-1273817682376806389357375848972288)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    22695803639, 3887, 117, 45391150065, 117, 117,
    10023, 117, 3887, 10023, 2077885455, 117,
    117, 247, 4040314346001945, 62140395855, 3491033475, 15170536795594915,
    188748543215, 1010078277118545, 188748543215, 188748543215, 62140395855, 3491033475,
    22695803639, 3315436809, 22695803639, 3315436809, 108614703735, 197527545225,
    108614703735, 3887, 3887, 515421, 117, 117,
    91, 268186533453315, 34169212593, 1919618685, 1007848157950545, 103787383569,
    67046611742955, 103787383569, 103787383569, 34169212593, 1919618685, 45391150065,
    6630372111, 45391150065, 6630372111, 140307873, 117, 117,
    3, 7, 88240887, 3315436809, 6630372111, 176983281,
    108614703735, 197527545225, 108614703735, 117
  ]
def negativeCoefficients : Array ℕ := #[
    837327362551597851590942261248, 150371029146946035266652995584, 18104873074548686520399691776, 837318928460399678625719255040, 18104873074548686520399691776, 18104873074548686520399691776,
    775492063359835405957120131072, 18104873074548686520399691776, 150371029146946035266652995584, 775492063359835405957120131072, 38330221202868525197458145280, 18104873074548686520399691776,
    18104873074548686520399691776, 19110699356468057993755230208, 1137247386444626796700678225920, 286571994744046708928198737920, 16099550266519478029674086400, 4270126491228228602357339914240,
    435224508871576556068856135680, 1137247038111527964535506862080, 435224508871576556068856135680, 435224508871576556068856135680, 286571994744046708928198737920, 16099550266519478029674086400,
    837327362551597851590942261248, 122318028616358513205143666688, 837327362551597851590942261248, 122318028616358513205143666688, 125224227652583121950720655360, 455467509284208023792988979200,
    125224227652583121950720655360, 150371029146946035266652995584, 150371029146946035266652995584, 77888219358948972982028992512, 18104873074548686520399691776, 18104873074548686520399691776,
    28163135893742401253955076096, 301951193031533623452956098560, 78788839987905566412726337536, 4426339325163234068130693120, 1134736147148028814393690030080, 119658706423579427641799737344,
    301951095662026459342102855680, 119658706423579427641799737344, 119658706423579427641799737344, 78788839987905566412726337536, 4426339325163234068130693120, 837318928460399678625719255040,
    122308777445078339349041381376, 837318928460399678625719255040, 122308777445078339349041381376, 662585196737930856198316228608, 18104873074548686520399691776, 18104873074548686520399691776,
    14855280471424563298789490688, 1083197534374707740536733696, 3255514118652248429936246784, 122318028616358513205143666688, 122308777445078339349041381376, 3264765289932422286038532096,
    125224227652583121950720655360, 455467509284208023792988979200, 125224227652583121950720655360, 18104873074548686520399691776
  ]
def negativeScales : Array ℕ := #[
    34, 11, 6, 35, 6, 6,
    13, 6, 11, 13, 30, 6,
    6, 7, 51, 35, 31, 53,
    37, 49, 37, 37, 35, 31,
    34, 31, 34, 31, 36, 37,
    36, 11, 11, 18, 6, 6,
    6, 47, 34, 30, 49, 36,
    45, 36, 36, 34, 30, 35,
    32, 35, 32, 27, 6, 6,
    1, 2, 26, 31, 32, 27,
    36, 37, 36, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34401706522651660, 11924441399065046, 6870364722125690, 35401691990840839, 6870364722125690, 6870364722125690,
    13291026768056127, 6870364722125690, 11924441399065046, 13291026768056127, 30952468991637313, 6870364722125690,
    6870364722125690, 7948367241724988, 51843388967262907, 35854812382708379, 31701007044805232, 53752121653368400,
    37457674553339927, 49843388525372662, 37457674553339927, 37457674553339927, 35854812382708379, 31701007044805232,
    34401706522651660, 31626551812016875, 34401706522651660, 31626551812016875, 36660428465251836, 37523262894968021,
    36660428465251836, 11924441399065046, 11924441399065046, 18975391809026432, 6870364722125690, 6870364722125690,
    6507794640199048, 47930230132356394, 34991977971888503, 30838172616367474, 49840199724026812, 36594840123601440,
    45930229667133705, 36594840123601440, 36594840123601440, 34991977971888503, 30838172616367474, 35401691990840839,
    32626442693812262, 35401691990840839, 32626442693812262, 27064020723291064, 6870364722125690, 6870364722125690,
    1584962500724866, 2807354922807594, 26394943957226849, 31626551812016875, 32626442693812262, 27399037839420517,
    36660428465251836, 37523262894968021, 36660428465251836, 6870364722125690
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
noncomputable def negativeCeiling : ℝ := 617820131 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 837327362551597851590942261248, coefficient := (-837327362551597851590942261248) }, { argument := 150371029146946035266652995584, coefficient := (-150371029146946035266652995584) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 837318928460399678625719255040, coefficient := (-837318928460399678625719255040) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 775492063359835405957120131072, coefficient := (-775492063359835405957120131072) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 150371029146946035266652995584, coefficient := (-150371029146946035266652995584) }, { argument := 775492063359835405957120131072, coefficient := (-775492063359835405957120131072) }, { argument := 38330221202868525197458145280, coefficient := (-38330221202868525197458145280) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 19110699356468057993755230208, coefficient := (-19110699356468057993755230208) }, { argument := 1137247386444626796700678225920, coefficient := (-1137247386444626796700678225920) }, { argument := 286571994744046708928198737920, coefficient := (-286571994744046708928198737920) }, { argument := 16099550266519478029674086400, coefficient := (-16099550266519478029674086400) }, { argument := 4270126491228228602357339914240, coefficient := (-4270126491228228602357339914240) }, { argument := 435224508871576556068856135680, coefficient := (-435224508871576556068856135680) }, { argument := 1137247038111527964535506862080, coefficient := (-1137247038111527964535506862080) }, { argument := 435224508871576556068856135680, coefficient := (-435224508871576556068856135680) }, { argument := 435224508871576556068856135680, coefficient := (-435224508871576556068856135680) }, { argument := 286571994744046708928198737920, coefficient := (-286571994744046708928198737920) }, { argument := 16099550266519478029674086400, coefficient := (-16099550266519478029674086400) }, { argument := 837327362551597851590942261248, coefficient := (-837327362551597851590942261248) }, { argument := 122318028616358513205143666688, coefficient := (-122318028616358513205143666688) }, { argument := 837327362551597851590942261248, coefficient := (-837327362551597851590942261248) }, { argument := 122318028616358513205143666688, coefficient := (-122318028616358513205143666688) }, { argument := 125224227652583121950720655360, coefficient := (-125224227652583121950720655360) }, { argument := 455467509284208023792988979200, coefficient := (-455467509284208023792988979200) }, { argument := 125224227652583121950720655360, coefficient := (-125224227652583121950720655360) }, { argument := 150371029146946035266652995584, coefficient := (-150371029146946035266652995584) }, { argument := 150371029146946035266652995584, coefficient := (-150371029146946035266652995584) }, { argument := 77888219358948972982028992512, coefficient := (-77888219358948972982028992512) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 28163135893742401253955076096, coefficient := (-28163135893742401253955076096) }, { argument := 301951193031533623452956098560, coefficient := (-301951193031533623452956098560) }, { argument := 78788839987905566412726337536, coefficient := (-78788839987905566412726337536) }, { argument := 4426339325163234068130693120, coefficient := (-4426339325163234068130693120) }, { argument := 1134736147148028814393690030080, coefficient := (-1134736147148028814393690030080) }, { argument := 119658706423579427641799737344, coefficient := (-119658706423579427641799737344) }, { argument := 301951095662026459342102855680, coefficient := (-301951095662026459342102855680) }, { argument := 119658706423579427641799737344, coefficient := (-119658706423579427641799737344) }, { argument := 119658706423579427641799737344, coefficient := (-119658706423579427641799737344) }, { argument := 78788839987905566412726337536, coefficient := (-78788839987905566412726337536) }, { argument := 4426339325163234068130693120, coefficient := (-4426339325163234068130693120) }, { argument := 837318928460399678625719255040, coefficient := (-837318928460399678625719255040) }, { argument := 122308777445078339349041381376, coefficient := (-122308777445078339349041381376) }, { argument := 837318928460399678625719255040, coefficient := (-837318928460399678625719255040) }, { argument := 122308777445078339349041381376, coefficient := (-122308777445078339349041381376) }, { argument := 662585196737930856198316228608, coefficient := (-662585196737930856198316228608) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 14855280471424563298789490688, coefficient := (-14855280471424563298789490688) }, { argument := 1083197534374707740536733696, coefficient := (-1083197534374707740536733696) }, { argument := 3255514118652248429936246784, coefficient := (-3255514118652248429936246784) }, { argument := 122318028616358513205143666688, coefficient := (-122318028616358513205143666688) }, { argument := 122308777445078339349041381376, coefficient := (-122308777445078339349041381376) }, { argument := 3264765289932422286038532096, coefficient := (-3264765289932422286038532096) }, { argument := 125224227652583121950720655360, coefficient := (-125224227652583121950720655360) }, { argument := 455467509284208023792988979200, coefficient := (-455467509284208023792988979200) }, { argument := 125224227652583121950720655360, coefficient := (-125224227652583121950720655360) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22
