import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 2912674800871466036276422982500352
def positiveArguments : Array ℕ := #[
    441, 5, 21, 91, 3, 3,
    7, 91, 91, 3, 1123, 45,
    21, 91, 7, 45, 7, 91,
    91, 3, 13, 247
  ]
def positiveCoefficients : Array ℕ := #[
    34939619668790572878752882098176, 1547425049106725343623905280, 25996740824992985772881608704, 56326271787484802507910152192, 1856910058928070412348686336, 29710560942849126597578981376,
    2166395068749415481073467392, 56326271787484802507910152192, 56326271787484802507910152192, 29710560942849126597578981376, 695103332058741024355858251776, 55707301767842112370460590080,
    25996740824992985772881608704, 56326271787484802507910152192, 2166395068749415481073467392, 55707301767842112370460590080, 2166395068749415481073467392, 56326271787484802507910152192,
    56326271787484802507910152192, 1856910058928070412348686336, 64372882042839774294754459648, 76442797425872231975020920832
  ]
def positiveScales : Array ℕ := #[
    8, 2, 4, 6, 1, 1,
    2, 6, 6, 1, 10, 5,
    4, 6, 2, 5, 2, 6,
    6, 1, 3, 7
  ]
def negativeArguments : Array ℕ := #[
    117, 108614703735, 197527545225, 108614703735, 10023, 10023,
    91, 117, 117, 91, 35758478295, 65030646825,
    35758478295, 3887, 3887, 3, 10023, 10023,
    1123, 45, 2077885455, 176983281, 2077885455, 176983281,
    515421, 91, 2008903275, 3653407125, 2008903275, 117,
    117, 7, 117, 117, 45, 7,
    247, 247, 91, 91, 286093, 1
  ]
def negativeCoefficients : Array ℕ := #[
    18104873074548686520399691776, 125224227652583121950720655360, 455467509284208023792988979200, 125224227652583121950720655360, 775492063359835405957120131072, 775492063359835405957120131072,
    28163135893742401253955076096, 18104873074548686520399691776, 18104873074548686520399691776, 28163135893742401253955076096, 82453437196645360199364771840, 299900924732141904692301004800,
    82453437196645360199364771840, 150371029146946035266652995584, 150371029146946035266652995584, 14855280471424563298789490688, 775492063359835405957120131072, 775492063359835405957120131072,
    347551666029370512177929125888, 27853650883921056185230295040, 38330221202868525197458145280, 3264765289932422286038532096, 38330221202868525197458145280, 3264765289932422286038532096,
    77888219358948972982028992512, 28163135893742401253955076096, 4632215572845244955020492800, 16848366557985500263612416000, 4632215572845244955020492800, 18104873074548686520399691776,
    18104873074548686520399691776, 1083197534374707740536733696, 18104873074548686520399691776, 18104873074548686520399691776, 27853650883921056185230295040, 1083197534374707740536733696,
    19110699356468057993755230208, 19110699356468057993755230208, 28163135893742401253955076096, 28163135893742401253955076096, 1351035994183625408121929728, 1267650600228229401496703205376
  ]
def negativeScales : Array ℕ := #[
    6, 36, 37, 36, 13, 13,
    6, 6, 6, 6, 35, 35,
    35, 11, 11, 1, 13, 13,
    10, 5, 30, 27, 30, 27,
    18, 6, 30, 31, 30, 6,
    6, 2, 6, 6, 5, 2,
    7, 7, 6, 6, 18, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8784634845528344, 2321928094887362, 4392317422778759, 6507794640198673, 1584962500720924, 1584962500720924,
    2807354922011143, 6507794640198673, 6507794640198673, 1584962500720924, 10133142212400601, 5491853096329661,
    4392317422778759, 6507794640198673, 2807354922011143, 5491853096329661, 2807354922011143, 6507794640198673,
    6507794640198673, 1584962500720924, 3700439718136550, 7948367230958674
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6870364722125690, 36660428465251836, 37523262894968021, 36660428465251836, 13291026768056127, 13291026768056127,
    6507794640199048, 6870364722125690, 6870364722125690, 6507794640199048, 35057566292694398, 35920400728705733,
    35057566292694398, 11924441399065046, 11924441399065046, 1584962500724866, 13291026768056127, 13291026768056127,
    10133142212400602, 5491853096329881, 30952468991637313, 27399037839420517, 30952468991637313, 27399037839420517,
    18975391809026432, 6507794640199048, 30903760961286902, 31766595386680513, 30903760961286902, 6870364722125690,
    6870364722125690, 2807354922807594, 6870364722125690, 6870364722125690, 5491853096329881, 2807354922807594,
    7948367241724988, 7948367241724988, 6507794640199048, 6507794640199048, 18126124673290384, 0
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
noncomputable def positiveFloor : ℝ := 23922359 / 6250000000
noncomputable def negativeCeiling : ℝ := 1185222787 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 125224227652583121950720655360, coefficient := (-125224227652583121950720655360) }, { argument := 455467509284208023792988979200, coefficient := (-455467509284208023792988979200) }, { argument := 125224227652583121950720655360, coefficient := (-125224227652583121950720655360) }, { argument := 775492063359835405957120131072, coefficient := (-775492063359835405957120131072) }, { argument := 775492063359835405957120131072, coefficient := (-775492063359835405957120131072) }, { argument := 28163135893742401253955076096, coefficient := (-28163135893742401253955076096) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 28163135893742401253955076096, coefficient := (-28163135893742401253955076096) }, { argument := 82453437196645360199364771840, coefficient := (-82453437196645360199364771840) }, { argument := 299900924732141904692301004800, coefficient := (-299900924732141904692301004800) }, { argument := 82453437196645360199364771840, coefficient := (-82453437196645360199364771840) }, { argument := 150371029146946035266652995584, coefficient := (-150371029146946035266652995584) }, { argument := 150371029146946035266652995584, coefficient := (-150371029146946035266652995584) }, { argument := 14855280471424563298789490688, coefficient := (-14855280471424563298789490688) }, { argument := 775492063359835405957120131072, coefficient := (-775492063359835405957120131072) }, { argument := 775492063359835405957120131072, coefficient := (-775492063359835405957120131072) }, { argument := 347551666029370512177929125888, coefficient := (-347551666029370512177929125888) }, { argument := 27853650883921056185230295040, coefficient := (-27853650883921056185230295040) }, { argument := 38330221202868525197458145280, coefficient := (-38330221202868525197458145280) }, { argument := 3264765289932422286038532096, coefficient := (-3264765289932422286038532096) }, { argument := 38330221202868525197458145280, coefficient := (-38330221202868525197458145280) }, { argument := 3264765289932422286038532096, coefficient := (-3264765289932422286038532096) }, { argument := 77888219358948972982028992512, coefficient := (-77888219358948972982028992512) }, { argument := 28163135893742401253955076096, coefficient := (-28163135893742401253955076096) }, { argument := 4632215572845244955020492800, coefficient := (-4632215572845244955020492800) }, { argument := 16848366557985500263612416000, coefficient := (-16848366557985500263612416000) }, { argument := 4632215572845244955020492800, coefficient := (-4632215572845244955020492800) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 1083197534374707740536733696, coefficient := (-1083197534374707740536733696) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 27853650883921056185230295040, coefficient := (-27853650883921056185230295040) }, { argument := 1083197534374707740536733696, coefficient := (-1083197534374707740536733696) }, { argument := 19110699356468057993755230208, coefficient := (-19110699356468057993755230208) }, { argument := 19110699356468057993755230208, coefficient := (-19110699356468057993755230208) }, { argument := 28163135893742401253955076096, coefficient := (-28163135893742401253955076096) }, { argument := 28163135893742401253955076096, coefficient := (-28163135893742401253955076096) }, { argument := 1351035994183625408121929728, coefficient := (-1351035994183625408121929728) }, { argument := 34939619668790572878752882098176, coefficient := 34939619668790572878752882098176 }, { argument := 1547425049106725343623905280, coefficient := 1547425049106725343623905280 }, { argument := 25996740824992985772881608704, coefficient := 25996740824992985772881608704 }, { argument := 56326271787484802507910152192, coefficient := 56326271787484802507910152192 }, { argument := 1856910058928070412348686336, coefficient := 1856910058928070412348686336 }, { argument := 29710560942849126597578981376, coefficient := 29710560942849126597578981376 }, { argument := 2166395068749415481073467392, coefficient := 2166395068749415481073467392 }, { argument := 56326271787484802507910152192, coefficient := 56326271787484802507910152192 }, { argument := 56326271787484802507910152192, coefficient := 56326271787484802507910152192 }, { argument := 29710560942849126597578981376, coefficient := 29710560942849126597578981376 }, { argument := 695103332058741024355858251776, coefficient := 695103332058741024355858251776 }, { argument := 55707301767842112370460590080, coefficient := 55707301767842112370460590080 }, { argument := 25996740824992985772881608704, coefficient := 25996740824992985772881608704 }, { argument := 56326271787484802507910152192, coefficient := 56326271787484802507910152192 }, { argument := 2166395068749415481073467392, coefficient := 2166395068749415481073467392 }, { argument := 55707301767842112370460590080, coefficient := 55707301767842112370460590080 }, { argument := 2166395068749415481073467392, coefficient := 2166395068749415481073467392 }, { argument := 56326271787484802507910152192, coefficient := 56326271787484802507910152192 }, { argument := 56326271787484802507910152192, coefficient := 56326271787484802507910152192 }, { argument := 1856910058928070412348686336, coefficient := 1856910058928070412348686336 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 64372882042839774294754459648, coefficient := 64372882042839774294754459648 }, { argument := 76442797425872231975020920832, coefficient := 76442797425872231975020920832 }] }

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
def constantNumerator : ℤ := (-1012842459926690217656726914596864)
def positiveArguments : Array ℕ := #[
    377, 3887, 117, 377, 117, 117,
    10023, 117, 3887, 10023, 13, 117,
    117, 247, 165, 2937, 165, 5225,
    8921, 165, 8921, 8921, 2937, 165,
    1449, 1623, 1449, 1623, 5, 13,
    89, 89, 476876827, 1713823805, 59609589, 337279,
    12507777, 200120687, 5400209, 44745, 429405, 140111265,
    429405, 89485
  ]
def positiveCoefficients : Array ℕ := #[
    58337924351323545454621229056, 601484116587784141066611982336, 72419492298194746081598767104, 58337924351323545454621229056, 72419492298194746081598767104, 72419492298194746081598767104,
    3101968253439341623828480524288, 72419492298194746081598767104, 601484116587784141066611982336, 3101968253439341623828480524288, 64372882042839774294754459648, 72419492298194746081598767104,
    72419492298194746081598767104, 76442797425872231975020920832, 51065026620521936339588874240, 908957473845290466844681961472, 51065026620521936339588874240, 808529588158263992043490508800,
    1380457886308109679046885900288, 51065026620521936339588874240, 1380457886308109679046885900288, 1380457886308109679046885900288, 908957473845290466844681961472, 51065026620521936339588874240,
    448443779231129004582207750144, 502294170940043046540319653888, 448443779231129004582207750144, 502294170940043046540319653888, 792281625142643375935439503360, 2059932225370872777432142708736,
    7051306463769526045825411579904, 7051306463769526045825411579904, 4503974288564052528246170845184, 16186608188552245358273033666560, 4503973202419761468227771695104, 101936322878450628353931083776,
    3780243640320501913729722482688, 3780172899270588526444421316608, 102007063928364015639232249856, 845209153104009100347310080, 129779697892904960191176376320, 1323313483416933641984283770880,
    129779697892904960191176376320, 845161929439180403895173120
  ]
def positiveScales : Array ℕ := #[
    8, 11, 6, 8, 6, 6,
    13, 6, 11, 13, 3, 6,
    6, 7, 7, 11, 7, 12,
    13, 7, 13, 13, 11, 7,
    10, 10, 10, 10, 2, 3,
    6, 6, 28, 30, 25, 18,
    23, 27, 22, 15, 18, 27,
    18, 16
  ]
def negativeArguments : Array ℕ := #[
    13, 11, 3, 5, 13, 89,
    159, 49, 5
  ]
def negativeCoefficients : Array ℕ := #[
    8239728901483491109728570834944, 6972078301255261708231867629568, 1901475900342344102245054808064, 792281625142643375935439503360, 2059932225370872777432142708736, 14102612927539052091650823159808,
    25194555679536059354746976206848, 7764359926397905084167307132928, 1584563250285286751870879006720
  ]
def negativeScales : Array ℕ := #[
    3, 3, 1, 2, 3, 6,
    7, 5, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8558420713268557, 11924441391923722, 6870364719426147, 8558420713268557, 6870364719426147, 6870364719426147,
    13291026768056126, 6870364719426147, 11924441391923722, 13291026768056126, 3700439718136550, 6870364719426147,
    6870364719426147, 7948367230958674, 7366322214245815, 11520127550324818, 7366322214245815, 12351215321855607,
    13122989722854570, 7366322214245815, 13122989722854570, 13122989722854570, 11520127550324818, 7366322214245815,
    10500841879556911, 10664447284546067, 10500841879556911, 10664447284546067, 2321928094887362, 3700439718136550,
    6475733430966389, 6475733430966389, 28829041438206636, 30674571650295974, 25829041090297197, 18363582969078005,
    23576322067139707, 27576295069219324, 22364583813161143, 15449438857943727, 18711979464493898, 27061997712771171,
    18711979464493898, 16449358249197184
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3700439718214233, 3459431618637364, 1584962500724866, 2321928094887363, 3700439718214233, 6475733430966516,
    7312882955284356, 5614709844123661, 2321928094887363
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
noncomputable def positiveFloor : ℝ := 3106145081 / 200000000000
noncomputable def negativeCeiling : ℝ := 2346803181 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 58337924351323545454621229056, coefficient := 58337924351323545454621229056 }, { argument := 601484116587784141066611982336, coefficient := 601484116587784141066611982336 }, { argument := 72419492298194746081598767104, coefficient := 72419492298194746081598767104 }, { argument := 58337924351323545454621229056, coefficient := 58337924351323545454621229056 }, { argument := 72419492298194746081598767104, coefficient := 72419492298194746081598767104 }, { argument := 72419492298194746081598767104, coefficient := 72419492298194746081598767104 }, { argument := 3101968253439341623828480524288, coefficient := 3101968253439341623828480524288 }, { argument := 72419492298194746081598767104, coefficient := 72419492298194746081598767104 }, { argument := 601484116587784141066611982336, coefficient := 601484116587784141066611982336 }, { argument := 3101968253439341623828480524288, coefficient := 3101968253439341623828480524288 }, { argument := 64372882042839774294754459648, coefficient := 64372882042839774294754459648 }, { argument := 72419492298194746081598767104, coefficient := 72419492298194746081598767104 }, { argument := 72419492298194746081598767104, coefficient := 72419492298194746081598767104 }, { argument := 76442797425872231975020920832, coefficient := 76442797425872231975020920832 }, { argument := 8239728901483491109728570834944, coefficient := (-8239728901483491109728570834944) }, { argument := 51065026620521936339588874240, coefficient := 51065026620521936339588874240 }, { argument := 908957473845290466844681961472, coefficient := 908957473845290466844681961472 }, { argument := 51065026620521936339588874240, coefficient := 51065026620521936339588874240 }, { argument := 808529588158263992043490508800, coefficient := 808529588158263992043490508800 }, { argument := 1380457886308109679046885900288, coefficient := 1380457886308109679046885900288 }, { argument := 51065026620521936339588874240, coefficient := 51065026620521936339588874240 }, { argument := 1380457886308109679046885900288, coefficient := 1380457886308109679046885900288 }, { argument := 1380457886308109679046885900288, coefficient := 1380457886308109679046885900288 }, { argument := 908957473845290466844681961472, coefficient := 908957473845290466844681961472 }, { argument := 51065026620521936339588874240, coefficient := 51065026620521936339588874240 }, { argument := 6972078301255261708231867629568, coefficient := (-6972078301255261708231867629568) }, { argument := 448443779231129004582207750144, coefficient := 448443779231129004582207750144 }, { argument := 502294170940043046540319653888, coefficient := 502294170940043046540319653888 }, { argument := 448443779231129004582207750144, coefficient := 448443779231129004582207750144 }, { argument := 502294170940043046540319653888, coefficient := 502294170940043046540319653888 }, { argument := 1901475900342344102245054808064, coefficient := (-1901475900342344102245054808064) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 2059932225370872777432142708736, coefficient := 2059932225370872777432142708736 }, { argument := 2059932225370872777432142708736, coefficient := (-2059932225370872777432142708736) }, { argument := 7051306463769526045825411579904, coefficient := 7051306463769526045825411579904 }, { argument := 7051306463769526045825411579904, coefficient := 7051306463769526045825411579904 }, { argument := 14102612927539052091650823159808, coefficient := (-14102612927539052091650823159808) }, { argument := 4503974288564052528246170845184, coefficient := 4503974288564052528246170845184 }, { argument := 16186608188552245358273033666560, coefficient := 16186608188552245358273033666560 }, { argument := 4503973202419761468227771695104, coefficient := 4503973202419761468227771695104 }, { argument := 25194555679536059354746976206848, coefficient := (-25194555679536059354746976206848) }, { argument := 101936322878450628353931083776, coefficient := 101936322878450628353931083776 }, { argument := 3780243640320501913729722482688, coefficient := 3780243640320501913729722482688 }, { argument := 3780172899270588526444421316608, coefficient := 3780172899270588526444421316608 }, { argument := 102007063928364015639232249856, coefficient := 102007063928364015639232249856 }, { argument := 7764359926397905084167307132928, coefficient := (-7764359926397905084167307132928) }, { argument := 845209153104009100347310080, coefficient := 845209153104009100347310080 }, { argument := 129779697892904960191176376320, coefficient := 129779697892904960191176376320 }, { argument := 1323313483416933641984283770880, coefficient := 1323313483416933641984283770880 }, { argument := 129779697892904960191176376320, coefficient := 129779697892904960191176376320 }, { argument := 845161929439180403895173120, coefficient := 845161929439180403895173120 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22
