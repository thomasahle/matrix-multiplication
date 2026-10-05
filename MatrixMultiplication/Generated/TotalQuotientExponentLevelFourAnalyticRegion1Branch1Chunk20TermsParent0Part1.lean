import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 20, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-8795967363642045748000418477113344)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    64009444149, 70929384057, 5121675, 3299601825, 35092652985, 1649805885,
    5121675, 37793919735, 1479063538953, 1479063538953, 37793919735, 12761756473329,
    290311875, 240544125, 1499843114323425, 1617451875, 408376142119935, 6478102125,
    6478102125, 4636695375, 240544125, 1673856585, 65506310583, 65506310583,
    1673856585, 46177303965, 166098389145, 23088659685, 620073157, 2819561,
    310036649, 2819561, 4816753576653, 820772307884115, 90815394761, 23178187125339609,
    28739048975, 3448685877, 90815394761, 180481227563, 28739048975, 2785388626657,
    178182103645, 3283090920034107, 90815394761, 3448685877, 178182103645, 3448685877,
    90815394761, 90815394761, 4816753576653, 5397898923903275, 70929384057, 85828275311498993,
    742163555133, 32869714563, 171656488324171963, 32869714563, 64009444149, 1209259498923,
    64009444149, 742163555133, 1209259498923, 674739961272327
  ]
def negativeCoefficients : Array ℕ := #[
    295191458629252070853046173696, 327104048751333375810132246528, 188956455907432735545753600, 60866910410919971032085299200, 647345188481794556540233973760, 60867093863789784073576120320,
    188956455907432735545753600, 87146845611733214684742942720, 3410488321477641162474972512256, 3410488321477641162474972512256, 87146845611733214684742942720, 919581467166039993194008018944,
    42842470877470065080401920000, 2218627956154699798806528000, 3377346445390590530923423334400, 59673441579333304933416960000, 919581320739169991207556218880, 59749945991614501478203392000,
    59749945991614501478203392000, 42765966465188868535615488000, 2218627956154699798806528000, 7719301009897114587459747840, 302094536634383133272841388032, 302094536634383133272841388032,
    7719301009897114587459747840, 425910454128124165047944478720, 1531987237806615834008915804160, 425910596214170392795765800960, 22876661668312244743175143424, 52011720167212577063960576,
    22876666870294073529268699136, 52011720167212577063960576, 21692729612949954641566629888, 924107464985730582551734517760, 418812086277267552915836370944, 6524079681300193184869729173504,
    265070940681814906908757196800, 15904256440908894414525431808, 418812086277267552915836370944, 416161376870449403846748798976, 265070940681814906908757196800, 6422668892720375194399186878464,
    410859958056813105708573655040, 924107940255566447874190344192, 418812086277267552915836370944, 15904256440908894414525431808, 410859958056813105708573655040, 15904256440908894414525431808,
    418812086277267552915836370944, 418812086277267552915836370944, 21692729612949954641566629888, 1519373473892149414611805798400, 327104048751333375810132246528, 48317023588839900796935592738816,
    3422625290593219956647481311232, 303169606159772397092317691904, 48317006053279296871800638537728, 303169606159772397092317691904, 295191458629252070853046173696, 11153450247667416082501582454784,
    295191458629252070853046173696, 3422625290593219956647481311232, 11153450247667416082501582454784, 1519379319079017389656790532096
  ]
def negativeScales : Array ℕ := #[
    35, 36, 22, 31, 35, 30,
    22, 35, 40, 40, 35, 43,
    28, 27, 50, 30, 48, 32,
    32, 32, 27, 30, 35, 35,
    30, 35, 37, 34, 29, 21,
    28, 21, 42, 49, 36, 54,
    34, 31, 36, 37, 34, 41,
    37, 51, 36, 31, 37, 31,
    36, 36, 42, 52, 36, 56,
    39, 34, 57, 34, 35, 40,
    35, 39, 40, 49
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35897565733506767, 36045664368315071, 22288184277791688, 31619644793692244, 35030449967677338, 30619649141968589,
    22288184277791688, 35137435102004108, 40427821169018685, 40427821169018685, 35137435102004108, 43536892142652310,
    28113028344681178, 27841726324341616, 50413733024015061, 30591075641490231, 48536891912928959, 32592924065882835,
    32592924065882835, 32110449800579402, 27841726324341616, 30640528777964860, 35930914852487430, 35930914852487430,
    30640528777964860, 35426464893534673, 37273247125587529, 34426465374825513, 29207863195590025, 21427039124705171,
    28207863523648054, 21427039124705171, 42131198256711811, 49543975384963431, 36402217828578824, 54363617249013195,
    34742293270366283, 31683399581171611, 36402217828578824, 37393057829293345, 34742293270366283, 41341015769853060,
    37374561485675953, 51543976126943434, 36402217828578824, 31683399581171611, 37374561485675953, 31683399581171611,
    36402217828578824, 36402217828578824, 42131198256711811, 52261319385786050, 36045664368315071, 56252302526430370,
    39432946201196557, 34936039885359499, 57252302002837048, 34936039885359499, 35897565733506767, 40137261009072424,
    35897565733506767, 39432946201196557, 40137261009072424, 49261324935972381
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
noncomputable def negativeCeiling : ℝ := 2027090557 / 20000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 295191458629252070853046173696, coefficient := (-295191458629252070853046173696) }, { argument := 327104048751333375810132246528, coefficient := (-327104048751333375810132246528) }, { argument := 188956455907432735545753600, coefficient := (-188956455907432735545753600) }, { argument := 60866910410919971032085299200, coefficient := (-60866910410919971032085299200) }, { argument := 647345188481794556540233973760, coefficient := (-647345188481794556540233973760) }, { argument := 60867093863789784073576120320, coefficient := (-60867093863789784073576120320) }, { argument := 188956455907432735545753600, coefficient := (-188956455907432735545753600) }, { argument := 87146845611733214684742942720, coefficient := (-87146845611733214684742942720) }, { argument := 3410488321477641162474972512256, coefficient := (-3410488321477641162474972512256) }, { argument := 3410488321477641162474972512256, coefficient := (-3410488321477641162474972512256) }, { argument := 87146845611733214684742942720, coefficient := (-87146845611733214684742942720) }, { argument := 919581467166039993194008018944, coefficient := (-919581467166039993194008018944) }, { argument := 42842470877470065080401920000, coefficient := (-42842470877470065080401920000) }, { argument := 2218627956154699798806528000, coefficient := (-2218627956154699798806528000) }, { argument := 3377346445390590530923423334400, coefficient := (-3377346445390590530923423334400) }, { argument := 59673441579333304933416960000, coefficient := (-59673441579333304933416960000) }, { argument := 919581320739169991207556218880, coefficient := (-919581320739169991207556218880) }, { argument := 59749945991614501478203392000, coefficient := (-59749945991614501478203392000) }, { argument := 59749945991614501478203392000, coefficient := (-59749945991614501478203392000) }, { argument := 42765966465188868535615488000, coefficient := (-42765966465188868535615488000) }, { argument := 2218627956154699798806528000, coefficient := (-2218627956154699798806528000) }, { argument := 7719301009897114587459747840, coefficient := (-7719301009897114587459747840) }, { argument := 302094536634383133272841388032, coefficient := (-302094536634383133272841388032) }, { argument := 302094536634383133272841388032, coefficient := (-302094536634383133272841388032) }, { argument := 7719301009897114587459747840, coefficient := (-7719301009897114587459747840) }, { argument := 425910454128124165047944478720, coefficient := (-425910454128124165047944478720) }, { argument := 1531987237806615834008915804160, coefficient := (-1531987237806615834008915804160) }, { argument := 425910596214170392795765800960, coefficient := (-425910596214170392795765800960) }, { argument := 22876661668312244743175143424, coefficient := (-22876661668312244743175143424) }, { argument := 52011720167212577063960576, coefficient := (-52011720167212577063960576) }, { argument := 22876666870294073529268699136, coefficient := (-22876666870294073529268699136) }, { argument := 52011720167212577063960576, coefficient := (-52011720167212577063960576) }, { argument := 21692729612949954641566629888, coefficient := (-21692729612949954641566629888) }, { argument := 924107464985730582551734517760, coefficient := (-924107464985730582551734517760) }, { argument := 418812086277267552915836370944, coefficient := (-418812086277267552915836370944) }, { argument := 6524079681300193184869729173504, coefficient := (-6524079681300193184869729173504) }, { argument := 265070940681814906908757196800, coefficient := (-265070940681814906908757196800) }, { argument := 15904256440908894414525431808, coefficient := (-15904256440908894414525431808) }, { argument := 418812086277267552915836370944, coefficient := (-418812086277267552915836370944) }, { argument := 416161376870449403846748798976, coefficient := (-416161376870449403846748798976) }, { argument := 265070940681814906908757196800, coefficient := (-265070940681814906908757196800) }, { argument := 6422668892720375194399186878464, coefficient := (-6422668892720375194399186878464) }, { argument := 410859958056813105708573655040, coefficient := (-410859958056813105708573655040) }, { argument := 924107940255566447874190344192, coefficient := (-924107940255566447874190344192) }, { argument := 418812086277267552915836370944, coefficient := (-418812086277267552915836370944) }, { argument := 15904256440908894414525431808, coefficient := (-15904256440908894414525431808) }, { argument := 410859958056813105708573655040, coefficient := (-410859958056813105708573655040) }, { argument := 15904256440908894414525431808, coefficient := (-15904256440908894414525431808) }, { argument := 418812086277267552915836370944, coefficient := (-418812086277267552915836370944) }, { argument := 418812086277267552915836370944, coefficient := (-418812086277267552915836370944) }, { argument := 21692729612949954641566629888, coefficient := (-21692729612949954641566629888) }, { argument := 1519373473892149414611805798400, coefficient := (-1519373473892149414611805798400) }, { argument := 327104048751333375810132246528, coefficient := (-327104048751333375810132246528) }, { argument := 48317023588839900796935592738816, coefficient := (-48317023588839900796935592738816) }, { argument := 3422625290593219956647481311232, coefficient := (-3422625290593219956647481311232) }, { argument := 303169606159772397092317691904, coefficient := (-303169606159772397092317691904) }, { argument := 48317006053279296871800638537728, coefficient := (-48317006053279296871800638537728) }, { argument := 303169606159772397092317691904, coefficient := (-303169606159772397092317691904) }, { argument := 295191458629252070853046173696, coefficient := (-295191458629252070853046173696) }, { argument := 11153450247667416082501582454784, coefficient := (-11153450247667416082501582454784) }, { argument := 295191458629252070853046173696, coefficient := (-295191458629252070853046173696) }, { argument := 3422625290593219956647481311232, coefficient := (-3422625290593219956647481311232) }, { argument := 11153450247667416082501582454784, coefficient := (-11153450247667416082501582454784) }, { argument := 1519379319079017389656790532096, coefficient := (-1519379319079017389656790532096) }] }

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


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4127825105100404040820556449185792)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    64009444149, 64009444149, 70929384057, 357657155399411, 3087588875, 2558287925,
    42406790359591235, 17202280875, 11445025149663325, 68897340325, 68897340325, 49313205175,
    2558287925, 1673856585, 65506310583, 65506310583, 1673856585, 14613070875,
    52562781375, 7306537875, 44020495869, 559217175, 44020496715, 559217175,
    1753568505, 6307533765, 876784545, 7491026051, 7491027837, 2819561,
    559217175, 559217175, 2819561, 20512965, 13215328335, 140550574263,
    6607684083, 20512965, 3259615455, 127564920609, 127564920609, 3259615455,
    20512965, 13215328335, 140550574263, 6607684083, 20512965, 61580302785,
    2409942689343, 2409942689343, 61580302785, 46177303965, 166098389145, 23088659685,
    3259615455, 127564920609, 127564920609, 3259615455, 91770085095, 330094267035,
    45885057855, 19318961921, 19318966527, 14682135
  ]
def negativeCoefficients : Array ℕ := #[
    295191458629252070853046173696, 295191458629252070853046173696, 327104048751333375810132246528, 6442978527132715844266228711424, 455647694255662332406398976000, 23596041309668227928188518400,
    23872900657679228502442057400320, 634652145570386820137484288000, 6442976374908713210428679782400, 635465802167271931445352857600, 635465802167271931445352857600, 454834037658777221098530406400,
    23596041309668227928188518400, 7719301009897114587459747840, 302094536634383133272841388032, 302094536634383133272841388032, 7719301009897114587459747840, 269563578562103901929078784000,
    969612175826972046841085952000, 269563668489981261263142912000, 203008705323307887104492568576, 10315736108847847225216204800, 203008709224794258694062735360, 10315736108847847225216204800,
    16173814713726234115744727040, 58176730549618322810465157120, 16173820109398875675788574720, 17273130051536014420373143552, 17273134169771628876030541824, 52011720167212577063960576,
    10315736108847847225216204800, 10315736108847847225216204800, 52011720167212577063960576, 189198707773980726232350720, 60944944911446791507767459840, 648175118210617370074259914752,
    60945128599512591489055064064, 189198707773980726232350720, 7516161509636664203579228160, 294144680407162524502503456768, 294144680407162524502503456768, 7516161509636664203579228160,
    189198707773980726232350720, 60944944911446791507767459840, 648175118210617370074259914752, 60945128599512591489055064064, 189198707773980726232350720, 283989021364109636664966512640,
    11113899005654411060932427907072, 11113899005654411060932427907072, 283989021364109636664966512640, 425910454128124165047944478720, 1531987237806615834008915804160, 425910596214170392795765800960,
    7516161509636664203579228160, 294144680407162524502503456768, 294144680407162524502503456768, 7516161509636664203579228160, 423214818342503126028653690880, 1522291116048346113540504944640,
    423214959529270580183134371840, 22273246645401702805218000896, 22273251955758153024355172352, 135418793400326793807790080
  ]
def negativeScales : Array ℕ := #[
    35, 35, 36, 48, 31, 31,
    55, 34, 53, 36, 36, 35,
    31, 30, 35, 35, 30, 33,
    35, 32, 35, 29, 35, 29,
    30, 32, 29, 32, 32, 21,
    29, 29, 21, 24, 33, 37,
    32, 24, 31, 36, 36, 31,
    24, 33, 37, 32, 24, 35,
    41, 41, 35, 35, 37, 34,
    31, 36, 36, 31, 36, 38,
    35, 34, 34, 23
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35897565733506767, 35897565733506767, 36045664368315071, 48345570633239479, 31523833518676513, 31252531496858529,
    55235144812084002, 34001880815480567, 53345570151318982, 36003729239872936, 36003729239872936, 35521254974574690,
    31252531496858529, 30640528777964860, 35930914852487430, 35930914852487430, 30640528777964860, 33766540335453724,
    35613322567193292, 32766540816744567, 35357456345436988, 29058833429373802, 35357456373163164, 29058833429373802,
    30707646646165271, 32554428878133102, 29707647127456111, 32802516193818542, 32802516537783848, 21427039124705171,
    29058833429373802, 29058833429373802, 21427039124705171, 24290032702184056, 33621493218085101, 37032298392069707,
    32621497566361446, 24290032702184056, 31602054630139497, 36892440700959720, 36892440700959720, 31602054630139497,
    24290032702184056, 33621493218085101, 37032298392069707, 32621497566361446, 24290032702184056, 35841749911358503,
    41132135976894556, 41132135976894556, 35841749911358503, 35426464893534673, 37273247125587529, 34426465374825513,
    31602054630139497, 36892440700959720, 36892440700959720, 31602054630139497, 36417304894249191, 38264087126302054,
    35417305375540031, 34169298523810185, 34169298867775487, 23807558437638343
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
noncomputable def negativeCeiling : ℝ := 2567251539 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 295191458629252070853046173696, coefficient := (-295191458629252070853046173696) }, { argument := 295191458629252070853046173696, coefficient := (-295191458629252070853046173696) }, { argument := 327104048751333375810132246528, coefficient := (-327104048751333375810132246528) }, { argument := 6442978527132715844266228711424, coefficient := (-6442978527132715844266228711424) }, { argument := 455647694255662332406398976000, coefficient := (-455647694255662332406398976000) }, { argument := 23596041309668227928188518400, coefficient := (-23596041309668227928188518400) }, { argument := 23872900657679228502442057400320, coefficient := (-23872900657679228502442057400320) }, { argument := 634652145570386820137484288000, coefficient := (-634652145570386820137484288000) }, { argument := 6442976374908713210428679782400, coefficient := (-6442976374908713210428679782400) }, { argument := 635465802167271931445352857600, coefficient := (-635465802167271931445352857600) }, { argument := 635465802167271931445352857600, coefficient := (-635465802167271931445352857600) }, { argument := 454834037658777221098530406400, coefficient := (-454834037658777221098530406400) }, { argument := 23596041309668227928188518400, coefficient := (-23596041309668227928188518400) }, { argument := 7719301009897114587459747840, coefficient := (-7719301009897114587459747840) }, { argument := 302094536634383133272841388032, coefficient := (-302094536634383133272841388032) }, { argument := 302094536634383133272841388032, coefficient := (-302094536634383133272841388032) }, { argument := 7719301009897114587459747840, coefficient := (-7719301009897114587459747840) }, { argument := 269563578562103901929078784000, coefficient := (-269563578562103901929078784000) }, { argument := 969612175826972046841085952000, coefficient := (-969612175826972046841085952000) }, { argument := 269563668489981261263142912000, coefficient := (-269563668489981261263142912000) }, { argument := 203008705323307887104492568576, coefficient := (-203008705323307887104492568576) }, { argument := 10315736108847847225216204800, coefficient := (-10315736108847847225216204800) }, { argument := 203008709224794258694062735360, coefficient := (-203008709224794258694062735360) }, { argument := 10315736108847847225216204800, coefficient := (-10315736108847847225216204800) }, { argument := 16173814713726234115744727040, coefficient := (-16173814713726234115744727040) }, { argument := 58176730549618322810465157120, coefficient := (-58176730549618322810465157120) }, { argument := 16173820109398875675788574720, coefficient := (-16173820109398875675788574720) }, { argument := 17273130051536014420373143552, coefficient := (-17273130051536014420373143552) }, { argument := 17273134169771628876030541824, coefficient := (-17273134169771628876030541824) }, { argument := 52011720167212577063960576, coefficient := (-52011720167212577063960576) }, { argument := 10315736108847847225216204800, coefficient := (-10315736108847847225216204800) }, { argument := 10315736108847847225216204800, coefficient := (-10315736108847847225216204800) }, { argument := 52011720167212577063960576, coefficient := (-52011720167212577063960576) }, { argument := 189198707773980726232350720, coefficient := (-189198707773980726232350720) }, { argument := 60944944911446791507767459840, coefficient := (-60944944911446791507767459840) }, { argument := 648175118210617370074259914752, coefficient := (-648175118210617370074259914752) }, { argument := 60945128599512591489055064064, coefficient := (-60945128599512591489055064064) }, { argument := 189198707773980726232350720, coefficient := (-189198707773980726232350720) }, { argument := 7516161509636664203579228160, coefficient := (-7516161509636664203579228160) }, { argument := 294144680407162524502503456768, coefficient := (-294144680407162524502503456768) }, { argument := 294144680407162524502503456768, coefficient := (-294144680407162524502503456768) }, { argument := 7516161509636664203579228160, coefficient := (-7516161509636664203579228160) }, { argument := 189198707773980726232350720, coefficient := (-189198707773980726232350720) }, { argument := 60944944911446791507767459840, coefficient := (-60944944911446791507767459840) }, { argument := 648175118210617370074259914752, coefficient := (-648175118210617370074259914752) }, { argument := 60945128599512591489055064064, coefficient := (-60945128599512591489055064064) }, { argument := 189198707773980726232350720, coefficient := (-189198707773980726232350720) }, { argument := 283989021364109636664966512640, coefficient := (-283989021364109636664966512640) }, { argument := 11113899005654411060932427907072, coefficient := (-11113899005654411060932427907072) }, { argument := 11113899005654411060932427907072, coefficient := (-11113899005654411060932427907072) }, { argument := 283989021364109636664966512640, coefficient := (-283989021364109636664966512640) }, { argument := 425910454128124165047944478720, coefficient := (-425910454128124165047944478720) }, { argument := 1531987237806615834008915804160, coefficient := (-1531987237806615834008915804160) }, { argument := 425910596214170392795765800960, coefficient := (-425910596214170392795765800960) }, { argument := 7516161509636664203579228160, coefficient := (-7516161509636664203579228160) }, { argument := 294144680407162524502503456768, coefficient := (-294144680407162524502503456768) }, { argument := 294144680407162524502503456768, coefficient := (-294144680407162524502503456768) }, { argument := 7516161509636664203579228160, coefficient := (-7516161509636664203579228160) }, { argument := 423214818342503126028653690880, coefficient := (-423214818342503126028653690880) }, { argument := 1522291116048346113540504944640, coefficient := (-1522291116048346113540504944640) }, { argument := 423214959529270580183134371840, coefficient := (-423214959529270580183134371840) }, { argument := 22273246645401702805218000896, coefficient := (-22273246645401702805218000896) }, { argument := 22273251955758153024355172352, coefficient := (-22273251955758153024355172352) }, { argument := 135418793400326793807790080, coefficient := (-135418793400326793807790080) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20
