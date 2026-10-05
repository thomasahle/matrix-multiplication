import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 12, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk12

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-60373395400458918133390382764916736)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    73173401, 875, 11457602897, 9875, 875, 5728801635,
    875, 875, 36275, 225, 9875, 36275,
    292695429, 875, 225, 875, 17511774963039731, 29418844749,
    763363237, 126891981997949541, 47387240943, 35028342827413941, 47387240943, 49383729409,
    29418844749, 1468006225, 17468259093154957, 49622855, 17468264319906675, 49622855,
    49622855, 5799948375, 1587930825, 29418844749, 29418851763, 291480225,
    763363237, 763363419, 945, 17511780186718733, 29418851763, 763363419,
    126892020183944603, 47387252241, 35028353275067979, 47387252241, 49383741183, 29418851763,
    1468006575, 253146913504108107, 5799948375, 253146989918618037, 5799948375, 11400595757,
    47387240943, 47387252241, 10665, 945, 69882637174116225, 1587930825,
    69882658081722495, 1587930825, 1425074513, 945
  ]
def negativeCoefficients : Array ℕ := #[
    1382206465279920719798032400384, 16924961474604808445886464000, 54106999894822947873805473677312, 191010279499111409603575808000, 16924961474604808445886464000, 54107001656265645984183138385920,
    16924961474604808445886464000, 16924961474604808445886464000, 701660545704330772999464550400, 17408531802450660115768934400, 191010279499111409603575808000, 701660545704330772999464550400,
    1382215083598751956900547395584, 16924961474604808445886464000, 17408531802450660115768934400, 16924961474604808445886464000, 39433011599070856947243352588288, 33917618751812319469344129024,
    1760195783527186239926042624, 142867670710567309843683380035584, 54633769127170742139242938368, 39438407926236852741596390621184, 54633769127170742139242938368, 56935563613321677991453917184,
    33917618751812319469344129024, 1692495945699217538390425600, 39335022571371971359689288974336, 3661520425567193567823134720, 39335034340970516131139184230400, 3661520425567193567823134720,
    3661520425567193567823134720, 13373770414294074264649728000, 3661519191941183638496870400, 33917618751812319469344129024, 33917626838403752781768818688, 1376476444959302832558283161600,
    1760195783527186239926042624, 1760196203190613916818341888, 18278958392573193121557381120, 39433023361750260402385567350784, 33917626838403752781768818688, 1760196203190613916818341888,
    142867713704175592842383455158272, 54633782152877901187400073216, 39438419689249560849760854736896, 54633782152877901187400073216, 56935577187819473232470212608, 33917626838403752781768818688,
    1692496349221744150786867200, 142509043165886556564811765776384, 13373770414294074264649728000, 142509086183431362370695063404544, 13373770414294074264649728000, 53837791287602690407357975887872,
    54633769127170742139242938368, 54633782152877901187400073216, 206291101859040322371861872640, 18278958392573193121557381120, 39340427342127175313388679987200, 3661519191941183638496870400,
    39340439112063151161019402813440, 3661519191941183638496870400, 53837792926263859963124865040384, 18278958392573193121557381120
  ]
def negativeScales : Array ℕ := #[
    26, 9, 33, 13, 9, 32,
    9, 9, 15, 7, 13, 15,
    28, 9, 7, 9, 53, 34,
    29, 56, 35, 54, 35, 35,
    34, 30, 53, 25, 53, 25,
    25, 32, 30, 34, 34, 28,
    29, 29, 9, 53, 34, 29,
    56, 35, 54, 35, 35, 34,
    30, 57, 32, 57, 32, 33,
    35, 35, 13, 9, 55, 30,
    55, 30, 30, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26124815979125368, 9773139207089529, 33415586191018333, 13269565032839191, 9773139207089529, 32415586237984984,
    9773139207089529, 9773139207089529, 15146687993841470, 7813781192070436, 13269565032839191, 15146687993841470,
    28124824974573868, 9773139207089529, 7813781192070436, 9773139207089529, 53959174850600335, 34776021543663192,
    29507794468216387, 56816378525580285, 35463779613352801, 54959372267005022, 35463779613352801, 35523316740330668,
    34776021543663192, 30451210939849717, 53955585364416740, 25564501405809335, 53955585796091646, 25564501405809335,
    25564501405809335, 32433392912939780, 30564500919741740, 34776021543663192, 34776021887628496, 28118822768554951,
    29507794468216387, 29507794812181688, 9884170522387776, 53959175280949412, 34776021887628496, 29507794812181688,
    56816378959734890, 35463779957318103, 54959372697307408, 35463779957318103, 35523317084295970, 34776021887628496,
    30451211283815019, 57812752508204581, 32433392912939780, 57812752943694068, 32433392912939780, 33408390165650659,
    35463779613352801, 35463779957318103, 13380596345227937, 9884170522387776, 55955783582221324, 30564500919741740,
    55955784013849299, 30564500919741740, 30408390209561976, 9884170522387776
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
noncomputable def negativeCeiling : ℝ := 343762106893 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1382206465279920719798032400384, coefficient := (-1382206465279920719798032400384) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 54106999894822947873805473677312, coefficient := (-54106999894822947873805473677312) }, { argument := 191010279499111409603575808000, coefficient := (-191010279499111409603575808000) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 54107001656265645984183138385920, coefficient := (-54107001656265645984183138385920) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 701660545704330772999464550400, coefficient := (-701660545704330772999464550400) }, { argument := 17408531802450660115768934400, coefficient := (-17408531802450660115768934400) }, { argument := 191010279499111409603575808000, coefficient := (-191010279499111409603575808000) }, { argument := 701660545704330772999464550400, coefficient := (-701660545704330772999464550400) }, { argument := 1382215083598751956900547395584, coefficient := (-1382215083598751956900547395584) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 17408531802450660115768934400, coefficient := (-17408531802450660115768934400) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 39433011599070856947243352588288, coefficient := (-39433011599070856947243352588288) }, { argument := 33917618751812319469344129024, coefficient := (-33917618751812319469344129024) }, { argument := 1760195783527186239926042624, coefficient := (-1760195783527186239926042624) }, { argument := 142867670710567309843683380035584, coefficient := (-142867670710567309843683380035584) }, { argument := 54633769127170742139242938368, coefficient := (-54633769127170742139242938368) }, { argument := 39438407926236852741596390621184, coefficient := (-39438407926236852741596390621184) }, { argument := 54633769127170742139242938368, coefficient := (-54633769127170742139242938368) }, { argument := 56935563613321677991453917184, coefficient := (-56935563613321677991453917184) }, { argument := 33917618751812319469344129024, coefficient := (-33917618751812319469344129024) }, { argument := 1692495945699217538390425600, coefficient := (-1692495945699217538390425600) }, { argument := 39335022571371971359689288974336, coefficient := (-39335022571371971359689288974336) }, { argument := 3661520425567193567823134720, coefficient := (-3661520425567193567823134720) }, { argument := 39335034340970516131139184230400, coefficient := (-39335034340970516131139184230400) }, { argument := 3661520425567193567823134720, coefficient := (-3661520425567193567823134720) }, { argument := 3661520425567193567823134720, coefficient := (-3661520425567193567823134720) }, { argument := 13373770414294074264649728000, coefficient := (-13373770414294074264649728000) }, { argument := 3661519191941183638496870400, coefficient := (-3661519191941183638496870400) }, { argument := 33917618751812319469344129024, coefficient := (-33917618751812319469344129024) }, { argument := 33917626838403752781768818688, coefficient := (-33917626838403752781768818688) }, { argument := 1376476444959302832558283161600, coefficient := (-1376476444959302832558283161600) }, { argument := 1760195783527186239926042624, coefficient := (-1760195783527186239926042624) }, { argument := 1760196203190613916818341888, coefficient := (-1760196203190613916818341888) }, { argument := 18278958392573193121557381120, coefficient := (-18278958392573193121557381120) }, { argument := 39433023361750260402385567350784, coefficient := (-39433023361750260402385567350784) }, { argument := 33917626838403752781768818688, coefficient := (-33917626838403752781768818688) }, { argument := 1760196203190613916818341888, coefficient := (-1760196203190613916818341888) }, { argument := 142867713704175592842383455158272, coefficient := (-142867713704175592842383455158272) }, { argument := 54633782152877901187400073216, coefficient := (-54633782152877901187400073216) }, { argument := 39438419689249560849760854736896, coefficient := (-39438419689249560849760854736896) }, { argument := 54633782152877901187400073216, coefficient := (-54633782152877901187400073216) }, { argument := 56935577187819473232470212608, coefficient := (-56935577187819473232470212608) }, { argument := 33917626838403752781768818688, coefficient := (-33917626838403752781768818688) }, { argument := 1692496349221744150786867200, coefficient := (-1692496349221744150786867200) }, { argument := 142509043165886556564811765776384, coefficient := (-142509043165886556564811765776384) }, { argument := 13373770414294074264649728000, coefficient := (-13373770414294074264649728000) }, { argument := 142509086183431362370695063404544, coefficient := (-142509086183431362370695063404544) }, { argument := 13373770414294074264649728000, coefficient := (-13373770414294074264649728000) }, { argument := 53837791287602690407357975887872, coefficient := (-53837791287602690407357975887872) }, { argument := 54633769127170742139242938368, coefficient := (-54633769127170742139242938368) }, { argument := 54633782152877901187400073216, coefficient := (-54633782152877901187400073216) }, { argument := 206291101859040322371861872640, coefficient := (-206291101859040322371861872640) }, { argument := 18278958392573193121557381120, coefficient := (-18278958392573193121557381120) }, { argument := 39340427342127175313388679987200, coefficient := (-39340427342127175313388679987200) }, { argument := 3661519191941183638496870400, coefficient := (-3661519191941183638496870400) }, { argument := 39340439112063151161019402813440, coefficient := (-39340439112063151161019402813440) }, { argument := 3661519191941183638496870400, coefficient := (-3661519191941183638496870400) }, { argument := 53837792926263859963124865040384, coefficient := (-53837792926263859963124865040384) }, { argument := 18278958392573193121557381120, coefficient := (-18278958392573193121557381120) }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 61755595480242096922834655965609984
def positiveArguments : Array ℕ := #[
    14039, 489, 535, 489, 535, 21,
    3507, 91, 3773, 5649, 175, 5649,
    5887, 3507, 175, 403, 455, 195,
    5135, 455, 195, 455, 455, 18863,
    117, 5135, 18863, 403, 455, 117,
    455, 2845, 46942643317, 46942657419, 16680645111, 60421088669,
    4170725915, 577571077
  ]
def positiveCoefficients : Array ℕ := #[
    1112284173537757035475763518767104, 37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096, 41393620063604902941939466240, 6499185206248246443220402176,
    135670491180432144502225895424, 7040783973435600313488769024, 145960867756991868037324865536, 218535102560097286653286023168, 6769984589841923378354585600, 218535102560097286653286023168,
    227742281602282302447848259584, 135670491180432144502225895424, 6769984589841923378354585600, 31180614739500515674021691392, 35203919867178001567443845120, 30174788457581144200666152960,
    397301381358151731975437680640, 35203919867178001567443845120, 30174788457581144200666152960, 35203919867178001567443845120, 35203919867178001567443845120, 1459453935065008007838886264832,
    36209746149097373040799383552, 397301381358151731975437680640, 1459453935065008007838886264832, 31180614739500515674021691392, 35203919867178001567443845120, 36209746149097373040799383552,
    35203919867178001567443845120, 225404122353082040453632538705920, 443360730835011091745735142539264, 443360864024635374601208749621248, 157544238769659625368285465280512, 570661047977961006050594938421248,
    157565570161854662876940961054720, 2727502295499723036682293870592
  ]
def positiveScales : Array ℕ := #[
    13, 8, 9, 8, 9, 4,
    11, 6, 11, 12, 7, 12,
    12, 11, 7, 8, 8, 7,
    12, 8, 7, 8, 8, 14,
    6, 12, 14, 8, 8, 6,
    8, 11, 35, 35, 33, 35,
    31, 29
  ]
def negativeArguments : Array ℕ := #[
    49622855, 5799948375, 1587930825, 47387240943, 47387252241, 945,
    49383729409, 49383741183, 39177, 243, 29418844749, 29418851763,
    10665, 39177, 145741013, 1468006225, 1468006575, 945,
    243, 945, 1, 7, 13, 2845,
    1399, 2795
  ]
def negativeCoefficients : Array ℕ := #[
    3661520425567193567823134720, 13373770414294074264649728000, 3661519191941183638496870400, 54633769127170742139242938368, 54633782152877901187400073216, 18278958392573193121557381120,
    56935563613321677991453917184, 56935577187819473232470212608, 757793389360677234839421714432, 18801214346646712925030449152, 33917618751812319469344129024, 33917626838403752781768818688,
    206291101859040322371861872640, 757793389360677234839421714432, 1376484949941338480789313028096, 1692495945699217538390425600, 1692496349221744150786867200, 18278958392573193121557381120,
    18801214346646712925030449152, 18278958392573193121557381120, 158456325028528675187087900672, 1109194275199700726309615304704, 4119864450741745554864285417472, 225404122353082040453632538705920,
    886721594859646466346943892160512, 885770856909475294295821364756480
  ]
def negativeScales : Array ℕ := #[
    25, 32, 30, 35, 35, 9,
    35, 35, 15, 7, 34, 34,
    13, 15, 27, 30, 30, 9,
    7, 9, 0, 2, 3, 11,
    10, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13777152555450350, 8933690654464738, 9063395081288509, 8933690654464738, 9063395081288509, 4392317422778759,
    11776021715228447, 6507794640198673, 11881496384617007, 12463779785335379, 7451211111832325, 12463779785335379,
    12523316912312711, 11776021715228447, 7451211111832325, 8654636028526477, 8829722735013603, 7607330313749179,
    12326148561205557, 8829722735013603, 7607330313749179, 8829722735013603, 8829722735013603, 14203271522207836,
    6870364719426147, 12326148561205557, 14203271522207836, 8654636028526477, 8829722735013603, 6870364719426147,
    8829722735013603, 11474212937193936, 35450180030465364, 35450180463864103, 33957456033116559, 35814333127643027,
    31957651359904454, 29105423257360283
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    25564501405809335, 32433392912939780, 30564500919741740, 35463779613352801, 35463779957318103, 9884170522387776,
    35523316740330668, 35523317084295970, 15257719306230214, 7924812510375204, 34776021543663192, 34776021887628496,
    13380596345227937, 15257719306230214, 27118831682661359, 30451210939849717, 30451211283815019, 9884170522387776,
    7924812510375204, 9884170522387776, 0, 2807354922807594, 3700439718214233, 11474212937194057,
    10450180247164801, 11448632567730597
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 966778141703 / 1000000000000
noncomputable def negativeCeiling : ℝ := 265863007821 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3661520425567193567823134720, coefficient := (-3661520425567193567823134720) }, { argument := 13373770414294074264649728000, coefficient := (-13373770414294074264649728000) }, { argument := 3661519191941183638496870400, coefficient := (-3661519191941183638496870400) }, { argument := 54633769127170742139242938368, coefficient := (-54633769127170742139242938368) }, { argument := 54633782152877901187400073216, coefficient := (-54633782152877901187400073216) }, { argument := 18278958392573193121557381120, coefficient := (-18278958392573193121557381120) }, { argument := 56935563613321677991453917184, coefficient := (-56935563613321677991453917184) }, { argument := 56935577187819473232470212608, coefficient := (-56935577187819473232470212608) }, { argument := 757793389360677234839421714432, coefficient := (-757793389360677234839421714432) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 33917618751812319469344129024, coefficient := (-33917618751812319469344129024) }, { argument := 33917626838403752781768818688, coefficient := (-33917626838403752781768818688) }, { argument := 206291101859040322371861872640, coefficient := (-206291101859040322371861872640) }, { argument := 757793389360677234839421714432, coefficient := (-757793389360677234839421714432) }, { argument := 1376484949941338480789313028096, coefficient := (-1376484949941338480789313028096) }, { argument := 1692495945699217538390425600, coefficient := (-1692495945699217538390425600) }, { argument := 1692496349221744150786867200, coefficient := (-1692496349221744150786867200) }, { argument := 18278958392573193121557381120, coefficient := (-18278958392573193121557381120) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 18278958392573193121557381120, coefficient := (-18278958392573193121557381120) }, { argument := 1112284173537757035475763518767104, coefficient := 1112284173537757035475763518767104 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 6499185206248246443220402176, coefficient := 6499185206248246443220402176 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 145960867756991868037324865536, coefficient := 145960867756991868037324865536 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 6769984589841923378354585600, coefficient := 6769984589841923378354585600 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 227742281602282302447848259584, coefficient := 227742281602282302447848259584 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 6769984589841923378354585600, coefficient := 6769984589841923378354585600 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 31180614739500515674021691392, coefficient := 31180614739500515674021691392 }, { argument := 35203919867178001567443845120, coefficient := 35203919867178001567443845120 }, { argument := 30174788457581144200666152960, coefficient := 30174788457581144200666152960 }, { argument := 397301381358151731975437680640, coefficient := 397301381358151731975437680640 }, { argument := 35203919867178001567443845120, coefficient := 35203919867178001567443845120 }, { argument := 30174788457581144200666152960, coefficient := 30174788457581144200666152960 }, { argument := 35203919867178001567443845120, coefficient := 35203919867178001567443845120 }, { argument := 35203919867178001567443845120, coefficient := 35203919867178001567443845120 }, { argument := 1459453935065008007838886264832, coefficient := 1459453935065008007838886264832 }, { argument := 36209746149097373040799383552, coefficient := 36209746149097373040799383552 }, { argument := 397301381358151731975437680640, coefficient := 397301381358151731975437680640 }, { argument := 1459453935065008007838886264832, coefficient := 1459453935065008007838886264832 }, { argument := 31180614739500515674021691392, coefficient := 31180614739500515674021691392 }, { argument := 35203919867178001567443845120, coefficient := 35203919867178001567443845120 }, { argument := 36209746149097373040799383552, coefficient := 36209746149097373040799383552 }, { argument := 35203919867178001567443845120, coefficient := 35203919867178001567443845120 }, { argument := 4119864450741745554864285417472, coefficient := (-4119864450741745554864285417472) }, { argument := 225404122353082040453632538705920, coefficient := 225404122353082040453632538705920 }, { argument := 225404122353082040453632538705920, coefficient := (-225404122353082040453632538705920) }, { argument := 443360730835011091745735142539264, coefficient := 443360730835011091745735142539264 }, { argument := 443360864024635374601208749621248, coefficient := 443360864024635374601208749621248 }, { argument := 886721594859646466346943892160512, coefficient := (-886721594859646466346943892160512) }, { argument := 157544238769659625368285465280512, coefficient := 157544238769659625368285465280512 }, { argument := 570661047977961006050594938421248, coefficient := 570661047977961006050594938421248 }, { argument := 157565570161854662876940961054720, coefficient := 157565570161854662876940961054720 }, { argument := 885770856909475294295821364756480, coefficient := (-885770856909475294295821364756480) }, { argument := 2727502295499723036682293870592, coefficient := 2727502295499723036682293870592 }] }

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


end Parent2

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-5291373118744107154271493116919808)
def positiveArguments : Array ℕ := #[
    11425904447, 11425904807, 577574703
  ]
def positiveCoefficients : Array ℕ := #[
    107914616393968057136962783412224, 107914619794071924803107337273344, 2727519418800589922015838732288
  ]
def positiveScales : Array ℕ := #[
    33, 33, 29
  ]
def negativeArguments : Array ℕ := #[
    2793
  ]
def negativeCoefficients : Array ℕ := #[
    221284257902340294898768253288448
  ]
def negativeScales : Array ℕ := #[
    11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    33411589318932131, 33411589364387631, 29105432314593247
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    11447599858279993
  ]

abbrev PositiveTerm := Fin 3
abbrev NegativeTerm := Fin 1
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
noncomputable def positiveFloor : ℝ := 17551441197 / 200000000000
noncomputable def negativeCeiling : ℝ := 30491968541 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 107914616393968057136962783412224, coefficient := 107914616393968057136962783412224 }, { argument := 107914619794071924803107337273344, coefficient := 107914619794071924803107337273344 }, { argument := 2727519418800589922015838732288, coefficient := 2727519418800589922015838732288 }, { argument := 221284257902340294898768253288448, coefficient := (-221284257902340294898768253288448) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk12
