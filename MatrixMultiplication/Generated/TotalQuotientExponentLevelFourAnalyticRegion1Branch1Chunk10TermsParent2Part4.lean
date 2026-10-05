import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 10, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10

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
def constantNumerator : ℤ := (-1016821898327773897629436234170368)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    9523168353, 9523166111, 10418561059, 10521, 273, 37514191399,
    16947, 5209325275, 16947, 17661, 10521, 525,
    18551408775, 18551404409, 93, 2928278955, 57109322865, 114218603835,
    366036615, 318799160367, 277053, 7189, 1147736442947, 446271,
    159400765895, 446271, 465073, 277053, 13825, 18545117319,
    18545112953, 10418195491, 277053, 7189, 37505981351, 446271,
    5209134875, 446271, 465073, 277053, 13825, 582817483785,
    582817346551, 939, 18545117319, 18545112953, 1911, 38661964921245,
    10521, 273, 141198381609639, 16947, 9665035101423, 16947,
    17661, 10521, 525, 557849821315177, 557849789857687, 229227,
    1504051377, 1504051023, 285, 93
  ]
def negativeCoefficients : Array ℕ := #[
    87835724689320550631655604224, 87835704010520444003248242688, 24023566183961170017851015168, 99368035532543074586591232, 5156824199293652573356032, 86501835983688635407136718848,
    160059889570383754873012224, 24023772536157907560536473600, 160059889570383754873012224, 166803428907921608238170112, 99368035532543074586591232, 4958484807013127474380800,
    85553272469798655662594457600, 85553252335177499208618868736, 3597763239173136423925579776, 3376075778707165548726190080, 131685132889188017684065812480, 131685084587541582180211752960,
    3376091879255977383344209920, 735100815275442276776106000384, 2616691602356967630780235776, 135796370581399517765042176, 2646500053389131643870766956544, 4214910425353438878322655232,
    735106283404588715341858734080, 4214910425353438878322655232, 4392490294575269016938479616, 2616691602356967630780235776, 130573433251345690158694400, 85524258250127904562401509376,
    85524238115506748108425920512, 768727143729407289157771853824, 2616691602356967630780235776, 135796370581399517765042176, 2767452956860880849201071652864, 4214910425353438878322655232,
    768732623076479967548145664000, 4214910425353438878322655232, 4392490294575269016938479616, 2616691602356967630780235776, 130573433251345690158694400, 2687771241266315360939425136640,
    2687770608386196308075273519104, 72651606055560754883142352896, 85524258250127904562401509376, 85524238115506748108425920512, 73928231721073803291632074752, 87059005406365084865538293760,
    99368035532543074586591232, 5156824199293652573356032, 317950489401243647798748905472, 160059889570383754873012224, 87054896962582773628315631616, 160059889570383754873012224,
    166803428907921608238170112, 99368035532543074586591232, 4958484807013127474380800, 157020765462733057127310426112, 157020756608236792001616412672, 8659951214150081307199143936,
    110979403300917762424389500928, 110979377180328154051664412672, 88203227799083344586562600960, 3597763239173136423925579776
  ]
def negativeScales : Array ℕ := #[
    33, 33, 33, 13, 8, 35,
    14, 32, 14, 14, 13, 9,
    34, 34, 6, 31, 35, 36,
    28, 38, 18, 12, 40, 18,
    37, 18, 18, 18, 13, 34,
    34, 33, 18, 12, 35, 18,
    32, 18, 18, 18, 13, 39,
    39, 9, 34, 34, 10, 45,
    13, 8, 47, 14, 43, 14,
    14, 13, 9, 48, 48, 17,
    30, 30, 8, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33148794491248197, 33148794151600452, 33278436984993259, 13360984215973970, 8092757140919853, 35126717410826177,
    14048742286056541, 32278449377075686, 14048742286056541, 14108279413033905, 13360984215973970, 9036173612553486,
    34110809696664923, 34110809357132365, 6539158811108986, 31447405848805486, 35733007227947319, 36733006698771722,
    28447412729020287, 38213856873415719, 18079802463429916, 12811575389192290, 40061928529697848, 18767560533841008,
    37213867605023272, 18767560533841008, 18827097661601281, 18079802463429916, 13754991860260137, 34110320343433562,
    34110320003785816, 33278386362609733, 18079802463429916, 12811575389192290, 35126401639876893, 18767560533841008,
    32278396645840578, 18767560533841008, 18827097661601281, 18079802463429916, 13754991860260137, 39084253200833232,
    39084252861126823, 9874981350423323, 34110320343433562, 34110320003785816, 10900112067353854, 45135980195195011,
    13360984215973970, 8092757140919853, 47004716881216807, 14048742286056541, 43135912110666539, 14048742286056541,
    14108279413033905, 13360984215973970, 9036173612553486, 48986870134159100, 48986870052804624, 17806417460244627,
    30486206702968167, 30486206363409219, 8154818109052105, 6539158811108986
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
noncomputable def negativeCeiling : ℝ := 7279835267 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 87835724689320550631655604224, coefficient := (-87835724689320550631655604224) }, { argument := 87835704010520444003248242688, coefficient := (-87835704010520444003248242688) }, { argument := 24023566183961170017851015168, coefficient := (-24023566183961170017851015168) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 5156824199293652573356032, coefficient := (-5156824199293652573356032) }, { argument := 86501835983688635407136718848, coefficient := (-86501835983688635407136718848) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 24023772536157907560536473600, coefficient := (-24023772536157907560536473600) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 166803428907921608238170112, coefficient := (-166803428907921608238170112) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 85553272469798655662594457600, coefficient := (-85553272469798655662594457600) }, { argument := 85553252335177499208618868736, coefficient := (-85553252335177499208618868736) }, { argument := 3597763239173136423925579776, coefficient := (-3597763239173136423925579776) }, { argument := 3376075778707165548726190080, coefficient := (-3376075778707165548726190080) }, { argument := 131685132889188017684065812480, coefficient := (-131685132889188017684065812480) }, { argument := 131685084587541582180211752960, coefficient := (-131685084587541582180211752960) }, { argument := 3376091879255977383344209920, coefficient := (-3376091879255977383344209920) }, { argument := 735100815275442276776106000384, coefficient := (-735100815275442276776106000384) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 135796370581399517765042176, coefficient := (-135796370581399517765042176) }, { argument := 2646500053389131643870766956544, coefficient := (-2646500053389131643870766956544) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 735106283404588715341858734080, coefficient := (-735106283404588715341858734080) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 4392490294575269016938479616, coefficient := (-4392490294575269016938479616) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 130573433251345690158694400, coefficient := (-130573433251345690158694400) }, { argument := 85524258250127904562401509376, coefficient := (-85524258250127904562401509376) }, { argument := 85524238115506748108425920512, coefficient := (-85524238115506748108425920512) }, { argument := 768727143729407289157771853824, coefficient := (-768727143729407289157771853824) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 135796370581399517765042176, coefficient := (-135796370581399517765042176) }, { argument := 2767452956860880849201071652864, coefficient := (-2767452956860880849201071652864) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 768732623076479967548145664000, coefficient := (-768732623076479967548145664000) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 4392490294575269016938479616, coefficient := (-4392490294575269016938479616) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 130573433251345690158694400, coefficient := (-130573433251345690158694400) }, { argument := 2687771241266315360939425136640, coefficient := (-2687771241266315360939425136640) }, { argument := 2687770608386196308075273519104, coefficient := (-2687770608386196308075273519104) }, { argument := 72651606055560754883142352896, coefficient := (-72651606055560754883142352896) }, { argument := 85524258250127904562401509376, coefficient := (-85524258250127904562401509376) }, { argument := 85524238115506748108425920512, coefficient := (-85524238115506748108425920512) }, { argument := 73928231721073803291632074752, coefficient := (-73928231721073803291632074752) }, { argument := 87059005406365084865538293760, coefficient := (-87059005406365084865538293760) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 5156824199293652573356032, coefficient := (-5156824199293652573356032) }, { argument := 317950489401243647798748905472, coefficient := (-317950489401243647798748905472) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 87054896962582773628315631616, coefficient := (-87054896962582773628315631616) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 166803428907921608238170112, coefficient := (-166803428907921608238170112) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 157020765462733057127310426112, coefficient := (-157020765462733057127310426112) }, { argument := 157020756608236792001616412672, coefficient := (-157020756608236792001616412672) }, { argument := 8659951214150081307199143936, coefficient := (-8659951214150081307199143936) }, { argument := 110979403300917762424389500928, coefficient := (-110979403300917762424389500928) }, { argument := 110979377180328154051664412672, coefficient := (-110979377180328154051664412672) }, { argument := 88203227799083344586562600960, coefficient := (-88203227799083344586562600960) }, { argument := 3597763239173136423925579776, coefficient := (-3597763239173136423925579776) }] }

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
def constantNumerator : ℤ := 424085132775656962658048609148207104
def positiveArguments : Array ℕ := #[
    55773, 21, 3507, 91, 3773, 5649,
    175, 5649, 5887, 3507, 175, 12183,
    13755, 5895, 155235, 13755, 5895, 13755,
    13755, 570243, 3537, 155235, 570243, 12183,
    13755, 3537, 13755, 8325, 241425, 213675,
    13875, 8325, 13875, 424575, 13875, 8325,
    6801525, 435675, 241425, 424575, 13875, 435675,
    13875, 424575, 13875, 8325, 11045, 8225,
    8695, 705, 151105, 273305, 8225, 151105,
    4465, 4465, 8695, 8695, 273305, 8695,
    11045
  ]
def positiveCoefficients : Array ℕ := #[
    4418792307908064900604726742089728, 6499185206248246443220402176, 135670491180432144502225895424, 7040783973435600313488769024, 145960867756991868037324865536, 218535102560097286653286023168,
    6769984589841923378354585600, 218535102560097286653286023168, 227742281602282302447848259584, 135670491180432144502225895424, 6769984589841923378354585600, 471306984331680871534250950656,
    532120788761575177538670428160, 456103533224207295033146081280, 6005363187452062717936423403520, 532120788761575177538670428160, 456103533224207295033146081280, 532120788761575177538670428160,
    532120788761575177538670428160, 22060207556944159503103165464576, 547324239869048754039775297536, 6005363187452062717936423403520, 22060207556944159503103165464576, 471306984331680871534250950656,
    532120788761575177538670428160, 547324239869048754039775297536, 532120788761575177538670428160, 322057838345337212141725286400, 4669838656007389576055016652800, 8266151184196988444970949017600,
    268381531954447676784771072000, 5152925413525395394267604582400, 268381531954447676784771072000, 8212474877806098909613994803200, 8588209022542325657112674304000, 5152925413525395394267604582400,
    131560626964070251159894779494400, 8427180103369657051041811660800, 4669838656007389576055016652800, 8212474877806098909613994803200, 268381531954447676784771072000, 8427180103369657051041811660800,
    268381531954447676784771072000, 8212474877806098909613994803200, 8588209022542325657112674304000, 322057838345337212141725286400, 427282741684594535508150845440, 318189275722570398782665523200,
    336371520049574421570246410240, 436373863848096546901941288960, 5845591551131793326207255183360, 10572975076152839250978285813760, 318189275722570398782665523200, 5845591551131793326207255183360,
    345462642213076432964036853760, 345462642213076432964036853760, 336371520049574421570246410240, 336371520049574421570246410240, 10572975076152839250978285813760, 336371520049574421570246410240,
    427282741684594535508150845440
  ]
def positiveScales : Array ℕ := #[
    15, 4, 11, 6, 11, 12,
    7, 12, 12, 11, 7, 13,
    13, 12, 17, 13, 12, 13,
    13, 19, 11, 17, 19, 13,
    13, 11, 13, 13, 17, 17,
    13, 13, 13, 18, 13, 13,
    22, 18, 17, 18, 13, 18,
    13, 18, 13, 13, 13, 13,
    13, 9, 17, 18, 13, 17,
    12, 12, 13, 13, 18, 13,
    13
  ]
def negativeArguments : Array ℕ := #[
    7, 393, 2775
  ]
def negativeCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 62273335736211769348525544964096, 219858150977083536822084462182400
  ]
def negativeScales : Array ℕ := #[
    2, 8, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    15767279254393674, 4392317422778759, 11776021715228447, 6507794640198673, 11881496384617007, 12463779785335379,
    7451211111832325, 12463779785335379, 12523316912312711, 11776021715228447, 7451211111832325, 13572581812645319,
    13747668519190317, 12525276097867086, 17244094345323071, 13747668519190317, 12525276097867086, 13747668519190317,
    13747668519190317, 19121217306325350, 11788310503669431, 17244094345323071, 19121217306325350, 13572581812645319,
    13747668519190317, 11788310503669431, 13747668519190317, 13023234556845986, 17881215551781447, 17705058596814672,
    13760200150994793, 13023234556845986, 13760200150994793, 18695659898813424, 13760200150994793, 13023234556845986,
    22697426824987439, 18732892805006900, 17881215551781447, 18695659898813424, 13760200150994793, 18732892805006900,
    13760200150994793, 18695659898813424, 13760200150994793, 13023234556845986, 13431105798242635, 13005799963509966,
    13085970312193949, 9461479447286151, 17205191873892946, 18060152328038218, 13005799963509966, 17205191873892946,
    12124444460008585, 12124444460008585, 13085970312193949, 13085970312193949, 18060152328038218, 13085970312193949,
    13431105798242635
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2807354922807594, 8618385502267938, 11438272056124861
  ]

abbrev PositiveTerm := Fin 61
abbrev NegativeTerm := Fin 3
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
noncomputable def positiveFloor : ℝ := 228463241037 / 250000000000
noncomputable def negativeCeiling : ℝ := 4596061579 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4418792307908064900604726742089728, coefficient := 4418792307908064900604726742089728 }, { argument := 6499185206248246443220402176, coefficient := 6499185206248246443220402176 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 145960867756991868037324865536, coefficient := 145960867756991868037324865536 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 6769984589841923378354585600, coefficient := 6769984589841923378354585600 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 227742281602282302447848259584, coefficient := 227742281602282302447848259584 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 6769984589841923378354585600, coefficient := 6769984589841923378354585600 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 471306984331680871534250950656, coefficient := 471306984331680871534250950656 }, { argument := 532120788761575177538670428160, coefficient := 532120788761575177538670428160 }, { argument := 456103533224207295033146081280, coefficient := 456103533224207295033146081280 }, { argument := 6005363187452062717936423403520, coefficient := 6005363187452062717936423403520 }, { argument := 532120788761575177538670428160, coefficient := 532120788761575177538670428160 }, { argument := 456103533224207295033146081280, coefficient := 456103533224207295033146081280 }, { argument := 532120788761575177538670428160, coefficient := 532120788761575177538670428160 }, { argument := 532120788761575177538670428160, coefficient := 532120788761575177538670428160 }, { argument := 22060207556944159503103165464576, coefficient := 22060207556944159503103165464576 }, { argument := 547324239869048754039775297536, coefficient := 547324239869048754039775297536 }, { argument := 6005363187452062717936423403520, coefficient := 6005363187452062717936423403520 }, { argument := 22060207556944159503103165464576, coefficient := 22060207556944159503103165464576 }, { argument := 471306984331680871534250950656, coefficient := 471306984331680871534250950656 }, { argument := 532120788761575177538670428160, coefficient := 532120788761575177538670428160 }, { argument := 547324239869048754039775297536, coefficient := 547324239869048754039775297536 }, { argument := 532120788761575177538670428160, coefficient := 532120788761575177538670428160 }, { argument := 62273335736211769348525544964096, coefficient := (-62273335736211769348525544964096) }, { argument := 322057838345337212141725286400, coefficient := 322057838345337212141725286400 }, { argument := 4669838656007389576055016652800, coefficient := 4669838656007389576055016652800 }, { argument := 8266151184196988444970949017600, coefficient := 8266151184196988444970949017600 }, { argument := 268381531954447676784771072000, coefficient := 268381531954447676784771072000 }, { argument := 5152925413525395394267604582400, coefficient := 5152925413525395394267604582400 }, { argument := 268381531954447676784771072000, coefficient := 268381531954447676784771072000 }, { argument := 8212474877806098909613994803200, coefficient := 8212474877806098909613994803200 }, { argument := 8588209022542325657112674304000, coefficient := 8588209022542325657112674304000 }, { argument := 5152925413525395394267604582400, coefficient := 5152925413525395394267604582400 }, { argument := 131560626964070251159894779494400, coefficient := 131560626964070251159894779494400 }, { argument := 8427180103369657051041811660800, coefficient := 8427180103369657051041811660800 }, { argument := 4669838656007389576055016652800, coefficient := 4669838656007389576055016652800 }, { argument := 8212474877806098909613994803200, coefficient := 8212474877806098909613994803200 }, { argument := 268381531954447676784771072000, coefficient := 268381531954447676784771072000 }, { argument := 8427180103369657051041811660800, coefficient := 8427180103369657051041811660800 }, { argument := 268381531954447676784771072000, coefficient := 268381531954447676784771072000 }, { argument := 8212474877806098909613994803200, coefficient := 8212474877806098909613994803200 }, { argument := 8588209022542325657112674304000, coefficient := 8588209022542325657112674304000 }, { argument := 322057838345337212141725286400, coefficient := 322057838345337212141725286400 }, { argument := 219858150977083536822084462182400, coefficient := (-219858150977083536822084462182400) }, { argument := 427282741684594535508150845440, coefficient := 427282741684594535508150845440 }, { argument := 318189275722570398782665523200, coefficient := 318189275722570398782665523200 }, { argument := 336371520049574421570246410240, coefficient := 336371520049574421570246410240 }, { argument := 436373863848096546901941288960, coefficient := 436373863848096546901941288960 }, { argument := 5845591551131793326207255183360, coefficient := 5845591551131793326207255183360 }, { argument := 10572975076152839250978285813760, coefficient := 10572975076152839250978285813760 }, { argument := 318189275722570398782665523200, coefficient := 318189275722570398782665523200 }, { argument := 5845591551131793326207255183360, coefficient := 5845591551131793326207255183360 }, { argument := 345462642213076432964036853760, coefficient := 345462642213076432964036853760 }, { argument := 345462642213076432964036853760, coefficient := 345462642213076432964036853760 }, { argument := 336371520049574421570246410240, coefficient := 336371520049574421570246410240 }, { argument := 336371520049574421570246410240, coefficient := 336371520049574421570246410240 }, { argument := 10572975076152839250978285813760, coefficient := 10572975076152839250978285813760 }, { argument := 336371520049574421570246410240, coefficient := 336371520049574421570246410240 }, { argument := 427282741684594535508150845440, coefficient := 427282741684594535508150845440 }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
