import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 1, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 24661472144719524630623569313792
def positiveArguments : Array ℕ := #[
    1, 466853, 4077587, 4077597, 466843, 103859
  ]
def positiveCoefficients : Array ℕ := #[
    633825300114114700748351602688, 4409301919254284953899237376, 154046881438279904143832252416, 154047259227598533715449348096, 4409207471924627560994963456, 1961841042177433928997011456
  ]
def positiveScales : Array ℕ := #[
    0, 18, 21, 21, 18, 16
  ]
def negativeArguments : Array ℕ := #[
    39344800907, 959398043835, 3837530728197, 78681115897, 5399075805, 268393026341,
    2926953041091, 268207264953, 10578269093, 687973178539, 67035223162509, 134068268014995,
    2751624376999, 268393026341, 418653080843, 18220973829847, 6694484650579, 65648274847,
    39344800907, 687973178539, 687974849687, 39343917297, 687974849687, 67035387593853,
    134068596873083, 2751631060271, 2926953041091, 18220973829847, 396964830030045, 72837656603847,
    89527576523, 959398043835, 67035223162509, 67035387593853, 14990273655, 39343917297,
    14990273655, 3837448610797, 78679348017, 268207264953, 6694484650579, 72837656603847,
    3345264823147, 262411271511, 3837530728197, 134068268014995, 134068596873083, 3837448610797,
    10578269093, 65648274847, 89527576523, 262411271511, 1294962661, 78681115897,
    2751624376999, 2751631060271, 78679348017, 1
  ]
def negativeCoefficients : Array ℕ := #[
    22149153837966444130729984, 1080186168178822196798423040, 1080168872345677335449567232, 22146765264676500570898432, 3039409472942882590556160, 75545920838635457343389696,
    823864039074272979185565696, 75493633656274418210439168, 2977518046591227168555008, 774588937627284028927246336, 37737475756921696853119991808, 37736862617158704339584286720,
    774513407432266850284601344, 75545920838635457343389696, 1885445858882044937401008128, 20514992737606627146782998528, 1884329911111568094945869824, 73913386534616276326678528,
    22149153837966444130729984, 774588937627284028927246336, 774590819172661549164658688, 22148656409758101525233664, 774590819172661549164658688, 37737568323539142656850395136,
    37736955182481365250445672448, 774515288606097401263947776, 823864039074272979185565696, 20514992737606627146782998528, 223471332575312867807503319040, 20501977696226593524135493632,
    806392720536732731824930816, 1080186168178822196798423040, 37737475756921696853119991808, 37737568323539142656850395136, 1080163053549436209809326080, 22148656409758101525233664,
    1080163053549436209809326080, 1080145758352424795826552832, 22146267650694673336369152, 75493633656274418210439168, 1884329911111568094945869824, 20501977696226593524135493632,
    1883216676372557175260708864, 73862206537172353302921216, 1080168872345677335449567232, 37736862617158704339584286720, 37736955182481365250445672448, 1080145758352424795826552832,
    2977518046591227168555008, 73913386534616276326678528, 806392720536732731824930816, 73862206537172353302921216, 2915996678769152966524928, 22146765264676500570898432,
    774513407432266850284601344, 774515288606097401263947776, 22146267650694673336369152, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    35, 39, 41, 36, 32, 37,
    41, 37, 33, 39, 45, 46,
    41, 37, 38, 44, 42, 35,
    35, 39, 39, 35, 39, 45,
    46, 41, 41, 44, 48, 46,
    36, 39, 45, 45, 33, 35,
    33, 41, 36, 37, 42, 46,
    41, 37, 41, 46, 46, 41,
    33, 35, 36, 37, 30, 36,
    41, 41, 36, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 18832608828243331, 21959284227392843, 21959287765498231, 18832577925357621, 16664266714139578
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    35195453956874625, 39803338542411224, 41803315441936914, 36195298367695606, 32330065326881937, 37965556243748196,
    41412536738536262, 37964557373237129, 33300384529516655, 39323561364585084, 45929984589182751, 46929961148796846,
    41323420680480871, 37965556243748196, 38606964285638615, 44050665300356596, 42606110138092493, 35934038056243800,
    35195453956874625, 39323561364585084, 39323564869015314, 35195421556301983, 39323564869015314, 45929988127979413,
    46929964687601506, 41323424184560767, 41412536738536262, 44050665300356596, 48496004522721351, 46049749740963130,
    36381613082480487, 39803338542411224, 45929984589182751, 45929988127979413, 33803307670215821, 35195421556301983,
    33803307670215821, 41803284570096826, 36195265951526442, 37964557373237129, 42606110138092493, 46049749740963130,
    41605257562949994, 37933038741811272, 41803315441936914, 46929961148796846, 46929964687601506, 41803284570096826,
    33300384529516655, 35934038056243800, 36381613082480487, 37933038741811272, 30270263353777047, 36195298367695606,
    41323420680480871, 41323424184560767, 36195265951526442, 0
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 58
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
noncomputable def positiveFloor : ℝ := 10478707 / 125000000000
noncomputable def negativeCeiling : ℝ := 356386111 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 22149153837966444130729984, coefficient := (-22149153837966444130729984) }, { argument := 1080186168178822196798423040, coefficient := (-1080186168178822196798423040) }, { argument := 1080168872345677335449567232, coefficient := (-1080168872345677335449567232) }, { argument := 22146765264676500570898432, coefficient := (-22146765264676500570898432) }, { argument := 3039409472942882590556160, coefficient := (-3039409472942882590556160) }, { argument := 75545920838635457343389696, coefficient := (-75545920838635457343389696) }, { argument := 823864039074272979185565696, coefficient := (-823864039074272979185565696) }, { argument := 75493633656274418210439168, coefficient := (-75493633656274418210439168) }, { argument := 2977518046591227168555008, coefficient := (-2977518046591227168555008) }, { argument := 774588937627284028927246336, coefficient := (-774588937627284028927246336) }, { argument := 37737475756921696853119991808, coefficient := (-37737475756921696853119991808) }, { argument := 37736862617158704339584286720, coefficient := (-37736862617158704339584286720) }, { argument := 774513407432266850284601344, coefficient := (-774513407432266850284601344) }, { argument := 75545920838635457343389696, coefficient := (-75545920838635457343389696) }, { argument := 1885445858882044937401008128, coefficient := (-1885445858882044937401008128) }, { argument := 20514992737606627146782998528, coefficient := (-20514992737606627146782998528) }, { argument := 1884329911111568094945869824, coefficient := (-1884329911111568094945869824) }, { argument := 73913386534616276326678528, coefficient := (-73913386534616276326678528) }, { argument := 22149153837966444130729984, coefficient := (-22149153837966444130729984) }, { argument := 774588937627284028927246336, coefficient := (-774588937627284028927246336) }, { argument := 774590819172661549164658688, coefficient := (-774590819172661549164658688) }, { argument := 22148656409758101525233664, coefficient := (-22148656409758101525233664) }, { argument := 774590819172661549164658688, coefficient := (-774590819172661549164658688) }, { argument := 37737568323539142656850395136, coefficient := (-37737568323539142656850395136) }, { argument := 37736955182481365250445672448, coefficient := (-37736955182481365250445672448) }, { argument := 774515288606097401263947776, coefficient := (-774515288606097401263947776) }, { argument := 823864039074272979185565696, coefficient := (-823864039074272979185565696) }, { argument := 20514992737606627146782998528, coefficient := (-20514992737606627146782998528) }, { argument := 223471332575312867807503319040, coefficient := (-223471332575312867807503319040) }, { argument := 20501977696226593524135493632, coefficient := (-20501977696226593524135493632) }, { argument := 806392720536732731824930816, coefficient := (-806392720536732731824930816) }, { argument := 1080186168178822196798423040, coefficient := (-1080186168178822196798423040) }, { argument := 37737475756921696853119991808, coefficient := (-37737475756921696853119991808) }, { argument := 37737568323539142656850395136, coefficient := (-37737568323539142656850395136) }, { argument := 1080163053549436209809326080, coefficient := (-1080163053549436209809326080) }, { argument := 22148656409758101525233664, coefficient := (-22148656409758101525233664) }, { argument := 1080163053549436209809326080, coefficient := (-1080163053549436209809326080) }, { argument := 1080145758352424795826552832, coefficient := (-1080145758352424795826552832) }, { argument := 22146267650694673336369152, coefficient := (-22146267650694673336369152) }, { argument := 75493633656274418210439168, coefficient := (-75493633656274418210439168) }, { argument := 1884329911111568094945869824, coefficient := (-1884329911111568094945869824) }, { argument := 20501977696226593524135493632, coefficient := (-20501977696226593524135493632) }, { argument := 1883216676372557175260708864, coefficient := (-1883216676372557175260708864) }, { argument := 73862206537172353302921216, coefficient := (-73862206537172353302921216) }, { argument := 1080168872345677335449567232, coefficient := (-1080168872345677335449567232) }, { argument := 37736862617158704339584286720, coefficient := (-37736862617158704339584286720) }, { argument := 37736955182481365250445672448, coefficient := (-37736955182481365250445672448) }, { argument := 1080145758352424795826552832, coefficient := (-1080145758352424795826552832) }, { argument := 2977518046591227168555008, coefficient := (-2977518046591227168555008) }, { argument := 73913386534616276326678528, coefficient := (-73913386534616276326678528) }, { argument := 806392720536732731824930816, coefficient := (-806392720536732731824930816) }, { argument := 73862206537172353302921216, coefficient := (-73862206537172353302921216) }, { argument := 2915996678769152966524928, coefficient := (-2915996678769152966524928) }, { argument := 22146765264676500570898432, coefficient := (-22146765264676500570898432) }, { argument := 774513407432266850284601344, coefficient := (-774513407432266850284601344) }, { argument := 774515288606097401263947776, coefficient := (-774515288606097401263947776) }, { argument := 22146267650694673336369152, coefficient := (-22146267650694673336369152) }, { argument := 633825300114114700748351602688, coefficient := 633825300114114700748351602688 }, { argument := 4409301919254284953899237376, coefficient := 4409301919254284953899237376 }, { argument := 154046881438279904143832252416, coefficient := 154046881438279904143832252416 }, { argument := 154047259227598533715449348096, coefficient := 154047259227598533715449348096 }, { argument := 4409207471924627560994963456, coefficient := 4409207471924627560994963456 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 1961841042177433928997011456, coefficient := 1961841042177433928997011456 }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-24380656798465704439052675055616)
def positiveArguments : Array ℕ := #[
    5174149, 56352797, 5170899, 203301, 42179, 8219967,
    16439667, 337399
  ]
def positiveCoefficients : Array ℕ := #[
    48868455629946983825599889408, 532237119537514188378864615424, 48837760247808331131710865408, 1920123656667763483179220992, 3186955134095340247495737344, 155270786604378195833156272128,
    155268264860676343442612158464, 3186643457907470850911633408
  ]
def positiveScales : Array ℕ := #[
    22, 25, 22, 17, 15, 22,
    23, 18
  ]
def negativeArguments : Array ℕ := #[
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    633825300114114700748351602688, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    22302890169242834, 25747983882721439, 22301983695142928, 17633257785985998, 15364237270979232, 22970701170469661,
    23970677739554537, 18364096172137041
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 280620353 / 1000000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 48868455629946983825599889408, coefficient := 48868455629946983825599889408 }, { argument := 532237119537514188378864615424, coefficient := 532237119537514188378864615424 }, { argument := 48837760247808331131710865408, coefficient := 48837760247808331131710865408 }, { argument := 1920123656667763483179220992, coefficient := 1920123656667763483179220992 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 3186955134095340247495737344, coefficient := 3186955134095340247495737344 }, { argument := 155270786604378195833156272128, coefficient := 155270786604378195833156272128 }, { argument := 155268264860676343442612158464, coefficient := 155268264860676343442612158464 }, { argument := 3186643457907470850911633408, coefficient := 3186643457907470850911633408 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk1
