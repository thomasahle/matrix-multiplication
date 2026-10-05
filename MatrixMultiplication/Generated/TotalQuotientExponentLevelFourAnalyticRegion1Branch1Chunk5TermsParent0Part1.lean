import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4728391901706058995370216275312640)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    570884499, 165672146606303, 7623844451903265, 6136362347, 497542893, 106640026733,
    192880794853, 7623844452223265, 106640026733, 3151104989, 3151104989, 6136362347,
    6136362347, 192880794853, 6136362347, 165672146286303, 497542893, 3255,
    78855, 59745, 33285, 3255, 33285, 66465,
    3255, 78855, 3255, 17833875, 3127894125, 781973625,
    4458375, 15348005693463, 388013064478419, 81567137729, 7509532144224925, 3177940431,
    5296567385, 162074961981, 5296567385, 3177940431, 2596377332127, 166312215889,
    388013078348499, 162074961981, 5296567385, 166312215889, 5296567385, 162074961981,
    5296567385, 15348005693463, 29723125, 5213156875, 1303289375, 7430625,
    7374285, 4750829415, 50527068687, 2375421867, 7374285, 4452503670313,
    3255, 43638984812725, 36735, 3255
  ]
def negativeCoefficients : Array ℕ := #[
    21061920497401792891629600768, 373060508860908187139014918144, 17167371516361083784067253534720, 226391811517313370301350805504, 293697485211649777688238882816, 3934322562314391813615366701056,
    7116045318773931071904621264896, 17167371517081659724446532894720, 3934322562314391813615366701056, 232510509125889407336522448896, 232510509125889407336522448896, 226391811517313370301350805504,
    226391811517313370301350805504, 7116045318773931071904621264896, 226391811517313370301350805504, 373060508140332246759735558144, 293697485211649777688238882816, 15371302901740695170580480,
    372382209006685873325998080, 282137785519046953292267520, 314367936764632281875742720, 15371302901740695170580480, 314367936764632281875742720, 313872088283930969128304640,
    15371302901740695170580480, 372382209006685873325998080, 15371302901740695170580480, 657953855935053859651584000, 115398924827069346912141312000, 115398938662127402194305024000,
    657940020876998577487872000, 17280318180490054463926566912, 1747455492599892046286709325824, 188081014313985190575638315008, 16909963083229067027704866406400, 117245307624302456462735572992,
    6106526438765752940767477760, 186859709026232039987484819456, 195408846040504094104559288320, 117245307624302456462735572992, 2993419260282972091564217597952, 191744930177244642340098801664,
    1747455555065179165885678485504, 186859709026232039987484819456, 6106526438765752940767477760, 191744930177244642340098801664, 6106526438765752940767477760, 186859709026232039987484819456,
    195408846040504094104559288320, 17280318180490054463926566912, 34268429996617388523520000, 6010360668076528485007360000, 6010361388652468864286720000, 34267709420677009244160000,
    68015774060797620419297280, 21909333589089066495938396160, 233014976215958176347400962048, 21909399623821164357705793536, 68015774060797620419297280, 1253268366905462035817955328,
    15371302901740695170580480, 49133128935353761042687590400, 173476132748216416925122560, 15371302901740695170580480
  ]
def negativeScales : Array ℕ := #[
    29, 47, 52, 32, 28, 36,
    37, 52, 36, 31, 31, 32,
    32, 37, 32, 47, 28, 11,
    16, 15, 15, 11, 15, 16,
    11, 16, 11, 24, 31, 29,
    22, 43, 48, 36, 52, 31,
    32, 37, 32, 31, 41, 37,
    48, 37, 32, 37, 32, 37,
    32, 43, 24, 32, 30, 22,
    22, 32, 35, 31, 22, 42,
    11, 45, 15, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29088623649038514, 47235324400320373, 52759440108055061, 32514736529263259, 28890245668018047, 36633958090975906,
    37488918545107274, 52759440108115616, 36633958090975906, 31553210677078920, 31553210677078920, 32514736529263259,
    32514736529263259, 37488918545107274, 32514736529263259, 47235324397533770, 28890245668018047, 11668441828086828,
    16266914615180395, 15866530362339582, 15022584547805530, 11668441828086828, 15022584547805530, 16020307207094464,
    11668441828086828, 16266914615180395, 11668441828086828, 24088116874515161, 31542544534176532, 29542544707139742,
    22088086538072384, 43803116439456507, 48463098557487393, 36247268976259297, 52737644451829482, 31565444936287661,
    32302410530451758, 37237870278257047, 32302410530451758, 31565444936287661, 41239637204431235, 37275103184456023,
    48463098609058582, 37237870278257047, 32302410530451758, 37275103184456023, 32302410530451758, 37237870278257047,
    32302410530451758, 43803116439456507, 24825082469749558, 32279510128341679, 30279510301304889, 22825052133306142,
    22814071744702316, 32145532259734847, 35556337433731201, 31145536608011191, 22814071744702316, 42017753939226266,
    11668441828086828, 45310682773724205, 15164867654172497, 11668441828086828
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
noncomputable def negativeCeiling : ℝ := 48129085353 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 21061920497401792891629600768, coefficient := (-21061920497401792891629600768) }, { argument := 373060508860908187139014918144, coefficient := (-373060508860908187139014918144) }, { argument := 17167371516361083784067253534720, coefficient := (-17167371516361083784067253534720) }, { argument := 226391811517313370301350805504, coefficient := (-226391811517313370301350805504) }, { argument := 293697485211649777688238882816, coefficient := (-293697485211649777688238882816) }, { argument := 3934322562314391813615366701056, coefficient := (-3934322562314391813615366701056) }, { argument := 7116045318773931071904621264896, coefficient := (-7116045318773931071904621264896) }, { argument := 17167371517081659724446532894720, coefficient := (-17167371517081659724446532894720) }, { argument := 3934322562314391813615366701056, coefficient := (-3934322562314391813615366701056) }, { argument := 232510509125889407336522448896, coefficient := (-232510509125889407336522448896) }, { argument := 232510509125889407336522448896, coefficient := (-232510509125889407336522448896) }, { argument := 226391811517313370301350805504, coefficient := (-226391811517313370301350805504) }, { argument := 226391811517313370301350805504, coefficient := (-226391811517313370301350805504) }, { argument := 7116045318773931071904621264896, coefficient := (-7116045318773931071904621264896) }, { argument := 226391811517313370301350805504, coefficient := (-226391811517313370301350805504) }, { argument := 373060508140332246759735558144, coefficient := (-373060508140332246759735558144) }, { argument := 293697485211649777688238882816, coefficient := (-293697485211649777688238882816) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 282137785519046953292267520, coefficient := (-282137785519046953292267520) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 313872088283930969128304640, coefficient := (-313872088283930969128304640) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 657953855935053859651584000, coefficient := (-657953855935053859651584000) }, { argument := 115398924827069346912141312000, coefficient := (-115398924827069346912141312000) }, { argument := 115398938662127402194305024000, coefficient := (-115398938662127402194305024000) }, { argument := 657940020876998577487872000, coefficient := (-657940020876998577487872000) }, { argument := 17280318180490054463926566912, coefficient := (-17280318180490054463926566912) }, { argument := 1747455492599892046286709325824, coefficient := (-1747455492599892046286709325824) }, { argument := 188081014313985190575638315008, coefficient := (-188081014313985190575638315008) }, { argument := 16909963083229067027704866406400, coefficient := (-16909963083229067027704866406400) }, { argument := 117245307624302456462735572992, coefficient := (-117245307624302456462735572992) }, { argument := 6106526438765752940767477760, coefficient := (-6106526438765752940767477760) }, { argument := 186859709026232039987484819456, coefficient := (-186859709026232039987484819456) }, { argument := 195408846040504094104559288320, coefficient := (-195408846040504094104559288320) }, { argument := 117245307624302456462735572992, coefficient := (-117245307624302456462735572992) }, { argument := 2993419260282972091564217597952, coefficient := (-2993419260282972091564217597952) }, { argument := 191744930177244642340098801664, coefficient := (-191744930177244642340098801664) }, { argument := 1747455555065179165885678485504, coefficient := (-1747455555065179165885678485504) }, { argument := 186859709026232039987484819456, coefficient := (-186859709026232039987484819456) }, { argument := 6106526438765752940767477760, coefficient := (-6106526438765752940767477760) }, { argument := 191744930177244642340098801664, coefficient := (-191744930177244642340098801664) }, { argument := 6106526438765752940767477760, coefficient := (-6106526438765752940767477760) }, { argument := 186859709026232039987484819456, coefficient := (-186859709026232039987484819456) }, { argument := 195408846040504094104559288320, coefficient := (-195408846040504094104559288320) }, { argument := 17280318180490054463926566912, coefficient := (-17280318180490054463926566912) }, { argument := 34268429996617388523520000, coefficient := (-34268429996617388523520000) }, { argument := 6010360668076528485007360000, coefficient := (-6010360668076528485007360000) }, { argument := 6010361388652468864286720000, coefficient := (-6010361388652468864286720000) }, { argument := 34267709420677009244160000, coefficient := (-34267709420677009244160000) }, { argument := 68015774060797620419297280, coefficient := (-68015774060797620419297280) }, { argument := 21909333589089066495938396160, coefficient := (-21909333589089066495938396160) }, { argument := 233014976215958176347400962048, coefficient := (-233014976215958176347400962048) }, { argument := 21909399623821164357705793536, coefficient := (-21909399623821164357705793536) }, { argument := 68015774060797620419297280, coefficient := (-68015774060797620419297280) }, { argument := 1253268366905462035817955328, coefficient := (-1253268366905462035817955328) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 49133128935353761042687590400, coefficient := (-49133128935353761042687590400) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }] }

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
def constantNumerator : ℤ := (-82468154417177468852812671614976)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    87277970518125, 3255, 3255, 134943, 837, 36735,
    134943, 4452530335273, 3255, 837, 3255, 3255,
    78855, 59745, 33285, 3255, 33285, 66465,
    3255, 78855, 3255, 134943, 3269103, 2476857,
    1379901, 134943, 1379901, 2755449, 134943, 3269103,
    134943, 909527625, 159522600375, 39880654875, 227377125, 837,
    20277, 15363, 8559, 837, 8559, 17091,
    837, 20277, 837, 29723125, 5213156875, 1303289375,
    7430625, 597915, 385202385, 4096789353, 192601773, 597915,
    36735, 889935, 674265, 375645, 36735, 375645,
    750105, 36735, 889935, 36735
  ]
def negativeCoefficients : Array ℕ := #[
    49133129437885110713057280000, 15371302901740695170580480, 15371302901740695170580480, 637250300297878534071779328, 15810482984647572175454208, 173476132748216416925122560,
    637250300297878534071779328, 1253275872424457026391769088, 15371302901740695170580480, 15810482984647572175454208, 15371302901740695170580480, 15371302901740695170580480,
    372382209006685873325998080, 282137785519046953292267520, 314367936764632281875742720, 15371302901740695170580480, 314367936764632281875742720, 313872088283930969128304640,
    15371302901740695170580480, 372382209006685873325998080, 15371302901740695170580480, 637250300297878534071779328, 15437902436248605777029234688, 11696626479661060835059433472,
    13032796464156612600048648192, 637250300297878534071779328, 13032796464156612600048648192, 13012240002856681034433429504, 637250300297878534071779328, 15437902436248605777029234688,
    637250300297878534071779328, 1048613957896492088819712000, 183917036443141771641225216000, 183917058492765547247173632000, 1048591908272716482871296000, 15810482984647572175454208,
    383021700692591183992455168, 290198865105305437672046592, 323349877815050347072192512, 15810482984647572175454208, 323349877815050347072192512, 322839862234900425389113344,
    15810482984647572175454208, 383021700692591183992455168, 15810482984647572175454208, 1096589759891756432752640000, 192331541378448911520235520000, 192331564436879003657175040000,
    1096566701461664295813120000, 88236679862656372435845120, 28422919250710140319055216640, 302289698874756553099330977792, 28423004917389618626212921344, 88236679862656372435845120,
    173476132748216416925122560, 4202599215932597713250549760, 3184126436572101330012733440, 3547866714915135752597667840, 173476132748216416925122560, 3547866714915135752597667840,
    3542270710632935223019438080, 173476132748216416925122560, 4202599215932597713250549760, 173476132748216416925122560
  ]
def negativeScales : Array ℕ := #[
    46, 11, 11, 17, 9, 15,
    17, 42, 11, 9, 11, 11,
    16, 15, 15, 11, 15, 16,
    11, 16, 11, 17, 21, 21,
    20, 17, 20, 21, 17, 21,
    17, 29, 37, 35, 27, 9,
    14, 13, 13, 9, 13, 14,
    9, 14, 9, 24, 32, 30,
    22, 19, 28, 31, 27, 19,
    15, 19, 19, 18, 15, 18,
    19, 15, 19, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    46310682788480022, 11668441828086828, 11668441828086828, 17041990615174776, 9709083812639846, 15164867654172497,
    17041990615174776, 42017762579149602, 11668441828086828, 9709083812639846, 11668441828086828, 11668441828086828,
    16266914615180395, 15866530362339582, 15022584547805530, 11668441828086828, 15022584547805530, 16020307207094464,
    11668441828086828, 16266914615180395, 11668441828086828, 17041990615174776, 21640463402318857, 21240079147094483,
    20396133334927314, 17041990615174776, 20396133334927314, 21393855994216248, 17041990615174776, 21640463402318857,
    17041990615174776, 29760542216769316, 37214969876146969, 35214970049110178, 27760511880326354, 9709083812639846,
    14307556599677741, 13907172349434197, 13063226532302876, 9709083812639846, 13063226532302876, 14060949191591810,
    9709083812639846, 14307556599677741, 9709083812639846, 24825082469749558, 32279510128341679, 30279510301304889,
    22825052133306142, 19189580878936148, 28521041394827593, 31931846576468521, 27521045743103937, 19189580878936148,
    15164867654172497, 19763340441600069, 19362956186092205, 18519010373925535, 15164867654172497, 18519010373925535,
    19516733033214433, 15164867654172497, 19763340441600069, 15164867654172497
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
noncomputable def negativeCeiling : ℝ := 99516119 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 49133129437885110713057280000, coefficient := (-49133129437885110713057280000) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 1253275872424457026391769088, coefficient := (-1253275872424457026391769088) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 282137785519046953292267520, coefficient := (-282137785519046953292267520) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 313872088283930969128304640, coefficient := (-313872088283930969128304640) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 15437902436248605777029234688, coefficient := (-15437902436248605777029234688) }, { argument := 11696626479661060835059433472, coefficient := (-11696626479661060835059433472) }, { argument := 13032796464156612600048648192, coefficient := (-13032796464156612600048648192) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 13032796464156612600048648192, coefficient := (-13032796464156612600048648192) }, { argument := 13012240002856681034433429504, coefficient := (-13012240002856681034433429504) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 15437902436248605777029234688, coefficient := (-15437902436248605777029234688) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 1048613957896492088819712000, coefficient := (-1048613957896492088819712000) }, { argument := 183917036443141771641225216000, coefficient := (-183917036443141771641225216000) }, { argument := 183917058492765547247173632000, coefficient := (-183917058492765547247173632000) }, { argument := 1048591908272716482871296000, coefficient := (-1048591908272716482871296000) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 383021700692591183992455168, coefficient := (-383021700692591183992455168) }, { argument := 290198865105305437672046592, coefficient := (-290198865105305437672046592) }, { argument := 323349877815050347072192512, coefficient := (-323349877815050347072192512) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 323349877815050347072192512, coefficient := (-323349877815050347072192512) }, { argument := 322839862234900425389113344, coefficient := (-322839862234900425389113344) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 383021700692591183992455168, coefficient := (-383021700692591183992455168) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 1096589759891756432752640000, coefficient := (-1096589759891756432752640000) }, { argument := 192331541378448911520235520000, coefficient := (-192331541378448911520235520000) }, { argument := 192331564436879003657175040000, coefficient := (-192331564436879003657175040000) }, { argument := 1096566701461664295813120000, coefficient := (-1096566701461664295813120000) }, { argument := 88236679862656372435845120, coefficient := (-88236679862656372435845120) }, { argument := 28422919250710140319055216640, coefficient := (-28422919250710140319055216640) }, { argument := 302289698874756553099330977792, coefficient := (-302289698874756553099330977792) }, { argument := 28423004917389618626212921344, coefficient := (-28423004917389618626212921344) }, { argument := 88236679862656372435845120, coefficient := (-88236679862656372435845120) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 4202599215932597713250549760, coefficient := (-4202599215932597713250549760) }, { argument := 3184126436572101330012733440, coefficient := (-3184126436572101330012733440) }, { argument := 3547866714915135752597667840, coefficient := (-3547866714915135752597667840) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 3547866714915135752597667840, coefficient := (-3547866714915135752597667840) }, { argument := 3542270710632935223019438080, coefficient := (-3542270710632935223019438080) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 4202599215932597713250549760, coefficient := (-4202599215932597713250549760) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5
