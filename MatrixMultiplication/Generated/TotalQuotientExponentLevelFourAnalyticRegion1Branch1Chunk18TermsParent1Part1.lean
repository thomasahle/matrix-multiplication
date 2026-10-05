import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-9822476575550391756815841676492800)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3690686455911, 7087259385, 64418092385733, 74156933565, 3284339715, 128836144310967,
    3284339715, 6395819445, 120829129515, 6395819445, 74156933565, 120829129515,
    461337492843, 6395819445, 6395819445, 7087259385, 2651735, 1708360965,
    18169137277, 854183057, 2651735, 12738845985, 498534228703, 498534228703,
    12738845985, 6400210543063, 10310335, 8542849, 738155281390567, 57443295,
    204806794049849, 230067761, 230067761, 164670779, 8542849, 98514454209145,
    1531642356571527, 4356944739, 11236331169, 9401828121, 263021874507, 382441000141995,
    9401828121, 8484576597, 4356944739, 4356944739, 8484576597, 263021874507,
    8484576597, 24628569772885, 11236331169, 17306825811581, 4154944751705763, 125683613069,
    135666435084245705, 39773295275, 4772795433, 125683613069, 249776294327, 39773295275,
    3854827778053, 246594430705, 16619788906355467, 125683613069
  ]
def negativeCoefficients : Array ℕ := #[
    265941986361313857829859229696, 32684215014772787863659479040, 9283625499657770383300337074176, 341988493691159170573412597760, 30292687086862583873635614720, 9283622584171558869311120474112,
    30292687086862583873635614720, 29495511110892515876960993280, 1114452014406155059351120773120, 29495511110892515876960993280, 341988493691159170573412597760, 1114452014406155059351120773120,
    265942958190051029159598096384, 29495511110892515876960993280, 29495511110892515876960993280, 32684215014772787863659479040, 97831753792596395708907520, 31513697506870480728427069440,
    335161425388915049937221189632, 31513792489155716258908340224, 97831753792596395708907520, 58747557919924366414907965440, 2299083332217106873731631808512, 2299083332217106873731631808512,
    58747557919924366414907965440, 57647971633662493285727338496, 190192111059210169860751360, 9849234322709098082074624, 207772240638257572603286781952, 264910440403899879448903680,
    57647987585365367110913490944, 265250069173648469037940736, 265250069173648469037940736, 189852482289461580271714304, 9849234322709098082074624, 55458707408364151651948298240,
    862237993290049670320094183424, 40185722271814129563690074112, 51818431350497167068968779776, 693732468692370236678439174144, 1212974301204494910777697763328, 861180572865344244912236789760,
    693732468692370236678439174144, 39128203264661126154119282688, 40185722271814129563690074112, 40185722271814129563690074112, 39128203264661126154119282688, 1212974301204494910777697763328,
    39128203264661126154119282688, 55458608825916573650234900480, 51818431350497167068968779776, 155886028552004547232349028352, 9356103817763536135639189684224, 2318453444542980100794827669504,
    76373413311511567768415591464960, 1467375597812012722022042828800, 88042535868720763321322569728, 2318453444542980100794827669504, 2303779688564859973574607241216, 1467375597812012722022042828800,
    35554510734985068254594097741824, 2274432176608619719134166384640, 9356109390704848052657485512704, 2318453444542980100794827669504
  ]
def negativeScales : Array ℕ := #[
    41, 32, 45, 36, 31, 46,
    31, 32, 36, 32, 36, 36,
    38, 32, 32, 32, 21, 30,
    34, 29, 21, 33, 38, 38,
    33, 42, 23, 23, 49, 25,
    47, 27, 27, 27, 23, 46,
    50, 32, 33, 33, 37, 48,
    33, 32, 32, 32, 32, 37,
    32, 44, 33, 43, 51, 36,
    56, 35, 32, 36, 37, 35,
    41, 37, 53, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    41747026316779472, 32722580704980114, 45872531174978377, 36109862537739541, 31612956213691642, 46872530721905559,
    31612956213691642, 32574482065871691, 36814177346475622, 32574482065871691, 36109862537739541, 36814177346475622,
    38747031588793732, 32574482065871691, 32574482065871691, 32722580704980114, 21338505176868039, 30669965692794070,
    34080770866753689, 29669970041070417, 21338505176868039, 33568515538312626, 38858901607375813, 38858901607375813,
    33568515538312626, 42541256503830241, 23297587873249950, 23026285851432555, 49390917667916319, 25775635170444446,
    47541256903036645, 27777483594852285, 27777483594852285, 27295009329148173, 23026285851432555, 46485400648317921,
    50444000885954314, 32020669669035017, 33387451999706644, 33130294160209516, 37936391839875979, 48442230526246870,
    33130294160209516, 32982195538994230, 32020669669035017, 32020669669035017, 32982195538994230, 37936391839875979,
    32982195538994230, 44485398083805669, 33387451999706644, 43976406398685869, 51883750720174027, 36871005606313091,
    56912841449667594, 35211081045337954, 32152187356284386, 36871005606313091, 37861845606622741, 35211081045337954,
    41809803545802504, 37843349262362253, 53883751579511743, 36871005606313091
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
noncomputable def negativeCeiling : ℝ := 106088080417 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 265941986361313857829859229696, coefficient := (-265941986361313857829859229696) }, { argument := 32684215014772787863659479040, coefficient := (-32684215014772787863659479040) }, { argument := 9283625499657770383300337074176, coefficient := (-9283625499657770383300337074176) }, { argument := 341988493691159170573412597760, coefficient := (-341988493691159170573412597760) }, { argument := 30292687086862583873635614720, coefficient := (-30292687086862583873635614720) }, { argument := 9283622584171558869311120474112, coefficient := (-9283622584171558869311120474112) }, { argument := 30292687086862583873635614720, coefficient := (-30292687086862583873635614720) }, { argument := 29495511110892515876960993280, coefficient := (-29495511110892515876960993280) }, { argument := 1114452014406155059351120773120, coefficient := (-1114452014406155059351120773120) }, { argument := 29495511110892515876960993280, coefficient := (-29495511110892515876960993280) }, { argument := 341988493691159170573412597760, coefficient := (-341988493691159170573412597760) }, { argument := 1114452014406155059351120773120, coefficient := (-1114452014406155059351120773120) }, { argument := 265942958190051029159598096384, coefficient := (-265942958190051029159598096384) }, { argument := 29495511110892515876960993280, coefficient := (-29495511110892515876960993280) }, { argument := 29495511110892515876960993280, coefficient := (-29495511110892515876960993280) }, { argument := 32684215014772787863659479040, coefficient := (-32684215014772787863659479040) }, { argument := 97831753792596395708907520, coefficient := (-97831753792596395708907520) }, { argument := 31513697506870480728427069440, coefficient := (-31513697506870480728427069440) }, { argument := 335161425388915049937221189632, coefficient := (-335161425388915049937221189632) }, { argument := 31513792489155716258908340224, coefficient := (-31513792489155716258908340224) }, { argument := 97831753792596395708907520, coefficient := (-97831753792596395708907520) }, { argument := 58747557919924366414907965440, coefficient := (-58747557919924366414907965440) }, { argument := 2299083332217106873731631808512, coefficient := (-2299083332217106873731631808512) }, { argument := 2299083332217106873731631808512, coefficient := (-2299083332217106873731631808512) }, { argument := 58747557919924366414907965440, coefficient := (-58747557919924366414907965440) }, { argument := 57647971633662493285727338496, coefficient := (-57647971633662493285727338496) }, { argument := 190192111059210169860751360, coefficient := (-190192111059210169860751360) }, { argument := 9849234322709098082074624, coefficient := (-9849234322709098082074624) }, { argument := 207772240638257572603286781952, coefficient := (-207772240638257572603286781952) }, { argument := 264910440403899879448903680, coefficient := (-264910440403899879448903680) }, { argument := 57647987585365367110913490944, coefficient := (-57647987585365367110913490944) }, { argument := 265250069173648469037940736, coefficient := (-265250069173648469037940736) }, { argument := 265250069173648469037940736, coefficient := (-265250069173648469037940736) }, { argument := 189852482289461580271714304, coefficient := (-189852482289461580271714304) }, { argument := 9849234322709098082074624, coefficient := (-9849234322709098082074624) }, { argument := 55458707408364151651948298240, coefficient := (-55458707408364151651948298240) }, { argument := 862237993290049670320094183424, coefficient := (-862237993290049670320094183424) }, { argument := 40185722271814129563690074112, coefficient := (-40185722271814129563690074112) }, { argument := 51818431350497167068968779776, coefficient := (-51818431350497167068968779776) }, { argument := 693732468692370236678439174144, coefficient := (-693732468692370236678439174144) }, { argument := 1212974301204494910777697763328, coefficient := (-1212974301204494910777697763328) }, { argument := 861180572865344244912236789760, coefficient := (-861180572865344244912236789760) }, { argument := 693732468692370236678439174144, coefficient := (-693732468692370236678439174144) }, { argument := 39128203264661126154119282688, coefficient := (-39128203264661126154119282688) }, { argument := 40185722271814129563690074112, coefficient := (-40185722271814129563690074112) }, { argument := 40185722271814129563690074112, coefficient := (-40185722271814129563690074112) }, { argument := 39128203264661126154119282688, coefficient := (-39128203264661126154119282688) }, { argument := 1212974301204494910777697763328, coefficient := (-1212974301204494910777697763328) }, { argument := 39128203264661126154119282688, coefficient := (-39128203264661126154119282688) }, { argument := 55458608825916573650234900480, coefficient := (-55458608825916573650234900480) }, { argument := 51818431350497167068968779776, coefficient := (-51818431350497167068968779776) }, { argument := 155886028552004547232349028352, coefficient := (-155886028552004547232349028352) }, { argument := 9356103817763536135639189684224, coefficient := (-9356103817763536135639189684224) }, { argument := 2318453444542980100794827669504, coefficient := (-2318453444542980100794827669504) }, { argument := 76373413311511567768415591464960, coefficient := (-76373413311511567768415591464960) }, { argument := 1467375597812012722022042828800, coefficient := (-1467375597812012722022042828800) }, { argument := 88042535868720763321322569728, coefficient := (-88042535868720763321322569728) }, { argument := 2318453444542980100794827669504, coefficient := (-2318453444542980100794827669504) }, { argument := 2303779688564859973574607241216, coefficient := (-2303779688564859973574607241216) }, { argument := 1467375597812012722022042828800, coefficient := (-1467375597812012722022042828800) }, { argument := 35554510734985068254594097741824, coefficient := (-35554510734985068254594097741824) }, { argument := 2274432176608619719134166384640, coefficient := (-2274432176608619719134166384640) }, { argument := 9356109390704848052657485512704, coefficient := (-9356109390704848052657485512704) }, { argument := 2318453444542980100794827669504, coefficient := (-2318453444542980100794827669504) }] }

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
def constantNumerator : ℤ := (-11616171537719407203098931387957248)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4772795433, 246594430705, 4772795433, 125683613069, 125683613069, 17306825811581,
    124416030874197, 75375983953, 2103550715314703, 788690173557, 34930334027, 4207099894781125,
    34930334027, 68022229421, 1285068604467, 68022229421, 788690173557, 1285068604467,
    15552067852953, 68022229421, 68022229421, 75375983953, 2651735, 1708360965,
    18169137277, 854183057, 2651735, 4031280375, 157763996425, 157763996425,
    4031280375, 99761716841001, 2044898625, 1694344575, 11752607001961497, 11393006625,
    3192373959853767, 45630452175, 45630452175, 32659952325, 1694344575, 483753645,
    18931679571, 18931679571, 483753645, 9055607613, 32572751289, 4527805317,
    1144093603, 1144093789, 230067761, 45630452175, 45630452175, 230067761,
    5163905, 3326808195, 35382004171, 1663409111, 5163905, 230067761,
    45630452175, 45630452175, 230067761, 97555935
  ]
def negativeCoefficients : Array ℕ := #[
    88042535868720763321322569728, 2274432176608619719134166384640, 88042535868720763321322569728, 2318453444542980100794827669504, 2318453444542980100794827669504, 155886028552004547232349028352,
    2241279961135798939597141966848, 347610371321257252947610304512, 75788401741169893953896137621504, 3637191446263886866207922454528, 322175466102628673463638818816, 75788374073786909917028810752000,
    322175466102628673463638818816, 313697164363085813635648323584, 11852665831880918039530712334336, 313697164363085813635648323584, 3637191446263886866207922454528, 11852665831880918039530712334336,
    2241289183596793618552917590016, 313697164363085813635648323584, 313697164363085813635648323584, 347610371321257252947610304512, 97831753792596395708907520, 31513697506870480728427069440,
    335161425388915049937221189632, 31513792489155716258908340224, 97831753792596395708907520, 37181998683496434439815168000, 1455116033048801818817488486400, 1455116033048801818817488486400,
    37181998683496434439815168000, 898573661581946077898701012992, 37721721592055560748924928000, 1953446296731448681640755200, 3308064782166605002585021612032, 52540969360363102471716864000,
    898573386001543738648430641152, 52608329577491773115911372800, 52608329577491773115911372800, 37654361374926890104730419200, 1953446296731448681640755200, 2230919921009786066388910080,
    87306961982928109129049309184, 87306961982928109129049309184, 2230919921009786066388910080, 41761619017236712191166513152, 150215301701193977102919008256, 41761632949140173860305371136,
    2638100236363657310482989056, 2638100665250457024230064128, 265250069173648469037940736, 52608329577491773115911372800, 52608329577491773115911372800, 265250069173648469037940736,
    95257233955949122137620480, 30684389677742310182942146560, 326341387878680443359925895168, 30684482160493723725779173376, 95257233955949122137620480, 265250069173648469037940736,
    52608329577491773115911372800, 52608329577491773115911372800, 265250069173648469037940736, 3599178731632888452659281920
  ]
def negativeScales : Array ℕ := #[
    32, 37, 32, 36, 36, 43,
    46, 36, 50, 39, 35, 51,
    35, 35, 40, 35, 39, 40,
    43, 35, 35, 36, 21, 30,
    34, 29, 21, 31, 37, 37,
    31, 46, 30, 30, 53, 33,
    51, 35, 35, 34, 30, 28,
    34, 34, 28, 33, 34, 32,
    30, 30, 27, 35, 35, 27,
    22, 31, 35, 30, 22, 27,
    35, 35, 27, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32152187356284386, 37843349262362253, 32152187356284386, 36871005606313091, 36871005606313091, 43976406398685869,
    46822165716609406, 36133385878852824, 50901748028833560, 39520667711734818, 35023761387678325, 51901747502161856,
    35023761387678325, 35985287258552752, 40224982519610176, 35985287258552752, 39520667711734818, 40224982519610176,
    43822171653026036, 35985287258552752, 35985287258552752, 36133385878852824, 21338505176868039, 30669965692794070,
    34080770866753689, 29669970041070417, 21338505176868039, 31908590984998721, 37198977046922497, 37198977046922497,
    31908590984998721, 46503551526858022, 30929382185246576, 30658080156127340, 53383830333849338, 33407429474723254,
    51503551084402875, 35409277899115623, 35409277899115623, 34926803640824563, 30658080156127340, 28849697292576513,
    34140083357868929, 34140083357868929, 28849697292576513, 33076164300335881, 34922946538941714, 32076164781626721,
    30091557943742117, 30091558178286962, 27777483594852285, 35409277899115623, 35409277899115623, 27777483594852285,
    22300031029053403, 31631491544957517, 35042296718939053, 30631495893233862, 22300031029053403, 27777483594852285,
    35409277899115623, 35409277899115623, 27777483594852285, 26539726308800860
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
noncomputable def negativeCeiling : ℝ := 60364374363 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 88042535868720763321322569728, coefficient := (-88042535868720763321322569728) }, { argument := 2274432176608619719134166384640, coefficient := (-2274432176608619719134166384640) }, { argument := 88042535868720763321322569728, coefficient := (-88042535868720763321322569728) }, { argument := 2318453444542980100794827669504, coefficient := (-2318453444542980100794827669504) }, { argument := 2318453444542980100794827669504, coefficient := (-2318453444542980100794827669504) }, { argument := 155886028552004547232349028352, coefficient := (-155886028552004547232349028352) }, { argument := 2241279961135798939597141966848, coefficient := (-2241279961135798939597141966848) }, { argument := 347610371321257252947610304512, coefficient := (-347610371321257252947610304512) }, { argument := 75788401741169893953896137621504, coefficient := (-75788401741169893953896137621504) }, { argument := 3637191446263886866207922454528, coefficient := (-3637191446263886866207922454528) }, { argument := 322175466102628673463638818816, coefficient := (-322175466102628673463638818816) }, { argument := 75788374073786909917028810752000, coefficient := (-75788374073786909917028810752000) }, { argument := 322175466102628673463638818816, coefficient := (-322175466102628673463638818816) }, { argument := 313697164363085813635648323584, coefficient := (-313697164363085813635648323584) }, { argument := 11852665831880918039530712334336, coefficient := (-11852665831880918039530712334336) }, { argument := 313697164363085813635648323584, coefficient := (-313697164363085813635648323584) }, { argument := 3637191446263886866207922454528, coefficient := (-3637191446263886866207922454528) }, { argument := 11852665831880918039530712334336, coefficient := (-11852665831880918039530712334336) }, { argument := 2241289183596793618552917590016, coefficient := (-2241289183596793618552917590016) }, { argument := 313697164363085813635648323584, coefficient := (-313697164363085813635648323584) }, { argument := 313697164363085813635648323584, coefficient := (-313697164363085813635648323584) }, { argument := 347610371321257252947610304512, coefficient := (-347610371321257252947610304512) }, { argument := 97831753792596395708907520, coefficient := (-97831753792596395708907520) }, { argument := 31513697506870480728427069440, coefficient := (-31513697506870480728427069440) }, { argument := 335161425388915049937221189632, coefficient := (-335161425388915049937221189632) }, { argument := 31513792489155716258908340224, coefficient := (-31513792489155716258908340224) }, { argument := 97831753792596395708907520, coefficient := (-97831753792596395708907520) }, { argument := 37181998683496434439815168000, coefficient := (-37181998683496434439815168000) }, { argument := 1455116033048801818817488486400, coefficient := (-1455116033048801818817488486400) }, { argument := 1455116033048801818817488486400, coefficient := (-1455116033048801818817488486400) }, { argument := 37181998683496434439815168000, coefficient := (-37181998683496434439815168000) }, { argument := 898573661581946077898701012992, coefficient := (-898573661581946077898701012992) }, { argument := 37721721592055560748924928000, coefficient := (-37721721592055560748924928000) }, { argument := 1953446296731448681640755200, coefficient := (-1953446296731448681640755200) }, { argument := 3308064782166605002585021612032, coefficient := (-3308064782166605002585021612032) }, { argument := 52540969360363102471716864000, coefficient := (-52540969360363102471716864000) }, { argument := 898573386001543738648430641152, coefficient := (-898573386001543738648430641152) }, { argument := 52608329577491773115911372800, coefficient := (-52608329577491773115911372800) }, { argument := 52608329577491773115911372800, coefficient := (-52608329577491773115911372800) }, { argument := 37654361374926890104730419200, coefficient := (-37654361374926890104730419200) }, { argument := 1953446296731448681640755200, coefficient := (-1953446296731448681640755200) }, { argument := 2230919921009786066388910080, coefficient := (-2230919921009786066388910080) }, { argument := 87306961982928109129049309184, coefficient := (-87306961982928109129049309184) }, { argument := 87306961982928109129049309184, coefficient := (-87306961982928109129049309184) }, { argument := 2230919921009786066388910080, coefficient := (-2230919921009786066388910080) }, { argument := 41761619017236712191166513152, coefficient := (-41761619017236712191166513152) }, { argument := 150215301701193977102919008256, coefficient := (-150215301701193977102919008256) }, { argument := 41761632949140173860305371136, coefficient := (-41761632949140173860305371136) }, { argument := 2638100236363657310482989056, coefficient := (-2638100236363657310482989056) }, { argument := 2638100665250457024230064128, coefficient := (-2638100665250457024230064128) }, { argument := 265250069173648469037940736, coefficient := (-265250069173648469037940736) }, { argument := 52608329577491773115911372800, coefficient := (-52608329577491773115911372800) }, { argument := 52608329577491773115911372800, coefficient := (-52608329577491773115911372800) }, { argument := 265250069173648469037940736, coefficient := (-265250069173648469037940736) }, { argument := 95257233955949122137620480, coefficient := (-95257233955949122137620480) }, { argument := 30684389677742310182942146560, coefficient := (-30684389677742310182942146560) }, { argument := 326341387878680443359925895168, coefficient := (-326341387878680443359925895168) }, { argument := 30684482160493723725779173376, coefficient := (-30684482160493723725779173376) }, { argument := 95257233955949122137620480, coefficient := (-95257233955949122137620480) }, { argument := 265250069173648469037940736, coefficient := (-265250069173648469037940736) }, { argument := 52608329577491773115911372800, coefficient := (-52608329577491773115911372800) }, { argument := 52608329577491773115911372800, coefficient := (-52608329577491773115911372800) }, { argument := 265250069173648469037940736, coefficient := (-265250069173648469037940736) }, { argument := 3599178731632888452659281920, coefficient := (-3599178731632888452659281920) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18
