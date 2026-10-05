import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
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

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1447868608979501752273513253699584)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    35382004171, 1663409111, 5163905, 24993938325, 978136777835, 978136777835,
    24993938325, 9055607613, 32572751289, 4527805317, 483753645, 18931679571,
    18931679571, 483753645, 9055607613, 32572751289, 4527805317, 780140451,
    780140637, 5722165, 3686463135, 39207085703, 1843237123, 5722165,
    12738845985, 498534228703, 498534228703, 12738845985, 17634604299, 63431147247,
    8817305091, 12738845985, 498534228703, 498534228703, 12738845985, 546672733269,
    1966365564657, 273336457821, 7977565257, 7977567159, 17634604299, 63431147247,
    8817305091, 15929964693, 15929968491, 14030898249, 11000915, 268250867795,
    115107135, 5097985, 536501650009, 5097985, 9927655, 187552185,
    9927655, 115107135, 187552185, 1753865847, 9927655, 9927655,
    11000915, 1600049783611, 10310335, 8542849
  ]
def negativeCoefficients : Array ℕ := #[
    326341387878680443359925895168, 30684482160493723725779173376, 95257233955949122137620480, 57632097959419473381713510400, 2255429851225642819167107153920, 2255429851225642819167107153920,
    57632097959419473381713510400, 41761619017236712191166513152, 150215301701193977102919008256, 41761632949140173860305371136, 2230919921009786066388910080, 87306961982928109129049309184,
    87306961982928109129049309184, 2230919921009786066388910080, 41761619017236712191166513152, 150215301701193977102919008256, 41761632949140173860305371136, 1798881405143168355089252352,
    1798881834029968068836327424, 105555313302538216422768640, 34001620994254992364881838080, 361621537919618869669107073024, 34001723475141693858295840768, 105555313302538216422768640,
    58747557919924366414907965440, 2299083332217106873731631808512, 2299083332217106873731631808512, 58747557919924366414907965440, 40662629043098903975609499648, 146262267445899398758105350144,
    40662642608373327179771019264, 58747557919924366414907965440, 2299083332217106873731631808512, 2299083332217106873731631808512, 58747557919924366414907965440, 1260541500336066023243894489088,
    4534130290822881361501265854464, 1260541920859573142572901597184, 36790026156798991520212451328, 36790034928225798569104244736, 40662629043098903975609499648, 146262267445899398758105350144,
    40662642608373327179771019264, 36731997724375018347467636736, 36732006481966767341077266432, 4044131080055663667242336256, 101465531790816256007864320, 154636097055151895805385768960,
    1061675930201467654326190080, 94041224586610188495093760, 154636072388108074365743005696, 94041224586610188495093760, 91566455518541499324170240, 3459727157160027460951080960,
    91566455518541499324170240, 1061675930201467654326190080, 3459727157160027460951080960, 4044139302403604147123257344, 91566455518541499324170240, 91566455518541499324170240,
    101465531790816256007864320, 57647868873957938861805928448, 190192111059210169860751360, 9849234322709098082074624
  ]
def negativeScales : Array ℕ := #[
    35, 30, 22, 34, 39, 39,
    34, 33, 34, 32, 28, 34,
    34, 28, 33, 34, 32, 29,
    29, 22, 31, 35, 30, 22,
    33, 38, 38, 33, 34, 35,
    33, 33, 38, 38, 33, 38,
    40, 37, 32, 32, 34, 35,
    33, 33, 33, 33, 23, 37,
    26, 22, 38, 22, 23, 27,
    23, 26, 27, 30, 23, 23,
    23, 40, 23, 23
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35042296718939053, 30631495893233862, 22300031029053403, 34540859195408458, 39831245263627619, 39831245263627619,
    34540859195408458, 33076164300335881, 34922946538941714, 32076164781626721, 28849697292576513, 34140083357868929,
    34140083357868929, 28849697292576513, 33076164300335881, 34922946538941714, 32076164781626721, 29539158639126325,
    29539158983091627, 22448129668042580, 31779590184357093, 35190395357928187, 30779594532633476, 22448129668042580,
    33568515538312626, 38858901607375813, 38858901607375813, 33568515538312626, 34037690152521246, 35884472387871606,
    33037690633812085, 33568515538312626, 38858901607375813, 38858901607375813, 33568515538312626, 38991886483699174,
    40838668696354009, 37991886964990175, 32893301362749349, 32893301706714675, 34037690152521246, 35884472387871606,
    33037690633812085, 33891024021881933, 33891024365847258, 33707888321275264, 23391120188967178, 37964791895240383,
    26778402022261855, 22281495697792675, 38964791665106325, 22281495697792675, 23243021549978039, 27482716829724676,
    23243021549978039, 26778402022261855, 27482716829724676, 30707891254495857, 23243021549978039, 23243021549978039,
    23391120188967178, 40541253932169104, 23297587873249950, 23026285851432555
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
noncomputable def negativeCeiling : ℝ := 2205433963 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 326341387878680443359925895168, coefficient := (-326341387878680443359925895168) }, { argument := 30684482160493723725779173376, coefficient := (-30684482160493723725779173376) }, { argument := 95257233955949122137620480, coefficient := (-95257233955949122137620480) }, { argument := 57632097959419473381713510400, coefficient := (-57632097959419473381713510400) }, { argument := 2255429851225642819167107153920, coefficient := (-2255429851225642819167107153920) }, { argument := 2255429851225642819167107153920, coefficient := (-2255429851225642819167107153920) }, { argument := 57632097959419473381713510400, coefficient := (-57632097959419473381713510400) }, { argument := 41761619017236712191166513152, coefficient := (-41761619017236712191166513152) }, { argument := 150215301701193977102919008256, coefficient := (-150215301701193977102919008256) }, { argument := 41761632949140173860305371136, coefficient := (-41761632949140173860305371136) }, { argument := 2230919921009786066388910080, coefficient := (-2230919921009786066388910080) }, { argument := 87306961982928109129049309184, coefficient := (-87306961982928109129049309184) }, { argument := 87306961982928109129049309184, coefficient := (-87306961982928109129049309184) }, { argument := 2230919921009786066388910080, coefficient := (-2230919921009786066388910080) }, { argument := 41761619017236712191166513152, coefficient := (-41761619017236712191166513152) }, { argument := 150215301701193977102919008256, coefficient := (-150215301701193977102919008256) }, { argument := 41761632949140173860305371136, coefficient := (-41761632949140173860305371136) }, { argument := 1798881405143168355089252352, coefficient := (-1798881405143168355089252352) }, { argument := 1798881834029968068836327424, coefficient := (-1798881834029968068836327424) }, { argument := 105555313302538216422768640, coefficient := (-105555313302538216422768640) }, { argument := 34001620994254992364881838080, coefficient := (-34001620994254992364881838080) }, { argument := 361621537919618869669107073024, coefficient := (-361621537919618869669107073024) }, { argument := 34001723475141693858295840768, coefficient := (-34001723475141693858295840768) }, { argument := 105555313302538216422768640, coefficient := (-105555313302538216422768640) }, { argument := 58747557919924366414907965440, coefficient := (-58747557919924366414907965440) }, { argument := 2299083332217106873731631808512, coefficient := (-2299083332217106873731631808512) }, { argument := 2299083332217106873731631808512, coefficient := (-2299083332217106873731631808512) }, { argument := 58747557919924366414907965440, coefficient := (-58747557919924366414907965440) }, { argument := 40662629043098903975609499648, coefficient := (-40662629043098903975609499648) }, { argument := 146262267445899398758105350144, coefficient := (-146262267445899398758105350144) }, { argument := 40662642608373327179771019264, coefficient := (-40662642608373327179771019264) }, { argument := 58747557919924366414907965440, coefficient := (-58747557919924366414907965440) }, { argument := 2299083332217106873731631808512, coefficient := (-2299083332217106873731631808512) }, { argument := 2299083332217106873731631808512, coefficient := (-2299083332217106873731631808512) }, { argument := 58747557919924366414907965440, coefficient := (-58747557919924366414907965440) }, { argument := 1260541500336066023243894489088, coefficient := (-1260541500336066023243894489088) }, { argument := 4534130290822881361501265854464, coefficient := (-4534130290822881361501265854464) }, { argument := 1260541920859573142572901597184, coefficient := (-1260541920859573142572901597184) }, { argument := 36790026156798991520212451328, coefficient := (-36790026156798991520212451328) }, { argument := 36790034928225798569104244736, coefficient := (-36790034928225798569104244736) }, { argument := 40662629043098903975609499648, coefficient := (-40662629043098903975609499648) }, { argument := 146262267445899398758105350144, coefficient := (-146262267445899398758105350144) }, { argument := 40662642608373327179771019264, coefficient := (-40662642608373327179771019264) }, { argument := 36731997724375018347467636736, coefficient := (-36731997724375018347467636736) }, { argument := 36732006481966767341077266432, coefficient := (-36732006481966767341077266432) }, { argument := 4044131080055663667242336256, coefficient := (-4044131080055663667242336256) }, { argument := 101465531790816256007864320, coefficient := (-101465531790816256007864320) }, { argument := 154636097055151895805385768960, coefficient := (-154636097055151895805385768960) }, { argument := 1061675930201467654326190080, coefficient := (-1061675930201467654326190080) }, { argument := 94041224586610188495093760, coefficient := (-94041224586610188495093760) }, { argument := 154636072388108074365743005696, coefficient := (-154636072388108074365743005696) }, { argument := 94041224586610188495093760, coefficient := (-94041224586610188495093760) }, { argument := 91566455518541499324170240, coefficient := (-91566455518541499324170240) }, { argument := 3459727157160027460951080960, coefficient := (-3459727157160027460951080960) }, { argument := 91566455518541499324170240, coefficient := (-91566455518541499324170240) }, { argument := 1061675930201467654326190080, coefficient := (-1061675930201467654326190080) }, { argument := 3459727157160027460951080960, coefficient := (-3459727157160027460951080960) }, { argument := 4044139302403604147123257344, coefficient := (-4044139302403604147123257344) }, { argument := 91566455518541499324170240, coefficient := (-91566455518541499324170240) }, { argument := 91566455518541499324170240, coefficient := (-91566455518541499324170240) }, { argument := 101465531790816256007864320, coefficient := (-101465531790816256007864320) }, { argument := 57647868873957938861805928448, coefficient := (-57647868873957938861805928448) }, { argument := 190192111059210169860751360, coefficient := (-190192111059210169860751360) }, { argument := 9849234322709098082074624, coefficient := (-9849234322709098082074624) }] }

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

end TermShard6


end Parent1

namespace Parent1

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 94743165922689869493274973078290432
def positiveArguments : Array ℕ := #[
    9809, 93, 2253, 1707, 951, 93,
    951, 1899, 93, 2253, 93, 117,
    351, 741, 1911, 1599, 44733, 1365,
    1599, 1443, 741, 741, 1443, 44733,
    1443, 117, 1911, 9297, 139455, 244821,
    9297, 77475, 9297, 244821, 486543, 77475,
    7508877, 480345, 139455, 244821, 9297, 480345,
    9297, 244821, 244821, 9297
  ]
def positiveCoefficients : Array ℕ := #[
    777149046102418887455072608845824, 7195526478346272847851159552, 174317431781872609959232929792, 132072727941259008078300315648, 147160122170049580178633392128, 7195526478346272847851159552,
    147160122170049580178633392128, 146928008412683571377089806336, 7195526478346272847851159552, 174317431781872609959232929792, 7195526478346272847851159552, 579355938385557968652790136832,
    434516953789168476489592602624, 458656784555233391850125524992, 591425853768590426333056598016, 7917864491269292238254798536704, 13844192944338228959265630978048, 422447038406136018809326141440,
    7917864491269292238254798536704, 446586869172200934169859063808, 458656784555233391850125524992, 458656784555233391850125524992, 446586869172200934169859063808, 13844192944338228959265630978048,
    446586869172200934169859063808, 579355938385557968652790136832, 591425853768590426333056598016, 359660267038630637991786184704, 5394904005579459569876792770560, 9471053698683940133783702863872,
    359660267038630637991786184704, 5994337783977177299863103078400, 359660267038630637991786184704, 9471053698683940133783702863872, 9411110320844168360785071833088, 5994337783977177299863103078400,
    145242804505767005975682987589632, 9291223565164624814787809771520, 5394904005579459569876792770560, 9471053698683940133783702863872, 359660267038630637991786184704, 9291223565164624814787809771520,
    359660267038630637991786184704, 9471053698683940133783702863872, 9471053698683940133783702863872, 359660267038630637991786184704
  ]
def positiveScales : Array ℕ := #[
    13, 6, 11, 10, 9, 6,
    9, 10, 6, 11, 6, 6,
    8, 9, 10, 10, 15, 10,
    10, 10, 9, 9, 10, 15,
    10, 6, 10, 13, 17, 17,
    13, 16, 13, 17, 18, 16,
    22, 18, 17, 17, 13, 18,
    13, 17, 17, 13
  ]
def negativeArguments : Array ℕ := #[
    184538486986123, 57443295, 51201607243541, 230067761, 230067761, 164670779,
    8542849, 1146036131, 1146036317, 23353935423, 84003411219, 11676971607,
    18899531571, 18899536077, 780140451, 780140637, 3, 39
  ]
def negativeCoefficients : Array ℕ := #[
    207771865306554667062632906752, 264910440403899879448903680, 57647884825695434109127491584, 265250069173648469037940736, 265250069173648469037940736, 189852482289461580271714304,
    9849234322709098082074624, 2642579400972659168968179712, 2642579829859458882715254784, 53850508732752602562293661696, 193698678509434338895869247488, 53850526697575487346183241728,
    43579352750403852731355758592, 43579363140532452248260706304, 1798881405143168355089252352, 1798881834029968068836327424, 950737950171172051122527404032, 49438373408900946658371425009664
  ]
def negativeScales : Array ℕ := #[
    47, 25, 45, 27, 27, 27,
    23, 30, 30, 34, 36, 33,
    34, 34, 29, 29, 1, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13259890349895821, 6539158811107971, 11137631598235427, 10737247343017206, 9893301530621223, 6539158811107971,
    9893301530621223, 10891024189919810, 6539158811107971, 11137631598235427, 6539158811107971, 6870364719426147,
    8455327220304556, 9533329732305783, 10900112062706946, 10642954223479225, 15449051894878070, 10414685235807213,
    10642954223479225, 10494855584491183, 9533329732305783, 9533329732305783, 10494855584491183, 15449051894878070,
    10494855584491183, 6870364719426147, 10900112062706946, 13182549540307371, 17089440135915890, 17901367787486663,
    13182549540307371, 16241443229360940, 13182549540307371, 17901367787486663, 18892207788243184, 16241443229360940,
    22840165728948798, 18873711444693131, 17089440135915890, 17901367787486663, 13182549540307371, 18873711444693131,
    13182549540307371, 17901367787486663, 17901367787486663, 13182549540307371
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    47390915061746824, 25775635170444446, 45541254331377086, 27777483594852285, 27777483594852285, 27295009329148173,
    23026285851432555, 30094005382542534, 30094005616689826, 34442946631007540, 36289728863060379, 33442947112298379,
    34137631426252767, 34137631770218069, 29539158639126325, 29539158983091627, 1584962500724866, 5285402218862249
  ]

abbrev PositiveTerm := Fin 46
abbrev NegativeTerm := Fin 18
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
noncomputable def positiveFloor : ℝ := 96708641791 / 500000000000
noncomputable def negativeCeiling : ℝ := 3481516597 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 207771865306554667062632906752, coefficient := (-207771865306554667062632906752) }, { argument := 264910440403899879448903680, coefficient := (-264910440403899879448903680) }, { argument := 57647884825695434109127491584, coefficient := (-57647884825695434109127491584) }, { argument := 265250069173648469037940736, coefficient := (-265250069173648469037940736) }, { argument := 265250069173648469037940736, coefficient := (-265250069173648469037940736) }, { argument := 189852482289461580271714304, coefficient := (-189852482289461580271714304) }, { argument := 9849234322709098082074624, coefficient := (-9849234322709098082074624) }, { argument := 2642579400972659168968179712, coefficient := (-2642579400972659168968179712) }, { argument := 2642579829859458882715254784, coefficient := (-2642579829859458882715254784) }, { argument := 53850508732752602562293661696, coefficient := (-53850508732752602562293661696) }, { argument := 193698678509434338895869247488, coefficient := (-193698678509434338895869247488) }, { argument := 53850526697575487346183241728, coefficient := (-53850526697575487346183241728) }, { argument := 43579352750403852731355758592, coefficient := (-43579352750403852731355758592) }, { argument := 43579363140532452248260706304, coefficient := (-43579363140532452248260706304) }, { argument := 1798881405143168355089252352, coefficient := (-1798881405143168355089252352) }, { argument := 1798881834029968068836327424, coefficient := (-1798881834029968068836327424) }, { argument := 777149046102418887455072608845824, coefficient := 777149046102418887455072608845824 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 174317431781872609959232929792, coefficient := 174317431781872609959232929792 }, { argument := 132072727941259008078300315648, coefficient := 132072727941259008078300315648 }, { argument := 147160122170049580178633392128, coefficient := 147160122170049580178633392128 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 147160122170049580178633392128, coefficient := 147160122170049580178633392128 }, { argument := 146928008412683571377089806336, coefficient := 146928008412683571377089806336 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 174317431781872609959232929792, coefficient := 174317431781872609959232929792 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 579355938385557968652790136832, coefficient := 579355938385557968652790136832 }, { argument := 434516953789168476489592602624, coefficient := 434516953789168476489592602624 }, { argument := 458656784555233391850125524992, coefficient := 458656784555233391850125524992 }, { argument := 591425853768590426333056598016, coefficient := 591425853768590426333056598016 }, { argument := 7917864491269292238254798536704, coefficient := 7917864491269292238254798536704 }, { argument := 13844192944338228959265630978048, coefficient := 13844192944338228959265630978048 }, { argument := 422447038406136018809326141440, coefficient := 422447038406136018809326141440 }, { argument := 7917864491269292238254798536704, coefficient := 7917864491269292238254798536704 }, { argument := 446586869172200934169859063808, coefficient := 446586869172200934169859063808 }, { argument := 458656784555233391850125524992, coefficient := 458656784555233391850125524992 }, { argument := 458656784555233391850125524992, coefficient := 458656784555233391850125524992 }, { argument := 446586869172200934169859063808, coefficient := 446586869172200934169859063808 }, { argument := 13844192944338228959265630978048, coefficient := 13844192944338228959265630978048 }, { argument := 446586869172200934169859063808, coefficient := 446586869172200934169859063808 }, { argument := 579355938385557968652790136832, coefficient := 579355938385557968652790136832 }, { argument := 591425853768590426333056598016, coefficient := 591425853768590426333056598016 }, { argument := 49438373408900946658371425009664, coefficient := (-49438373408900946658371425009664) }, { argument := 359660267038630637991786184704, coefficient := 359660267038630637991786184704 }, { argument := 5394904005579459569876792770560, coefficient := 5394904005579459569876792770560 }, { argument := 9471053698683940133783702863872, coefficient := 9471053698683940133783702863872 }, { argument := 359660267038630637991786184704, coefficient := 359660267038630637991786184704 }, { argument := 5994337783977177299863103078400, coefficient := 5994337783977177299863103078400 }, { argument := 359660267038630637991786184704, coefficient := 359660267038630637991786184704 }, { argument := 9471053698683940133783702863872, coefficient := 9471053698683940133783702863872 }, { argument := 9411110320844168360785071833088, coefficient := 9411110320844168360785071833088 }, { argument := 5994337783977177299863103078400, coefficient := 5994337783977177299863103078400 }, { argument := 145242804505767005975682987589632, coefficient := 145242804505767005975682987589632 }, { argument := 9291223565164624814787809771520, coefficient := 9291223565164624814787809771520 }, { argument := 5394904005579459569876792770560, coefficient := 5394904005579459569876792770560 }, { argument := 9471053698683940133783702863872, coefficient := 9471053698683940133783702863872 }, { argument := 359660267038630637991786184704, coefficient := 359660267038630637991786184704 }, { argument := 9291223565164624814787809771520, coefficient := 9291223565164624814787809771520 }, { argument := 359660267038630637991786184704, coefficient := 359660267038630637991786184704 }, { argument := 9471053698683940133783702863872, coefficient := 9471053698683940133783702863872 }, { argument := 9471053698683940133783702863872, coefficient := 9471053698683940133783702863872 }, { argument := 359660267038630637991786184704, coefficient := 359660267038630637991786184704 }] }

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

end TermShard7


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18
