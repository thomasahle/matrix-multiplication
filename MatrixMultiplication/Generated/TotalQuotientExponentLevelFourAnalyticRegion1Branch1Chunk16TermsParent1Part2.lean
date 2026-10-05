import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 16, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4054853029843222649143087878635520)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1323963545, 72839985, 2850589903, 2850589903, 72839985, 84694325,
    54563702175, 580307918215, 27281933315, 84694325, 2037742995, 79746990701,
    79746990701, 2037742995, 96799979029, 348186645937, 48400005661, 1745563926303,
    64877255866593, 1070235705, 2760081555, 2309455995, 64608439665, 16212105746589,
    2309455995, 2084143215, 1070235705, 1070235705, 2084143215, 64608439665,
    2084143215, 436389192675, 2760081555, 2416258121133, 735356506172787, 13957407555,
    25755971527362873, 4416901125, 530028135, 13957407555, 27738139065, 4416901125,
    428086057035, 27384786975, 2941428467649371, 13957407555, 530028135, 27384786975,
    530028135, 13957407555, 13957407555, 2416258121133, 254620230014335, 9239603175,
    4649390035238445, 96677799075, 4281767325, 9298776723629775, 4281767325, 8338178475,
    157523966325, 8338178475, 96677799075, 157523966325
  ]
def negativeCoefficients : Array ℕ := #[
    12211408338768119628939919360, 85994275944181928580234608640, 3365382553583458277838523727872, 3365382553583458277838523727872, 85994275944181928580234608640, 781167268885290360084889600,
    251630662434083555457053491200, 2676197912814819602710512271360, 251631420848907715933131243520, 781167268885290360084889600, 150358894067037609880379719680, 5884289312439369885184126091264,
    5884289312439369885184126091264, 150358894067037609880379719680, 111602777468025914166612066304, 401431871717697542418451136512, 111602814699320062435521462272, 7861321048049570741420556288,
    292181185345608560350360240128, 4935591037170278484745912320, 6364314758456411730330255360, 85203887378518491736666275840, 148976918937744984789567406080, 292051333596917189011964952576,
    85203887378518491736666275840, 4805707062507902735147335680, 4935591037170278484745912320, 4935591037170278484745912320, 4805707062507902735147335680, 148976918937744984789567406080,
    4805707062507902735147335680, 7861288822078566330217267200, 6364314758456411730330255360, 21763718347931027172476583936, 1655875643592116687430720946176, 257468725099545172600820858880,
    14499322971649567445431275749376, 162954889303509602911911936000, 9777293358210576174714716160, 257468725099545172600820858880, 255839176206510076571701739520, 162954889303509602911911936000,
    3948396967824037678555626209280, 252580078420439884513463500800, 1655877018855334535491854794752, 257468725099545172600820858880, 9777293358210576174714716160, 252580078420439884513463500800,
    9777293358210576174714716160, 257468725099545172600820858880, 257468725099545172600820858880, 21763718347931027172476583936, 286676893253387271848109015040, 21305074388982400892377497600,
    10469495615099979084277858959360, 222923827143254877629998694400, 19746166506861737412447436800, 10469491846885124089272965529600, 19746166506861737412447436800, 19226530546154849585804083200,
    726451073068229181647408332800, 19226530546154849585804083200, 222923827143254877629998694400, 726451073068229181647408332800
  ]
def negativeScales : Array ℕ := #[
    30, 26, 31, 31, 26, 26,
    35, 39, 34, 26, 30, 36,
    36, 30, 36, 38, 35, 40,
    45, 29, 31, 31, 35, 43,
    31, 30, 29, 29, 30, 35,
    30, 38, 31, 41, 49, 33,
    54, 32, 28, 33, 34, 32,
    38, 34, 51, 33, 28, 34,
    28, 33, 33, 41, 47, 33,
    52, 36, 31, 53, 31, 32,
    37, 32, 36, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30302216252436693, 26118227289430903, 31408613356445470, 31408613356445470, 26118227289430903, 26335761968259584,
    35667222484183314, 39078027658145234, 34667226832459661, 26335761968259584, 30924324967540876, 36214711027843202,
    36214711027843202, 30924324967540876, 36494287683824534, 38341069915877186, 35494288165115373, 40666830331132416,
    45882778035458777, 29995281441714674, 31362063750430195, 31104905910933069, 35911003587643887, 43882136727480168,
    31104905910933069, 30956807283632447, 29995281441714674, 29995281441714674, 30956807283632447, 35911003587643887,
    30956807283632447, 38666824417069932, 31362063750430195, 41135911720044453, 49385437177000637, 33700311949601055,
    54515756478421496, 32040387391125756, 28981493719644172, 33700311949601055, 34691151950301361, 32040387391125756,
    38639109890818488, 34672655606662797, 51385438375209336, 33700311949601055, 28981493719644172, 34672655606662797,
    28981493719644172, 33700311949601055, 33700311949601055, 41135911720044453, 47855340378730894, 33105183745697582,
    52045962881282007, 36492465578579254, 31995559276577170, 53045962362022430, 31995559276577170, 32957085118451481,
    37196780386454935, 32957085118451481, 36492465578579254, 37196780386454935
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
noncomputable def negativeCeiling : ℝ := 9695539639 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 12211408338768119628939919360, coefficient := (-12211408338768119628939919360) }, { argument := 85994275944181928580234608640, coefficient := (-85994275944181928580234608640) }, { argument := 3365382553583458277838523727872, coefficient := (-3365382553583458277838523727872) }, { argument := 3365382553583458277838523727872, coefficient := (-3365382553583458277838523727872) }, { argument := 85994275944181928580234608640, coefficient := (-85994275944181928580234608640) }, { argument := 781167268885290360084889600, coefficient := (-781167268885290360084889600) }, { argument := 251630662434083555457053491200, coefficient := (-251630662434083555457053491200) }, { argument := 2676197912814819602710512271360, coefficient := (-2676197912814819602710512271360) }, { argument := 251631420848907715933131243520, coefficient := (-251631420848907715933131243520) }, { argument := 781167268885290360084889600, coefficient := (-781167268885290360084889600) }, { argument := 150358894067037609880379719680, coefficient := (-150358894067037609880379719680) }, { argument := 5884289312439369885184126091264, coefficient := (-5884289312439369885184126091264) }, { argument := 5884289312439369885184126091264, coefficient := (-5884289312439369885184126091264) }, { argument := 150358894067037609880379719680, coefficient := (-150358894067037609880379719680) }, { argument := 111602777468025914166612066304, coefficient := (-111602777468025914166612066304) }, { argument := 401431871717697542418451136512, coefficient := (-401431871717697542418451136512) }, { argument := 111602814699320062435521462272, coefficient := (-111602814699320062435521462272) }, { argument := 7861321048049570741420556288, coefficient := (-7861321048049570741420556288) }, { argument := 292181185345608560350360240128, coefficient := (-292181185345608560350360240128) }, { argument := 4935591037170278484745912320, coefficient := (-4935591037170278484745912320) }, { argument := 6364314758456411730330255360, coefficient := (-6364314758456411730330255360) }, { argument := 85203887378518491736666275840, coefficient := (-85203887378518491736666275840) }, { argument := 148976918937744984789567406080, coefficient := (-148976918937744984789567406080) }, { argument := 292051333596917189011964952576, coefficient := (-292051333596917189011964952576) }, { argument := 85203887378518491736666275840, coefficient := (-85203887378518491736666275840) }, { argument := 4805707062507902735147335680, coefficient := (-4805707062507902735147335680) }, { argument := 4935591037170278484745912320, coefficient := (-4935591037170278484745912320) }, { argument := 4935591037170278484745912320, coefficient := (-4935591037170278484745912320) }, { argument := 4805707062507902735147335680, coefficient := (-4805707062507902735147335680) }, { argument := 148976918937744984789567406080, coefficient := (-148976918937744984789567406080) }, { argument := 4805707062507902735147335680, coefficient := (-4805707062507902735147335680) }, { argument := 7861288822078566330217267200, coefficient := (-7861288822078566330217267200) }, { argument := 6364314758456411730330255360, coefficient := (-6364314758456411730330255360) }, { argument := 21763718347931027172476583936, coefficient := (-21763718347931027172476583936) }, { argument := 1655875643592116687430720946176, coefficient := (-1655875643592116687430720946176) }, { argument := 257468725099545172600820858880, coefficient := (-257468725099545172600820858880) }, { argument := 14499322971649567445431275749376, coefficient := (-14499322971649567445431275749376) }, { argument := 162954889303509602911911936000, coefficient := (-162954889303509602911911936000) }, { argument := 9777293358210576174714716160, coefficient := (-9777293358210576174714716160) }, { argument := 257468725099545172600820858880, coefficient := (-257468725099545172600820858880) }, { argument := 255839176206510076571701739520, coefficient := (-255839176206510076571701739520) }, { argument := 162954889303509602911911936000, coefficient := (-162954889303509602911911936000) }, { argument := 3948396967824037678555626209280, coefficient := (-3948396967824037678555626209280) }, { argument := 252580078420439884513463500800, coefficient := (-252580078420439884513463500800) }, { argument := 1655877018855334535491854794752, coefficient := (-1655877018855334535491854794752) }, { argument := 257468725099545172600820858880, coefficient := (-257468725099545172600820858880) }, { argument := 9777293358210576174714716160, coefficient := (-9777293358210576174714716160) }, { argument := 252580078420439884513463500800, coefficient := (-252580078420439884513463500800) }, { argument := 9777293358210576174714716160, coefficient := (-9777293358210576174714716160) }, { argument := 257468725099545172600820858880, coefficient := (-257468725099545172600820858880) }, { argument := 257468725099545172600820858880, coefficient := (-257468725099545172600820858880) }, { argument := 21763718347931027172476583936, coefficient := (-21763718347931027172476583936) }, { argument := 286676893253387271848109015040, coefficient := (-286676893253387271848109015040) }, { argument := 21305074388982400892377497600, coefficient := (-21305074388982400892377497600) }, { argument := 10469495615099979084277858959360, coefficient := (-10469495615099979084277858959360) }, { argument := 222923827143254877629998694400, coefficient := (-222923827143254877629998694400) }, { argument := 19746166506861737412447436800, coefficient := (-19746166506861737412447436800) }, { argument := 10469491846885124089272965529600, coefficient := (-10469491846885124089272965529600) }, { argument := 19746166506861737412447436800, coefficient := (-19746166506861737412447436800) }, { argument := 19226530546154849585804083200, coefficient := (-19226530546154849585804083200) }, { argument := 726451073068229181647408332800, coefficient := (-726451073068229181647408332800) }, { argument := 19226530546154849585804083200, coefficient := (-19226530546154849585804083200) }, { argument := 222923827143254877629998694400, coefficient := (-222923827143254877629998694400) }, { argument := 726451073068229181647408332800, coefficient := (-726451073068229181647408332800) }] }

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

end TermShard4


end Parent1

namespace Parent1

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1097954122175394012939300445880320)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    31827668203755, 8338178475, 8338178475, 9239603175, 43166785, 27809886915,
    295769842187, 13904985367, 43166785, 72839985, 2850589903, 2850589903,
    72839985, 22797917121649, 2647946986902113, 729533303529343, 65733645, 2572483571,
    2572483571, 65733645, 40859644943, 146970927779, 20429829287, 8388607,
    8388609, 42040917, 8338178475, 8338178475, 42040917, 1639245,
    1056071655, 11231766159, 528037419, 1639245, 42040917, 8338178475,
    8338178475, 42040917, 84694325, 54563702175, 580307918215, 27281933315,
    84694325, 33755115, 1321005077, 1321005077, 33755115, 1639245,
    1056071655, 11231766159, 528037419, 1639245, 33755115, 1321005077,
    1321005077, 33755115, 3995738149, 14372551297, 1997869741, 46585881,
    9239603175, 9239603175, 46585881, 43166785
  ]
def negativeCoefficients : Array ℕ := #[
    286678149325005603516406824960, 19226530546154849585804083200, 19226530546154849585804083200, 21305074388982400892377497600, 796286635379844367054274560, 256500933319904527498157752320,
    2727995291772525788569425412096, 256501706413725284628611203072, 796286635379844367054274560, 85994275944181928580234608640, 3365382553583458277838523727872, 3365382553583458277838523727872,
    85994275944181928580234608640, 205345382107763774253650935808, 745330816469323984948196016128, 205345369620569755573716779008, 4850286905388309996141281280, 189815784272237738231746002944,
    189815784272237738231746002944, 4850286905388309996141281280, 94215926650770212492186484736, 338891886376857845397201092608, 94215958081716271084048744448, 9903519133691421481781690368,
    9903521494874662916604297216, 96939754565383142699433984, 19226530546154849585804083200, 19226530546154849585804083200, 96939754565383142699433984, 30238732989108013938769920,
    9740541771641944082208522240, 103594757915412371717826281472, 9740571129635137390959919104, 30238732989108013938769920, 96939754565383142699433984, 19226530546154849585804083200,
    19226530546154849585804083200, 96939754565383142699433984, 781167268885290360084889600, 251630662434083555457053491200, 2676197912814819602710512271360, 251631420848907715933131243520,
    781167268885290360084889600, 4981375740669075131172126720, 194945940603919839265036435456, 194945940603919839265036435456, 4981375740669075131172126720, 30238732989108013938769920,
    9740541771641944082208522240, 103594757915412371717826281472, 9740571129635137390959919104, 30238732989108013938769920, 4981375740669075131172126720, 194945940603919839265036435456,
    194945940603919839265036435456, 4981375740669075131172126720, 4606772438760057708608487424, 16570423466376329979989327872, 4606773975604423349535506432, 107419728031911050018291712,
    21305074388982400892377497600, 21305074388982400892377497600, 107419728031911050018291712, 796286635379844367054274560
  ]
def negativeScales : Array ℕ := #[
    44, 32, 32, 33, 25, 34,
    38, 33, 25, 26, 31, 31,
    26, 44, 51, 49, 25, 31,
    31, 25, 35, 37, 34, 22,
    23, 25, 32, 32, 25, 20,
    29, 33, 28, 20, 25, 32,
    32, 25, 26, 35, 39, 34,
    26, 25, 30, 30, 25, 20,
    29, 33, 28, 20, 25, 30,
    30, 25, 31, 33, 30, 25,
    33, 33, 25, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    44855346699869546, 32957085118451481, 32957085118451481, 33105183745697582, 25363418311162450, 34694878827117496,
    38105684001048099, 33694883175393847, 25363418311162450, 26118227289430903, 31408613356445470, 31408613356445470,
    26118227289430903, 44373967255490025, 51233795662336602, 49373967167758744, 25970128665027614, 31260514717456327,
    31260514717456327, 25970128665027614, 35249957616449446, 37096739848502321, 34249958097740285, 22999999851693669,
    23000000171982641, 25325290802039798, 32957085118451481, 32957085118451481, 25325290802039798, 20644600063725062,
    29976060595677288, 33386865753592156, 28976064943954778, 20644600063725062, 25325290802039798, 32957085118451481,
    32957085118451481, 25325290802039798, 26335761968259584, 35667222484183314, 39078027658145234, 34667226832459661,
    26335761968259584, 25008602798256405, 30298988865270963, 30298988865270963, 25008602798256405, 20644600063725062,
    29976060595677288, 33386865753592156, 28976064943954778, 20644600063725062, 25008602798256405, 30298988865270963,
    30298988865270963, 25008602798256405, 31895814900748032, 33742597128940913, 30895815382038907, 25473389441029040,
    33105183745697582, 33105183745697582, 25473389441029040, 25363418311162450
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
noncomputable def negativeCeiling : ℝ := 903887521 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 286678149325005603516406824960, coefficient := (-286678149325005603516406824960) }, { argument := 19226530546154849585804083200, coefficient := (-19226530546154849585804083200) }, { argument := 19226530546154849585804083200, coefficient := (-19226530546154849585804083200) }, { argument := 21305074388982400892377497600, coefficient := (-21305074388982400892377497600) }, { argument := 796286635379844367054274560, coefficient := (-796286635379844367054274560) }, { argument := 256500933319904527498157752320, coefficient := (-256500933319904527498157752320) }, { argument := 2727995291772525788569425412096, coefficient := (-2727995291772525788569425412096) }, { argument := 256501706413725284628611203072, coefficient := (-256501706413725284628611203072) }, { argument := 796286635379844367054274560, coefficient := (-796286635379844367054274560) }, { argument := 85994275944181928580234608640, coefficient := (-85994275944181928580234608640) }, { argument := 3365382553583458277838523727872, coefficient := (-3365382553583458277838523727872) }, { argument := 3365382553583458277838523727872, coefficient := (-3365382553583458277838523727872) }, { argument := 85994275944181928580234608640, coefficient := (-85994275944181928580234608640) }, { argument := 205345382107763774253650935808, coefficient := (-205345382107763774253650935808) }, { argument := 745330816469323984948196016128, coefficient := (-745330816469323984948196016128) }, { argument := 205345369620569755573716779008, coefficient := (-205345369620569755573716779008) }, { argument := 4850286905388309996141281280, coefficient := (-4850286905388309996141281280) }, { argument := 189815784272237738231746002944, coefficient := (-189815784272237738231746002944) }, { argument := 189815784272237738231746002944, coefficient := (-189815784272237738231746002944) }, { argument := 4850286905388309996141281280, coefficient := (-4850286905388309996141281280) }, { argument := 94215926650770212492186484736, coefficient := (-94215926650770212492186484736) }, { argument := 338891886376857845397201092608, coefficient := (-338891886376857845397201092608) }, { argument := 94215958081716271084048744448, coefficient := (-94215958081716271084048744448) }, { argument := 9903519133691421481781690368, coefficient := (-9903519133691421481781690368) }, { argument := 9903521494874662916604297216, coefficient := (-9903521494874662916604297216) }, { argument := 96939754565383142699433984, coefficient := (-96939754565383142699433984) }, { argument := 19226530546154849585804083200, coefficient := (-19226530546154849585804083200) }, { argument := 19226530546154849585804083200, coefficient := (-19226530546154849585804083200) }, { argument := 96939754565383142699433984, coefficient := (-96939754565383142699433984) }, { argument := 30238732989108013938769920, coefficient := (-30238732989108013938769920) }, { argument := 9740541771641944082208522240, coefficient := (-9740541771641944082208522240) }, { argument := 103594757915412371717826281472, coefficient := (-103594757915412371717826281472) }, { argument := 9740571129635137390959919104, coefficient := (-9740571129635137390959919104) }, { argument := 30238732989108013938769920, coefficient := (-30238732989108013938769920) }, { argument := 96939754565383142699433984, coefficient := (-96939754565383142699433984) }, { argument := 19226530546154849585804083200, coefficient := (-19226530546154849585804083200) }, { argument := 19226530546154849585804083200, coefficient := (-19226530546154849585804083200) }, { argument := 96939754565383142699433984, coefficient := (-96939754565383142699433984) }, { argument := 781167268885290360084889600, coefficient := (-781167268885290360084889600) }, { argument := 251630662434083555457053491200, coefficient := (-251630662434083555457053491200) }, { argument := 2676197912814819602710512271360, coefficient := (-2676197912814819602710512271360) }, { argument := 251631420848907715933131243520, coefficient := (-251631420848907715933131243520) }, { argument := 781167268885290360084889600, coefficient := (-781167268885290360084889600) }, { argument := 4981375740669075131172126720, coefficient := (-4981375740669075131172126720) }, { argument := 194945940603919839265036435456, coefficient := (-194945940603919839265036435456) }, { argument := 194945940603919839265036435456, coefficient := (-194945940603919839265036435456) }, { argument := 4981375740669075131172126720, coefficient := (-4981375740669075131172126720) }, { argument := 30238732989108013938769920, coefficient := (-30238732989108013938769920) }, { argument := 9740541771641944082208522240, coefficient := (-9740541771641944082208522240) }, { argument := 103594757915412371717826281472, coefficient := (-103594757915412371717826281472) }, { argument := 9740571129635137390959919104, coefficient := (-9740571129635137390959919104) }, { argument := 30238732989108013938769920, coefficient := (-30238732989108013938769920) }, { argument := 4981375740669075131172126720, coefficient := (-4981375740669075131172126720) }, { argument := 194945940603919839265036435456, coefficient := (-194945940603919839265036435456) }, { argument := 194945940603919839265036435456, coefficient := (-194945940603919839265036435456) }, { argument := 4981375740669075131172126720, coefficient := (-4981375740669075131172126720) }, { argument := 4606772438760057708608487424, coefficient := (-4606772438760057708608487424) }, { argument := 16570423466376329979989327872, coefficient := (-16570423466376329979989327872) }, { argument := 4606773975604423349535506432, coefficient := (-4606773975604423349535506432) }, { argument := 107419728031911050018291712, coefficient := (-107419728031911050018291712) }, { argument := 21305074388982400892377497600, coefficient := (-21305074388982400892377497600) }, { argument := 21305074388982400892377497600, coefficient := (-21305074388982400892377497600) }, { argument := 107419728031911050018291712, coefficient := (-107419728031911050018291712) }, { argument := 796286635379844367054274560, coefficient := (-796286635379844367054274560) }] }

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

end TermShard5


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16
