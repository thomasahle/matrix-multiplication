import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 21, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk21

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4117754805786247226284226625142784)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1529515, 77316171, 637, 589156911, 21, 49,
    637, 637, 21, 7861, 315, 38658087,
    637, 49, 315, 49, 637, 637,
    1758861, 2761610099, 17930653875, 5452772104413, 282171868875, 8493467625,
    5452706464969, 8493467625, 8493467625, 727607059875, 8493467625, 282171868875,
    727607059875, 44202171445, 8493467625, 8493467625, 17930653875, 14573356327403889,
    515330025, 28951125, 26468943951176707, 1565290825, 14573353922672265, 1565290825,
    1565290825, 515330025, 28951125, 45698811, 1656140037, 13249125165,
    365585619, 4225706205, 7253055267, 4225706205, 1397505819, 45698811,
    2795011407, 45698811, 237399225, 407475015, 237399225, 18408804645,
    18408795867, 1529515, 1380804937, 17930645325
  ]
def negativeCoefficients : Array ℕ := #[
    7222930371046365399026237440, 365115294514218060051451478016, 197141951256196808777685532672, 2782214849657414589767070253056, 103986963299971943091526434816, 7582382740622954183757135872,
    197141951256196808777685532672, 197141951256196808777685532672, 103986963299971943091526434816, 2432861662205593585245503881216, 194975556187447393296612065280, 365115308681317508660387119104,
    197141951256196808777685532672, 7582382740622954183757135872, 194975556187447393296612065280, 7582382740622954183757135872, 197141951256196808777685532672, 197141951256196808777685532672,
    8305986234426587050206560256, 407541717820997585084058959872, 82690545776598364326985728000, 12573236437796158519064370610176, 650644031242181866678124544000, 78338411788356345151881216000,
    12573085083543082445316175167488, 78338411788356345151881216000, 78338411788356345151881216000, 3355495304934596784005578752000, 78338411788356345151881216000, 650644031242181866678124544000,
    3355495304934596784005578752000, 407693072074073658832254402560, 78338411788356345151881216000, 78338411788356345151881216000, 82690545776598364326985728000, 4102035132852100912789202141184,
    152098577354773521232193126400, 8544863896335591080460288000, 14900690764426245214302931779584, 230996153997605478875109785600, 4102034455980323052011221155840, 230996153997605478875109785600,
    230996153997605478875109785600, 152098577354773521232193126400, 8544863896335591080460288000, 3371977083959291472777314304, 122201565651051470162302599168, 122201610559649917608206008320,
    3371932175360844026873905152, 155901041788642859262997954560, 535181017051280398306548645888, 155901041788642859262997954560, 412470914953805812787853656064, 3371977083959291472777314304,
    412470880864222764572602269696, 3371977083959291472777314304, 8758485493743980857471795200, 30066349272543842601491496960, 8758485493743980857471795200, 84895626997307654042372014080,
    84895586515927784286760992768, 7222930371046365399026237440, 407541684616858252406866051072, 82690506346682906772819148800
  ]
def negativeScales : Array ℕ := #[
    20, 26, 9, 29, 4, 5,
    9, 9, 4, 12, 8, 25,
    9, 5, 8, 5, 9, 9,
    20, 31, 34, 42, 38, 32,
    42, 32, 32, 39, 32, 38,
    39, 35, 32, 32, 34, 53,
    28, 24, 54, 30, 53, 30,
    30, 28, 24, 25, 30, 33,
    28, 31, 32, 31, 30, 25,
    31, 25, 27, 28, 27, 34,
    34, 20, 30, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    20544642824844825, 26204266855613552, 9315149562256301, 29134076679357578, 4392317422778766, 5614709844123661,
    9315149562256301, 9315149562256301, 4392317422778766, 12940497143328889, 8299208018387279, 25204266911592593,
    9315149562256301, 5614709844123661, 8299208018387279, 5614709844123661, 9315149562256301, 9315149562256301,
    20746210042941097, 31362862499452449, 34061709048625884, 42310126998726152, 38037783209380403, 32983706554840414,
    42310109631730335, 32983706554840414, 32983706554840414, 39404368585097340, 32983706554840414, 38037783209380403,
    39404368585097340, 35363398193060096, 32983706554840414, 32983706554840414, 34061709048625884, 53694182694858246,
    28940921419629758, 24787116075111205, 54555150154030280, 30543783583225410, 53694182456800890, 30543783583225410,
    30543783583225410, 28940921419629758, 24787116075111205, 25445653293680507, 30625177520882823, 33625178051067523,
    28445634079480024, 31976545336633367, 32755941696272846, 31976545336633367, 30380207144228229, 25445653293680507,
    31380207024993460, 25445653293680507, 27822739985366182, 28602136359943887, 27822739985366182, 34099676898824904,
    34099676210894301, 20544642824844825, 30362862381910006, 34061708360695280
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
noncomputable def negativeCeiling : ℝ := 17698191911 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7222930371046365399026237440, coefficient := (-7222930371046365399026237440) }, { argument := 365115294514218060051451478016, coefficient := (-365115294514218060051451478016) }, { argument := 197141951256196808777685532672, coefficient := (-197141951256196808777685532672) }, { argument := 2782214849657414589767070253056, coefficient := (-2782214849657414589767070253056) }, { argument := 103986963299971943091526434816, coefficient := (-103986963299971943091526434816) }, { argument := 7582382740622954183757135872, coefficient := (-7582382740622954183757135872) }, { argument := 197141951256196808777685532672, coefficient := (-197141951256196808777685532672) }, { argument := 197141951256196808777685532672, coefficient := (-197141951256196808777685532672) }, { argument := 103986963299971943091526434816, coefficient := (-103986963299971943091526434816) }, { argument := 2432861662205593585245503881216, coefficient := (-2432861662205593585245503881216) }, { argument := 194975556187447393296612065280, coefficient := (-194975556187447393296612065280) }, { argument := 365115308681317508660387119104, coefficient := (-365115308681317508660387119104) }, { argument := 197141951256196808777685532672, coefficient := (-197141951256196808777685532672) }, { argument := 7582382740622954183757135872, coefficient := (-7582382740622954183757135872) }, { argument := 194975556187447393296612065280, coefficient := (-194975556187447393296612065280) }, { argument := 7582382740622954183757135872, coefficient := (-7582382740622954183757135872) }, { argument := 197141951256196808777685532672, coefficient := (-197141951256196808777685532672) }, { argument := 197141951256196808777685532672, coefficient := (-197141951256196808777685532672) }, { argument := 8305986234426587050206560256, coefficient := (-8305986234426587050206560256) }, { argument := 407541717820997585084058959872, coefficient := (-407541717820997585084058959872) }, { argument := 82690545776598364326985728000, coefficient := (-82690545776598364326985728000) }, { argument := 12573236437796158519064370610176, coefficient := (-12573236437796158519064370610176) }, { argument := 650644031242181866678124544000, coefficient := (-650644031242181866678124544000) }, { argument := 78338411788356345151881216000, coefficient := (-78338411788356345151881216000) }, { argument := 12573085083543082445316175167488, coefficient := (-12573085083543082445316175167488) }, { argument := 78338411788356345151881216000, coefficient := (-78338411788356345151881216000) }, { argument := 78338411788356345151881216000, coefficient := (-78338411788356345151881216000) }, { argument := 3355495304934596784005578752000, coefficient := (-3355495304934596784005578752000) }, { argument := 78338411788356345151881216000, coefficient := (-78338411788356345151881216000) }, { argument := 650644031242181866678124544000, coefficient := (-650644031242181866678124544000) }, { argument := 3355495304934596784005578752000, coefficient := (-3355495304934596784005578752000) }, { argument := 407693072074073658832254402560, coefficient := (-407693072074073658832254402560) }, { argument := 78338411788356345151881216000, coefficient := (-78338411788356345151881216000) }, { argument := 78338411788356345151881216000, coefficient := (-78338411788356345151881216000) }, { argument := 82690545776598364326985728000, coefficient := (-82690545776598364326985728000) }, { argument := 4102035132852100912789202141184, coefficient := (-4102035132852100912789202141184) }, { argument := 152098577354773521232193126400, coefficient := (-152098577354773521232193126400) }, { argument := 8544863896335591080460288000, coefficient := (-8544863896335591080460288000) }, { argument := 14900690764426245214302931779584, coefficient := (-14900690764426245214302931779584) }, { argument := 230996153997605478875109785600, coefficient := (-230996153997605478875109785600) }, { argument := 4102034455980323052011221155840, coefficient := (-4102034455980323052011221155840) }, { argument := 230996153997605478875109785600, coefficient := (-230996153997605478875109785600) }, { argument := 230996153997605478875109785600, coefficient := (-230996153997605478875109785600) }, { argument := 152098577354773521232193126400, coefficient := (-152098577354773521232193126400) }, { argument := 8544863896335591080460288000, coefficient := (-8544863896335591080460288000) }, { argument := 3371977083959291472777314304, coefficient := (-3371977083959291472777314304) }, { argument := 122201565651051470162302599168, coefficient := (-122201565651051470162302599168) }, { argument := 122201610559649917608206008320, coefficient := (-122201610559649917608206008320) }, { argument := 3371932175360844026873905152, coefficient := (-3371932175360844026873905152) }, { argument := 155901041788642859262997954560, coefficient := (-155901041788642859262997954560) }, { argument := 535181017051280398306548645888, coefficient := (-535181017051280398306548645888) }, { argument := 155901041788642859262997954560, coefficient := (-155901041788642859262997954560) }, { argument := 412470914953805812787853656064, coefficient := (-412470914953805812787853656064) }, { argument := 3371977083959291472777314304, coefficient := (-3371977083959291472777314304) }, { argument := 412470880864222764572602269696, coefficient := (-412470880864222764572602269696) }, { argument := 3371977083959291472777314304, coefficient := (-3371977083959291472777314304) }, { argument := 8758485493743980857471795200, coefficient := (-8758485493743980857471795200) }, { argument := 30066349272543842601491496960, coefficient := (-30066349272543842601491496960) }, { argument := 8758485493743980857471795200, coefficient := (-8758485493743980857471795200) }, { argument := 84895626997307654042372014080, coefficient := (-84895626997307654042372014080) }, { argument := 84895586515927784286760992768, coefficient := (-84895586515927784286760992768) }, { argument := 7222930371046365399026237440, coefficient := (-7222930371046365399026237440) }, { argument := 407541684616858252406866051072, coefficient := (-407541684616858252406866051072) }, { argument := 82690506346682906772819148800, coefficient := (-82690506346682906772819148800) }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-11333605593788792403557718694035456)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5452772091363, 282171734325, 8493463575, 5452706451919, 8493463575, 8493463575,
    727606712925, 8493463575, 282171734325, 727606712925, 44202167845, 8493463575,
    8493463575, 17930645325, 52944623147964419, 884518935, 49692075, 96084217041149205,
    2686684855, 52944614401437139, 2686684855, 2686684855, 884518935, 49692075,
    5503709129099, 1656140037, 5503709115701, 1656140037, 12835384765, 22030815811,
    12835384765, 289696452045, 289696313907, 77316171, 8719960095, 8719955937,
    637, 3643338476947875, 515330025, 28951125, 3308617443856349, 1565290825,
    3643337875764969, 1565290825, 1565290825, 515330025, 28951125, 5503639061879,
    13249125165, 5503639048481, 13249125165, 589156911, 8719960095, 8719955937,
    21, 49, 45698811, 1656140037, 13249125165, 365585619,
    12835384765, 22030815811, 12835384765, 8719960095
  ]
def negativeCoefficients : Array ℕ := #[
    12573236407704907248825664536576, 650643720991004976975603302400, 78338374433699595890039193600, 12573085053451831175077469093888, 78338374433699595890039193600, 78338374433699595890039193600,
    3355493704910132690623345459200, 78338374433699595890039193600, 650643720991004976975603302400, 3355493704910132690623345459200, 407693038869934326155061493760, 78338374433699595890039193600,
    78338374433699595890039193600, 82690506346682906772819148800, 14902586567527743394718746148864, 522127821513444291030779166720, 29333023680530578147796582400, 54090605507838177670778018856960,
    792969406830343295928767610880, 14902584105599180957601375453184, 792969406830343295928767610880, 792969406830343295928767610880, 522127821513444291030779166720, 29333023680530578147796582400,
    12690689220078516973346643509248, 122201565651051470162302599168, 12690689189184832335901571940352, 122201565651051470162302599168, 236771057847545615846987530240, 812793642001101878326986801152,
    236771057847545615846987530240, 667994538741973383122874531840, 667994220217431776361619390464, 365115294514218060051451478016, 80427436102712514355931381760, 80427397751931585113773572096,
    197141951256196808777685532672, 4102034451791760070199476224000, 152098577354773521232193126400, 8544863896335591080460288000, 14900688287262976326460824879104, 230996153997605478875109785600,
    4102033774919982209421495238656, 230996153997605478875109785600, 230996153997605478875109785600, 152098577354773521232193126400, 8544863896335591080460288000, 12690527656069104935425496055808,
    122201610559649917608206008320, 12690527625175420297980424486912, 122201610559649917608206008320, 2782214849657414589767070253056, 80427436102712514355931381760, 80427397751931585113773572096,
    103986963299971943091526434816, 7582382740622954183757135872, 3371977083959291472777314304, 122201565651051470162302599168, 122201610559649917608206008320, 3371932175360844026873905152,
    236771057847545615846987530240, 812793642001101878326986801152, 236771057847545615846987530240, 80427436102712514355931381760
  ]
def negativeScales : Array ℕ := #[
    42, 38, 32, 42, 32, 32,
    39, 32, 38, 39, 35, 32,
    32, 34, 55, 29, 25, 56,
    31, 55, 31, 31, 29, 25,
    42, 30, 42, 30, 33, 34,
    33, 38, 38, 26, 33, 33,
    9, 51, 28, 24, 51, 30,
    51, 30, 30, 28, 24, 42,
    33, 42, 33, 29, 33, 33,
    4, 5, 25, 30, 33, 28,
    33, 34, 33, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    42310126995273381, 38037782521449800, 32983705866909607, 42310109628277523, 32983705866909607, 32983705866909607,
    39404367897166737, 32983705866909607, 38037782521449800, 39404367897166737, 35363398075561291, 32983705866909607,
    32983705866909607, 34061708360695280, 55555333695303704, 29720317786402106, 25566512450209344, 56415148989087766,
    31323179958815922, 55555333456968405, 31323179958815922, 31323179958815922, 29720317786402106, 25566512450209344,
    42323541364303341, 30625177520882823, 42323541360791304, 30625177520882823, 33579407492958196, 34358803868546644,
    33579407492958196, 38075751059579424, 38075750371648820, 26204266855613552, 33021674386823631, 33021673698893028,
    9315149562256301, 51694182455327762, 28940921419629758, 24787116075111205, 51555149914189623, 30543783583225410,
    51694182217270367, 30543783583225410, 30543783583225410, 28940921419629758, 24787116075111205, 42323522997367169,
    33625178051067523, 42323522993855087, 33625178051067523, 29134076679357578, 33021674386823631, 33021673698893028,
    4392317422778766, 5614709844123661, 25445653293680507, 30625177520882823, 33625178051067523, 28445634079480024,
    33579407492958196, 34358803868546644, 33579407492958196, 33021674386823631
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
noncomputable def negativeCeiling : ℝ := 118741855413 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 12573236407704907248825664536576, coefficient := (-12573236407704907248825664536576) }, { argument := 650643720991004976975603302400, coefficient := (-650643720991004976975603302400) }, { argument := 78338374433699595890039193600, coefficient := (-78338374433699595890039193600) }, { argument := 12573085053451831175077469093888, coefficient := (-12573085053451831175077469093888) }, { argument := 78338374433699595890039193600, coefficient := (-78338374433699595890039193600) }, { argument := 78338374433699595890039193600, coefficient := (-78338374433699595890039193600) }, { argument := 3355493704910132690623345459200, coefficient := (-3355493704910132690623345459200) }, { argument := 78338374433699595890039193600, coefficient := (-78338374433699595890039193600) }, { argument := 650643720991004976975603302400, coefficient := (-650643720991004976975603302400) }, { argument := 3355493704910132690623345459200, coefficient := (-3355493704910132690623345459200) }, { argument := 407693038869934326155061493760, coefficient := (-407693038869934326155061493760) }, { argument := 78338374433699595890039193600, coefficient := (-78338374433699595890039193600) }, { argument := 78338374433699595890039193600, coefficient := (-78338374433699595890039193600) }, { argument := 82690506346682906772819148800, coefficient := (-82690506346682906772819148800) }, { argument := 14902586567527743394718746148864, coefficient := (-14902586567527743394718746148864) }, { argument := 522127821513444291030779166720, coefficient := (-522127821513444291030779166720) }, { argument := 29333023680530578147796582400, coefficient := (-29333023680530578147796582400) }, { argument := 54090605507838177670778018856960, coefficient := (-54090605507838177670778018856960) }, { argument := 792969406830343295928767610880, coefficient := (-792969406830343295928767610880) }, { argument := 14902584105599180957601375453184, coefficient := (-14902584105599180957601375453184) }, { argument := 792969406830343295928767610880, coefficient := (-792969406830343295928767610880) }, { argument := 792969406830343295928767610880, coefficient := (-792969406830343295928767610880) }, { argument := 522127821513444291030779166720, coefficient := (-522127821513444291030779166720) }, { argument := 29333023680530578147796582400, coefficient := (-29333023680530578147796582400) }, { argument := 12690689220078516973346643509248, coefficient := (-12690689220078516973346643509248) }, { argument := 122201565651051470162302599168, coefficient := (-122201565651051470162302599168) }, { argument := 12690689189184832335901571940352, coefficient := (-12690689189184832335901571940352) }, { argument := 122201565651051470162302599168, coefficient := (-122201565651051470162302599168) }, { argument := 236771057847545615846987530240, coefficient := (-236771057847545615846987530240) }, { argument := 812793642001101878326986801152, coefficient := (-812793642001101878326986801152) }, { argument := 236771057847545615846987530240, coefficient := (-236771057847545615846987530240) }, { argument := 667994538741973383122874531840, coefficient := (-667994538741973383122874531840) }, { argument := 667994220217431776361619390464, coefficient := (-667994220217431776361619390464) }, { argument := 365115294514218060051451478016, coefficient := (-365115294514218060051451478016) }, { argument := 80427436102712514355931381760, coefficient := (-80427436102712514355931381760) }, { argument := 80427397751931585113773572096, coefficient := (-80427397751931585113773572096) }, { argument := 197141951256196808777685532672, coefficient := (-197141951256196808777685532672) }, { argument := 4102034451791760070199476224000, coefficient := (-4102034451791760070199476224000) }, { argument := 152098577354773521232193126400, coefficient := (-152098577354773521232193126400) }, { argument := 8544863896335591080460288000, coefficient := (-8544863896335591080460288000) }, { argument := 14900688287262976326460824879104, coefficient := (-14900688287262976326460824879104) }, { argument := 230996153997605478875109785600, coefficient := (-230996153997605478875109785600) }, { argument := 4102033774919982209421495238656, coefficient := (-4102033774919982209421495238656) }, { argument := 230996153997605478875109785600, coefficient := (-230996153997605478875109785600) }, { argument := 230996153997605478875109785600, coefficient := (-230996153997605478875109785600) }, { argument := 152098577354773521232193126400, coefficient := (-152098577354773521232193126400) }, { argument := 8544863896335591080460288000, coefficient := (-8544863896335591080460288000) }, { argument := 12690527656069104935425496055808, coefficient := (-12690527656069104935425496055808) }, { argument := 122201610559649917608206008320, coefficient := (-122201610559649917608206008320) }, { argument := 12690527625175420297980424486912, coefficient := (-12690527625175420297980424486912) }, { argument := 122201610559649917608206008320, coefficient := (-122201610559649917608206008320) }, { argument := 2782214849657414589767070253056, coefficient := (-2782214849657414589767070253056) }, { argument := 80427436102712514355931381760, coefficient := (-80427436102712514355931381760) }, { argument := 80427397751931585113773572096, coefficient := (-80427397751931585113773572096) }, { argument := 103986963299971943091526434816, coefficient := (-103986963299971943091526434816) }, { argument := 7582382740622954183757135872, coefficient := (-7582382740622954183757135872) }, { argument := 3371977083959291472777314304, coefficient := (-3371977083959291472777314304) }, { argument := 122201565651051470162302599168, coefficient := (-122201565651051470162302599168) }, { argument := 122201610559649917608206008320, coefficient := (-122201610559649917608206008320) }, { argument := 3371932175360844026873905152, coefficient := (-3371932175360844026873905152) }, { argument := 236771057847545615846987530240, coefficient := (-236771057847545615846987530240) }, { argument := 812793642001101878326986801152, coefficient := (-812793642001101878326986801152) }, { argument := 236771057847545615846987530240, coefficient := (-236771057847545615846987530240) }, { argument := 80427436102712514355931381760, coefficient := (-80427436102712514355931381760) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk21
