import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 4, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4

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
def constantNumerator : ℤ := (-827185937620745116568521994665984)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    18058858232195, 3507, 159476643235453, 5649, 175, 5649,
    3773, 18299376400771, 3507, 21, 14718628044641, 189803487178911,
    3077792865, 2726045109, 127596498489, 34735090905, 94901775468927, 127596498489,
    3077792865, 3077792865, 1319054085, 3077792865, 34735090905, 1319054085,
    7359282142849, 2726045109, 14048505, 1181328135, 590663925, 7024395,
    17050842842147, 1045827613243305, 1908453303, 8430777677121235, 1958347507, 62367755,
    1908453303, 1085198937, 1958347507, 30572673501, 37420653, 522914072861855,
    1908453303, 62367755, 37420653, 62367755, 960463427, 1085198937,
    17050842842147, 4584249, 385486023, 192742965, 2292171, 69760925,
    5151661775, 53694909125, 5151661775, 69760925, 17100029828409, 35417085,
    295190187533739, 876384465, 27881535, 295190310319245
  ]
def negativeCoefficients : Array ℕ := #[
    5083116700328126008178769920, 33917622795108036125556473856, 89777368881185457798524174336, 54633775640024321663321505792, 1692496147460480844588646400, 54633775640024321663321505792,
    36490216939247967009331216384, 5150816546226545241962315776, 33917622795108036125556473856, 1624796301562061610805100544, 66286807777250139764934311936, 854798914132564294652034809856,
    56775257292544292046074019840, 50286656459110658669379846144, 2353739952328050507395811508224, 640749332301571295948549652480, 854799201277316230988729155584, 2353739952328050507395811508224,
    56775257292544292046074019840, 56775257292544292046074019840, 48664506250752250325206302720, 56775257292544292046074019840, 640749332301571295948549652480, 48664506250752250325206302720,
    66286520632498203428239966208, 50286656459110658669379846144, 518298352706458008850268160, 43583315546835214284431032320, 43583305032191092269986611200, 518308867350580023294689280,
    4799385591890382384300818432, 294374303081020225352714158080, 70409499314133338488408375296, 2373052950320418111627628380160, 72250270538032249298562842624, 2300964029873638512693084160,
    70409499314133338488408375296, 40036774119801310120859664384, 72250270538032249298562842624, 1127932567444057598922149855232, 44178509373573859443707215872, 294374452960929821608388853760,
    70409499314133338488408375296, 2300964029873638512693084160, 44178509373573859443707215872, 2300964029873638512693084160, 70869692120108066190946992128, 40036774119801310120859664384,
    4799385591890382384300818432, 21141117018289734571524096, 1777740502568278477391265792, 1777740073681478763644190720, 21141545905089448318599168, 160857741227530812758425600,
    23757846579434319878134169600, 247624061672491668916404224000, 23757846579434319878134169600, 160857741227530812758425600, 4813230497702946190921826304, 163332475707954363723939840,
    166177302322546724254481645568, 4041609984007466489594511360, 128580885131793860803952640, 166177371444641607766706749440
  ]
def negativeScales : Array ℕ := #[
    44, 11, 47, 12, 7, 12,
    11, 44, 11, 4, 43, 47,
    31, 31, 36, 35, 46, 36,
    31, 31, 30, 31, 35, 30,
    42, 31, 23, 30, 29, 22,
    43, 49, 30, 52, 30, 25,
    30, 30, 30, 34, 25, 48,
    30, 25, 25, 25, 29, 30,
    43, 22, 28, 27, 21, 26,
    32, 35, 32, 26, 43, 25,
    48, 29, 24, 48
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    44037771915124045, 11776021715645854, 47180338472439226, 12463779785335462, 7451211111832378, 12463779785335462,
    11881496387932734, 44056859719266657, 11776021715645854, 4392317422778766, 43742708434644111, 47431499827049272,
    31519248995759208, 31344162289200608, 36892797786716831, 35015674821878198, 46431500311680491, 36892797786716831,
    31519248995759208, 31519248995759208, 30296856574422251, 31519248995759208, 35015674821878198, 30296856574422251,
    42742702185086732, 31344162289200608, 23743913275719710, 30137762608715976, 29137762260660153, 22743942543169723,
    43954908299892157, 49893566494832211, 30829756741551150, 52904587143344281, 30866989648966417, 25894296996516585,
    30829756741551150, 30015312393536242, 30866989648966417, 34831523667766544, 25157331398408670, 48893567229376498,
    30829756741551150, 25894296996516585, 25157331398408670, 25894296996516585, 29839155439788620, 30015312393536242,
    43954908299892157, 22128253977578882, 28522103310772461, 27522102962716638, 21128283245028767, 26055915833971809,
    32262390732464439, 35644066260039690, 32262390732464439, 26055915833971809, 43959064087350077, 25077942140301808,
    48068638093751943, 29706988670182637, 24732806654406840, 48068638693846428
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
noncomputable def negativeCeiling : ℝ := 6821272439 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5083116700328126008178769920, coefficient := (-5083116700328126008178769920) }, { argument := 33917622795108036125556473856, coefficient := (-33917622795108036125556473856) }, { argument := 89777368881185457798524174336, coefficient := (-89777368881185457798524174336) }, { argument := 54633775640024321663321505792, coefficient := (-54633775640024321663321505792) }, { argument := 1692496147460480844588646400, coefficient := (-1692496147460480844588646400) }, { argument := 54633775640024321663321505792, coefficient := (-54633775640024321663321505792) }, { argument := 36490216939247967009331216384, coefficient := (-36490216939247967009331216384) }, { argument := 5150816546226545241962315776, coefficient := (-5150816546226545241962315776) }, { argument := 33917622795108036125556473856, coefficient := (-33917622795108036125556473856) }, { argument := 1624796301562061610805100544, coefficient := (-1624796301562061610805100544) }, { argument := 66286807777250139764934311936, coefficient := (-66286807777250139764934311936) }, { argument := 854798914132564294652034809856, coefficient := (-854798914132564294652034809856) }, { argument := 56775257292544292046074019840, coefficient := (-56775257292544292046074019840) }, { argument := 50286656459110658669379846144, coefficient := (-50286656459110658669379846144) }, { argument := 2353739952328050507395811508224, coefficient := (-2353739952328050507395811508224) }, { argument := 640749332301571295948549652480, coefficient := (-640749332301571295948549652480) }, { argument := 854799201277316230988729155584, coefficient := (-854799201277316230988729155584) }, { argument := 2353739952328050507395811508224, coefficient := (-2353739952328050507395811508224) }, { argument := 56775257292544292046074019840, coefficient := (-56775257292544292046074019840) }, { argument := 56775257292544292046074019840, coefficient := (-56775257292544292046074019840) }, { argument := 48664506250752250325206302720, coefficient := (-48664506250752250325206302720) }, { argument := 56775257292544292046074019840, coefficient := (-56775257292544292046074019840) }, { argument := 640749332301571295948549652480, coefficient := (-640749332301571295948549652480) }, { argument := 48664506250752250325206302720, coefficient := (-48664506250752250325206302720) }, { argument := 66286520632498203428239966208, coefficient := (-66286520632498203428239966208) }, { argument := 50286656459110658669379846144, coefficient := (-50286656459110658669379846144) }, { argument := 518298352706458008850268160, coefficient := (-518298352706458008850268160) }, { argument := 43583315546835214284431032320, coefficient := (-43583315546835214284431032320) }, { argument := 43583305032191092269986611200, coefficient := (-43583305032191092269986611200) }, { argument := 518308867350580023294689280, coefficient := (-518308867350580023294689280) }, { argument := 4799385591890382384300818432, coefficient := (-4799385591890382384300818432) }, { argument := 294374303081020225352714158080, coefficient := (-294374303081020225352714158080) }, { argument := 70409499314133338488408375296, coefficient := (-70409499314133338488408375296) }, { argument := 2373052950320418111627628380160, coefficient := (-2373052950320418111627628380160) }, { argument := 72250270538032249298562842624, coefficient := (-72250270538032249298562842624) }, { argument := 2300964029873638512693084160, coefficient := (-2300964029873638512693084160) }, { argument := 70409499314133338488408375296, coefficient := (-70409499314133338488408375296) }, { argument := 40036774119801310120859664384, coefficient := (-40036774119801310120859664384) }, { argument := 72250270538032249298562842624, coefficient := (-72250270538032249298562842624) }, { argument := 1127932567444057598922149855232, coefficient := (-1127932567444057598922149855232) }, { argument := 44178509373573859443707215872, coefficient := (-44178509373573859443707215872) }, { argument := 294374452960929821608388853760, coefficient := (-294374452960929821608388853760) }, { argument := 70409499314133338488408375296, coefficient := (-70409499314133338488408375296) }, { argument := 2300964029873638512693084160, coefficient := (-2300964029873638512693084160) }, { argument := 44178509373573859443707215872, coefficient := (-44178509373573859443707215872) }, { argument := 2300964029873638512693084160, coefficient := (-2300964029873638512693084160) }, { argument := 70869692120108066190946992128, coefficient := (-70869692120108066190946992128) }, { argument := 40036774119801310120859664384, coefficient := (-40036774119801310120859664384) }, { argument := 4799385591890382384300818432, coefficient := (-4799385591890382384300818432) }, { argument := 21141117018289734571524096, coefficient := (-21141117018289734571524096) }, { argument := 1777740502568278477391265792, coefficient := (-1777740502568278477391265792) }, { argument := 1777740073681478763644190720, coefficient := (-1777740073681478763644190720) }, { argument := 21141545905089448318599168, coefficient := (-21141545905089448318599168) }, { argument := 160857741227530812758425600, coefficient := (-160857741227530812758425600) }, { argument := 23757846579434319878134169600, coefficient := (-23757846579434319878134169600) }, { argument := 247624061672491668916404224000, coefficient := (-247624061672491668916404224000) }, { argument := 23757846579434319878134169600, coefficient := (-23757846579434319878134169600) }, { argument := 160857741227530812758425600, coefficient := (-160857741227530812758425600) }, { argument := 4813230497702946190921826304, coefficient := (-4813230497702946190921826304) }, { argument := 163332475707954363723939840, coefficient := (-163332475707954363723939840) }, { argument := 166177302322546724254481645568, coefficient := (-166177302322546724254481645568) }, { argument := 4041609984007466489594511360, coefficient := (-4041609984007466489594511360) }, { argument := 128580885131793860803952640, coefficient := (-128580885131793860803952640) }, { argument := 166177371444641607766706749440, coefficient := (-166177371444641607766706749440) }] }

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
def constantNumerator : ℤ := (-10911649058509916190848302157135872)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    14317545, 14317545, 484535865, 26374425, 876384465, 484535865,
    17099841646167, 27881535, 26374425, 35417085, 18053411341949, 3507,
    159450263746947, 5649, 175, 5649, 3773, 18293929510525,
    3507, 21, 400276358480011, 5242657213923189, 5216443295, 4620278347,
    216258834887, 58871288615, 2621329472421141, 216258834887, 5216443295, 5216443295,
    2235618555, 5216443295, 58871288615, 2235618555, 200137313780459, 4620278347,
    294476258596457, 16988053112362235, 69162979401, 132157612831256185, 70971161869, 2260228085,
    69162979401, 39327968679, 70971161869, 1107963807267, 1356136851, 8494031215052765,
    69162979401, 2260228085, 1356136851, 2260228085, 34807512509, 39327968679,
    294476258596457, 46286127, 3892165329, 1946082195, 23143533, 1726211825,
    127476226475, 1328663389625, 127476226475, 1726211825
  ]
def negativeCoefficients : Array ℕ := #[
    132056044189409911095951360, 132056044189409911095951360, 2234527274047120337755176960, 121630567016561760219955200, 4041609984007466489594511360, 2234527274047120337755176960,
    4813177529110761881890455552, 128580885131793860803952640, 121630567016561760219955200, 163332475707954363723939840, 5081583537022987658848108544, 33917622795108036125556473856,
    89762518549359727063244734464, 54633775640024321663321505792, 1692496147460480844588646400, 54633775640024321663321505792, 36490216939247967009331216384, 5149283382921406892631654400,
    33917622795108036125556473856, 1624796301562061610805100544, 225335557361974577033413394432, 2951353634381964589272523603968, 192452788875766352609479229440, 170458184432821626596967317504,
    7978542761678199361038696054784, 2171967188740791693735551303680, 2951354608802787369682137513984, 7978542761678199361038696054784, 192452788875766352609479229440, 192452788875766352609479229440,
    164959533322085445093839339520, 192452788875766352609479229440, 2171967188740791693735551303680, 164959533322085445093839339520, 225334582941151796623799484416, 170458184432821626596967317504,
    165775396060557695578311491584, 9563423708323094545100512952320, 2551663560770985088148708524032, 74398121987627454453871510814720, 2618373719222514110061093060608, 83387698064411277390480670720,
    2551663560770985088148708524032, 1450945946320756226594363670528, 2618373719222514110061093060608, 40876649591174408176813624786944, 1601043802836696525897228877824, 9563428953746248457092711055360,
    2551663560770985088148708524032, 83387698064411277390480670720, 1601043802836696525897228877824, 83387698064411277390480670720, 2568341100383867343626804658176, 1450945946320756226594363670528,
    165775396060557695578311491584, 426914169466108833605615616, 35898888858314268607965560832, 35898880197567926001331077120, 426922830212451440240099328, 3980373469098262451873382400,
    587880331316640723792979558400, 6127378377129953424463364096000, 587880331316640723792979558400, 3980373469098262451873382400
  ]
def negativeScales : Array ℕ := #[
    23, 23, 28, 24, 29, 28,
    43, 24, 24, 25, 44, 11,
    47, 12, 7, 12, 11, 44,
    11, 4, 48, 52, 32, 32,
    37, 35, 51, 37, 32, 32,
    31, 32, 35, 31, 47, 32,
    48, 53, 36, 56, 36, 31,
    36, 35, 36, 40, 30, 52,
    36, 31, 30, 31, 35, 35,
    48, 25, 31, 30, 24, 30,
    36, 40, 36, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23771280802423319, 23771280802423319, 28852028217752524, 24652636305591918, 29706988670182637, 28852028217752524,
    43959048210703139, 24732806654406840, 24652636305591918, 25077942140301808, 44037336705612240, 11776021715645854,
    47180099812379492, 12463779785335462, 7451211111832378, 12463779785335462, 11881496387932734, 44056430230790090,
    11776021715645854, 4392317422778766, 48507989736777224, 52219219643026974, 32280419329445445, 32105332622887354,
    37653968116590785, 35776845155964859, 51219220119348022, 37653968116590785, 32280419329445445, 32280419329445445,
    31058026908108997, 32280419329445445, 35776845155964859, 31058026908108997, 47507983498103023, 32105332622887354,
    48065144653528580, 53915370048260663, 36009280967571339, 56875037148499261, 36046513873770314, 31073821219766050,
    36009280967571339, 35194836620727416, 36046513873770314, 40011047893745527, 30336855625599844, 52915370839561445,
    36009280967571339, 31073821219766050, 30336855625599844, 31073821219766050, 35018679665573589, 35194836620727416,
    48065144653528580, 25464076514124703, 31857925849331139, 30857925501275303, 24464105781574588, 30684962363818002,
    36891437266003043, 40273112789816965, 36891437266003043, 30684962363818002
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
noncomputable def negativeCeiling : ℝ := 27371023623 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 132056044189409911095951360, coefficient := (-132056044189409911095951360) }, { argument := 132056044189409911095951360, coefficient := (-132056044189409911095951360) }, { argument := 2234527274047120337755176960, coefficient := (-2234527274047120337755176960) }, { argument := 121630567016561760219955200, coefficient := (-121630567016561760219955200) }, { argument := 4041609984007466489594511360, coefficient := (-4041609984007466489594511360) }, { argument := 2234527274047120337755176960, coefficient := (-2234527274047120337755176960) }, { argument := 4813177529110761881890455552, coefficient := (-4813177529110761881890455552) }, { argument := 128580885131793860803952640, coefficient := (-128580885131793860803952640) }, { argument := 121630567016561760219955200, coefficient := (-121630567016561760219955200) }, { argument := 163332475707954363723939840, coefficient := (-163332475707954363723939840) }, { argument := 5081583537022987658848108544, coefficient := (-5081583537022987658848108544) }, { argument := 33917622795108036125556473856, coefficient := (-33917622795108036125556473856) }, { argument := 89762518549359727063244734464, coefficient := (-89762518549359727063244734464) }, { argument := 54633775640024321663321505792, coefficient := (-54633775640024321663321505792) }, { argument := 1692496147460480844588646400, coefficient := (-1692496147460480844588646400) }, { argument := 54633775640024321663321505792, coefficient := (-54633775640024321663321505792) }, { argument := 36490216939247967009331216384, coefficient := (-36490216939247967009331216384) }, { argument := 5149283382921406892631654400, coefficient := (-5149283382921406892631654400) }, { argument := 33917622795108036125556473856, coefficient := (-33917622795108036125556473856) }, { argument := 1624796301562061610805100544, coefficient := (-1624796301562061610805100544) }, { argument := 225335557361974577033413394432, coefficient := (-225335557361974577033413394432) }, { argument := 2951353634381964589272523603968, coefficient := (-2951353634381964589272523603968) }, { argument := 192452788875766352609479229440, coefficient := (-192452788875766352609479229440) }, { argument := 170458184432821626596967317504, coefficient := (-170458184432821626596967317504) }, { argument := 7978542761678199361038696054784, coefficient := (-7978542761678199361038696054784) }, { argument := 2171967188740791693735551303680, coefficient := (-2171967188740791693735551303680) }, { argument := 2951354608802787369682137513984, coefficient := (-2951354608802787369682137513984) }, { argument := 7978542761678199361038696054784, coefficient := (-7978542761678199361038696054784) }, { argument := 192452788875766352609479229440, coefficient := (-192452788875766352609479229440) }, { argument := 192452788875766352609479229440, coefficient := (-192452788875766352609479229440) }, { argument := 164959533322085445093839339520, coefficient := (-164959533322085445093839339520) }, { argument := 192452788875766352609479229440, coefficient := (-192452788875766352609479229440) }, { argument := 2171967188740791693735551303680, coefficient := (-2171967188740791693735551303680) }, { argument := 164959533322085445093839339520, coefficient := (-164959533322085445093839339520) }, { argument := 225334582941151796623799484416, coefficient := (-225334582941151796623799484416) }, { argument := 170458184432821626596967317504, coefficient := (-170458184432821626596967317504) }, { argument := 165775396060557695578311491584, coefficient := (-165775396060557695578311491584) }, { argument := 9563423708323094545100512952320, coefficient := (-9563423708323094545100512952320) }, { argument := 2551663560770985088148708524032, coefficient := (-2551663560770985088148708524032) }, { argument := 74398121987627454453871510814720, coefficient := (-74398121987627454453871510814720) }, { argument := 2618373719222514110061093060608, coefficient := (-2618373719222514110061093060608) }, { argument := 83387698064411277390480670720, coefficient := (-83387698064411277390480670720) }, { argument := 2551663560770985088148708524032, coefficient := (-2551663560770985088148708524032) }, { argument := 1450945946320756226594363670528, coefficient := (-1450945946320756226594363670528) }, { argument := 2618373719222514110061093060608, coefficient := (-2618373719222514110061093060608) }, { argument := 40876649591174408176813624786944, coefficient := (-40876649591174408176813624786944) }, { argument := 1601043802836696525897228877824, coefficient := (-1601043802836696525897228877824) }, { argument := 9563428953746248457092711055360, coefficient := (-9563428953746248457092711055360) }, { argument := 2551663560770985088148708524032, coefficient := (-2551663560770985088148708524032) }, { argument := 83387698064411277390480670720, coefficient := (-83387698064411277390480670720) }, { argument := 1601043802836696525897228877824, coefficient := (-1601043802836696525897228877824) }, { argument := 83387698064411277390480670720, coefficient := (-83387698064411277390480670720) }, { argument := 2568341100383867343626804658176, coefficient := (-2568341100383867343626804658176) }, { argument := 1450945946320756226594363670528, coefficient := (-1450945946320756226594363670528) }, { argument := 165775396060557695578311491584, coefficient := (-165775396060557695578311491584) }, { argument := 426914169466108833605615616, coefficient := (-426914169466108833605615616) }, { argument := 35898888858314268607965560832, coefficient := (-35898888858314268607965560832) }, { argument := 35898880197567926001331077120, coefficient := (-35898880197567926001331077120) }, { argument := 426922830212451440240099328, coefficient := (-426922830212451440240099328) }, { argument := 3980373469098262451873382400, coefficient := (-3980373469098262451873382400) }, { argument := 587880331316640723792979558400, coefficient := (-587880331316640723792979558400) }, { argument := 6127378377129953424463364096000, coefficient := (-6127378377129953424463364096000) }, { argument := 587880331316640723792979558400, coefficient := (-587880331316640723792979558400) }, { argument := 3980373469098262451873382400, coefficient := (-3980373469098262451873382400) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
