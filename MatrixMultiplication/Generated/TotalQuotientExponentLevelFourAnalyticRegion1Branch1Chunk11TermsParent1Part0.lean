import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 11, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1055815364912171988198104898732032)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    25165827, 15914798935, 63596247127, 31724683515, 63596247127, 2335525997531,
    123151591, 87693599945021, 3305469891, 162126311, 1652001041, 3316385909,
    293055883357, 123151591, 162126311, 136609010969, 9956169677543, 32614455,
    84320829, 70571733, 2002366335, 1244391897275, 70571733, 64943265,
    32976951, 32614455, 64218273, 2002366335, 64218273, 17076077253,
    84320829, 25165821, 58484368971, 233711051595, 116591364127, 233711051595,
    91377110246437, 77041855679, 3431457692700355, 64621447635, 792380429, 2018525669,
    8104261687, 11465779492259, 77041855679, 792380429, 37251986745933, 3688329110001075,
    837010035, 2159391825, 1806903945, 50654536155, 1843995082661955, 1806903945,
    1635332805, 838369395, 837010035, 1632614085, 50654536155, 1632614085,
    18625866796989, 2159391825, 219067, 163135
  ]
def negativeCoefficients : Array ℕ := #[
    118842257938495954999251566592, 73394055734622583389411082240, 73321480925009709261968637952, 73152139702579669631269601280, 73321480925009709261968637952, 2629568503048679390229561344,
    18173967051577220427256168448, 98734216008793481028099375104, 15243789280657401886449598464, 747675641657910422241542144, 15237020206414380000637616128, 15294130528244903584502644736,
    2639612734170633480798470144, 18173967051577220427256168448, 747675641657910422241542144, 307616145447720200345485312, 22419301024910043058655985664, 150407626122129213562552320,
    194430594080753312184926208, 2603637394978325592388141056, 4617142415444595590477905920, 22416971539482218147191193600, 2603637394978325592388141056, 149748973595762367953633280,
    152079343857065067968200704, 150407626122129213562552320, 148077255860826513547984896, 4617142415444595590477905920, 148077255860826513547984896, 307615260614242411795709952,
    194430594080753312184926208, 118842229604297057781380284416, 269711546680109259349278326784, 269450497248155843798205726720, 268841381906931207512369659904, 269450497248155843798205726720,
    102881479914011601279215730688, 710585697337089906881836613632, 3863477896545735187520573931520, 596027653097734184976336814080, 29233677965558364261767446528, 595763622756101727798022897664,
    597988964985834492509990944768, 103274560497699814452313980928, 710585697337089906881836613632, 29233677965558364261767446528, 41942008406948628662103048192, 4152689401355148630384495820800,
    15440109902771674377942466560, 19916874175317801592002969600, 266651957113529276793052200960, 467205632311876233650755338240, 4152307783574703753618354339840, 266651957113529276793052200960,
    15083282864588283899742781440, 15465185668795712194027192320, 15440109902771674377942466560, 15058207098564246083658055680, 467205632311876233650755338240, 15058207098564246083658055680,
    41941723383186077133960118272, 19916874175317801592002969600, 2069029316605609136057483264, 1540766512365879143872593920
  ]
def negativeScales : Array ℕ := #[
    24, 33, 35, 34, 35, 41,
    26, 46, 31, 27, 30, 31,
    38, 26, 27, 36, 43, 24,
    26, 26, 30, 40, 26, 25,
    24, 24, 25, 30, 25, 33,
    26, 24, 35, 37, 36, 37,
    46, 36, 51, 35, 29, 30,
    32, 43, 36, 29, 45, 51,
    29, 31, 30, 35, 50, 30,
    30, 29, 29, 30, 35, 30,
    44, 31, 17, 17
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    24584962672707506, 33889649882810021, 35888222585665459, 34884886724028741, 35888222585665459, 41086884643003025,
    26875860028102133, 46317536789267238, 31622208227462958, 27272542999670255, 30621567449860961, 31626964748831172,
    38092384844771938, 26875860028102133, 27272542999670255, 36991261713795772, 43178727956237676, 24959008197075949,
    26329385715108744, 26072587102285461, 30899058799157535, 40178578044709114, 26072587102285461, 25952676592554119,
    24974954695499376, 24959008197075949, 25936480540175077, 30899058799157535, 25936480540175077, 33991257563990411,
    26329385715108744, 24584962328742205, 35767332038489512, 37765935001152904, 36762669976741482, 37765935001152904,
    46376898052323530, 36164923402141294, 51607742990760795, 35911294024106140, 29561618006651087, 30910654792532207,
    32916033619375681, 43382399672308682, 36164923402141294, 29561618006651087, 45082382603864091, 51711888816749757,
    29640669678615245, 31007977900355233, 30750872668799005, 35559972418203732, 50711756231977311, 30750872668799005,
    30606937121070438, 29643010810811211, 29640669678615245, 30604536662985166, 35559972418203732, 30604536662985166,
    44082372799761198, 31007977900355233, 17741012649401125, 17315706814483911
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
noncomputable def negativeCeiling : ℝ := 10467500699 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 118842257938495954999251566592, coefficient := (-118842257938495954999251566592) }, { argument := 73394055734622583389411082240, coefficient := (-73394055734622583389411082240) }, { argument := 73321480925009709261968637952, coefficient := (-73321480925009709261968637952) }, { argument := 73152139702579669631269601280, coefficient := (-73152139702579669631269601280) }, { argument := 73321480925009709261968637952, coefficient := (-73321480925009709261968637952) }, { argument := 2629568503048679390229561344, coefficient := (-2629568503048679390229561344) }, { argument := 18173967051577220427256168448, coefficient := (-18173967051577220427256168448) }, { argument := 98734216008793481028099375104, coefficient := (-98734216008793481028099375104) }, { argument := 15243789280657401886449598464, coefficient := (-15243789280657401886449598464) }, { argument := 747675641657910422241542144, coefficient := (-747675641657910422241542144) }, { argument := 15237020206414380000637616128, coefficient := (-15237020206414380000637616128) }, { argument := 15294130528244903584502644736, coefficient := (-15294130528244903584502644736) }, { argument := 2639612734170633480798470144, coefficient := (-2639612734170633480798470144) }, { argument := 18173967051577220427256168448, coefficient := (-18173967051577220427256168448) }, { argument := 747675641657910422241542144, coefficient := (-747675641657910422241542144) }, { argument := 307616145447720200345485312, coefficient := (-307616145447720200345485312) }, { argument := 22419301024910043058655985664, coefficient := (-22419301024910043058655985664) }, { argument := 150407626122129213562552320, coefficient := (-150407626122129213562552320) }, { argument := 194430594080753312184926208, coefficient := (-194430594080753312184926208) }, { argument := 2603637394978325592388141056, coefficient := (-2603637394978325592388141056) }, { argument := 4617142415444595590477905920, coefficient := (-4617142415444595590477905920) }, { argument := 22416971539482218147191193600, coefficient := (-22416971539482218147191193600) }, { argument := 2603637394978325592388141056, coefficient := (-2603637394978325592388141056) }, { argument := 149748973595762367953633280, coefficient := (-149748973595762367953633280) }, { argument := 152079343857065067968200704, coefficient := (-152079343857065067968200704) }, { argument := 150407626122129213562552320, coefficient := (-150407626122129213562552320) }, { argument := 148077255860826513547984896, coefficient := (-148077255860826513547984896) }, { argument := 4617142415444595590477905920, coefficient := (-4617142415444595590477905920) }, { argument := 148077255860826513547984896, coefficient := (-148077255860826513547984896) }, { argument := 307615260614242411795709952, coefficient := (-307615260614242411795709952) }, { argument := 194430594080753312184926208, coefficient := (-194430594080753312184926208) }, { argument := 118842229604297057781380284416, coefficient := (-118842229604297057781380284416) }, { argument := 269711546680109259349278326784, coefficient := (-269711546680109259349278326784) }, { argument := 269450497248155843798205726720, coefficient := (-269450497248155843798205726720) }, { argument := 268841381906931207512369659904, coefficient := (-268841381906931207512369659904) }, { argument := 269450497248155843798205726720, coefficient := (-269450497248155843798205726720) }, { argument := 102881479914011601279215730688, coefficient := (-102881479914011601279215730688) }, { argument := 710585697337089906881836613632, coefficient := (-710585697337089906881836613632) }, { argument := 3863477896545735187520573931520, coefficient := (-3863477896545735187520573931520) }, { argument := 596027653097734184976336814080, coefficient := (-596027653097734184976336814080) }, { argument := 29233677965558364261767446528, coefficient := (-29233677965558364261767446528) }, { argument := 595763622756101727798022897664, coefficient := (-595763622756101727798022897664) }, { argument := 597988964985834492509990944768, coefficient := (-597988964985834492509990944768) }, { argument := 103274560497699814452313980928, coefficient := (-103274560497699814452313980928) }, { argument := 710585697337089906881836613632, coefficient := (-710585697337089906881836613632) }, { argument := 29233677965558364261767446528, coefficient := (-29233677965558364261767446528) }, { argument := 41942008406948628662103048192, coefficient := (-41942008406948628662103048192) }, { argument := 4152689401355148630384495820800, coefficient := (-4152689401355148630384495820800) }, { argument := 15440109902771674377942466560, coefficient := (-15440109902771674377942466560) }, { argument := 19916874175317801592002969600, coefficient := (-19916874175317801592002969600) }, { argument := 266651957113529276793052200960, coefficient := (-266651957113529276793052200960) }, { argument := 467205632311876233650755338240, coefficient := (-467205632311876233650755338240) }, { argument := 4152307783574703753618354339840, coefficient := (-4152307783574703753618354339840) }, { argument := 266651957113529276793052200960, coefficient := (-266651957113529276793052200960) }, { argument := 15083282864588283899742781440, coefficient := (-15083282864588283899742781440) }, { argument := 15465185668795712194027192320, coefficient := (-15465185668795712194027192320) }, { argument := 15440109902771674377942466560, coefficient := (-15440109902771674377942466560) }, { argument := 15058207098564246083658055680, coefficient := (-15058207098564246083658055680) }, { argument := 467205632311876233650755338240, coefficient := (-467205632311876233650755338240) }, { argument := 15058207098564246083658055680, coefficient := (-15058207098564246083658055680) }, { argument := 41941723383186077133960118272, coefficient := (-41941723383186077133960118272) }, { argument := 19916874175317801592002969600, coefficient := (-19916874175317801592002969600) }, { argument := 2069029316605609136057483264, coefficient := (-2069029316605609136057483264) }, { argument := 1540766512365879143872593920, coefficient := (-1540766512365879143872593920) }] }

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


end Parent1

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-5621144550045454220711992867422208)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    172457, 13983, 2997023, 5420743, 163135, 2997023,
    88559, 88559, 172457, 172457, 5420743, 172457,
    219067, 13983, 34289650769, 37589964484437, 107677, 1496596697544133,
    34075, 4089, 107677, 213991, 34075, 3302549,
    211265, 150360025577639, 107677, 4089, 211265, 4089,
    107677, 107677, 34289650769, 7956292911, 31793697327, 15860128627,
    31793697327, 91377114436645, 9630233497, 3431457770213059, 129242916339, 6339044455,
    64592831953, 129668207797, 11465780016035, 9630233497, 6339044455, 741116983331411,
    74846074386658733, 16205750781, 41793883263, 34970400903, 978332328213, 74839095425445091,
    34970400903, 31559282763, 16205932029, 16205750781, 31558920267, 978332328213,
    31558920267, 741111598576413, 41793883263, 69325
  ]
def negativeCoefficients : Array ℕ := #[
    1628810313072500809236742144, 2113051216958919968739557376, 28306081927178865414573654016, 51197470110900498409252192256, 1540766512365879143872593920, 28306081927178865414573654016,
    1672832213425811641918816256, 1672832213425811641918816256, 1628810313072500809236742144, 1628810313072500809236742144, 51197470110900498409252192256, 1628810313072500809236742144,
    2069029316605609136057483264, 2113051216958919968739557376, 308853716851865683228622848, 42322537511245162996656242688, 2033961023103819150700576768, 421254520586479517805731381248,
    1287317103230265285253529600, 77239026193815917115211776, 2033961023103819150700576768, 2021087852071516497848041472, 1287317103230265285253529600, 31191693411269327861693022208,
    1995341510006911192142970880, 42322584697679577998566621184, 2033961023103819150700576768, 77239026193815917115211776, 1995341510006911192142970880, 77239026193815917115211776,
    2033961023103819150700576768, 2033961023103819150700576768, 308853716851865683228622848, 73383849552343283497684697088, 73311274718519057773498466304, 73141933439595864417063927808,
    73311274718519057773498466304, 102881484631766398130433556480, 710585810756895844085014724608, 3863477983817281400240462626816, 596027750261346907222972563456, 29233682683313161112985272320,
    595763720016559856431633793024, 597989060931962105891796287488, 103274565215454611303531806720, 710585810756895844085014724608, 29233682683313161112985272320, 417211771246161084355006431232,
    42134594089737586861381513117696, 149471668589712843834075906048, 192740267099763516901794250752, 2580360142450649609567566036992, 4511761519395406429004394135552, 42130665283847437954415845179392,
    2580360142450649609567566036992, 145541503069723563445821898752, 149473340307447779688481554432, 149471668589712843834075906048, 145539831351988627591416250368, 4511761519395406429004394135552,
    145539831351988627591416250368, 417208739898585775078014713856, 192740267099763516901794250752, 1309512225699752617757900800
  ]
def negativeScales : Array ℕ := #[
    17, 13, 21, 22, 17, 21,
    16, 16, 17, 17, 22, 17,
    17, 13, 34, 45, 16, 50,
    15, 11, 16, 17, 15, 21,
    17, 47, 16, 11, 17, 11,
    16, 16, 34, 32, 34, 33,
    34, 46, 33, 51, 36, 32,
    35, 36, 43, 33, 32, 49,
    56, 33, 35, 35, 39, 56,
    35, 34, 33, 33, 34, 39,
    34, 49, 35, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    17395877163167900, 13771386298616460, 21515098724867337, 22370059179012165, 17315706814483911, 21515098724867337,
    16434351310982556, 16434351310982556, 17395877163167900, 17395877163167900, 22370059179012165, 17395877163167900,
    17741012649401125, 13771386298616460, 34997054182343884, 45095412785837343, 16716350595088157, 50410606920028495,
    15056426036579935, 11997532370288072, 16716350595088157, 17707190595782487, 15056426036579935, 21655148536280831,
    17688694252134803, 47095414394332508, 16716350595088157, 11997532370288072, 17688694252134803, 11997532370288072,
    16716350595088157, 16716350595088157, 34997054182343884, 32889449247577860, 34888021751351276, 33884685423653511,
    34888021751351276, 46376898118480056, 33164923632416375, 51607743023349625, 36911294259292315, 32561618239474371,
    35910655028057131, 36916033850853206, 43382399738213404, 33164923632416375, 32561618239474371, 49396694614478272,
    56054776168330265, 33915786814121328, 35282572761230853, 35025415284155884, 39831533660277811, 56054641639134708,
    35025415284155884, 34877345369855087, 33915802949390755, 33915786814121328, 34877328798685937, 39831533660277811,
    34877328798685937, 49396684132209306, 35282572761230853, 16081088090814204
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
noncomputable def negativeCeiling : ℝ := 68755935439 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 2113051216958919968739557376, coefficient := (-2113051216958919968739557376) }, { argument := 28306081927178865414573654016, coefficient := (-28306081927178865414573654016) }, { argument := 51197470110900498409252192256, coefficient := (-51197470110900498409252192256) }, { argument := 1540766512365879143872593920, coefficient := (-1540766512365879143872593920) }, { argument := 28306081927178865414573654016, coefficient := (-28306081927178865414573654016) }, { argument := 1672832213425811641918816256, coefficient := (-1672832213425811641918816256) }, { argument := 1672832213425811641918816256, coefficient := (-1672832213425811641918816256) }, { argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 51197470110900498409252192256, coefficient := (-51197470110900498409252192256) }, { argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 2069029316605609136057483264, coefficient := (-2069029316605609136057483264) }, { argument := 2113051216958919968739557376, coefficient := (-2113051216958919968739557376) }, { argument := 308853716851865683228622848, coefficient := (-308853716851865683228622848) }, { argument := 42322537511245162996656242688, coefficient := (-42322537511245162996656242688) }, { argument := 2033961023103819150700576768, coefficient := (-2033961023103819150700576768) }, { argument := 421254520586479517805731381248, coefficient := (-421254520586479517805731381248) }, { argument := 1287317103230265285253529600, coefficient := (-1287317103230265285253529600) }, { argument := 77239026193815917115211776, coefficient := (-77239026193815917115211776) }, { argument := 2033961023103819150700576768, coefficient := (-2033961023103819150700576768) }, { argument := 2021087852071516497848041472, coefficient := (-2021087852071516497848041472) }, { argument := 1287317103230265285253529600, coefficient := (-1287317103230265285253529600) }, { argument := 31191693411269327861693022208, coefficient := (-31191693411269327861693022208) }, { argument := 1995341510006911192142970880, coefficient := (-1995341510006911192142970880) }, { argument := 42322584697679577998566621184, coefficient := (-42322584697679577998566621184) }, { argument := 2033961023103819150700576768, coefficient := (-2033961023103819150700576768) }, { argument := 77239026193815917115211776, coefficient := (-77239026193815917115211776) }, { argument := 1995341510006911192142970880, coefficient := (-1995341510006911192142970880) }, { argument := 77239026193815917115211776, coefficient := (-77239026193815917115211776) }, { argument := 2033961023103819150700576768, coefficient := (-2033961023103819150700576768) }, { argument := 2033961023103819150700576768, coefficient := (-2033961023103819150700576768) }, { argument := 308853716851865683228622848, coefficient := (-308853716851865683228622848) }, { argument := 73383849552343283497684697088, coefficient := (-73383849552343283497684697088) }, { argument := 73311274718519057773498466304, coefficient := (-73311274718519057773498466304) }, { argument := 73141933439595864417063927808, coefficient := (-73141933439595864417063927808) }, { argument := 73311274718519057773498466304, coefficient := (-73311274718519057773498466304) }, { argument := 102881484631766398130433556480, coefficient := (-102881484631766398130433556480) }, { argument := 710585810756895844085014724608, coefficient := (-710585810756895844085014724608) }, { argument := 3863477983817281400240462626816, coefficient := (-3863477983817281400240462626816) }, { argument := 596027750261346907222972563456, coefficient := (-596027750261346907222972563456) }, { argument := 29233682683313161112985272320, coefficient := (-29233682683313161112985272320) }, { argument := 595763720016559856431633793024, coefficient := (-595763720016559856431633793024) }, { argument := 597989060931962105891796287488, coefficient := (-597989060931962105891796287488) }, { argument := 103274565215454611303531806720, coefficient := (-103274565215454611303531806720) }, { argument := 710585810756895844085014724608, coefficient := (-710585810756895844085014724608) }, { argument := 29233682683313161112985272320, coefficient := (-29233682683313161112985272320) }, { argument := 417211771246161084355006431232, coefficient := (-417211771246161084355006431232) }, { argument := 42134594089737586861381513117696, coefficient := (-42134594089737586861381513117696) }, { argument := 149471668589712843834075906048, coefficient := (-149471668589712843834075906048) }, { argument := 192740267099763516901794250752, coefficient := (-192740267099763516901794250752) }, { argument := 2580360142450649609567566036992, coefficient := (-2580360142450649609567566036992) }, { argument := 4511761519395406429004394135552, coefficient := (-4511761519395406429004394135552) }, { argument := 42130665283847437954415845179392, coefficient := (-42130665283847437954415845179392) }, { argument := 2580360142450649609567566036992, coefficient := (-2580360142450649609567566036992) }, { argument := 145541503069723563445821898752, coefficient := (-145541503069723563445821898752) }, { argument := 149473340307447779688481554432, coefficient := (-149473340307447779688481554432) }, { argument := 149471668589712843834075906048, coefficient := (-149471668589712843834075906048) }, { argument := 145539831351988627591416250368, coefficient := (-145539831351988627591416250368) }, { argument := 4511761519395406429004394135552, coefficient := (-4511761519395406429004394135552) }, { argument := 145539831351988627591416250368, coefficient := (-145539831351988627591416250368) }, { argument := 417208739898585775078014713856, coefficient := (-417208739898585775078014713856) }, { argument := 192740267099763516901794250752, coefficient := (-192740267099763516901794250752) }, { argument := 1309512225699752617757900800, coefficient := (-1309512225699752617757900800) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
