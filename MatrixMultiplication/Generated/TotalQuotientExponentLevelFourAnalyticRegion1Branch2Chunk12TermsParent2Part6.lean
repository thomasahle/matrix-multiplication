import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 6, for level-four region 1, branch 2,
parent chunk 12, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard12

/-! Directed signed-log shard 12.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3329094605130407180164639152406528)
def positiveArguments : Array ℕ := #[
    2201, 27135, 21105, 3015, 28341, 334665,
    23517, 21105, 334665, 3015, 23517, 23517,
    23517, 23517, 23517, 27135, 28341, 7185,
    30177, 130767, 4311, 4311, 10059, 130767,
    130767, 4311, 1613751, 64665, 30177, 130767,
    10059, 64665, 10059, 130767, 130767, 4311,
    13, 247, 377, 3887, 117, 377,
    117, 117, 10023, 117, 3887, 10023,
    13, 117, 117, 247, 5242881, 5242879,
    26366139, 1488316583, 421858217, 283795525
  ]
def positiveCoefficients : Array ℕ := #[
    85147063327097562032905388032, 1049734467687774804980866744320, 816460141534935959429563023360, 933097304611355382205214883840, 1096389332918342574091127488512, 12946725101482555928097356513280,
    29112635903874287924802704375808, 816460141534935959429563023360, 12946725101482555928097356513280, 933097304611355382205214883840, 909769871996071497650084511744, 909769871996071497650084511744,
    909769871996071497650084511744, 29112635903874287924802704375808, 909769871996071497650084511744, 1049734467687774804980866744320, 1096389332918342574091127488512, 138978112222897769924221992960,
    2334832285344682534726929481728, 5058803284913478825241680543744, 166773734667477323909066391552, 2668379754679637182545062264832, 194569357112056877893910790144, 5058803284913478825241680543744,
    5058803284913478825241680543744, 2668379754679637182545062264832, 62428968010525678249960519237632, 5003212040024319717271991746560, 2334832285344682534726929481728, 5058803284913478825241680543744,
    194569357112056877893910790144, 5003212040024319717271991746560, 194569357112056877893910790144, 5058803284913478825241680543744, 5058803284913478825241680543744, 166773734667477323909066391552,
    32186441021419887147377229824, 38221398712936115987510460416, 29168962175661772727310614528, 300742058293892070533305991168, 36209746149097373040799383552, 29168962175661772727310614528,
    36209746149097373040799383552, 36209746149097373040799383552, 1550984126719670811914240262144, 36209746149097373040799383552, 300742058293892070533305991168, 1550984126719670811914240262144,
    32186441021419887147377229824, 36209746149097373040799383552, 36209746149097373040799383552, 38221398712936115987510460416, 396140888129185413882043170816, 396140737013457962053396332544,
    3984338275081029906719790071808, 14056752694916556797740671041536, 3984338208967899146544757080064, 5360745900993577879938374041600
  ]
def positiveScales : Array ℕ := #[
    11, 14, 14, 11, 14, 18,
    14, 14, 18, 11, 14, 14,
    14, 14, 14, 14, 14, 12,
    14, 16, 12, 12, 13, 16,
    16, 12, 20, 15, 14, 16,
    13, 15, 13, 16, 16, 12,
    3, 7, 8, 11, 6, 8,
    6, 6, 13, 6, 11, 13,
    3, 6, 6, 7, 22, 22,
    24, 30, 28, 28
  ]
def negativeArguments : Array ℕ := #[
    71, 603, 1437, 13, 5, 139
  ]
def negativeCoefficients : Array ℕ := #[
    11250399077025535938283240947712, 95549163992202791137814004105216, 113850869532997853121922656632832, 4119864450741745554864285417472, 792281625142643375935439503360, 22025429178965485851005218193408
  ]
def negativeScales : Array ℕ := #[
    6, 9, 10, 3, 2, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11103943429891557, 14727867288221222, 14365297208845050, 11557942286787341, 14790603043544707, 18352358153137552,
    14521416410762298, 14365297208845050, 18352358153137552, 11557942286787341, 14521416410762298, 14521416410762298,
    14521416410762298, 14521416410762298, 14521416410762298, 14727867288221222, 14790603043544707, 12810772441294931,
    14881161769044174, 16996638985272618, 12073806847178492, 12073806847178492, 13296199268514940, 16996638985272618,
    16996638985272618, 12073806847178492, 20621986558857298, 15980697441717134, 14881161769044174, 16996638985272618,
    13296199268514940, 15980697441717134, 13296199268514940, 16996638985272618, 16996638985272618, 12073806847178492,
    3700439718136550, 7948367230958674, 8558420713268557, 11924441391923722, 6870364719426147, 8558420713268557,
    6870364719426147, 6870364719426147, 13291026768056126, 6870364719426147, 11924441391923722, 13291026768056126,
    3700439718136550, 6870364719426147, 6870364719426147, 7948367230958674, 22321928370059577, 22321927819715094,
    24652182985758446, 30471034291819556, 28652182961819443, 28080276599691131
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6149747119504683, 9236014191900085, 10488844346457523, 3700439718214233, 2321928094887363, 7118941072723508
  ]

abbrev PositiveTerm := Fin 58
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 53610177343 / 1000000000000
noncomputable def negativeCeiling : ℝ := 5584540233 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 85147063327097562032905388032, coefficient := 85147063327097562032905388032 }, { argument := 11250399077025535938283240947712, coefficient := (-11250399077025535938283240947712) }, { argument := 1049734467687774804980866744320, coefficient := 1049734467687774804980866744320 }, { argument := 816460141534935959429563023360, coefficient := 816460141534935959429563023360 }, { argument := 933097304611355382205214883840, coefficient := 933097304611355382205214883840 }, { argument := 1096389332918342574091127488512, coefficient := 1096389332918342574091127488512 }, { argument := 12946725101482555928097356513280, coefficient := 12946725101482555928097356513280 }, { argument := 29112635903874287924802704375808, coefficient := 29112635903874287924802704375808 }, { argument := 816460141534935959429563023360, coefficient := 816460141534935959429563023360 }, { argument := 12946725101482555928097356513280, coefficient := 12946725101482555928097356513280 }, { argument := 933097304611355382205214883840, coefficient := 933097304611355382205214883840 }, { argument := 909769871996071497650084511744, coefficient := 909769871996071497650084511744 }, { argument := 909769871996071497650084511744, coefficient := 909769871996071497650084511744 }, { argument := 909769871996071497650084511744, coefficient := 909769871996071497650084511744 }, { argument := 29112635903874287924802704375808, coefficient := 29112635903874287924802704375808 }, { argument := 909769871996071497650084511744, coefficient := 909769871996071497650084511744 }, { argument := 1049734467687774804980866744320, coefficient := 1049734467687774804980866744320 }, { argument := 1096389332918342574091127488512, coefficient := 1096389332918342574091127488512 }, { argument := 95549163992202791137814004105216, coefficient := (-95549163992202791137814004105216) }, { argument := 138978112222897769924221992960, coefficient := 138978112222897769924221992960 }, { argument := 2334832285344682534726929481728, coefficient := 2334832285344682534726929481728 }, { argument := 5058803284913478825241680543744, coefficient := 5058803284913478825241680543744 }, { argument := 166773734667477323909066391552, coefficient := 166773734667477323909066391552 }, { argument := 2668379754679637182545062264832, coefficient := 2668379754679637182545062264832 }, { argument := 194569357112056877893910790144, coefficient := 194569357112056877893910790144 }, { argument := 5058803284913478825241680543744, coefficient := 5058803284913478825241680543744 }, { argument := 5058803284913478825241680543744, coefficient := 5058803284913478825241680543744 }, { argument := 2668379754679637182545062264832, coefficient := 2668379754679637182545062264832 }, { argument := 62428968010525678249960519237632, coefficient := 62428968010525678249960519237632 }, { argument := 5003212040024319717271991746560, coefficient := 5003212040024319717271991746560 }, { argument := 2334832285344682534726929481728, coefficient := 2334832285344682534726929481728 }, { argument := 5058803284913478825241680543744, coefficient := 5058803284913478825241680543744 }, { argument := 194569357112056877893910790144, coefficient := 194569357112056877893910790144 }, { argument := 5003212040024319717271991746560, coefficient := 5003212040024319717271991746560 }, { argument := 194569357112056877893910790144, coefficient := 194569357112056877893910790144 }, { argument := 5058803284913478825241680543744, coefficient := 5058803284913478825241680543744 }, { argument := 5058803284913478825241680543744, coefficient := 5058803284913478825241680543744 }, { argument := 166773734667477323909066391552, coefficient := 166773734667477323909066391552 }, { argument := 113850869532997853121922656632832, coefficient := (-113850869532997853121922656632832) }, { argument := 32186441021419887147377229824, coefficient := 32186441021419887147377229824 }, { argument := 38221398712936115987510460416, coefficient := 38221398712936115987510460416 }, { argument := 29168962175661772727310614528, coefficient := 29168962175661772727310614528 }, { argument := 300742058293892070533305991168, coefficient := 300742058293892070533305991168 }, { argument := 36209746149097373040799383552, coefficient := 36209746149097373040799383552 }, { argument := 29168962175661772727310614528, coefficient := 29168962175661772727310614528 }, { argument := 36209746149097373040799383552, coefficient := 36209746149097373040799383552 }, { argument := 36209746149097373040799383552, coefficient := 36209746149097373040799383552 }, { argument := 1550984126719670811914240262144, coefficient := 1550984126719670811914240262144 }, { argument := 36209746149097373040799383552, coefficient := 36209746149097373040799383552 }, { argument := 300742058293892070533305991168, coefficient := 300742058293892070533305991168 }, { argument := 1550984126719670811914240262144, coefficient := 1550984126719670811914240262144 }, { argument := 32186441021419887147377229824, coefficient := 32186441021419887147377229824 }, { argument := 36209746149097373040799383552, coefficient := 36209746149097373040799383552 }, { argument := 36209746149097373040799383552, coefficient := 36209746149097373040799383552 }, { argument := 38221398712936115987510460416, coefficient := 38221398712936115987510460416 }, { argument := 4119864450741745554864285417472, coefficient := (-4119864450741745554864285417472) }, { argument := 396140888129185413882043170816, coefficient := 396140888129185413882043170816 }, { argument := 396140737013457962053396332544, coefficient := 396140737013457962053396332544 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 3984338275081029906719790071808, coefficient := 3984338275081029906719790071808 }, { argument := 14056752694916556797740671041536, coefficient := 14056752694916556797740671041536 }, { argument := 3984338208967899146544757080064, coefficient := 3984338208967899146544757080064 }, { argument := 22025429178965485851005218193408, coefficient := (-22025429178965485851005218193408) }, { argument := 5360745900993577879938374041600, coefficient := 5360745900993577879938374041600 }] }

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

end TermShard12


end Parent2

namespace Parent2

namespace TermShard13

/-! Directed signed-log shard 13.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-48037749146397706893439226938916864)
def positiveArguments : Array ℕ := #[
    10529120187, 21057396469, 568434955, 145149999, 21412440081, 219431478693,
    10706220759, 145142893, 397379343, 32752744689, 455, 403,
    18863, 5135, 16376371437, 18863, 455, 455,
    195, 455, 5135, 195, 198690579, 403,
    88291999, 3507, 436186465, 5649, 175, 5649,
    3773, 88320671, 3507, 21, 535, 489,
    535, 489
  ]
def positiveCoefficients : Array ℕ := #[
    198889457060779884436217929924608, 198881486603406432220329801678848, 5368716358367030095826502287360, 685451490266162519898329186304, 101117389354968991071994040549376, 1036235860266347903205603255779328,
    101117396141009626955674212630528, 685417933129935248199440662528, 1876570890367960369661611081728, 154670463741320381752195934060544, 35203919867178001567443845120, 31180614739500515674021691392,
    1459453935065008007838886264832, 397301381358151731975437680640, 154670455170225215343789871202304, 1459453935065008007838886264832, 35203919867178001567443845120, 35203919867178001567443845120,
    30174788457581144200666152960, 35203919867178001567443845120, 397301381358151731975437680640, 30174788457581144200666152960, 1876579461463126778067673939968, 31180614739500515674021691392,
    833894353566320464676004036608, 135670491180432144502225895424, 8239329370389574406264911298560, 218535102560097286653286023168, 6769984589841923378354585600, 218535102560097286653286023168,
    145960867756991868037324865536, 834165152949914141611138220032, 135670491180432144502225895424, 6499185206248246443220402176, 41393620063604902941939466240, 37834542450659434651604484096,
    41393620063604902941939466240, 37834542450659434651604484096
  ]
def positiveScales : Array ℕ := #[
    33, 34, 29, 27, 34, 37,
    33, 27, 28, 34, 8, 8,
    14, 12, 33, 14, 8, 8,
    7, 8, 12, 7, 27, 8,
    26, 11, 28, 12, 7, 12,
    11, 26, 11, 4, 9, 8,
    9, 8
  ]
def negativeArguments : Array ℕ := #[
    1289, 15649, 2001, 17, 1
  ]
def negativeCoefficients : Array ℕ := #[
    408500405923546924632312607932416, 1239841515185722619001369278808064, 317071106382085879049362889244672, 10775030101939949912721977245696, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    10, 13, 10, 4, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    33293665838714750, 34293608021825352, 29082420032635581, 27112969321124134, 34317730158056681, 37674979547150807,
    33317730254876693, 27112898690452525, 28565941637911714, 34930896758365688, 8829722735013603, 8654636028526477,
    14203271522207836, 12326148561205557, 33930896678418447, 14203271522207836, 8829722735013603, 8829722735013603,
    7607330313749179, 8829722735013603, 12326148561205557, 7607330313749179, 27565948227296807, 8654636028526477,
    26395779371326291, 11776021715228447, 28700369762497288, 12463779785335379, 7451211111832325, 12463779785335379,
    11881496384617007, 26396247796978604, 11776021715228447, 4392317422778759, 9063395081288509, 8933690654464738,
    9063395081288509, 8933690654464738
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    10332036548361652, 13933782856681540, 10966505465643660, 4087462841250340, 0
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 850018961943 / 1000000000000
noncomputable def negativeCeiling : ℝ := 301137540997 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 198889457060779884436217929924608, coefficient := 198889457060779884436217929924608 }, { argument := 198881486603406432220329801678848, coefficient := 198881486603406432220329801678848 }, { argument := 5368716358367030095826502287360, coefficient := 5368716358367030095826502287360 }, { argument := 408500405923546924632312607932416, coefficient := (-408500405923546924632312607932416) }, { argument := 685451490266162519898329186304, coefficient := 685451490266162519898329186304 }, { argument := 101117389354968991071994040549376, coefficient := 101117389354968991071994040549376 }, { argument := 1036235860266347903205603255779328, coefficient := 1036235860266347903205603255779328 }, { argument := 101117396141009626955674212630528, coefficient := 101117396141009626955674212630528 }, { argument := 685417933129935248199440662528, coefficient := 685417933129935248199440662528 }, { argument := 1239841515185722619001369278808064, coefficient := (-1239841515185722619001369278808064) }, { argument := 1876570890367960369661611081728, coefficient := 1876570890367960369661611081728 }, { argument := 154670463741320381752195934060544, coefficient := 154670463741320381752195934060544 }, { argument := 35203919867178001567443845120, coefficient := 35203919867178001567443845120 }, { argument := 31180614739500515674021691392, coefficient := 31180614739500515674021691392 }, { argument := 1459453935065008007838886264832, coefficient := 1459453935065008007838886264832 }, { argument := 397301381358151731975437680640, coefficient := 397301381358151731975437680640 }, { argument := 154670455170225215343789871202304, coefficient := 154670455170225215343789871202304 }, { argument := 1459453935065008007838886264832, coefficient := 1459453935065008007838886264832 }, { argument := 35203919867178001567443845120, coefficient := 35203919867178001567443845120 }, { argument := 35203919867178001567443845120, coefficient := 35203919867178001567443845120 }, { argument := 30174788457581144200666152960, coefficient := 30174788457581144200666152960 }, { argument := 35203919867178001567443845120, coefficient := 35203919867178001567443845120 }, { argument := 397301381358151731975437680640, coefficient := 397301381358151731975437680640 }, { argument := 30174788457581144200666152960, coefficient := 30174788457581144200666152960 }, { argument := 1876579461463126778067673939968, coefficient := 1876579461463126778067673939968 }, { argument := 31180614739500515674021691392, coefficient := 31180614739500515674021691392 }, { argument := 317071106382085879049362889244672, coefficient := (-317071106382085879049362889244672) }, { argument := 833894353566320464676004036608, coefficient := 833894353566320464676004036608 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 8239329370389574406264911298560, coefficient := 8239329370389574406264911298560 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 6769984589841923378354585600, coefficient := 6769984589841923378354585600 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 145960867756991868037324865536, coefficient := 145960867756991868037324865536 }, { argument := 834165152949914141611138220032, coefficient := 834165152949914141611138220032 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 6499185206248246443220402176, coefficient := 6499185206248246443220402176 }, { argument := 10775030101939949912721977245696, coefficient := (-10775030101939949912721977245696) }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end TermShard13


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
