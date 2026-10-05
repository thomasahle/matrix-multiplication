import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 18, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent2

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2575407632740871021726443788828672)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    20448968925, 10813275, 432150459, 75795130437, 18948784881, 108035343,
    1048022613, 495478177227, 18807956539713, 1981914068211, 1048022613, 1882779573,
    36719270319, 73438513701, 235348569, 67042305, 31695880095, 1203150335805,
    126783607335, 67042305, 52671906591, 1027243976973, 2054487200367, 6584019723,
    487602521, 56991268425, 15603275415, 143958249, 1079698527, 27390495,
    70638645, 59105805, 1653520935, 538407717, 59105805, 53339385,
    27390495, 27390495, 53339385, 1653520935, 53339385, 35989533,
    70638645, 1384836351, 36840937275, 32366963363, 351759960777, 10242709925,
    1229125191, 32366963363, 64324218329, 10242709925, 992723445931, 63504801535,
    73681899795, 32366963363, 1229125191, 63504801535, 1229125191, 32366963363,
    32366963363, 1384836351, 18422811687, 598470481
  ]
def negativeCoefficients : Array ℕ := #[
    94304224082678632617816883200, 797878866094566607002009600, 3985884459254556281769295872, 699086686602386103593752068096, 699086770415167802493099835392, 3985800646472857382421528576,
    19332604925471348887658692608, 2284989782353643291728788062208, 21684097552346099239216257957888, 2284991349523303268329703079936, 19332604925471348887658692608, 34731152930339150117593939968,
    1354701964295904573760374571008, 1354701467395959460246182690816, 34731318563654187955657900032, 1236712242446578240853114880, 146171447075862447469237370880, 1387137895424533793676648775680,
    146171547328151880557616168960, 1236712242446578240853114880, 60726573797407020098902818816, 2368663343060064856864557367296, 2368662474242630336741420040192, 60726863403218526806615261184,
    17989357829165174379482447872, 65706458942003690102115532800, 17989351768256824661287895040, 2655560976602353985214480384, 19916922404330182305625669632, 2021061805268884419961159680,
    2606106012057245699423600640, 34889909059378636302487388160, 61004155016931853413038161920, 19863738725618478813328441344, 34889909059378636302487388160, 1967875968288124303646392320,
    2021061805268884419961159680, 2021061805268884419961159680, 1967875968288124303646392320, 61004155016931853413038161920, 1967875968288124303646392320, 2655558818333297361196941312,
    2606106012057245699423600640, 6386430437716702623436898304, 169898835336877891913357721600, 149266272400098607164557361152, 811103246478928634166802120704, 94472324303859877952251494400,
    5668339458231592677135089664, 149266272400098607164557361152, 148321549157060008385034846208, 94472324303859877952251494400, 2289064417882524842783053709312, 146432102670982810825989816320,
    169898893547884659513061539840, 149266272400098607164557361152, 5668339458231592677135089664, 146432102670982810825989816320, 5668339458231592677135089664, 149266272400098607164557361152,
    149266272400098607164557361152, 6386430437716702623436898304, 21240055769264644809673408512, 22079663597353709619843694592
  ]
def negativeScales : Array ℕ := #[
    34, 23, 28, 36, 34, 26,
    29, 38, 44, 40, 29, 30,
    35, 36, 27, 25, 34, 40,
    36, 25, 35, 39, 40, 32,
    28, 35, 33, 27, 30, 24,
    26, 25, 30, 29, 25, 25,
    24, 24, 25, 30, 25, 25,
    26, 30, 35, 34, 38, 33,
    30, 34, 35, 33, 39, 35,
    36, 34, 30, 35, 30, 34,
    34, 30, 34, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34251309050510546, 23366300200298554, 28686958452701546, 36141386112308758, 34141386285271968, 26686928116258730,
    29965022713379499, 38850030562442301, 44096408343950801, 40850031551920335, 29965022713379499, 30810216960651897,
    35095818338844852, 36095817809669257, 27810223840866807, 25998568438939737, 34883576279775953, 40129954059773692,
    36883577269254013, 25998568438939737, 35616314631263956, 39901916014762661, 40901915485587023, 32616321511478758,
    28861130346229564, 35730021851367526, 33861129860161949, 27101075218722165, 30007981393858889, 24707172002906790,
    26073954333492800, 25816796494902051, 30622894165403941, 29004123847349216, 25816796494902051, 25668697855040585,
    24707172002906790, 24707172002906790, 25668697855040585, 30622894165403941, 25668697855040585, 25101074046192008,
    26073954333492800, 30367068354051231, 35100590714558940, 34913802974107388, 38355800320556461, 33253878410122679,
    30194984721069111, 34913802974107388, 35904642973985194, 33253878410122679, 39852600911619437, 35886146629022019,
    36100591208857304, 34913802974107388, 30194984721069111, 35886146629022019, 30194984721069111, 34913802974107388,
    34913802974107388, 30367068354051231, 34100774211026627, 29156704848431127
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
noncomputable def negativeCeiling : ℝ := 1052007923 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 94304224082678632617816883200, coefficient := (-94304224082678632617816883200) }, { argument := 797878866094566607002009600, coefficient := (-797878866094566607002009600) }, { argument := 3985884459254556281769295872, coefficient := (-3985884459254556281769295872) }, { argument := 699086686602386103593752068096, coefficient := (-699086686602386103593752068096) }, { argument := 699086770415167802493099835392, coefficient := (-699086770415167802493099835392) }, { argument := 3985800646472857382421528576, coefficient := (-3985800646472857382421528576) }, { argument := 19332604925471348887658692608, coefficient := (-19332604925471348887658692608) }, { argument := 2284989782353643291728788062208, coefficient := (-2284989782353643291728788062208) }, { argument := 21684097552346099239216257957888, coefficient := (-21684097552346099239216257957888) }, { argument := 2284991349523303268329703079936, coefficient := (-2284991349523303268329703079936) }, { argument := 19332604925471348887658692608, coefficient := (-19332604925471348887658692608) }, { argument := 34731152930339150117593939968, coefficient := (-34731152930339150117593939968) }, { argument := 1354701964295904573760374571008, coefficient := (-1354701964295904573760374571008) }, { argument := 1354701467395959460246182690816, coefficient := (-1354701467395959460246182690816) }, { argument := 34731318563654187955657900032, coefficient := (-34731318563654187955657900032) }, { argument := 1236712242446578240853114880, coefficient := (-1236712242446578240853114880) }, { argument := 146171447075862447469237370880, coefficient := (-146171447075862447469237370880) }, { argument := 1387137895424533793676648775680, coefficient := (-1387137895424533793676648775680) }, { argument := 146171547328151880557616168960, coefficient := (-146171547328151880557616168960) }, { argument := 1236712242446578240853114880, coefficient := (-1236712242446578240853114880) }, { argument := 60726573797407020098902818816, coefficient := (-60726573797407020098902818816) }, { argument := 2368663343060064856864557367296, coefficient := (-2368663343060064856864557367296) }, { argument := 2368662474242630336741420040192, coefficient := (-2368662474242630336741420040192) }, { argument := 60726863403218526806615261184, coefficient := (-60726863403218526806615261184) }, { argument := 17989357829165174379482447872, coefficient := (-17989357829165174379482447872) }, { argument := 65706458942003690102115532800, coefficient := (-65706458942003690102115532800) }, { argument := 17989351768256824661287895040, coefficient := (-17989351768256824661287895040) }, { argument := 2655560976602353985214480384, coefficient := (-2655560976602353985214480384) }, { argument := 19916922404330182305625669632, coefficient := (-19916922404330182305625669632) }, { argument := 2021061805268884419961159680, coefficient := (-2021061805268884419961159680) }, { argument := 2606106012057245699423600640, coefficient := (-2606106012057245699423600640) }, { argument := 34889909059378636302487388160, coefficient := (-34889909059378636302487388160) }, { argument := 61004155016931853413038161920, coefficient := (-61004155016931853413038161920) }, { argument := 19863738725618478813328441344, coefficient := (-19863738725618478813328441344) }, { argument := 34889909059378636302487388160, coefficient := (-34889909059378636302487388160) }, { argument := 1967875968288124303646392320, coefficient := (-1967875968288124303646392320) }, { argument := 2021061805268884419961159680, coefficient := (-2021061805268884419961159680) }, { argument := 2021061805268884419961159680, coefficient := (-2021061805268884419961159680) }, { argument := 1967875968288124303646392320, coefficient := (-1967875968288124303646392320) }, { argument := 61004155016931853413038161920, coefficient := (-61004155016931853413038161920) }, { argument := 1967875968288124303646392320, coefficient := (-1967875968288124303646392320) }, { argument := 2655558818333297361196941312, coefficient := (-2655558818333297361196941312) }, { argument := 2606106012057245699423600640, coefficient := (-2606106012057245699423600640) }, { argument := 6386430437716702623436898304, coefficient := (-6386430437716702623436898304) }, { argument := 169898835336877891913357721600, coefficient := (-169898835336877891913357721600) }, { argument := 149266272400098607164557361152, coefficient := (-149266272400098607164557361152) }, { argument := 811103246478928634166802120704, coefficient := (-811103246478928634166802120704) }, { argument := 94472324303859877952251494400, coefficient := (-94472324303859877952251494400) }, { argument := 5668339458231592677135089664, coefficient := (-5668339458231592677135089664) }, { argument := 149266272400098607164557361152, coefficient := (-149266272400098607164557361152) }, { argument := 148321549157060008385034846208, coefficient := (-148321549157060008385034846208) }, { argument := 94472324303859877952251494400, coefficient := (-94472324303859877952251494400) }, { argument := 2289064417882524842783053709312, coefficient := (-2289064417882524842783053709312) }, { argument := 146432102670982810825989816320, coefficient := (-146432102670982810825989816320) }, { argument := 169898893547884659513061539840, coefficient := (-169898893547884659513061539840) }, { argument := 149266272400098607164557361152, coefficient := (-149266272400098607164557361152) }, { argument := 5668339458231592677135089664, coefficient := (-5668339458231592677135089664) }, { argument := 146432102670982810825989816320, coefficient := (-146432102670982810825989816320) }, { argument := 5668339458231592677135089664, coefficient := (-5668339458231592677135089664) }, { argument := 149266272400098607164557361152, coefficient := (-149266272400098607164557361152) }, { argument := 149266272400098607164557361152, coefficient := (-149266272400098607164557361152) }, { argument := 6386430437716702623436898304, coefficient := (-6386430437716702623436898304) }, { argument := 21240055769264644809673408512, coefficient := (-21240055769264644809673408512) }, { argument := 22079663597353709619843694592, coefficient := (-22079663597353709619843694592) }] }

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


end Parent2

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-578521885325878649414783474860032)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    38819301157, 6262044789, 277339979, 77638579319, 277339979, 540083117,
    10203191859, 540083117, 6262044789, 10203191859, 2302852419, 540083117,
    540083117, 598470481, 34169949, 16154674371, 613218558249, 64618741803,
    34169949, 1882779573, 36719270319, 73438513701, 235348569, 369435199,
    43179802575, 11821922385, 1699093761, 33136902483, 66273780657, 212387733,
    205818907, 24056234475, 6586202805, 10307267, 465869717, 1295285,
    22874917, 4012045531, 1003011503, 5718609, 1297593, 613468647,
    23286780693, 2453876271, 1297593, 22874917, 4012045531, 1003011503,
    5718609, 67042305, 31695880095, 1203150335805, 126783607335, 67042305,
    872507607, 17016247221, 34032481959, 109063971, 1297593, 613468647,
    23286780693, 2453876271, 1297593, 872507607
  ]
def negativeCoefficients : Array ℕ := #[
    89511214195429511291117502464, 231028675201579059192998658048, 20464078456083925989123424256, 89511187683999512856671289344, 20464078456083925989123424256, 19925550075660664778883334144,
    752862675831719171915645976576, 19925550075660664778883334144, 231028675201579059192998658048, 752862675831719171915645976576, 21240064606407977621155479552, 19925550075660664778883334144,
    19925550075660664778883334144, 22079663597353709619843694592, 1260648608429415239063175168, 149000571857975914194448416768, 1413985725658557028392971010048, 149000674050632239536150675456,
    1260648608429415239063175168, 34731152930339150117593939968, 1354701964295904573760374571008, 1354701467395959460246182690816, 34731318563654187955657900032, 13629753135545917738915463168,
    49782922953395605416915763200, 13629748543459564889843957760, 1958921735400226454803316736, 76408494937421446995630882816, 76408466911052591507787743232, 1958931077523178284084363264,
    15186754811838509396260814848, 55469900092184207090201395200, 15186749695172871951073935360, 11883469778024501809774592, 537111215074405996971425792, 11946895448757438282465280,
    105491934901586968830803968, 18502294280606785288246657024, 18502296498827760151820238848, 105489716680612105257222144, 47872731965673996420120576, 5658249564226933450422091776,
    53695660468046469432644468736, 5658253444960717957069012992, 47872731965673996420120576, 105491934901586968830803968, 18502294280606785288246657024, 18502296498827760151820238848,
    105489716680612105257222144, 1236712242446578240853114880, 146171447075862447469237370880, 1387137895424533793676648775680, 146171547328151880557616168960, 1236712242446578240853114880,
    2011865566086719061689892864, 78473589395189594211729014784, 78473560611351310197187411968, 2011875160699480399870427136, 47872731965673996420120576, 5658249564226933450422091776,
    53695660468046469432644468736, 5658253444960717957069012992, 47872731965673996420120576, 2011865566086719061689892864
  ]
def negativeScales : Array ℕ := #[
    35, 32, 28, 36, 28, 29,
    33, 29, 32, 33, 31, 29,
    29, 29, 25, 33, 39, 35,
    25, 30, 35, 36, 27, 28,
    35, 33, 30, 34, 35, 27,
    27, 34, 32, 23, 28, 20,
    24, 31, 29, 22, 20, 29,
    34, 31, 20, 24, 31, 29,
    22, 25, 34, 40, 36, 25,
    29, 33, 34, 26, 20, 29,
    34, 31, 20, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35176055095096102, 32543986681313696, 28047080357256629, 36176054667798645, 28047080357256629, 29008606209441993,
    33248301489188480, 29008606209441993, 32543986681313696, 33248301489188480, 31100774811274590, 29008606209441993,
    29008606209441993, 29156704848431127, 25026224758700931, 33911232624769567, 39157610402676557, 35911233614247661,
    25026224758700931, 30810216960651897, 35095818338844852, 36095817809669257, 27810223840866807, 28460746088883029,
    35329637596015433, 33460745602815435, 30662118320897169, 34947719709885504, 35947719180709819, 27662125201111974,
    27616800276724727, 34485691783848424, 32616799790657132, 23297158513092729, 28795351313455617, 20304838136617414,
    24447263172902002, 31901690837064168, 29901691010027392, 22447232836459224, 20307406511244984, 29192414371978977,
    34438792155220641, 31192415361456978, 20307406511244984, 24447263172902002, 31901690837064168, 29901691010027392,
    22447232836459224, 25998568438939737, 34883576279775953, 40129954059773692, 36883577269254013, 25998568438939737,
    29700592468756294, 33986193866635986, 34986193337460228, 26700599348971106, 20307406511244984, 29192414371978977,
    34438792155220641, 31192415361456978, 20307406511244984, 29700592468756294
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
noncomputable def negativeCeiling : ℝ := 3972614721 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 89511214195429511291117502464, coefficient := (-89511214195429511291117502464) }, { argument := 231028675201579059192998658048, coefficient := (-231028675201579059192998658048) }, { argument := 20464078456083925989123424256, coefficient := (-20464078456083925989123424256) }, { argument := 89511187683999512856671289344, coefficient := (-89511187683999512856671289344) }, { argument := 20464078456083925989123424256, coefficient := (-20464078456083925989123424256) }, { argument := 19925550075660664778883334144, coefficient := (-19925550075660664778883334144) }, { argument := 752862675831719171915645976576, coefficient := (-752862675831719171915645976576) }, { argument := 19925550075660664778883334144, coefficient := (-19925550075660664778883334144) }, { argument := 231028675201579059192998658048, coefficient := (-231028675201579059192998658048) }, { argument := 752862675831719171915645976576, coefficient := (-752862675831719171915645976576) }, { argument := 21240064606407977621155479552, coefficient := (-21240064606407977621155479552) }, { argument := 19925550075660664778883334144, coefficient := (-19925550075660664778883334144) }, { argument := 19925550075660664778883334144, coefficient := (-19925550075660664778883334144) }, { argument := 22079663597353709619843694592, coefficient := (-22079663597353709619843694592) }, { argument := 1260648608429415239063175168, coefficient := (-1260648608429415239063175168) }, { argument := 149000571857975914194448416768, coefficient := (-149000571857975914194448416768) }, { argument := 1413985725658557028392971010048, coefficient := (-1413985725658557028392971010048) }, { argument := 149000674050632239536150675456, coefficient := (-149000674050632239536150675456) }, { argument := 1260648608429415239063175168, coefficient := (-1260648608429415239063175168) }, { argument := 34731152930339150117593939968, coefficient := (-34731152930339150117593939968) }, { argument := 1354701964295904573760374571008, coefficient := (-1354701964295904573760374571008) }, { argument := 1354701467395959460246182690816, coefficient := (-1354701467395959460246182690816) }, { argument := 34731318563654187955657900032, coefficient := (-34731318563654187955657900032) }, { argument := 13629753135545917738915463168, coefficient := (-13629753135545917738915463168) }, { argument := 49782922953395605416915763200, coefficient := (-49782922953395605416915763200) }, { argument := 13629748543459564889843957760, coefficient := (-13629748543459564889843957760) }, { argument := 1958921735400226454803316736, coefficient := (-1958921735400226454803316736) }, { argument := 76408494937421446995630882816, coefficient := (-76408494937421446995630882816) }, { argument := 76408466911052591507787743232, coefficient := (-76408466911052591507787743232) }, { argument := 1958931077523178284084363264, coefficient := (-1958931077523178284084363264) }, { argument := 15186754811838509396260814848, coefficient := (-15186754811838509396260814848) }, { argument := 55469900092184207090201395200, coefficient := (-55469900092184207090201395200) }, { argument := 15186749695172871951073935360, coefficient := (-15186749695172871951073935360) }, { argument := 11883469778024501809774592, coefficient := (-11883469778024501809774592) }, { argument := 537111215074405996971425792, coefficient := (-537111215074405996971425792) }, { argument := 11946895448757438282465280, coefficient := (-11946895448757438282465280) }, { argument := 105491934901586968830803968, coefficient := (-105491934901586968830803968) }, { argument := 18502294280606785288246657024, coefficient := (-18502294280606785288246657024) }, { argument := 18502296498827760151820238848, coefficient := (-18502296498827760151820238848) }, { argument := 105489716680612105257222144, coefficient := (-105489716680612105257222144) }, { argument := 47872731965673996420120576, coefficient := (-47872731965673996420120576) }, { argument := 5658249564226933450422091776, coefficient := (-5658249564226933450422091776) }, { argument := 53695660468046469432644468736, coefficient := (-53695660468046469432644468736) }, { argument := 5658253444960717957069012992, coefficient := (-5658253444960717957069012992) }, { argument := 47872731965673996420120576, coefficient := (-47872731965673996420120576) }, { argument := 105491934901586968830803968, coefficient := (-105491934901586968830803968) }, { argument := 18502294280606785288246657024, coefficient := (-18502294280606785288246657024) }, { argument := 18502296498827760151820238848, coefficient := (-18502296498827760151820238848) }, { argument := 105489716680612105257222144, coefficient := (-105489716680612105257222144) }, { argument := 1236712242446578240853114880, coefficient := (-1236712242446578240853114880) }, { argument := 146171447075862447469237370880, coefficient := (-146171447075862447469237370880) }, { argument := 1387137895424533793676648775680, coefficient := (-1387137895424533793676648775680) }, { argument := 146171547328151880557616168960, coefficient := (-146171547328151880557616168960) }, { argument := 1236712242446578240853114880, coefficient := (-1236712242446578240853114880) }, { argument := 2011865566086719061689892864, coefficient := (-2011865566086719061689892864) }, { argument := 78473589395189594211729014784, coefficient := (-78473589395189594211729014784) }, { argument := 78473560611351310197187411968, coefficient := (-78473560611351310197187411968) }, { argument := 2011875160699480399870427136, coefficient := (-2011875160699480399870427136) }, { argument := 47872731965673996420120576, coefficient := (-47872731965673996420120576) }, { argument := 5658249564226933450422091776, coefficient := (-5658249564226933450422091776) }, { argument := 53695660468046469432644468736, coefficient := (-53695660468046469432644468736) }, { argument := 5658253444960717957069012992, coefficient := (-5658253444960717957069012992) }, { argument := 47872731965673996420120576, coefficient := (-47872731965673996420120576) }, { argument := 2011865566086719061689892864, coefficient := (-2011865566086719061689892864) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18
