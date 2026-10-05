import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 1, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1

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
def constantNumerator : ℤ := (-711209515396287295730312139505664)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1091339235, 20817495, 22735864645, 397849288655, 397849483785, 22735669515,
    969422475, 26516168985, 7755377295, 556924185, 1371374469, 497521185,
    440661621, 20625806841, 5614881945, 1371374919, 20625806841, 497521185,
    497521185, 213223365, 497521185, 5614881945, 213223365, 556922385,
    440661621, 10894287, 7360801795, 7120251117, 78656269195, 7306401473,
    232687945, 7120251117, 4048770243, 7306401473, 114063630639, 139612767,
    3680402285, 7120251117, 232687945, 139612767, 232687945, 3583394353,
    4048770243, 10894287, 5292845415, 584417223, 10905213033, 14461217667,
    460073133, 10905217479, 236253771, 236253771, 7995324987, 435204315,
    14461217667, 7995324987, 5292840969, 460073133, 435204315, 584417223,
    1061692245, 111316517055, 1199880793125, 55658300985
  ]
def negativeCoefficients : Array ℕ := #[
    80526622262571862691193815040, 768030005041456444436643840, 26212667275051016786563563520, 917378000965772749688075714560, 917378450904919137556176568320, 26212442305477822852513136640,
    8941344147813547979361484800, 30571061442595610403652239360, 8941341259745178939209809920, 2568359477288567990114058240, 25297393858862333207620091904, 2294411492735925866452746240,
    2032193036423248624572432384, 95119745027423669492083851264, 25894072560876877635680993280, 25297402159897166376918319104, 95119745027423669492083851264, 2294411492735925866452746240,
    2294411492735925866452746240, 1966638422345079314102353920, 2294411492735925866452746240, 25894072560876877635680993280, 1966638422345079314102353920, 2568351176253734820815831040,
    2032193036423248624572432384, 6430851972945312318272569344, 271565653779333759687395901440, 131345450095843565227393155072, 1450952067632969414150843269120, 134779318072205488501311930368,
    4292334970452404092398469120, 131345450095843565227393155072, 74686628485871831207733362688, 134779318072205488501311930368, 2104102602515768486093729562624, 82412831432686158574050607104,
    271565756158763368775407370240, 131345450095843565227393155072, 4292334970452404092398469120, 82412831432686158574050607104, 4292334970452404092398469120, 132203917089934046045872848896,
    74686628485871831207733362688, 6430851972945312318272569344, 24408941198053005578112860160, 21561189889898086927995764736, 100582836944516457469694705664, 533524762594712236111895199744,
    16973702679281472687996665856, 100582877951628533326027948032, 17432451400343134111996575744, 17432451400343134111996575744, 294975427642648295631942057984, 16056205237158149839996846080,
    533524762594712236111895199744, 294975427642648295631942057984, 24408920694496967649946238976, 16973702679281472687996665856, 16056205237158149839996846080, 21561189889898086927995764736,
    1224047820534821208320901120, 128339206330644342473679175680, 1383368369358531890868387840000, 128339304230973906164090142720
  ]
def negativeScales : Array ℕ := #[
    30, 24, 34, 38, 38, 34,
    29, 34, 32, 29, 30, 28,
    28, 34, 32, 30, 34, 28,
    28, 27, 28, 32, 27, 29,
    28, 23, 32, 32, 36, 32,
    27, 32, 31, 32, 36, 27,
    31, 32, 27, 27, 27, 31,
    31, 23, 32, 29, 33, 33,
    28, 33, 27, 27, 32, 28,
    33, 32, 32, 28, 28, 29,
    29, 36, 40, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30023452476801862, 24311293141662280, 34404250819696074, 38533431063254765, 38533431770841840, 34404238437748179,
    29852550291116229, 34626153301047966, 32852549825123347, 29052905703595831, 30352975422771285, 28890182721265722,
    28715096011151627, 34263731504728659, 32386608543726384, 30352975896174193, 34263731504728659, 28890182721265722,
    28890182721265722, 27667790296303722, 28890182721265722, 32386608543726384, 27667790296303722, 29052901040743435,
    28715096011151627, 23377068443480940, 32777215778642685, 32729280977182587, 36194842707217521, 32766513883560812,
    27793821229804550, 32729280977182587, 31914836635881572, 32766513883560812, 36731047903362532, 27056855635069075,
    31777216322534251, 32729280977182587, 27793821229804550, 27056855635069075, 27793821229804550, 31738679675218059,
    31914836635881572, 23377068443480940, 32301396372635102, 29122423454643720, 33344298902130662, 33751469984671515,
    28777287968998690, 33344299490309988, 27815762117297534, 27815762117297534, 32896509534396156, 28697117619978681,
    33751469984671515, 32896509534396156, 32301395160768074, 28777287968998690, 28697117619978681, 29122423454643720,
    29983718501853114, 36695876718315895, 40126028221390399, 35695877818839035
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
noncomputable def negativeCeiling : ℝ := 151494309 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 80526622262571862691193815040, coefficient := (-80526622262571862691193815040) }, { argument := 768030005041456444436643840, coefficient := (-768030005041456444436643840) }, { argument := 26212667275051016786563563520, coefficient := (-26212667275051016786563563520) }, { argument := 917378000965772749688075714560, coefficient := (-917378000965772749688075714560) }, { argument := 917378450904919137556176568320, coefficient := (-917378450904919137556176568320) }, { argument := 26212442305477822852513136640, coefficient := (-26212442305477822852513136640) }, { argument := 8941344147813547979361484800, coefficient := (-8941344147813547979361484800) }, { argument := 30571061442595610403652239360, coefficient := (-30571061442595610403652239360) }, { argument := 8941341259745178939209809920, coefficient := (-8941341259745178939209809920) }, { argument := 2568359477288567990114058240, coefficient := (-2568359477288567990114058240) }, { argument := 25297393858862333207620091904, coefficient := (-25297393858862333207620091904) }, { argument := 2294411492735925866452746240, coefficient := (-2294411492735925866452746240) }, { argument := 2032193036423248624572432384, coefficient := (-2032193036423248624572432384) }, { argument := 95119745027423669492083851264, coefficient := (-95119745027423669492083851264) }, { argument := 25894072560876877635680993280, coefficient := (-25894072560876877635680993280) }, { argument := 25297402159897166376918319104, coefficient := (-25297402159897166376918319104) }, { argument := 95119745027423669492083851264, coefficient := (-95119745027423669492083851264) }, { argument := 2294411492735925866452746240, coefficient := (-2294411492735925866452746240) }, { argument := 2294411492735925866452746240, coefficient := (-2294411492735925866452746240) }, { argument := 1966638422345079314102353920, coefficient := (-1966638422345079314102353920) }, { argument := 2294411492735925866452746240, coefficient := (-2294411492735925866452746240) }, { argument := 25894072560876877635680993280, coefficient := (-25894072560876877635680993280) }, { argument := 1966638422345079314102353920, coefficient := (-1966638422345079314102353920) }, { argument := 2568351176253734820815831040, coefficient := (-2568351176253734820815831040) }, { argument := 2032193036423248624572432384, coefficient := (-2032193036423248624572432384) }, { argument := 6430851972945312318272569344, coefficient := (-6430851972945312318272569344) }, { argument := 271565653779333759687395901440, coefficient := (-271565653779333759687395901440) }, { argument := 131345450095843565227393155072, coefficient := (-131345450095843565227393155072) }, { argument := 1450952067632969414150843269120, coefficient := (-1450952067632969414150843269120) }, { argument := 134779318072205488501311930368, coefficient := (-134779318072205488501311930368) }, { argument := 4292334970452404092398469120, coefficient := (-4292334970452404092398469120) }, { argument := 131345450095843565227393155072, coefficient := (-131345450095843565227393155072) }, { argument := 74686628485871831207733362688, coefficient := (-74686628485871831207733362688) }, { argument := 134779318072205488501311930368, coefficient := (-134779318072205488501311930368) }, { argument := 2104102602515768486093729562624, coefficient := (-2104102602515768486093729562624) }, { argument := 82412831432686158574050607104, coefficient := (-82412831432686158574050607104) }, { argument := 271565756158763368775407370240, coefficient := (-271565756158763368775407370240) }, { argument := 131345450095843565227393155072, coefficient := (-131345450095843565227393155072) }, { argument := 4292334970452404092398469120, coefficient := (-4292334970452404092398469120) }, { argument := 82412831432686158574050607104, coefficient := (-82412831432686158574050607104) }, { argument := 4292334970452404092398469120, coefficient := (-4292334970452404092398469120) }, { argument := 132203917089934046045872848896, coefficient := (-132203917089934046045872848896) }, { argument := 74686628485871831207733362688, coefficient := (-74686628485871831207733362688) }, { argument := 6430851972945312318272569344, coefficient := (-6430851972945312318272569344) }, { argument := 24408941198053005578112860160, coefficient := (-24408941198053005578112860160) }, { argument := 21561189889898086927995764736, coefficient := (-21561189889898086927995764736) }, { argument := 100582836944516457469694705664, coefficient := (-100582836944516457469694705664) }, { argument := 533524762594712236111895199744, coefficient := (-533524762594712236111895199744) }, { argument := 16973702679281472687996665856, coefficient := (-16973702679281472687996665856) }, { argument := 100582877951628533326027948032, coefficient := (-100582877951628533326027948032) }, { argument := 17432451400343134111996575744, coefficient := (-17432451400343134111996575744) }, { argument := 17432451400343134111996575744, coefficient := (-17432451400343134111996575744) }, { argument := 294975427642648295631942057984, coefficient := (-294975427642648295631942057984) }, { argument := 16056205237158149839996846080, coefficient := (-16056205237158149839996846080) }, { argument := 533524762594712236111895199744, coefficient := (-533524762594712236111895199744) }, { argument := 294975427642648295631942057984, coefficient := (-294975427642648295631942057984) }, { argument := 24408920694496967649946238976, coefficient := (-24408920694496967649946238976) }, { argument := 16973702679281472687996665856, coefficient := (-16973702679281472687996665856) }, { argument := 16056205237158149839996846080, coefficient := (-16056205237158149839996846080) }, { argument := 21561189889898086927995764736, coefficient := (-21561189889898086927995764736) }, { argument := 1224047820534821208320901120, coefficient := (-1224047820534821208320901120) }, { argument := 128339206330644342473679175680, coefficient := (-128339206330644342473679175680) }, { argument := 1383368369358531890868387840000, coefficient := (-1383368369358531890868387840000) }, { argument := 128339304230973906164090142720, coefficient := (-128339304230973906164090142720) }] }

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
def constantNumerator : ℤ := (-658017675087616870306072949161984)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1061692245, 83518328101, 1461466627439, 1461467344233, 83517611307, 1627313975,
    44511173885, 13018507595, 2014570285, 35252468615, 35252485905, 2014552995,
    1561524825, 42711673395, 12492194565, 91579625, 7667882775, 3833942775,
    45788425, 34695825, 3637794675, 39211790625, 1818898725, 34695825,
    86629375, 7253402625, 3626702625, 43313375, 20817495, 2182676805,
    23527074375, 1091339235, 20817495, 2014570285, 35252468615, 35252485905,
    2014552995, 34695825, 3637794675, 39211790625, 1818898725, 34695825,
    863387265, 15108200835, 15108208245, 863379855, 48374375, 1323162125,
    386994875, 116330875, 9740283525, 4870143525, 58163675, 534315705,
    56022037995, 603861575625, 28011040365, 534315705, 2014570285, 35252468615,
    35252485905, 2014552995, 603707355, 63297627345
  ]
def negativeCoefficients : Array ℕ := #[
    1224047820534821208320901120, 96290076496453228752667672576, 3369912606079332303284551548928, 3369914258893766249605094178816, 96289250089236255592396357632, 15009322212197991717850316800,
    51317889567311194310322421760, 15009317364163064846058782720, 2322641404118444525391708160, 81286658313422901871095316480, 81286698181448531175863746560, 2322621470105629873007493120,
    14402524405759547344001433600, 49243206754839635919655403520, 14402519753721276255373885440, 211168238092661636988928000, 17680933892203850148662476800, 17680940290918200716663193600,
    211161839378311068988211200, 40001562762575856481075200, 4194091710151775897832652800, 45208116645703656564326400000, 4194094909508951181833011200, 40001562762575856481075200,
    199753738736301548503040000, 16725207735868506897383424000, 16725213788706406083330048000, 199747685898402362556416000, 768030005041456444436643840, 80526560834914097238386933760,
    867995839597510206035066880000, 80526622262571862691193815040, 768030005041456444436643840, 2322641404118444525391708160, 81286658313422901871095316480, 81286698181448531175863746560,
    2322621470105629873007493120, 40001562762575856481075200, 4194091710151775897832652800, 45208116645703656564326400000, 4194094909508951181833011200, 40001562762575856481075200,
    1990835489244381021764321280, 69674278554362487318081699840, 69674312726955883865026068480, 1990818402947682748292136960, 446174857675326745477120000, 1525502067993792934313984000,
    446174713560138669621248000, 268240734874462079418368000, 22459564673880566405057740800, 22459572801977173883328921600, 268232606777854601147187200, 1232048133087336379617116160,
    129178024672674697653245706240, 1392409992687672622181253120000, 129178123212875696400456744960, 1232048133087336379617116160, 2322641404118444525391708160, 81286658313422901871095316480,
    81286698181448531175863746560, 2322621470105629873007493120, 696027192068819902770708480, 72977195756640900622288158720
  ]
def negativeScales : Array ℕ := #[
    29, 36, 40, 40, 36, 30,
    35, 33, 30, 35, 35, 30,
    30, 35, 33, 26, 32, 31,
    25, 25, 31, 35, 30, 25,
    26, 32, 31, 25, 24, 31,
    34, 30, 24, 30, 35, 35,
    30, 25, 31, 35, 30, 25,
    29, 33, 33, 29, 25, 30,
    28, 26, 33, 32, 25, 28,
    35, 39, 34, 28, 30, 35,
    35, 30, 29, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29983718501853114, 36281373780698345, 40410554024256256, 40410554731843331, 36281361398750450, 30599845486363411,
    35373448498096429, 33599845020370545, 30907824998598603, 35037005237134468, 35037005944721543, 30907812616649604,
    30540308359381406, 35313911371119063, 33540307893388539, 26448523321691397, 32836181136866017, 31836181658975997,
    25448479605205383, 25048258735828486, 31760416970726828, 35190568473585109, 30760418071249973, 25048258735828486,
    26368352973007371, 32756010787110957, 31756011309220926, 25368309256521358, 24311293141662280, 31023451376278724,
    34453602879418956, 30023452476801862, 24311293141662280, 30907824998598603, 35037005237134468, 35037005944721543,
    30907812616649604, 25048258735828486, 31760416970726828, 35190568473585109, 30760418071249973, 25048258735828486,
    29685432572291307, 33814612816665734, 33814613524252821, 29685420190343397, 25527739685878029, 30301342697616007,
    28527739219885163, 26793658808307411, 33181316621587323, 32181317143697289, 25793615091820888, 28993117202842617,
    35705275416334380, 39135426919392648, 34705276516857520, 28993117202842617, 30907824998598603, 35037005237134468,
    35037005944721543, 30907812616649604, 29169274136789852, 35881432374525255
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
noncomputable def negativeCeiling : ℝ := 1001092257 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1224047820534821208320901120, coefficient := (-1224047820534821208320901120) }, { argument := 96290076496453228752667672576, coefficient := (-96290076496453228752667672576) }, { argument := 3369912606079332303284551548928, coefficient := (-3369912606079332303284551548928) }, { argument := 3369914258893766249605094178816, coefficient := (-3369914258893766249605094178816) }, { argument := 96289250089236255592396357632, coefficient := (-96289250089236255592396357632) }, { argument := 15009322212197991717850316800, coefficient := (-15009322212197991717850316800) }, { argument := 51317889567311194310322421760, coefficient := (-51317889567311194310322421760) }, { argument := 15009317364163064846058782720, coefficient := (-15009317364163064846058782720) }, { argument := 2322641404118444525391708160, coefficient := (-2322641404118444525391708160) }, { argument := 81286658313422901871095316480, coefficient := (-81286658313422901871095316480) }, { argument := 81286698181448531175863746560, coefficient := (-81286698181448531175863746560) }, { argument := 2322621470105629873007493120, coefficient := (-2322621470105629873007493120) }, { argument := 14402524405759547344001433600, coefficient := (-14402524405759547344001433600) }, { argument := 49243206754839635919655403520, coefficient := (-49243206754839635919655403520) }, { argument := 14402519753721276255373885440, coefficient := (-14402519753721276255373885440) }, { argument := 211168238092661636988928000, coefficient := (-211168238092661636988928000) }, { argument := 17680933892203850148662476800, coefficient := (-17680933892203850148662476800) }, { argument := 17680940290918200716663193600, coefficient := (-17680940290918200716663193600) }, { argument := 211161839378311068988211200, coefficient := (-211161839378311068988211200) }, { argument := 40001562762575856481075200, coefficient := (-40001562762575856481075200) }, { argument := 4194091710151775897832652800, coefficient := (-4194091710151775897832652800) }, { argument := 45208116645703656564326400000, coefficient := (-45208116645703656564326400000) }, { argument := 4194094909508951181833011200, coefficient := (-4194094909508951181833011200) }, { argument := 40001562762575856481075200, coefficient := (-40001562762575856481075200) }, { argument := 199753738736301548503040000, coefficient := (-199753738736301548503040000) }, { argument := 16725207735868506897383424000, coefficient := (-16725207735868506897383424000) }, { argument := 16725213788706406083330048000, coefficient := (-16725213788706406083330048000) }, { argument := 199747685898402362556416000, coefficient := (-199747685898402362556416000) }, { argument := 768030005041456444436643840, coefficient := (-768030005041456444436643840) }, { argument := 80526560834914097238386933760, coefficient := (-80526560834914097238386933760) }, { argument := 867995839597510206035066880000, coefficient := (-867995839597510206035066880000) }, { argument := 80526622262571862691193815040, coefficient := (-80526622262571862691193815040) }, { argument := 768030005041456444436643840, coefficient := (-768030005041456444436643840) }, { argument := 2322641404118444525391708160, coefficient := (-2322641404118444525391708160) }, { argument := 81286658313422901871095316480, coefficient := (-81286658313422901871095316480) }, { argument := 81286698181448531175863746560, coefficient := (-81286698181448531175863746560) }, { argument := 2322621470105629873007493120, coefficient := (-2322621470105629873007493120) }, { argument := 40001562762575856481075200, coefficient := (-40001562762575856481075200) }, { argument := 4194091710151775897832652800, coefficient := (-4194091710151775897832652800) }, { argument := 45208116645703656564326400000, coefficient := (-45208116645703656564326400000) }, { argument := 4194094909508951181833011200, coefficient := (-4194094909508951181833011200) }, { argument := 40001562762575856481075200, coefficient := (-40001562762575856481075200) }, { argument := 1990835489244381021764321280, coefficient := (-1990835489244381021764321280) }, { argument := 69674278554362487318081699840, coefficient := (-69674278554362487318081699840) }, { argument := 69674312726955883865026068480, coefficient := (-69674312726955883865026068480) }, { argument := 1990818402947682748292136960, coefficient := (-1990818402947682748292136960) }, { argument := 446174857675326745477120000, coefficient := (-446174857675326745477120000) }, { argument := 1525502067993792934313984000, coefficient := (-1525502067993792934313984000) }, { argument := 446174713560138669621248000, coefficient := (-446174713560138669621248000) }, { argument := 268240734874462079418368000, coefficient := (-268240734874462079418368000) }, { argument := 22459564673880566405057740800, coefficient := (-22459564673880566405057740800) }, { argument := 22459572801977173883328921600, coefficient := (-22459572801977173883328921600) }, { argument := 268232606777854601147187200, coefficient := (-268232606777854601147187200) }, { argument := 1232048133087336379617116160, coefficient := (-1232048133087336379617116160) }, { argument := 129178024672674697653245706240, coefficient := (-129178024672674697653245706240) }, { argument := 1392409992687672622181253120000, coefficient := (-1392409992687672622181253120000) }, { argument := 129178123212875696400456744960, coefficient := (-129178123212875696400456744960) }, { argument := 1232048133087336379617116160, coefficient := (-1232048133087336379617116160) }, { argument := 2322641404118444525391708160, coefficient := (-2322641404118444525391708160) }, { argument := 81286658313422901871095316480, coefficient := (-81286658313422901871095316480) }, { argument := 81286698181448531175863746560, coefficient := (-81286698181448531175863746560) }, { argument := 2322621470105629873007493120, coefficient := (-2322621470105629873007493120) }, { argument := 696027192068819902770708480, coefficient := (-696027192068819902770708480) }, { argument := 72977195756640900622288158720, coefficient := (-72977195756640900622288158720) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1
