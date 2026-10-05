import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 23, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23

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
def constantNumerator : ℤ := (-124078196812316462767583315099648)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    47557, 8341051, 2085263, 11889, 2004627, 217343565,
    711, 4248435207, 225, 27, 711, 1413,
    225, 21807, 1395, 869374565, 711, 27,
    1395, 27, 711, 711, 2004627, 703195167,
    193946523, 732139197, 2029342887, 89877657, 1464278079, 89877657,
    175024911, 3306551697, 175024911, 2029342887, 3306551697, 87899409,
    175024911, 175024911, 193946523, 258285, 122110515, 4635217785,
    488442395, 258285, 110085675, 2146967025, 4293932475, 13760775,
    1378209661, 212832305, 176346767, 22682005883, 1185779985, 1378209211,
    4749200863, 4749200863, 3399235957, 176346767, 91213845, 1778915535,
    3557829765, 11401785, 95071825, 11112050625
  ]
def negativeCoefficients : Array ℕ := #[
    224581582825831717427740672, 39389499674306337079344234496, 39389504396672819948989448192, 224576860459348847782526976, 591661459715970517237235712, 16037124478490626891091804160,
    13752740123936021491457458176, 78369796977266262177598144512, 8704265901225330057884467200, 522255954073519803473068032, 13752740123936021491457458176, 13665697464923768190878613504,
    8704265901225330057884467200, 210904362786689747302540640256, 13491612146899261589720924160, 16037130104747569372505047040, 13752740123936021491457458176, 522255954073519803473068032,
    13491612146899261589720924160, 522255954073519803473068032, 13752740123936021491457458176, 13752740123936021491457458176, 591661459715970517237235712, 6485830639759224229054119936,
    7155363747533646495624462336, 13505584393390219931368292352, 74869537748583764551777910784, 6631800546494599191066574848, 13505581488028028322113912832, 6631800546494599191066574848,
    6457279479481583422880612352, 243980451684196043923975569408, 6457279479481583422880612352, 74869537748583764551777910784, 243980451684196043923975569408, 6485831608213288098805579776,
    6457279479481583422880612352, 6457279479481583422880612352, 7155363747533646495624462336, 76232276689249144626216960, 9010165675655485232995368960, 85504676205801864574858690560,
    9010171855314749925695160320, 76232276689249144626216960, 4061444545813131487189401600, 158418204979474306988349849600, 158418146872230474803262259200, 4061463914894408882218598400,
    6355870224095250036287340544, 3926063060952693770949754880, 203313979942193070281326592, 26150572350129714711712759808, 5468444977755537752394301440, 6355868148836541743962783744,
    5475455804650096134128140288, 5475455804650096134128140288, 3919052234058135389215916032, 203313979942193070281326592, 210324806836751452015165440, 8203799900722776611896688640,
    8203796891597649588026081280, 210325809878460459972034560, 7015062497582006368259276800, 25622644251684908637880320000
  ]
def negativeScales : Array ℕ := #[
    15, 22, 20, 13, 20, 27,
    9, 31, 7, 4, 9, 10,
    7, 14, 10, 29, 9, 4,
    10, 4, 9, 9, 20, 29,
    27, 29, 30, 26, 30, 26,
    27, 31, 27, 30, 31, 26,
    27, 27, 27, 17, 26, 32,
    28, 17, 26, 30, 31, 23,
    30, 27, 27, 34, 30, 30,
    32, 32, 31, 27, 26, 30,
    31, 23, 26, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15537370089132821, 22991797769553624, 20991797942516892, 13537339752690042, 20934902397450046, 27695402140816090,
    9473705749619526, 31984284434848281, 7813781192070436, 4754887502413606, 9473705749619526, 10464545750334019,
    7813781192070436, 14412503690893670, 10446049406716591, 29695402646952436, 9473705749619526, 4754887502413606,
    10446049406716591, 4754887502413606, 9473705749619526, 9473705749619526, 20934902397450046, 29389349914095162,
    27531083671109095, 29447542724179557, 30918365510038374, 26421459179933871, 30447542413822600, 26421459179933871,
    27382985032119223, 31622680311876171, 27382985032119223, 30918365510038374, 31622680311876171, 26389350129516107,
    27382985032119223, 27382985032119223, 27531083671109095, 17978604352023330, 26863612198235179, 32109989979235796,
    28863613187713221, 17978604352023330, 26714051508292011, 30999652910724777, 31999652381548983, 23714058388506827,
    30360148229602168, 27665141907741845, 27393839885893281, 34400829179519421, 30143189204515315, 30360147758546934,
    32145037628907683, 32145037628907683, 31662563363638131, 27393839885893281, 26442749486374258, 30728350865500756,
    31728350336325159, 23442756366589058, 26502514518911877, 33371406026044057
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
noncomputable def negativeCeiling : ℝ := 118392913 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 224581582825831717427740672, coefficient := (-224581582825831717427740672) }, { argument := 39389499674306337079344234496, coefficient := (-39389499674306337079344234496) }, { argument := 39389504396672819948989448192, coefficient := (-39389504396672819948989448192) }, { argument := 224576860459348847782526976, coefficient := (-224576860459348847782526976) }, { argument := 591661459715970517237235712, coefficient := (-591661459715970517237235712) }, { argument := 16037124478490626891091804160, coefficient := (-16037124478490626891091804160) }, { argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 78369796977266262177598144512, coefficient := (-78369796977266262177598144512) }, { argument := 8704265901225330057884467200, coefficient := (-8704265901225330057884467200) }, { argument := 522255954073519803473068032, coefficient := (-522255954073519803473068032) }, { argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 13665697464923768190878613504, coefficient := (-13665697464923768190878613504) }, { argument := 8704265901225330057884467200, coefficient := (-8704265901225330057884467200) }, { argument := 210904362786689747302540640256, coefficient := (-210904362786689747302540640256) }, { argument := 13491612146899261589720924160, coefficient := (-13491612146899261589720924160) }, { argument := 16037130104747569372505047040, coefficient := (-16037130104747569372505047040) }, { argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 522255954073519803473068032, coefficient := (-522255954073519803473068032) }, { argument := 13491612146899261589720924160, coefficient := (-13491612146899261589720924160) }, { argument := 522255954073519803473068032, coefficient := (-522255954073519803473068032) }, { argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 591661459715970517237235712, coefficient := (-591661459715970517237235712) }, { argument := 6485830639759224229054119936, coefficient := (-6485830639759224229054119936) }, { argument := 7155363747533646495624462336, coefficient := (-7155363747533646495624462336) }, { argument := 13505584393390219931368292352, coefficient := (-13505584393390219931368292352) }, { argument := 74869537748583764551777910784, coefficient := (-74869537748583764551777910784) }, { argument := 6631800546494599191066574848, coefficient := (-6631800546494599191066574848) }, { argument := 13505581488028028322113912832, coefficient := (-13505581488028028322113912832) }, { argument := 6631800546494599191066574848, coefficient := (-6631800546494599191066574848) }, { argument := 6457279479481583422880612352, coefficient := (-6457279479481583422880612352) }, { argument := 243980451684196043923975569408, coefficient := (-243980451684196043923975569408) }, { argument := 6457279479481583422880612352, coefficient := (-6457279479481583422880612352) }, { argument := 74869537748583764551777910784, coefficient := (-74869537748583764551777910784) }, { argument := 243980451684196043923975569408, coefficient := (-243980451684196043923975569408) }, { argument := 6485831608213288098805579776, coefficient := (-6485831608213288098805579776) }, { argument := 6457279479481583422880612352, coefficient := (-6457279479481583422880612352) }, { argument := 6457279479481583422880612352, coefficient := (-6457279479481583422880612352) }, { argument := 7155363747533646495624462336, coefficient := (-7155363747533646495624462336) }, { argument := 76232276689249144626216960, coefficient := (-76232276689249144626216960) }, { argument := 9010165675655485232995368960, coefficient := (-9010165675655485232995368960) }, { argument := 85504676205801864574858690560, coefficient := (-85504676205801864574858690560) }, { argument := 9010171855314749925695160320, coefficient := (-9010171855314749925695160320) }, { argument := 76232276689249144626216960, coefficient := (-76232276689249144626216960) }, { argument := 4061444545813131487189401600, coefficient := (-4061444545813131487189401600) }, { argument := 158418204979474306988349849600, coefficient := (-158418204979474306988349849600) }, { argument := 158418146872230474803262259200, coefficient := (-158418146872230474803262259200) }, { argument := 4061463914894408882218598400, coefficient := (-4061463914894408882218598400) }, { argument := 6355870224095250036287340544, coefficient := (-6355870224095250036287340544) }, { argument := 3926063060952693770949754880, coefficient := (-3926063060952693770949754880) }, { argument := 203313979942193070281326592, coefficient := (-203313979942193070281326592) }, { argument := 26150572350129714711712759808, coefficient := (-26150572350129714711712759808) }, { argument := 5468444977755537752394301440, coefficient := (-5468444977755537752394301440) }, { argument := 6355868148836541743962783744, coefficient := (-6355868148836541743962783744) }, { argument := 5475455804650096134128140288, coefficient := (-5475455804650096134128140288) }, { argument := 5475455804650096134128140288, coefficient := (-5475455804650096134128140288) }, { argument := 3919052234058135389215916032, coefficient := (-3919052234058135389215916032) }, { argument := 203313979942193070281326592, coefficient := (-203313979942193070281326592) }, { argument := 210324806836751452015165440, coefficient := (-210324806836751452015165440) }, { argument := 8203799900722776611896688640, coefficient := (-8203799900722776611896688640) }, { argument := 8203796891597649588026081280, coefficient := (-8203796891597649588026081280) }, { argument := 210325809878460459972034560, coefficient := (-210325809878460459972034560) }, { argument := 7015062497582006368259276800, coefficient := (-7015062497582006368259276800) }, { argument := 25622644251684908637880320000, coefficient := (-25622644251684908637880320000) }] }

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
def constantNumerator : ℤ := (-344529069622143414276416853770240)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3042297375, 2004627, 258285, 2004627, 258285, 2004627,
    217343565, 711, 4248435207, 225, 27, 711,
    1413, 225, 21807, 1395, 869374565, 711,
    27, 1395, 27, 711, 711, 2004627,
    11590764855, 22668583275, 36382275915, 237190785975, 10504953225, 72764528385,
    10504953225, 20457014175, 386471700225, 20457014175, 237190785975, 386471700225,
    5795386335, 20457014175, 20457014175, 22668583275, 1423779783, 4150802915,
    3439236701, 70460486249, 23125901955, 1423779583, 92622202189, 92622202189,
    66294252271, 3439236701, 613334475, 11961673425, 23923338075, 76667175,
    994775925, 116269993125, 31832818875, 217343565, 122110515, 217343565,
    122110515, 44057675, 5149486875, 1409845125
  ]
def negativeCoefficients : Array ℕ := #[
    7015060134092921924222976000, 591661459715970517237235712, 76232276689249144626216960, 591661459715970517237235712, 76232276689249144626216960, 591661459715970517237235712,
    16037124478490626891091804160, 13752740123936021491457458176, 78369796977266262177598144512, 8704265901225330057884467200, 522255954073519803473068032, 13752740123936021491457458176,
    13665697464923768190878613504, 8704265901225330057884467200, 210904362786689747302540640256, 13491612146899261589720924160, 16037130104747569372505047040, 13752740123936021491457458176,
    522255954073519803473068032, 13491612146899261589720924160, 522255954073519803473068032, 13752740123936021491457458176, 13752740123936021491457458176, 591661459715970517237235712,
    26726484112341525043567656960, 26135097136718606810637926400, 167783633155773001116061532160, 273462357845177617603991961600, 24222772955983098995225395200, 167783579095283650101006827520,
    24222772955983098995225395200, 23585331562404596390087884800, 891143068222746641982239539200, 23585331562404596390087884800, 273462357845177617603991961600, 891143068222746641982239539200,
    26726502132504642048585891840, 23585331562404596390087884800, 23585331562404596390087884800, 26135097136718606810637926400, 13132050637161360702427889664, 153137598146825163422071521280,
    7930339904032017391500132352, 162470819643054263007390466048, 213298797418792191909313904640, 13132048792486953331472728064, 213572257415482951129710460928, 213572257415482951129710460928,
    152864138150134404201674964992, 7930339904032017391500132352, 5657012045954004571442380800, 220653928364267784733773004800, 220653847429178161333115289600, 5657039024317212371661619200,
    73401507596650749560566579200, 268100350828605507454894080000, 73401482866484475743698944000, 16037124478490626891091804160, 9010165675655485232995368960, 16037124478490626891091804160,
    9010165675655485232995368960, 6501765241661371755947622400, 23747816623512842152181760000, 6501763051110513002938368000
  ]
def negativeScales : Array ℕ := #[
    31, 20, 17, 20, 17, 20,
    27, 9, 31, 7, 4, 9,
    10, 7, 14, 10, 29, 9,
    4, 10, 4, 9, 9, 20,
    33, 34, 35, 37, 33, 36,
    33, 34, 38, 34, 37, 38,
    32, 34, 34, 34, 30, 31,
    31, 36, 34, 30, 36, 36,
    35, 31, 29, 33, 34, 26,
    29, 36, 34, 27, 26, 27,
    26, 25, 32, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31502514032844283, 20934902397450046, 17978604352023330, 20934902397450046, 17978604352023330, 20934902397450046,
    27695402140816090, 9473705749619526, 31984284434848281, 7813781192070436, 4754887502413606, 9473705749619526,
    10464545750334019, 7813781192070436, 14412503690893670, 10446049406716591, 29695402646952436, 9473705749619526,
    4754887502413606, 10446049406716591, 4754887502413606, 9473705749619526, 9473705749619526, 20934902397450046,
    33432256719368784, 34399975178240832, 35082516743335885, 37787257011619388, 33290350687066327, 36082516278494285,
    33290350687066327, 34251876539251692, 38491571818998382, 34251876539251692, 37787257011619388, 38491571818998382,
    32432257692096476, 34251876539251692, 34251876539251692, 34399975178240832, 30407078874909645, 31950743297253785,
    31679441264925027, 36036095379803582, 34428790583502799, 30407078672252582, 36430639007895169, 36430639007895169,
    35948164752701984, 31679441264925027, 29192098804996261, 33477700183983851, 34477699654808255, 26192105685211061,
    29889796355426317, 36758687859197099, 34889795869358690, 27695402140816090, 26863612198235179, 27695402140816090,
    26863612198235179, 25392890027737089, 32261781534869557, 30392889541669495
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
noncomputable def negativeCeiling : ℝ := 2292340579 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7015060134092921924222976000, coefficient := (-7015060134092921924222976000) }, { argument := 591661459715970517237235712, coefficient := (-591661459715970517237235712) }, { argument := 76232276689249144626216960, coefficient := (-76232276689249144626216960) }, { argument := 591661459715970517237235712, coefficient := (-591661459715970517237235712) }, { argument := 76232276689249144626216960, coefficient := (-76232276689249144626216960) }, { argument := 591661459715970517237235712, coefficient := (-591661459715970517237235712) }, { argument := 16037124478490626891091804160, coefficient := (-16037124478490626891091804160) }, { argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 78369796977266262177598144512, coefficient := (-78369796977266262177598144512) }, { argument := 8704265901225330057884467200, coefficient := (-8704265901225330057884467200) }, { argument := 522255954073519803473068032, coefficient := (-522255954073519803473068032) }, { argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 13665697464923768190878613504, coefficient := (-13665697464923768190878613504) }, { argument := 8704265901225330057884467200, coefficient := (-8704265901225330057884467200) }, { argument := 210904362786689747302540640256, coefficient := (-210904362786689747302540640256) }, { argument := 13491612146899261589720924160, coefficient := (-13491612146899261589720924160) }, { argument := 16037130104747569372505047040, coefficient := (-16037130104747569372505047040) }, { argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 522255954073519803473068032, coefficient := (-522255954073519803473068032) }, { argument := 13491612146899261589720924160, coefficient := (-13491612146899261589720924160) }, { argument := 522255954073519803473068032, coefficient := (-522255954073519803473068032) }, { argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 13752740123936021491457458176, coefficient := (-13752740123936021491457458176) }, { argument := 591661459715970517237235712, coefficient := (-591661459715970517237235712) }, { argument := 26726484112341525043567656960, coefficient := (-26726484112341525043567656960) }, { argument := 26135097136718606810637926400, coefficient := (-26135097136718606810637926400) }, { argument := 167783633155773001116061532160, coefficient := (-167783633155773001116061532160) }, { argument := 273462357845177617603991961600, coefficient := (-273462357845177617603991961600) }, { argument := 24222772955983098995225395200, coefficient := (-24222772955983098995225395200) }, { argument := 167783579095283650101006827520, coefficient := (-167783579095283650101006827520) }, { argument := 24222772955983098995225395200, coefficient := (-24222772955983098995225395200) }, { argument := 23585331562404596390087884800, coefficient := (-23585331562404596390087884800) }, { argument := 891143068222746641982239539200, coefficient := (-891143068222746641982239539200) }, { argument := 23585331562404596390087884800, coefficient := (-23585331562404596390087884800) }, { argument := 273462357845177617603991961600, coefficient := (-273462357845177617603991961600) }, { argument := 891143068222746641982239539200, coefficient := (-891143068222746641982239539200) }, { argument := 26726502132504642048585891840, coefficient := (-26726502132504642048585891840) }, { argument := 23585331562404596390087884800, coefficient := (-23585331562404596390087884800) }, { argument := 23585331562404596390087884800, coefficient := (-23585331562404596390087884800) }, { argument := 26135097136718606810637926400, coefficient := (-26135097136718606810637926400) }, { argument := 13132050637161360702427889664, coefficient := (-13132050637161360702427889664) }, { argument := 153137598146825163422071521280, coefficient := (-153137598146825163422071521280) }, { argument := 7930339904032017391500132352, coefficient := (-7930339904032017391500132352) }, { argument := 162470819643054263007390466048, coefficient := (-162470819643054263007390466048) }, { argument := 213298797418792191909313904640, coefficient := (-213298797418792191909313904640) }, { argument := 13132048792486953331472728064, coefficient := (-13132048792486953331472728064) }, { argument := 213572257415482951129710460928, coefficient := (-213572257415482951129710460928) }, { argument := 213572257415482951129710460928, coefficient := (-213572257415482951129710460928) }, { argument := 152864138150134404201674964992, coefficient := (-152864138150134404201674964992) }, { argument := 7930339904032017391500132352, coefficient := (-7930339904032017391500132352) }, { argument := 5657012045954004571442380800, coefficient := (-5657012045954004571442380800) }, { argument := 220653928364267784733773004800, coefficient := (-220653928364267784733773004800) }, { argument := 220653847429178161333115289600, coefficient := (-220653847429178161333115289600) }, { argument := 5657039024317212371661619200, coefficient := (-5657039024317212371661619200) }, { argument := 73401507596650749560566579200, coefficient := (-73401507596650749560566579200) }, { argument := 268100350828605507454894080000, coefficient := (-268100350828605507454894080000) }, { argument := 73401482866484475743698944000, coefficient := (-73401482866484475743698944000) }, { argument := 16037124478490626891091804160, coefficient := (-16037124478490626891091804160) }, { argument := 9010165675655485232995368960, coefficient := (-9010165675655485232995368960) }, { argument := 16037124478490626891091804160, coefficient := (-16037124478490626891091804160) }, { argument := 9010165675655485232995368960, coefficient := (-9010165675655485232995368960) }, { argument := 6501765241661371755947622400, coefficient := (-6501765241661371755947622400) }, { argument := 23747816623512842152181760000, coefficient := (-23747816623512842152181760000) }, { argument := 6501763051110513002938368000, coefficient := (-6501763051110513002938368000) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23
