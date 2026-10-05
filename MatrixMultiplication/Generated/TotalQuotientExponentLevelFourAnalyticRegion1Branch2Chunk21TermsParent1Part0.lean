import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 21, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-17009512260432832242339142518702080)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    79711659, 1007, 1350885673, 15847, 477, 2701717803,
    477, 477, 40863, 477, 15847, 40863,
    9970651, 477, 477, 1007, 35816330924309, 1869,
    105, 129297471954391, 5677, 8954081682501, 5677, 5677,
    1869, 105, 18506107246628917, 421007823, 18506104160366539, 421007823,
    2947054761, 4994859863, 2947054761, 7743, 7743, 81082939,
    435, 435, 1045, 35816324908203, 1869, 105,
    129297450432169, 5677, 8954080178475, 5677, 5677, 1869,
    105, 66821190446440855, 713551409, 66821179405540969, 713551409, 1371421409,
    23519, 23519, 16445, 495, 4626526273737613, 421007823,
    4626525502172275, 421007823, 685697623, 495
  ]
def negativeCoefficients : Array ℕ := #[
    376427666755534500725117681664, 38956425611261810525731815424, 12758754448728007291549899554816, 306525559414928456505100337152, 36906087421195399445430140928, 12758501599059415002136222629888,
    36906087421195399445430140928, 36906087421195399445430140928, 1580810744541202942912591036416, 36906087421195399445430140928, 306525559414928456505100337152, 1580810744541202942912591036416,
    376680544758325687356665888768, 36906087421195399445430140928, 36906087421195399445430140928, 38956425611261810525731815424, 10323354534687768638392050384896, 144606870839023483361653948416,
    8123981507810308054025502720, 37267458976879517746007747067904, 219618300094471994393822756864, 10323353325761660793386723966976, 219618300094471994393822756864, 219618300094471994393822756864,
    144606870839023483361653948416, 8123981507810308054025502720, 10418012212499553289882623279104, 31064894255642439440633167872, 10418010475088291348835014279168, 31064894255642439440633167872,
    27181782473687134510554021888, 92138901576804952886485188608, 27181782473687134510554021888, 149771401940417179195998732288, 149771401940417179195998732288, 382903353466163987813754732544,
    8414123704517819055954984960, 8414123704517819055954984960, 40426479407913199602174525440, 10323352800663273289822117036032, 144606870839023483361653948416, 8123981507810308054025502720,
    37267452773521375065361912692736, 219618300094471994393822756864, 10323351591737741905569094041600, 219618300094471994393822756864, 219618300094471994393822756864, 144606870839023483361653948416,
    8123981507810308054025502720, 37616986049380497728900704501760, 105301601802062803298840215552, 37616979833906421175831733731328, 105301601802062803298840215552, 12952708991502926404594148835328,
    227461810812131708479316426752, 227461810812131708479316426752, 318092561657001228448689029120, 38298769965391452254691655680, 10418011001212261640492520833024, 31064894255642439440633167872,
    10418009263801577286097122099200, 31064894255642439440633167872, 12952461888954343767538696978432, 38298769965391452254691655680
  ]
def negativeScales : Array ℕ := #[
    26, 9, 30, 13, 8, 31,
    8, 8, 15, 8, 13, 15,
    23, 8, 8, 9, 45, 10,
    6, 46, 12, 43, 12, 12,
    10, 6, 54, 28, 54, 28,
    31, 32, 31, 12, 12, 26,
    8, 8, 10, 45, 10, 6,
    46, 12, 43, 12, 12, 10,
    6, 55, 29, 55, 29, 30,
    14, 14, 14, 8, 52, 28,
    52, 28, 29, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26248287419183971, 9975847984030745, 30331258436884330, 13951922139528846, 8897845460207421, 31331229845646910,
    8897845460207421, 8897845460207421, 15318507504478234, 8897845460207421, 13951922139528846, 15318507504478234,
    23249256272925598, 8897845460207421, 8897845460207421, 9975847984030745, 45025682786704803, 10868050856180197,
    6714245517766967, 46877687398945782, 12470913026274977, 43025682617756638, 12470913026274977, 12470913026274977,
    10868050856180197, 6714245517766967, 54038850974907626, 28649271800246275, 54038850734309441, 28649271800246275,
    31456626722283024, 32217797055969710, 31456626722283024, 12918676932896795, 12918676932896795, 26272895047094784,
    8764871591046276, 8764871591046276, 10029287226968246, 45025682544373810, 10868050856180197, 6714245517766967,
    46877687158801820, 12470913026274977, 43025682375425698, 12470913026274977, 12470913026274977, 10868050856180197,
    6714245517766967, 55891155207017220, 29410442133912116, 55891154968639936, 29410442133912116, 30353024803117645,
    14521539099345394, 14521539099345394, 14005361387722765, 8951284725619456, 52038850807167539, 28649271800246275,
    52038850566569407, 28649271800246275, 29352997280147572, 8951284725619456
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
noncomputable def negativeCeiling : ℝ := 161648011211 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 376427666755534500725117681664, coefficient := (-376427666755534500725117681664) }, { argument := 38956425611261810525731815424, coefficient := (-38956425611261810525731815424) }, { argument := 12758754448728007291549899554816, coefficient := (-12758754448728007291549899554816) }, { argument := 306525559414928456505100337152, coefficient := (-306525559414928456505100337152) }, { argument := 36906087421195399445430140928, coefficient := (-36906087421195399445430140928) }, { argument := 12758501599059415002136222629888, coefficient := (-12758501599059415002136222629888) }, { argument := 36906087421195399445430140928, coefficient := (-36906087421195399445430140928) }, { argument := 36906087421195399445430140928, coefficient := (-36906087421195399445430140928) }, { argument := 1580810744541202942912591036416, coefficient := (-1580810744541202942912591036416) }, { argument := 36906087421195399445430140928, coefficient := (-36906087421195399445430140928) }, { argument := 306525559414928456505100337152, coefficient := (-306525559414928456505100337152) }, { argument := 1580810744541202942912591036416, coefficient := (-1580810744541202942912591036416) }, { argument := 376680544758325687356665888768, coefficient := (-376680544758325687356665888768) }, { argument := 36906087421195399445430140928, coefficient := (-36906087421195399445430140928) }, { argument := 36906087421195399445430140928, coefficient := (-36906087421195399445430140928) }, { argument := 38956425611261810525731815424, coefficient := (-38956425611261810525731815424) }, { argument := 10323354534687768638392050384896, coefficient := (-10323354534687768638392050384896) }, { argument := 144606870839023483361653948416, coefficient := (-144606870839023483361653948416) }, { argument := 8123981507810308054025502720, coefficient := (-8123981507810308054025502720) }, { argument := 37267458976879517746007747067904, coefficient := (-37267458976879517746007747067904) }, { argument := 219618300094471994393822756864, coefficient := (-219618300094471994393822756864) }, { argument := 10323353325761660793386723966976, coefficient := (-10323353325761660793386723966976) }, { argument := 219618300094471994393822756864, coefficient := (-219618300094471994393822756864) }, { argument := 219618300094471994393822756864, coefficient := (-219618300094471994393822756864) }, { argument := 144606870839023483361653948416, coefficient := (-144606870839023483361653948416) }, { argument := 8123981507810308054025502720, coefficient := (-8123981507810308054025502720) }, { argument := 10418012212499553289882623279104, coefficient := (-10418012212499553289882623279104) }, { argument := 31064894255642439440633167872, coefficient := (-31064894255642439440633167872) }, { argument := 10418010475088291348835014279168, coefficient := (-10418010475088291348835014279168) }, { argument := 31064894255642439440633167872, coefficient := (-31064894255642439440633167872) }, { argument := 27181782473687134510554021888, coefficient := (-27181782473687134510554021888) }, { argument := 92138901576804952886485188608, coefficient := (-92138901576804952886485188608) }, { argument := 27181782473687134510554021888, coefficient := (-27181782473687134510554021888) }, { argument := 149771401940417179195998732288, coefficient := (-149771401940417179195998732288) }, { argument := 149771401940417179195998732288, coefficient := (-149771401940417179195998732288) }, { argument := 382903353466163987813754732544, coefficient := (-382903353466163987813754732544) }, { argument := 8414123704517819055954984960, coefficient := (-8414123704517819055954984960) }, { argument := 8414123704517819055954984960, coefficient := (-8414123704517819055954984960) }, { argument := 40426479407913199602174525440, coefficient := (-40426479407913199602174525440) }, { argument := 10323352800663273289822117036032, coefficient := (-10323352800663273289822117036032) }, { argument := 144606870839023483361653948416, coefficient := (-144606870839023483361653948416) }, { argument := 8123981507810308054025502720, coefficient := (-8123981507810308054025502720) }, { argument := 37267452773521375065361912692736, coefficient := (-37267452773521375065361912692736) }, { argument := 219618300094471994393822756864, coefficient := (-219618300094471994393822756864) }, { argument := 10323351591737741905569094041600, coefficient := (-10323351591737741905569094041600) }, { argument := 219618300094471994393822756864, coefficient := (-219618300094471994393822756864) }, { argument := 219618300094471994393822756864, coefficient := (-219618300094471994393822756864) }, { argument := 144606870839023483361653948416, coefficient := (-144606870839023483361653948416) }, { argument := 8123981507810308054025502720, coefficient := (-8123981507810308054025502720) }, { argument := 37616986049380497728900704501760, coefficient := (-37616986049380497728900704501760) }, { argument := 105301601802062803298840215552, coefficient := (-105301601802062803298840215552) }, { argument := 37616979833906421175831733731328, coefficient := (-37616979833906421175831733731328) }, { argument := 105301601802062803298840215552, coefficient := (-105301601802062803298840215552) }, { argument := 12952708991502926404594148835328, coefficient := (-12952708991502926404594148835328) }, { argument := 227461810812131708479316426752, coefficient := (-227461810812131708479316426752) }, { argument := 227461810812131708479316426752, coefficient := (-227461810812131708479316426752) }, { argument := 318092561657001228448689029120, coefficient := (-318092561657001228448689029120) }, { argument := 38298769965391452254691655680, coefficient := (-38298769965391452254691655680) }, { argument := 10418011001212261640492520833024, coefficient := (-10418011001212261640492520833024) }, { argument := 31064894255642439440633167872, coefficient := (-31064894255642439440633167872) }, { argument := 10418009263801577286097122099200, coefficient := (-10418009263801577286097122099200) }, { argument := 31064894255642439440633167872, coefficient := (-31064894255642439440633167872) }, { argument := 12952461888954343767538696978432, coefficient := (-12952461888954343767538696978432) }, { argument := 38298769965391452254691655680, coefficient := (-38298769965391452254691655680) }] }

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
def constantNumerator : ℤ := 39831643412068409423585844658176000
def positiveArguments : Array ℕ := #[
    471, 27, 513, 783, 8073, 243,
    783, 243, 243, 20817, 243, 8073,
    20817, 27, 243, 243, 513, 855,
    15219, 855, 27075, 46227, 855, 46227,
    46227, 15219, 855, 7245, 8115, 7245,
    8115, 3, 767, 12499026945, 12499024895, 8801974035,
    31687513563, 4400986505
  ]
def positiveCoefficients : Array ℕ := #[
    298531716353748024052473604866048, 66848762121410534844552708096, 79382905019175010127906340864, 60581690672528297202875891712, 624618121071929684953789366272, 75204857386586851700121796608,
    60581690672528297202875891712, 75204857386586851700121796608, 75204857386586851700121796608, 3221274724725470147821883621376, 75204857386586851700121796608, 624618121071929684953789366272,
    3221274724725470147821883621376, 66848762121410534844552708096, 75204857386586851700121796608, 75204857386586851700121796608, 79382905019175010127906340864, 33076210424656254219960975360,
    588756545558881325115305361408, 33076210424656254219960975360, 523706665057057358482715443200, 894160221813207405746278367232, 33076210424656254219960975360, 894160221813207405746278367232,
    894160221813207405746278367232, 588756545558881325115305361408, 33076210424656254219960975360, 280277362019455627863879843840, 313933856837526904087699783680, 280277362019455627863879843840,
    313933856837526904087699783680, 475368975085586025561263702016, 60768000648440746934248209907712, 118049971827105152897153174077440, 118049952465402573131607797923840, 41566147165972889460614218383360,
    149640051975388489869990033358848, 41566142325547244519227874344960
  ]
def positiveScales : Array ℕ := #[
    8, 4, 9, 9, 12, 7,
    9, 7, 7, 14, 7, 12,
    14, 4, 7, 7, 9, 9,
    13, 9, 14, 15, 9, 15,
    15, 13, 9, 12, 12, 12,
    12, 1, 9, 33, 33, 33,
    34, 32
  ]
def negativeArguments : Array ℕ := #[
    2947054761, 4994859863, 2947054761, 23519, 23519, 495,
    23519, 23519, 42405, 495, 7743, 7743,
    16445, 42405, 81135271, 435, 435, 495,
    495, 1045, 27, 57, 15, 3,
    767, 745
  ]
def negativeCoefficients : Array ℕ := #[
    27181782473687134510554021888, 92138901576804952886485188608, 27181782473687134510554021888, 227461810812131708479316426752, 227461810812131708479316426752, 38298769965391452254691655680,
    227461810812131708479316426752, 227461810812131708479316426752, 1640463980184267204909292584960, 38298769965391452254691655680, 149771401940417179195998732288, 149771401940417179195998732288,
    318092561657001228448689029120, 1640463980184267204909292584960, 383150484348945522087077871616, 8414123704517819055954984960, 8414123704517819055954984960, 38298769965391452254691655680,
    38298769965391452254691655680, 40426479407913199602174525440, 8556641551540548460102746636288, 4516005263313067242832005169152, 1188422437713965063903159255040, 475368975085586025561263702016,
    60768000648440746934248209907712, 236099924292507726028760972001280
  ]
def negativeScales : Array ℕ := #[
    31, 32, 31, 14, 14, 8,
    14, 14, 15, 8, 12, 12,
    14, 15, 26, 8, 8, 8,
    8, 10, 4, 5, 3, 1,
    9, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8879583249426338, 4754887502147955, 9002815015607054, 9612868497290540, 12978889175322745, 7924812503187618,
    9612868497290540, 7924812503187618, 7924812503187618, 14345474552078502, 7924812503187618, 12978889175322745,
    14345474552078502, 4754887502147955, 7924812503187618, 7924812503187618, 9002815015607054, 9739780609762119,
    13893585945611723, 9739780609762119, 14724673717375109, 15496448118381999, 9739780609762119, 15496448118381999,
    15496448118381999, 13893585945611723, 9739780609762119, 12822769974381095, 12986375378262269, 12822769974381095,
    12986375378262269, 1584962500720924, 9583082767502714, 33541096733659668, 33541096497039242, 33035179969909587,
    34883195408297893, 32035179801906080
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    31456626722283024, 32217797055969710, 31456626722283024, 14521539099345394, 14521539099345394, 8951284725619456,
    14521539099345394, 14521539099345394, 15371946763439696, 8951284725619456, 12918676932896795, 12918676932896795,
    14005361387722765, 15371946763439696, 26273825881179304, 8764871591046276, 8764871591046276, 8951284725619456,
    8951284725619456, 10029287226968246, 4754887502413606, 5832890015409720, 3906890600547867, 1584962500724866,
    9583082767506450, 9541096615350537
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 232018516509 / 1000000000000
noncomputable def negativeCeiling : ℝ := 36063780679 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 27181782473687134510554021888, coefficient := (-27181782473687134510554021888) }, { argument := 92138901576804952886485188608, coefficient := (-92138901576804952886485188608) }, { argument := 27181782473687134510554021888, coefficient := (-27181782473687134510554021888) }, { argument := 227461810812131708479316426752, coefficient := (-227461810812131708479316426752) }, { argument := 227461810812131708479316426752, coefficient := (-227461810812131708479316426752) }, { argument := 38298769965391452254691655680, coefficient := (-38298769965391452254691655680) }, { argument := 227461810812131708479316426752, coefficient := (-227461810812131708479316426752) }, { argument := 227461810812131708479316426752, coefficient := (-227461810812131708479316426752) }, { argument := 1640463980184267204909292584960, coefficient := (-1640463980184267204909292584960) }, { argument := 38298769965391452254691655680, coefficient := (-38298769965391452254691655680) }, { argument := 149771401940417179195998732288, coefficient := (-149771401940417179195998732288) }, { argument := 149771401940417179195998732288, coefficient := (-149771401940417179195998732288) }, { argument := 318092561657001228448689029120, coefficient := (-318092561657001228448689029120) }, { argument := 1640463980184267204909292584960, coefficient := (-1640463980184267204909292584960) }, { argument := 383150484348945522087077871616, coefficient := (-383150484348945522087077871616) }, { argument := 8414123704517819055954984960, coefficient := (-8414123704517819055954984960) }, { argument := 8414123704517819055954984960, coefficient := (-8414123704517819055954984960) }, { argument := 38298769965391452254691655680, coefficient := (-38298769965391452254691655680) }, { argument := 38298769965391452254691655680, coefficient := (-38298769965391452254691655680) }, { argument := 40426479407913199602174525440, coefficient := (-40426479407913199602174525440) }, { argument := 298531716353748024052473604866048, coefficient := 298531716353748024052473604866048 }, { argument := 66848762121410534844552708096, coefficient := 66848762121410534844552708096 }, { argument := 79382905019175010127906340864, coefficient := 79382905019175010127906340864 }, { argument := 60581690672528297202875891712, coefficient := 60581690672528297202875891712 }, { argument := 624618121071929684953789366272, coefficient := 624618121071929684953789366272 }, { argument := 75204857386586851700121796608, coefficient := 75204857386586851700121796608 }, { argument := 60581690672528297202875891712, coefficient := 60581690672528297202875891712 }, { argument := 75204857386586851700121796608, coefficient := 75204857386586851700121796608 }, { argument := 75204857386586851700121796608, coefficient := 75204857386586851700121796608 }, { argument := 3221274724725470147821883621376, coefficient := 3221274724725470147821883621376 }, { argument := 75204857386586851700121796608, coefficient := 75204857386586851700121796608 }, { argument := 624618121071929684953789366272, coefficient := 624618121071929684953789366272 }, { argument := 3221274724725470147821883621376, coefficient := 3221274724725470147821883621376 }, { argument := 66848762121410534844552708096, coefficient := 66848762121410534844552708096 }, { argument := 75204857386586851700121796608, coefficient := 75204857386586851700121796608 }, { argument := 75204857386586851700121796608, coefficient := 75204857386586851700121796608 }, { argument := 79382905019175010127906340864, coefficient := 79382905019175010127906340864 }, { argument := 8556641551540548460102746636288, coefficient := (-8556641551540548460102746636288) }, { argument := 33076210424656254219960975360, coefficient := 33076210424656254219960975360 }, { argument := 588756545558881325115305361408, coefficient := 588756545558881325115305361408 }, { argument := 33076210424656254219960975360, coefficient := 33076210424656254219960975360 }, { argument := 523706665057057358482715443200, coefficient := 523706665057057358482715443200 }, { argument := 894160221813207405746278367232, coefficient := 894160221813207405746278367232 }, { argument := 33076210424656254219960975360, coefficient := 33076210424656254219960975360 }, { argument := 894160221813207405746278367232, coefficient := 894160221813207405746278367232 }, { argument := 894160221813207405746278367232, coefficient := 894160221813207405746278367232 }, { argument := 588756545558881325115305361408, coefficient := 588756545558881325115305361408 }, { argument := 33076210424656254219960975360, coefficient := 33076210424656254219960975360 }, { argument := 4516005263313067242832005169152, coefficient := (-4516005263313067242832005169152) }, { argument := 280277362019455627863879843840, coefficient := 280277362019455627863879843840 }, { argument := 313933856837526904087699783680, coefficient := 313933856837526904087699783680 }, { argument := 280277362019455627863879843840, coefficient := 280277362019455627863879843840 }, { argument := 313933856837526904087699783680, coefficient := 313933856837526904087699783680 }, { argument := 1188422437713965063903159255040, coefficient := (-1188422437713965063903159255040) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 60768000648440746934248209907712, coefficient := 60768000648440746934248209907712 }, { argument := 60768000648440746934248209907712, coefficient := (-60768000648440746934248209907712) }, { argument := 118049971827105152897153174077440, coefficient := 118049971827105152897153174077440 }, { argument := 118049952465402573131607797923840, coefficient := 118049952465402573131607797923840 }, { argument := 236099924292507726028760972001280, coefficient := (-236099924292507726028760972001280) }, { argument := 41566147165972889460614218383360, coefficient := 41566147165972889460614218383360 }, { argument := 149640051975388489869990033358848, coefficient := 149640051975388489869990033358848 }, { argument := 41566142325547244519227874344960, coefficient := 41566142325547244519227874344960 }] }

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

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-23791404350260578242675101013114880)
def positiveArguments : Array ℕ := #[
    73319411, 1357946373, 5431679623, 146744703
  ]
def positiveCoefficients : Array ℕ := #[
    692482258100287953694319706112, 25650881749558405398941172498432, 25650381797341230472472043716608, 692982266985860674599191052288
  ]
def positiveScales : Array ℕ := #[
    26, 30, 32, 27
  ]
def negativeArguments : Array ℕ := #[
    1469, 665
  ]
def negativeCoefficients : Array ℕ := #[
    232772341466908623849832126087168, 52686728071985784499706726973440
  ]
def negativeScales : Array ℕ := #[
    10, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    26127691860471328, 30338779360863010, 32338751241532820, 27128733186839305
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    10520618680556813, 9377210530388555
  ]

abbrev PositiveTerm := Fin 4
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 4949069557 / 250000000000
noncomputable def negativeCeiling : ℝ := 8856158897 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 232772341466908623849832126087168, coefficient := (-232772341466908623849832126087168) }, { argument := 692482258100287953694319706112, coefficient := 692482258100287953694319706112 }, { argument := 25650881749558405398941172498432, coefficient := 25650881749558405398941172498432 }, { argument := 25650381797341230472472043716608, coefficient := 25650381797341230472472043716608 }, { argument := 692982266985860674599191052288, coefficient := 692982266985860674599191052288 }, { argument := 52686728071985784499706726973440, coefficient := (-52686728071985784499706726973440) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk21
