import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 13, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-95660352133458280691957482286743552)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    24156142941, 1324707414325735219, 24156142941, 24149519709, 1000269896661, 6208126071,
    272620273653, 1000269896661, 67551197325319513, 24149519709, 6208126071, 24176012637,
    359452007456548025, 1503, 39, 1313870147583495249, 2421, 179721723988805499,
    2421, 2523, 1503, 75, 21789, 99261,
    2421, 1038609, 45999, 2421, 45999, 89577,
    1692279, 89577, 1038609, 1692279, 21789, 89577,
    89577, 99261, 550549941, 644787, 16731, 64943414757,
    1038609, 17618910075, 1038609, 1082367, 644787, 32175,
    12723045597510255, 12723046342395281, 48782877, 28557, 741, 5754458829,
    45999, 1561168275, 45999, 47937, 28557, 1425,
    99623097443, 99623119773, 12947113, 4619618671348501
  ]
def negativeCoefficients : Array ℕ := #[
    27850136665035785559569596416, 745743977191539298370898863587328, 27850136665035785559569596416, 27842500598432985343259049984, 1153232674271335460116560347136, 28629928202265253267252445184,
    314309776086347122774615523328, 1153232674271335460116560347136, 19013971693921237800428951830528, 27842500598432985343259049984, 28629928202265253267252445184, 27873044864844186208501235712,
    202353490854860804381525986508800, 227126938360098456197922816, 11787026741242634453385216, 739643138383780973618970847346688, 365851176160877153995456512, 202348672296591894330726338789376,
    365851176160877153995456512, 381264980360963675972960256, 227126938360098456197922816, 11333679558887148512870400, 411582573180986798244888576, 468746819456123853556678656,
    365851176160877153995456512, 4904692330406759345751588864, 434448271691041620369604608, 365851176160877153995456512, 434448271691041620369604608, 423015422436014209307246592,
    15983123258528320665176506368, 423015422436014209307246592, 4904692330406759345751588864, 15983123258528320665176506368, 411582573180986798244888576, 423015422436014209307246592,
    423015422436014209307246592, 468746819456123853556678656, 81246830891383146346602037248, 3044920517390069928403402752, 158019827249784068140695552, 299498637823787797537596899328,
    4904692330406759345751588864, 81252881252806940397718732800, 4904692330406759345751588864, 5111333642964169281012498432, 3044920517390069928403402752, 151942141586330834750668800,
    14324875852991253512092511109120, 14324876691657234893958067257344, 7199081977586015921667833856, 269713239302616916735033344, 13997094255225628413394944, 26537757325315339019580604416,
    434448271691041620369604608, 7199617906229903386843545600, 434448271691041620369604608, 452752164178644365217890304, 269713239302616916735033344, 13458744476178488859033600,
    229715222795156179390075764736, 229715274284630575131861712896, 61141012481125860851631259648, 5201228231719723732467265306624
  ]
def negativeScales : Array ℕ := #[
    34, 60, 34, 34, 39, 32,
    37, 39, 55, 34, 32, 34,
    58, 10, 5, 60, 11, 57,
    11, 11, 10, 6, 14, 16,
    11, 19, 15, 11, 15, 16,
    20, 16, 19, 20, 14, 16,
    16, 16, 29, 19, 14, 35,
    19, 34, 19, 20, 19, 14,
    53, 53, 25, 14, 9, 32,
    15, 30, 15, 15, 14, 10,
    36, 36, 23, 52
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34491671063962309, 60200379457449565, 34491671063962309, 34491275445581489, 39863526466923605, 32531510709218193,
    37988101916774133, 39863526466923605, 55906830864259355, 34491275445581489, 32531510709218193, 34492857268597939,
    58318576773940393, 10553629293917849, 5285402218862249, 60188528406239690, 11241387363998937, 57318542419243275,
    11241387363998937, 11300924490976301, 10553629293917849, 6228818690495881, 14411312365441260, 16598939368622512,
    11241387363998937, 19986221220472518, 15489314877442711, 11241387363998937, 15489314877442711, 16450840729627935,
    20690536009432220, 16450840729627935, 19986221220472518, 20690536009432220, 14411312365441260, 16450840729627935,
    16450840729627935, 16598939368622512, 29036298197302870, 19298463131415911, 14030236056361794, 35918464199172762,
    19986221220472518, 34036405629203032, 19986221220472518, 20045758328475847, 19298463131415911, 14973652543452428,
    53498293577380724, 53498293661844926, 25539871508677834, 14801556808026795, 9533329732306630, 32422033112243191,
    15489314877442711, 30539978904707118, 15489314877442711, 15548852004421171, 14801556808026795, 10476746203939589,
    36535761216301223, 36535761539673789, 23626127099978878, 52036695191908551
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
noncomputable def negativeCeiling : ℝ := 1394194012263 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 27850136665035785559569596416, coefficient := (-27850136665035785559569596416) }, { argument := 745743977191539298370898863587328, coefficient := (-745743977191539298370898863587328) }, { argument := 27850136665035785559569596416, coefficient := (-27850136665035785559569596416) }, { argument := 27842500598432985343259049984, coefficient := (-27842500598432985343259049984) }, { argument := 1153232674271335460116560347136, coefficient := (-1153232674271335460116560347136) }, { argument := 28629928202265253267252445184, coefficient := (-28629928202265253267252445184) }, { argument := 314309776086347122774615523328, coefficient := (-314309776086347122774615523328) }, { argument := 1153232674271335460116560347136, coefficient := (-1153232674271335460116560347136) }, { argument := 19013971693921237800428951830528, coefficient := (-19013971693921237800428951830528) }, { argument := 27842500598432985343259049984, coefficient := (-27842500598432985343259049984) }, { argument := 28629928202265253267252445184, coefficient := (-28629928202265253267252445184) }, { argument := 27873044864844186208501235712, coefficient := (-27873044864844186208501235712) }, { argument := 202353490854860804381525986508800, coefficient := (-202353490854860804381525986508800) }, { argument := 227126938360098456197922816, coefficient := (-227126938360098456197922816) }, { argument := 11787026741242634453385216, coefficient := (-11787026741242634453385216) }, { argument := 739643138383780973618970847346688, coefficient := (-739643138383780973618970847346688) }, { argument := 365851176160877153995456512, coefficient := (-365851176160877153995456512) }, { argument := 202348672296591894330726338789376, coefficient := (-202348672296591894330726338789376) }, { argument := 365851176160877153995456512, coefficient := (-365851176160877153995456512) }, { argument := 381264980360963675972960256, coefficient := (-381264980360963675972960256) }, { argument := 227126938360098456197922816, coefficient := (-227126938360098456197922816) }, { argument := 11333679558887148512870400, coefficient := (-11333679558887148512870400) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 468746819456123853556678656, coefficient := (-468746819456123853556678656) }, { argument := 365851176160877153995456512, coefficient := (-365851176160877153995456512) }, { argument := 4904692330406759345751588864, coefficient := (-4904692330406759345751588864) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 365851176160877153995456512, coefficient := (-365851176160877153995456512) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 15983123258528320665176506368, coefficient := (-15983123258528320665176506368) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 4904692330406759345751588864, coefficient := (-4904692330406759345751588864) }, { argument := 15983123258528320665176506368, coefficient := (-15983123258528320665176506368) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 468746819456123853556678656, coefficient := (-468746819456123853556678656) }, { argument := 81246830891383146346602037248, coefficient := (-81246830891383146346602037248) }, { argument := 3044920517390069928403402752, coefficient := (-3044920517390069928403402752) }, { argument := 158019827249784068140695552, coefficient := (-158019827249784068140695552) }, { argument := 299498637823787797537596899328, coefficient := (-299498637823787797537596899328) }, { argument := 4904692330406759345751588864, coefficient := (-4904692330406759345751588864) }, { argument := 81252881252806940397718732800, coefficient := (-81252881252806940397718732800) }, { argument := 4904692330406759345751588864, coefficient := (-4904692330406759345751588864) }, { argument := 5111333642964169281012498432, coefficient := (-5111333642964169281012498432) }, { argument := 3044920517390069928403402752, coefficient := (-3044920517390069928403402752) }, { argument := 151942141586330834750668800, coefficient := (-151942141586330834750668800) }, { argument := 14324875852991253512092511109120, coefficient := (-14324875852991253512092511109120) }, { argument := 14324876691657234893958067257344, coefficient := (-14324876691657234893958067257344) }, { argument := 7199081977586015921667833856, coefficient := (-7199081977586015921667833856) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 13997094255225628413394944, coefficient := (-13997094255225628413394944) }, { argument := 26537757325315339019580604416, coefficient := (-26537757325315339019580604416) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 7199617906229903386843545600, coefficient := (-7199617906229903386843545600) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 452752164178644365217890304, coefficient := (-452752164178644365217890304) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 13458744476178488859033600, coefficient := (-13458744476178488859033600) }, { argument := 229715222795156179390075764736, coefficient := (-229715222795156179390075764736) }, { argument := 229715274284630575131861712896, coefficient := (-229715274284630575131861712896) }, { argument := 61141012481125860851631259648, coefficient := (-61141012481125860851631259648) }, { argument := 5201228231719723732467265306624, coefficient := (-5201228231719723732467265306624) }] }

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


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-91432242300508779568859578795819008)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    6557244675, 181198910301005339, 73992832875, 6556323075, 362397872110529607, 6556323075,
    6556015875, 271751933835, 1685751465, 73992832875, 271751933835, 9239307177558361,
    6556015875, 1685751465, 6557244675, 179726029204422531, 1503, 39,
    1313870338791255601, 2421, 359443498915517129, 2421, 2523, 1503,
    75, 522970797020912093, 522970825749063203, 48782877, 28557, 741,
    5754458829, 45999, 1561168275, 45999, 47937, 28557,
    1425, 3884973645, 3884974515, 1447702871, 6534724907, 6534726357,
    519, 21789, 99261, 2421, 1038609, 45999,
    2421, 45999, 89577, 1692279, 89577, 1038609,
    1692279, 21789, 89577, 89577, 99261, 48780573,
    55611, 1443, 5752803021, 89577
  ]
def negativeCoefficients : Array ℕ := #[
    7559988396776235301915852800, 204011836227886893479072456769536, 85307928208367970875867136000, 7558925864317589631742771200, 204011865224605225360389920784384, 7558925864317589631742771200,
    7558571686831374408351744000, 313308648436868527109921832960, 7774156461683986155291279360, 85307928208367970875867136000, 313308648436868527109921832960, 5201267545251672965298501189632,
    7558571686831374408351744000, 7774156461683986155291279360, 7559988396776235301915852800, 202353519538454048069529416761344, 227126938360098456197922816, 11787026741242634453385216,
    739643246024180757570758232768512, 365851176160877153995456512, 202348700972083778156339289653248, 365851176160877153995456512, 381264980360963675972960256, 227126938360098456197922816,
    11333679558887148512870400, 147203192911814437602978072363008, 147203200998070102230434387591168, 7199081977586015921667833856, 269713239302616916735033344, 13997094255225628413394944,
    26537757325315339019580604416, 434448271691041620369604608, 7199617906229903386843545600, 434448271691041620369604608, 452752164178644365217890304, 269713239302616916735033344,
    13458744476178488859033600, 143330229124843090825854320640, 143330261222177779080474132480, 6836583515164557694619107721216, 7534024871970278176804831232, 7534026543706459856732946432,
    20077840012159761333520171008, 411582573180986798244888576, 468746819456123853556678656, 365851176160877153995456512, 4904692330406759345751588864, 434448271691041620369604608,
    365851176160877153995456512, 434448271691041620369604608, 423015422436014209307246592, 15983123258528320665176506368, 423015422436014209307246592, 4904692330406759345751588864,
    15983123258528320665176506368, 411582573180986798244888576, 423015422436014209307246592, 423015422436014209307246592, 468746819456123853556678656, 7198741967199249307212447744,
    262615522478863839978848256, 13628749669561796086726656, 26530121258712538803270057984, 423015422436014209307246592
  ]
def negativeScales : Array ℕ := #[
    32, 57, 36, 32, 58, 32,
    32, 37, 30, 36, 37, 53,
    32, 30, 32, 57, 10, 5,
    60, 11, 58, 11, 11, 10,
    6, 58, 58, 25, 14, 9,
    32, 15, 30, 15, 15, 14,
    10, 31, 31, 30, 32, 32,
    9, 14, 16, 11, 19, 15,
    11, 15, 16, 20, 16, 19,
    20, 14, 16, 16, 16, 25,
    15, 10, 32, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32610442582136705, 57330351892376247, 36106666483446883, 32610239801661172, 58330352097430128, 32610239801661172,
    32610172201835020, 37983499363678709, 30650744705446659, 36106666483446883, 37983499363678709, 53036706096491220,
    32610172201835020, 30650744705446659, 32610442582136705, 57318576978442300, 10553629293917849, 5285402218862249,
    60188528616195345, 11241387363998937, 58318542623692291, 11241387363998937, 11300924490976301, 10553629293917849,
    6228818690495881, 58859508002990617, 58859508082241623, 25539871508677834, 14801556808026795, 9533329732306630,
    32422033112243191, 15489314877442711, 30539978904707118, 15489314877442711, 15548852004421171, 14801556808026795,
    10476746203939589, 31855257667569159, 31855257990645892, 30431118385604972, 32605479358007361, 32605479678129112,
    9019590728357881, 14411312365441260, 16598939368622512, 11241387363998937, 19986221220472518, 15489314877442711,
    11241387363998937, 15489314877442711, 16450840729627935, 20690536009432220, 16450840729627935, 19986221220472518,
    20690536009432220, 14411312365441260, 16450840729627935, 16450840729627935, 16598939368622512, 25539803369033840,
    15763082659843835, 10494855584491427, 32421617926417424, 16450840729627935
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
noncomputable def negativeCeiling : ℝ := 1316505882529 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7559988396776235301915852800, coefficient := (-7559988396776235301915852800) }, { argument := 204011836227886893479072456769536, coefficient := (-204011836227886893479072456769536) }, { argument := 85307928208367970875867136000, coefficient := (-85307928208367970875867136000) }, { argument := 7558925864317589631742771200, coefficient := (-7558925864317589631742771200) }, { argument := 204011865224605225360389920784384, coefficient := (-204011865224605225360389920784384) }, { argument := 7558925864317589631742771200, coefficient := (-7558925864317589631742771200) }, { argument := 7558571686831374408351744000, coefficient := (-7558571686831374408351744000) }, { argument := 313308648436868527109921832960, coefficient := (-313308648436868527109921832960) }, { argument := 7774156461683986155291279360, coefficient := (-7774156461683986155291279360) }, { argument := 85307928208367970875867136000, coefficient := (-85307928208367970875867136000) }, { argument := 313308648436868527109921832960, coefficient := (-313308648436868527109921832960) }, { argument := 5201267545251672965298501189632, coefficient := (-5201267545251672965298501189632) }, { argument := 7558571686831374408351744000, coefficient := (-7558571686831374408351744000) }, { argument := 7774156461683986155291279360, coefficient := (-7774156461683986155291279360) }, { argument := 7559988396776235301915852800, coefficient := (-7559988396776235301915852800) }, { argument := 202353519538454048069529416761344, coefficient := (-202353519538454048069529416761344) }, { argument := 227126938360098456197922816, coefficient := (-227126938360098456197922816) }, { argument := 11787026741242634453385216, coefficient := (-11787026741242634453385216) }, { argument := 739643246024180757570758232768512, coefficient := (-739643246024180757570758232768512) }, { argument := 365851176160877153995456512, coefficient := (-365851176160877153995456512) }, { argument := 202348700972083778156339289653248, coefficient := (-202348700972083778156339289653248) }, { argument := 365851176160877153995456512, coefficient := (-365851176160877153995456512) }, { argument := 381264980360963675972960256, coefficient := (-381264980360963675972960256) }, { argument := 227126938360098456197922816, coefficient := (-227126938360098456197922816) }, { argument := 11333679558887148512870400, coefficient := (-11333679558887148512870400) }, { argument := 147203192911814437602978072363008, coefficient := (-147203192911814437602978072363008) }, { argument := 147203200998070102230434387591168, coefficient := (-147203200998070102230434387591168) }, { argument := 7199081977586015921667833856, coefficient := (-7199081977586015921667833856) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 13997094255225628413394944, coefficient := (-13997094255225628413394944) }, { argument := 26537757325315339019580604416, coefficient := (-26537757325315339019580604416) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 7199617906229903386843545600, coefficient := (-7199617906229903386843545600) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 452752164178644365217890304, coefficient := (-452752164178644365217890304) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 13458744476178488859033600, coefficient := (-13458744476178488859033600) }, { argument := 143330229124843090825854320640, coefficient := (-143330229124843090825854320640) }, { argument := 143330261222177779080474132480, coefficient := (-143330261222177779080474132480) }, { argument := 6836583515164557694619107721216, coefficient := (-6836583515164557694619107721216) }, { argument := 7534024871970278176804831232, coefficient := (-7534024871970278176804831232) }, { argument := 7534026543706459856732946432, coefficient := (-7534026543706459856732946432) }, { argument := 20077840012159761333520171008, coefficient := (-20077840012159761333520171008) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 468746819456123853556678656, coefficient := (-468746819456123853556678656) }, { argument := 365851176160877153995456512, coefficient := (-365851176160877153995456512) }, { argument := 4904692330406759345751588864, coefficient := (-4904692330406759345751588864) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 365851176160877153995456512, coefficient := (-365851176160877153995456512) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 15983123258528320665176506368, coefficient := (-15983123258528320665176506368) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 4904692330406759345751588864, coefficient := (-4904692330406759345751588864) }, { argument := 15983123258528320665176506368, coefficient := (-15983123258528320665176506368) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 468746819456123853556678656, coefficient := (-468746819456123853556678656) }, { argument := 7198741967199249307212447744, coefficient := (-7198741967199249307212447744) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 13628749669561796086726656, coefficient := (-13628749669561796086726656) }, { argument := 26530121258712538803270057984, coefficient := (-26530121258712538803270057984) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }] }

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

end TermShard3


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
