import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 2,
parent chunk 7, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-188494518616545285997295904489472)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    6575456885, 3848437131, 959386669591, 57087291229673, 130806375, 131782323,
    3904454991, 2572529583, 28543648099047, 3904454991, 130806375, 129430119,
    59303907, 129430119, 2572529583, 59303907, 479690850585, 131782323,
    240811139173, 57678263938297, 392445, 583543865718435, 402705, 12825,
    392445, 223155, 402705, 6286815, 7695, 3604892261741,
    392445, 12825, 7695, 12825, 197505, 223155,
    240806748773, 2146502740143, 77882187854417, 623055088152793, 17174440032039, 33100421,
    3095559625, 409887, 106091645755, 420603, 13395, 409887,
    233073, 420603, 6566229, 8037, 3095559625, 409887,
    13395, 8037, 13395, 206283, 233073, 132394089,
    6692510601, 122721935019, 122715762693, 6704875287
  ]
def negativeCoefficients : Array ℕ := #[
    242591540650612837327380152320, 70991134839318039348375453696, 540086680959281095761723392, 32137287938693288397924990976, 150809482677167453110272000, 151934674113745496202805248,
    4501530122893433168216457216, 2965924677477984630114091008, 32137290735665658925393379328, 4501530122893433168216457216, 150809482677167453110272000, 149222767538923252318470144,
    136745499375009049255870464, 149222767538923252318470144, 2965924677477984630114091008, 136745499375009049255870464, 540083883986910568293335040, 151934674113745496202805248,
    542258478323093726145019904, 64939951994972871572825571328, 1853269114369777915888926720, 657011984050970655274240573440, 1901720594484020475781447680, 60564350142803199865651200,
    1853269114369777915888926720, 1053819692484775677662330880, 1901720594484020475781447680, 29688644440002128574142218240, 1162835522741821437420503040, 64939965786750208536051974144,
    1853269114369777915888926720, 60564350142803199865651200, 1162835522741821437420503040, 60564350142803199865651200, 1865381984398338555862056960, 1053819692484775677662330880,
    542248592021191722432200704, 9666988940657763405873020928, 350750192199951370573769080832, 350748832854526261468558524416, 9668350216073471222945415168, 152648748729760297552707584,
    14275749041820827989835776000, 1935636630563990267706212352, 122315339850071209925284986880, 1986241509794421385816178688, 63256099038038897637457920, 1935636630563990267706212352,
    1100656123261876818891767808, 1986241509794421385816178688, 31008139748446667621881872384, 1214517101530346834639192064, 14275749041820827989835776000, 1935636630563990267706212352,
    63256099038038897637457920, 1214517101530346834639192064, 63256099038038897637457920, 1948287850371598047233703936, 1100656123261876818891767808, 152639992290932808549924864,
    15431878783404387448129585152, 565955031881476734924594610176, 565926567051961359079122665472, 15460389808178609880746164224
  ]
def negativeScales : Array ℕ := #[
    32, 31, 39, 45, 26, 26,
    31, 31, 44, 31, 26, 26,
    25, 26, 31, 25, 38, 26,
    37, 45, 18, 49, 18, 13,
    18, 17, 18, 22, 12, 41,
    18, 13, 12, 13, 17, 17,
    37, 40, 46, 49, 43, 24,
    31, 18, 36, 18, 13, 18,
    17, 18, 22, 12, 31, 18,
    13, 12, 13, 17, 17, 26,
    32, 36, 36, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32614443995216839, 31841625534742786, 39803321438287423, 45698234842229517, 26962857625990738, 26973581637823261,
    31862474037925870, 31260540521582472, 44698234967790143, 31862474037925870, 26962857625990738, 26947598147456563,
    25821623819286474, 26947598147456563, 31260540521582472, 25821623819286474, 38803313966915112, 26973581637823261,
    37809111172756708, 45713092975097141, 18582130953190490, 49051834437613265, 18619363859395622, 13646671205401350,
    18582130953190490, 17767686606672550, 18619363859395622, 22583897879364855, 12909705616407956, 41713093281492913,
    18582130953190490, 13646671205401350, 12909705616407956, 13646671205401350, 17591529651193783, 17767686606672550,
    37809084869712052, 40965125166551500, 46146358646129904, 49146353054900740, 43965328308137695, 24980346248060028,
    31527553101949431, 18644866708553718, 36626520098683453, 18682099614781241, 13709406960819918, 18644866708553718,
    17830422362877459, 18682099614781241, 22646633634728772, 12972441381715804, 31527553101949431, 18644866708553718,
    13709406960819918, 12972441381715804, 13709406960819918, 17654265406561020, 17830422362877459, 26980263487887587,
    32639900373113138, 36836602180936609, 36836529618453933, 32642563351756303
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
noncomputable def negativeCeiling : ℝ := 163518329 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 242591540650612837327380152320, coefficient := (-242591540650612837327380152320) }, { argument := 70991134839318039348375453696, coefficient := (-70991134839318039348375453696) }, { argument := 540086680959281095761723392, coefficient := (-540086680959281095761723392) }, { argument := 32137287938693288397924990976, coefficient := (-32137287938693288397924990976) }, { argument := 150809482677167453110272000, coefficient := (-150809482677167453110272000) }, { argument := 151934674113745496202805248, coefficient := (-151934674113745496202805248) }, { argument := 4501530122893433168216457216, coefficient := (-4501530122893433168216457216) }, { argument := 2965924677477984630114091008, coefficient := (-2965924677477984630114091008) }, { argument := 32137290735665658925393379328, coefficient := (-32137290735665658925393379328) }, { argument := 4501530122893433168216457216, coefficient := (-4501530122893433168216457216) }, { argument := 150809482677167453110272000, coefficient := (-150809482677167453110272000) }, { argument := 149222767538923252318470144, coefficient := (-149222767538923252318470144) }, { argument := 136745499375009049255870464, coefficient := (-136745499375009049255870464) }, { argument := 149222767538923252318470144, coefficient := (-149222767538923252318470144) }, { argument := 2965924677477984630114091008, coefficient := (-2965924677477984630114091008) }, { argument := 136745499375009049255870464, coefficient := (-136745499375009049255870464) }, { argument := 540083883986910568293335040, coefficient := (-540083883986910568293335040) }, { argument := 151934674113745496202805248, coefficient := (-151934674113745496202805248) }, { argument := 542258478323093726145019904, coefficient := (-542258478323093726145019904) }, { argument := 64939951994972871572825571328, coefficient := (-64939951994972871572825571328) }, { argument := 1853269114369777915888926720, coefficient := (-1853269114369777915888926720) }, { argument := 657011984050970655274240573440, coefficient := (-657011984050970655274240573440) }, { argument := 1901720594484020475781447680, coefficient := (-1901720594484020475781447680) }, { argument := 60564350142803199865651200, coefficient := (-60564350142803199865651200) }, { argument := 1853269114369777915888926720, coefficient := (-1853269114369777915888926720) }, { argument := 1053819692484775677662330880, coefficient := (-1053819692484775677662330880) }, { argument := 1901720594484020475781447680, coefficient := (-1901720594484020475781447680) }, { argument := 29688644440002128574142218240, coefficient := (-29688644440002128574142218240) }, { argument := 1162835522741821437420503040, coefficient := (-1162835522741821437420503040) }, { argument := 64939965786750208536051974144, coefficient := (-64939965786750208536051974144) }, { argument := 1853269114369777915888926720, coefficient := (-1853269114369777915888926720) }, { argument := 60564350142803199865651200, coefficient := (-60564350142803199865651200) }, { argument := 1162835522741821437420503040, coefficient := (-1162835522741821437420503040) }, { argument := 60564350142803199865651200, coefficient := (-60564350142803199865651200) }, { argument := 1865381984398338555862056960, coefficient := (-1865381984398338555862056960) }, { argument := 1053819692484775677662330880, coefficient := (-1053819692484775677662330880) }, { argument := 542248592021191722432200704, coefficient := (-542248592021191722432200704) }, { argument := 9666988940657763405873020928, coefficient := (-9666988940657763405873020928) }, { argument := 350750192199951370573769080832, coefficient := (-350750192199951370573769080832) }, { argument := 350748832854526261468558524416, coefficient := (-350748832854526261468558524416) }, { argument := 9668350216073471222945415168, coefficient := (-9668350216073471222945415168) }, { argument := 152648748729760297552707584, coefficient := (-152648748729760297552707584) }, { argument := 14275749041820827989835776000, coefficient := (-14275749041820827989835776000) }, { argument := 1935636630563990267706212352, coefficient := (-1935636630563990267706212352) }, { argument := 122315339850071209925284986880, coefficient := (-122315339850071209925284986880) }, { argument := 1986241509794421385816178688, coefficient := (-1986241509794421385816178688) }, { argument := 63256099038038897637457920, coefficient := (-63256099038038897637457920) }, { argument := 1935636630563990267706212352, coefficient := (-1935636630563990267706212352) }, { argument := 1100656123261876818891767808, coefficient := (-1100656123261876818891767808) }, { argument := 1986241509794421385816178688, coefficient := (-1986241509794421385816178688) }, { argument := 31008139748446667621881872384, coefficient := (-31008139748446667621881872384) }, { argument := 1214517101530346834639192064, coefficient := (-1214517101530346834639192064) }, { argument := 14275749041820827989835776000, coefficient := (-14275749041820827989835776000) }, { argument := 1935636630563990267706212352, coefficient := (-1935636630563990267706212352) }, { argument := 63256099038038897637457920, coefficient := (-63256099038038897637457920) }, { argument := 1214517101530346834639192064, coefficient := (-1214517101530346834639192064) }, { argument := 63256099038038897637457920, coefficient := (-63256099038038897637457920) }, { argument := 1948287850371598047233703936, coefficient := (-1948287850371598047233703936) }, { argument := 1100656123261876818891767808, coefficient := (-1100656123261876818891767808) }, { argument := 152639992290932808549924864, coefficient := (-152639992290932808549924864) }, { argument := 15431878783404387448129585152, coefficient := (-15431878783404387448129585152) }, { argument := 565955031881476734924594610176, coefficient := (-565955031881476734924594610176) }, { argument := 565926567051961359079122665472, coefficient := (-565926567051961359079122665472) }, { argument := 15460389808178609880746164224, coefficient := (-15460389808178609880746164224) }] }

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

end TermShard10


end Parent0

namespace Parent0

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 44171992759839482830470504620490752
def positiveArguments : Array ℕ := #[
    3703, 3, 13, 13, 13, 13,
    837, 10017, 14985, 4347, 837, 17361,
    8721, 837, 10017, 837, 5085, 3955,
    565, 5311, 62715, 4407, 3955, 62715,
    565, 4407, 4407, 4407, 4407, 4407,
    5085, 5311, 3, 3, 30961449, 52924631,
    30961449, 45873797, 52437035, 1677935773, 22961599, 17283697,
    535910901, 17289, 11018821949
  ]
def positiveCoefficients : Array ℕ := #[
    293381885790320842108893248094208, 475368975085586025561263702016, 257491528171359097179017838592, 257491528171359097179017838592, 257491528171359097179017838592, 257491528171359097179017838592,
    32379869152558227815330217984, 775027835845103388354032959488, 579704109021606981855105515520, 672665668846693506873311625216, 32379869152558227815330217984, 671621156938546467266365489152,
    674754692662987586087203897344, 32379869152558227815330217984, 775027835845103388354032959488, 32379869152558227815330217984, 98358204683846229654094479360, 76500825865213734175406817280,
    87429515274529981914750648320, 102729680447572728749832011776, 1213084524434103499067165245440, 2727800876565335435740220227584, 76500825865213734175406817280, 1213084524434103499067165245440,
    87429515274529981914750648320, 85243777392666732366881882112, 85243777392666732366881882112, 85243777392666732366881882112, 2727800876565335435740220227584, 85243777392666732366881882112,
    98358204683846229654094479360, 102729680447572728749832011776, 237684487542793012780631851008, 237684487542793012780631851008, 584845236074711575727771222016, 1999436028421150352286215569408,
    584845236074711575727771222016, 433265762789532163990223847424, 15848121378883999136522216407040, 15847655309646338799757495894016, 433732342042772650676627439616, 163239902825749276742043828224,
    20246141413494981056177287200768, 334417895925077180823921229824, 208139661810663916746065120854016
  ]
def positiveScales : Array ℕ := #[
    11, 1, 3, 3, 3, 3,
    9, 13, 13, 12, 9, 14,
    13, 9, 13, 9, 12, 11,
    9, 12, 15, 12, 11, 15,
    9, 12, 12, 12, 12, 12,
    12, 12, 1, 1, 24, 25,
    24, 25, 25, 30, 24, 24,
    28, 14, 33
  ]
def negativeArguments : Array ℕ := #[
    4079274101, 6971668363, 4079274101, 612602541, 11257394439, 11256802833,
    613787427, 3848437131, 6575456885, 3848437131, 3, 3,
    3, 13, 27, 113, 3, 5,
    411
  ]
def negativeCoefficients : Array ℕ := #[
    75249325347658608903471497216, 257209164118077242104365449216, 75249325347658608903471497216, 706282643295697663495766016, 25957784269129264057892732928, 25956420118569955181268566016,
    707648723845605251981770752, 70991134839318039348375453696, 242591540650612837327380152320, 70991134839318039348375453696, 118842243771396506390315925504, 118842243771396506390315925504,
    475368975085586025561263702016, 1029966112685436388716071354368, 4278320775770274230051373318144, 8952782364111870148070466387968, 475368975085586025561263702016, 3169126500570573503741758013440,
    32562774793362642750946563588096
  ]
def negativeScales : Array ℕ := #[
    31, 32, 31, 29, 33, 33,
    29, 31, 32, 31, 1, 1,
    1, 3, 4, 6, 1, 2,
    8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11854478834054907, 1584962500720924, 3700439718136550, 3700439718136550, 3700439718136550, 3700439718136550,
    9709083812544787, 13290162878784271, 13871231463241128, 12085804380278085, 9709083812544787, 14083562429491415,
    13090277856857393, 9709083812544787, 13290162878784271, 9709083812544787, 12312032058744862, 11949461978722474,
    9142107057302549, 12374767814092824, 15936522923140884, 12105581181277435, 11949461978722474, 15936522923140884,
    9142107057302549, 12105581181277435, 12105581181277435, 12105581181277435, 12105581181277435, 12105581181277435,
    12312032058744862, 12374767814092824, 1584962500720924, 1584962500720924, 24883969655394808, 25657435969749823,
    24883969655394808, 25451166989254232, 25644082776319835, 30644040348220690, 24452719776131301, 24042908508627828,
    28997417920003559, 14077566805107839, 33359250938736866
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    31925665311078071, 32698856797238788, 31925665311078071, 29190376110169783, 33390153898412570, 33390078078961204,
    29193163852621560, 31841625534742786, 32614443995216839, 31841625534742786, 1584962500724866, 1584962500724866,
    1584962500724866, 3700439718214233, 4754887502413606, 6820178963384638, 1584962500724866, 2321928094887363,
    8682994583729950
  ]

abbrev PositiveTerm := Fin 45
abbrev NegativeTerm := Fin 19
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
noncomputable def positiveFloor : ℝ := 146731105527 / 1000000000000
noncomputable def negativeCeiling : ℝ := 4870450191 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 75249325347658608903471497216, coefficient := (-75249325347658608903471497216) }, { argument := 257209164118077242104365449216, coefficient := (-257209164118077242104365449216) }, { argument := 75249325347658608903471497216, coefficient := (-75249325347658608903471497216) }, { argument := 706282643295697663495766016, coefficient := (-706282643295697663495766016) }, { argument := 25957784269129264057892732928, coefficient := (-25957784269129264057892732928) }, { argument := 25956420118569955181268566016, coefficient := (-25956420118569955181268566016) }, { argument := 707648723845605251981770752, coefficient := (-707648723845605251981770752) }, { argument := 70991134839318039348375453696, coefficient := (-70991134839318039348375453696) }, { argument := 242591540650612837327380152320, coefficient := (-242591540650612837327380152320) }, { argument := 70991134839318039348375453696, coefficient := (-70991134839318039348375453696) }, { argument := 118842243771396506390315925504, coefficient := (-118842243771396506390315925504) }, { argument := 118842243771396506390315925504, coefficient := (-118842243771396506390315925504) }, { argument := 293381885790320842108893248094208, coefficient := 293381885790320842108893248094208 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 257491528171359097179017838592, coefficient := 257491528171359097179017838592 }, { argument := 257491528171359097179017838592, coefficient := 257491528171359097179017838592 }, { argument := 257491528171359097179017838592, coefficient := 257491528171359097179017838592 }, { argument := 257491528171359097179017838592, coefficient := 257491528171359097179017838592 }, { argument := 1029966112685436388716071354368, coefficient := (-1029966112685436388716071354368) }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 775027835845103388354032959488, coefficient := 775027835845103388354032959488 }, { argument := 579704109021606981855105515520, coefficient := 579704109021606981855105515520 }, { argument := 672665668846693506873311625216, coefficient := 672665668846693506873311625216 }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 671621156938546467266365489152, coefficient := 671621156938546467266365489152 }, { argument := 674754692662987586087203897344, coefficient := 674754692662987586087203897344 }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 775027835845103388354032959488, coefficient := 775027835845103388354032959488 }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 4278320775770274230051373318144, coefficient := (-4278320775770274230051373318144) }, { argument := 98358204683846229654094479360, coefficient := 98358204683846229654094479360 }, { argument := 76500825865213734175406817280, coefficient := 76500825865213734175406817280 }, { argument := 87429515274529981914750648320, coefficient := 87429515274529981914750648320 }, { argument := 102729680447572728749832011776, coefficient := 102729680447572728749832011776 }, { argument := 1213084524434103499067165245440, coefficient := 1213084524434103499067165245440 }, { argument := 2727800876565335435740220227584, coefficient := 2727800876565335435740220227584 }, { argument := 76500825865213734175406817280, coefficient := 76500825865213734175406817280 }, { argument := 1213084524434103499067165245440, coefficient := 1213084524434103499067165245440 }, { argument := 87429515274529981914750648320, coefficient := 87429515274529981914750648320 }, { argument := 85243777392666732366881882112, coefficient := 85243777392666732366881882112 }, { argument := 85243777392666732366881882112, coefficient := 85243777392666732366881882112 }, { argument := 85243777392666732366881882112, coefficient := 85243777392666732366881882112 }, { argument := 2727800876565335435740220227584, coefficient := 2727800876565335435740220227584 }, { argument := 85243777392666732366881882112, coefficient := 85243777392666732366881882112 }, { argument := 98358204683846229654094479360, coefficient := 98358204683846229654094479360 }, { argument := 102729680447572728749832011776, coefficient := 102729680447572728749832011776 }, { argument := 8952782364111870148070466387968, coefficient := (-8952782364111870148070466387968) }, { argument := 237684487542793012780631851008, coefficient := 237684487542793012780631851008 }, { argument := 237684487542793012780631851008, coefficient := 237684487542793012780631851008 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 584845236074711575727771222016, coefficient := 584845236074711575727771222016 }, { argument := 1999436028421150352286215569408, coefficient := 1999436028421150352286215569408 }, { argument := 584845236074711575727771222016, coefficient := 584845236074711575727771222016 }, { argument := 3169126500570573503741758013440, coefficient := (-3169126500570573503741758013440) }, { argument := 433265762789532163990223847424, coefficient := 433265762789532163990223847424 }, { argument := 15848121378883999136522216407040, coefficient := 15848121378883999136522216407040 }, { argument := 15847655309646338799757495894016, coefficient := 15847655309646338799757495894016 }, { argument := 433732342042772650676627439616, coefficient := 433732342042772650676627439616 }, { argument := 32562774793362642750946563588096, coefficient := (-32562774793362642750946563588096) }, { argument := 163239902825749276742043828224, coefficient := 163239902825749276742043828224 }, { argument := 20246141413494981056177287200768, coefficient := 20246141413494981056177287200768 }, { argument := 334417895925077180823921229824, coefficient := 334417895925077180823921229824 }, { argument := 208139661810663916746065120854016, coefficient := 208139661810663916746065120854016 }] }

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

end TermShard11


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
