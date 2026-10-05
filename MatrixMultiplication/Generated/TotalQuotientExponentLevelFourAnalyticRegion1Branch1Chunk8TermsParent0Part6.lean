import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 6, for level-four region 1, branch 1,
parent chunk 8, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard12

/-! Directed signed-log shard 12.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3185267652572179528132965378818048)
def positiveArguments : Array ℕ := #[
    405, 1575, 4623, 134067, 118657, 7705,
    4623, 7705, 235773, 7705, 4623, 3776991,
    241937, 134067, 235773, 7705, 241937, 7705,
    235773, 7705, 4623, 8507, 6335, 6697,
    543, 116383, 210503, 6335, 116383, 3439,
    3439, 6697, 6697, 210503, 6697, 8507,
    543, 4371, 13395, 39621, 88407, 4371,
    44133, 89817, 4371, 13395, 4371, 1285,
    5125, 2545, 5125, 1, 1, 1,
    1, 93, 2253, 1707
  ]
def positiveCoefficients : Array ℕ := #[
    31335357244411188208384081920, 30464930654288655202595635200, 178843650050509781589332852736, 2593232925732391833045326364672, 4590320351296417727459543220224, 149036375042091484657777377280,
    2861498400808156505429325643776, 149036375042091484657777377280, 4560513076287999430527987744768, 4769164001346927509048876072960, 2861498400808156505429325643776, 73057631045633245779242470342656,
    4679742176321672618254209646592, 2593232925732391833045326364672, 4560513076287999430527987744768, 149036375042091484657777377280, 4679742176321672618254209646592, 149036375042091484657777377280,
    4560513076287999430527987744768, 4769164001346927509048876072960, 178843650050509781589332852736, 1316394489275091249820856221696, 980293768609110505185743994880, 1036310555386773962624929366016,
    1344402882663922978540448907264, 18009396949018801566698096820224, 32573761511211300500886293315584, 980293768609110505185743994880, 18009396949018801566698096820224, 1064318948775605691344522051584,
    1064318948775605691344522051584, 1036310555386773962624929366016, 1036310555386773962624929366016, 32573761511211300500886293315584, 1036310555386773962624929366016, 1316394489275091249820856221696,
    1344402882663922978540448907264, 84547436120568705962251124736, 2072775853278458597784221122560, 1532763196766439120993068777472, 1710040078954728343171982426112, 84547436120568705962251124736,
    1707312742305677739753845293056, 1737313445445234377353353756672, 84547436120568705962251124736, 2072775853278458597784221122560, 84547436120568705962251124736, 198844118810214206655671828480,
    198263834416799184651812864000, 196909837498830799976141946880, 198263834416799184651812864000, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168,
    39614081257132168796771975168, 7195526478346272847851159552, 174317431781872609959232929792, 132072727941259008078300315648
  ]
def positiveScales : Array ℕ := #[
    8, 10, 12, 17, 16, 12,
    12, 12, 17, 12, 12, 21,
    17, 17, 17, 12, 17, 12,
    17, 12, 12, 13, 12, 12,
    9, 16, 17, 12, 16, 11,
    11, 12, 12, 17, 12, 13,
    9, 12, 13, 15, 16, 12,
    15, 16, 12, 13, 12, 10,
    12, 11, 12, 0, 0, 0,
    0, 6, 11, 10
  ]
def negativeArguments : Array ℕ := #[
    45, 1541, 181, 141, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    3565267313141895191709477765120, 122090598434481344231651227467776, 114722379320654760835451640086528, 11171170914511271600689696997376, 792281625142643375935439503360, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    5, 10, 7, 7, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8661778097770205, 10621136113274016, 12174613647235941, 17032594642363513, 16856437687088554, 12911579241070476,
    12174613647235941, 12911579241070476, 17847038989106135, 12911579241070476, 12174613647235941, 21848805915276843,
    17884271895203256, 17032594642363513, 17847038989106135, 12911579241070476, 17884271895203256, 12911579241070476,
    17847038989106135, 12911579241070476, 12174613647235941, 13054434738760842, 12629128904027399, 12709299252706570,
    9084808387804361, 16828520814340383, 17683481268553390, 12629128904027399, 16828520814340383, 11747773400513505,
    11747773400513505, 12709299252706570, 12709299252706570, 17683481268553390, 12709299252706570, 13054434738760842,
    9084808387804361, 12093747662785668, 13709406960724143, 15273977672619719, 16431872985200830, 12093747662785668,
    15429570199331410, 16454700914655090, 12093747662785668, 13709406960724143, 12093747662785668, 10327552644081240,
    12323336289280170, 11313449940963057, 12323336289280170, 0, 0, 0,
    0, 6539158811107971, 11137631598235427, 10737247343017206
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    5491853096329881, 10589651146519021, 7499845887083475, 7139551352398794, 2321928094887363, 0
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
noncomputable def positiveFloor : ℝ := 53906061693 / 1000000000000
noncomputable def negativeCeiling : ℝ := 13568620049 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 31335357244411188208384081920, coefficient := 31335357244411188208384081920 }, { argument := 30464930654288655202595635200, coefficient := 30464930654288655202595635200 }, { argument := 3565267313141895191709477765120, coefficient := (-3565267313141895191709477765120) }, { argument := 178843650050509781589332852736, coefficient := 178843650050509781589332852736 }, { argument := 2593232925732391833045326364672, coefficient := 2593232925732391833045326364672 }, { argument := 4590320351296417727459543220224, coefficient := 4590320351296417727459543220224 }, { argument := 149036375042091484657777377280, coefficient := 149036375042091484657777377280 }, { argument := 2861498400808156505429325643776, coefficient := 2861498400808156505429325643776 }, { argument := 149036375042091484657777377280, coefficient := 149036375042091484657777377280 }, { argument := 4560513076287999430527987744768, coefficient := 4560513076287999430527987744768 }, { argument := 4769164001346927509048876072960, coefficient := 4769164001346927509048876072960 }, { argument := 2861498400808156505429325643776, coefficient := 2861498400808156505429325643776 }, { argument := 73057631045633245779242470342656, coefficient := 73057631045633245779242470342656 }, { argument := 4679742176321672618254209646592, coefficient := 4679742176321672618254209646592 }, { argument := 2593232925732391833045326364672, coefficient := 2593232925732391833045326364672 }, { argument := 4560513076287999430527987744768, coefficient := 4560513076287999430527987744768 }, { argument := 149036375042091484657777377280, coefficient := 149036375042091484657777377280 }, { argument := 4679742176321672618254209646592, coefficient := 4679742176321672618254209646592 }, { argument := 149036375042091484657777377280, coefficient := 149036375042091484657777377280 }, { argument := 4560513076287999430527987744768, coefficient := 4560513076287999430527987744768 }, { argument := 4769164001346927509048876072960, coefficient := 4769164001346927509048876072960 }, { argument := 178843650050509781589332852736, coefficient := 178843650050509781589332852736 }, { argument := 122090598434481344231651227467776, coefficient := (-122090598434481344231651227467776) }, { argument := 1316394489275091249820856221696, coefficient := 1316394489275091249820856221696 }, { argument := 980293768609110505185743994880, coefficient := 980293768609110505185743994880 }, { argument := 1036310555386773962624929366016, coefficient := 1036310555386773962624929366016 }, { argument := 1344402882663922978540448907264, coefficient := 1344402882663922978540448907264 }, { argument := 18009396949018801566698096820224, coefficient := 18009396949018801566698096820224 }, { argument := 32573761511211300500886293315584, coefficient := 32573761511211300500886293315584 }, { argument := 980293768609110505185743994880, coefficient := 980293768609110505185743994880 }, { argument := 18009396949018801566698096820224, coefficient := 18009396949018801566698096820224 }, { argument := 1064318948775605691344522051584, coefficient := 1064318948775605691344522051584 }, { argument := 1064318948775605691344522051584, coefficient := 1064318948775605691344522051584 }, { argument := 1036310555386773962624929366016, coefficient := 1036310555386773962624929366016 }, { argument := 1036310555386773962624929366016, coefficient := 1036310555386773962624929366016 }, { argument := 32573761511211300500886293315584, coefficient := 32573761511211300500886293315584 }, { argument := 1036310555386773962624929366016, coefficient := 1036310555386773962624929366016 }, { argument := 1316394489275091249820856221696, coefficient := 1316394489275091249820856221696 }, { argument := 1344402882663922978540448907264, coefficient := 1344402882663922978540448907264 }, { argument := 114722379320654760835451640086528, coefficient := (-114722379320654760835451640086528) }, { argument := 84547436120568705962251124736, coefficient := 84547436120568705962251124736 }, { argument := 2072775853278458597784221122560, coefficient := 2072775853278458597784221122560 }, { argument := 1532763196766439120993068777472, coefficient := 1532763196766439120993068777472 }, { argument := 1710040078954728343171982426112, coefficient := 1710040078954728343171982426112 }, { argument := 84547436120568705962251124736, coefficient := 84547436120568705962251124736 }, { argument := 1707312742305677739753845293056, coefficient := 1707312742305677739753845293056 }, { argument := 1737313445445234377353353756672, coefficient := 1737313445445234377353353756672 }, { argument := 84547436120568705962251124736, coefficient := 84547436120568705962251124736 }, { argument := 2072775853278458597784221122560, coefficient := 2072775853278458597784221122560 }, { argument := 84547436120568705962251124736, coefficient := 84547436120568705962251124736 }, { argument := 11171170914511271600689696997376, coefficient := (-11171170914511271600689696997376) }, { argument := 198844118810214206655671828480, coefficient := 198844118810214206655671828480 }, { argument := 198263834416799184651812864000, coefficient := 198263834416799184651812864000 }, { argument := 196909837498830799976141946880, coefficient := 196909837498830799976141946880 }, { argument := 198263834416799184651812864000, coefficient := 198263834416799184651812864000 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 174317431781872609959232929792, coefficient := 174317431781872609959232929792 }, { argument := 132072727941259008078300315648, coefficient := 132072727941259008078300315648 }] }

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


end Parent0

namespace Parent0

namespace TermShard13

/-! Directed signed-log shard 13.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-48548689486466990760713278921375744)
def positiveArguments : Array ℕ := #[
    951, 93, 951, 1899, 93, 2253,
    93, 135, 405, 855, 2205, 1845,
    51615, 1575, 1845, 1665, 855, 855,
    1665, 51615, 1665, 135, 2205, 6291455,
    6291457, 753056945, 2755297915, 188264501, 487124445, 19142215239,
    9571108911, 243563967, 14049285, 5611401469, 232664333427, 22445637449,
    14049285, 35242925, 6742752339, 13485505131, 70485397, 35897723,
    1622511773, 4511165
  ]
def positiveCoefficients : Array ℕ := #[
    147160122170049580178633392128, 7195526478346272847851159552, 147160122170049580178633392128, 146928008412683571377089806336, 7195526478346272847851159552, 174317431781872609959232929792,
    7195526478346272847851159552, 41780476325881584277845442560, 31335357244411188208384081920, 33076210424656254219960975360, 42650902916004117283633889280, 570999843120381651797221048320,
    998379298870545357639348387840, 30464930654288655202595635200, 570999843120381651797221048320, 32205783834533721214172528640, 33076210424656254219960975360, 33076210424656254219960975360,
    32205783834533721214172528640, 998379298870545357639348387840, 32205783834533721214172528640, 41780476325881584277845442560, 42650902916004117283633889280, 475368899527722299646940282880,
    475369050643449751475587121152, 3556210876760209857859781918720, 13011526524116616674086318243840, 3556215877746315216814063222784, 4600760304108955864137140797440, 180793111305060310120269965426688,
    180793135700805560624857139380224, 4600793256782273328521441968128, 530766980738266107648808058880, 105996376876524361950570213277696, 1098726249934872417776560811016192, 105996525975801325593878545301504,
    530766980738266107648808058880, 665720031113154764171588403200, 127366990591938014786995435339776, 127366994870402048266893998948352, 665715752649121284273024794624, 169522203906538768989534814208,
    7662095214876602183554860843008, 170426995157557144403543326720
  ]
def positiveScales : Array ℕ := #[
    9, 6, 9, 10, 6, 11,
    6, 7, 8, 9, 11, 10,
    15, 10, 10, 10, 9, 9,
    10, 15, 10, 7, 11, 22,
    22, 29, 31, 27, 28, 34,
    33, 27, 23, 32, 37, 34,
    23, 25, 32, 33, 26, 25,
    30, 22
  ]
def negativeArguments : Array ℕ := #[
    3, 45, 3, 127, 585, 16557,
    101, 101
  ]
def negativeCoefficients : Array ℕ := #[
    950737950171172051122527404032, 3565267313141895191709477765120, 950737950171172051122527404032, 20123953278623141748760163385344, 370787800566757099937785687572480, 1311780686748674637536307185713152,
    256065421246102339102334047485952, 8002044413940698096947938983936
  ]
def negativeScales : Array ℕ := #[
    1, 5, 1, 6, 9, 14,
    6, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9893301530621223, 6539158811107971, 9893301530621223, 10891024189919810, 6539158811107971, 11137631598235427,
    6539158811107971, 7076815597050830, 8661778097770205, 9739780609762119, 11106562940444882, 10849405100841772,
    15655502772343977, 10621136113274016, 10849405100841772, 10701306461953989, 9739780609762119, 9739780609762119,
    10701306461953989, 15655502772343977, 10701306461953989, 7076815597050830, 11106562940444882, 22584962271410705,
    22584962730031107, 29488183722485912, 31359561171786796, 27488185751300577, 28859715141646202, 34156038744705317,
    33156038939378765, 27859725474826996, 23743993374488772, 32385713988433083, 37759459111677512, 34385716017791468,
    23743993374488772, 25070830330464027, 32650690462497970, 33650690510960438, 26070821058490239, 25097389000716950,
    30595581800492085, 22105068624241635
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 5491853096329881, 1584962500724866, 6988684706517367, 9192292814470767, 14015153670912853,
    6658211482778016, 6658211482778016
  ]

abbrev PositiveTerm := Fin 44
abbrev NegativeTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 169549656373 / 200000000000
noncomputable def negativeCeiling : ℝ := 35681837437 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 147160122170049580178633392128, coefficient := 147160122170049580178633392128 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 147160122170049580178633392128, coefficient := 147160122170049580178633392128 }, { argument := 146928008412683571377089806336, coefficient := 146928008412683571377089806336 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 174317431781872609959232929792, coefficient := 174317431781872609959232929792 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 41780476325881584277845442560, coefficient := 41780476325881584277845442560 }, { argument := 31335357244411188208384081920, coefficient := 31335357244411188208384081920 }, { argument := 33076210424656254219960975360, coefficient := 33076210424656254219960975360 }, { argument := 42650902916004117283633889280, coefficient := 42650902916004117283633889280 }, { argument := 570999843120381651797221048320, coefficient := 570999843120381651797221048320 }, { argument := 998379298870545357639348387840, coefficient := 998379298870545357639348387840 }, { argument := 30464930654288655202595635200, coefficient := 30464930654288655202595635200 }, { argument := 570999843120381651797221048320, coefficient := 570999843120381651797221048320 }, { argument := 32205783834533721214172528640, coefficient := 32205783834533721214172528640 }, { argument := 33076210424656254219960975360, coefficient := 33076210424656254219960975360 }, { argument := 33076210424656254219960975360, coefficient := 33076210424656254219960975360 }, { argument := 32205783834533721214172528640, coefficient := 32205783834533721214172528640 }, { argument := 998379298870545357639348387840, coefficient := 998379298870545357639348387840 }, { argument := 32205783834533721214172528640, coefficient := 32205783834533721214172528640 }, { argument := 41780476325881584277845442560, coefficient := 41780476325881584277845442560 }, { argument := 42650902916004117283633889280, coefficient := 42650902916004117283633889280 }, { argument := 3565267313141895191709477765120, coefficient := (-3565267313141895191709477765120) }, { argument := 475368899527722299646940282880, coefficient := 475368899527722299646940282880 }, { argument := 475369050643449751475587121152, coefficient := 475369050643449751475587121152 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 3556210876760209857859781918720, coefficient := 3556210876760209857859781918720 }, { argument := 13011526524116616674086318243840, coefficient := 13011526524116616674086318243840 }, { argument := 3556215877746315216814063222784, coefficient := 3556215877746315216814063222784 }, { argument := 20123953278623141748760163385344, coefficient := (-20123953278623141748760163385344) }, { argument := 4600760304108955864137140797440, coefficient := 4600760304108955864137140797440 }, { argument := 180793111305060310120269965426688, coefficient := 180793111305060310120269965426688 }, { argument := 180793135700805560624857139380224, coefficient := 180793135700805560624857139380224 }, { argument := 4600793256782273328521441968128, coefficient := 4600793256782273328521441968128 }, { argument := 370787800566757099937785687572480, coefficient := (-370787800566757099937785687572480) }, { argument := 530766980738266107648808058880, coefficient := 530766980738266107648808058880 }, { argument := 105996376876524361950570213277696, coefficient := 105996376876524361950570213277696 }, { argument := 1098726249934872417776560811016192, coefficient := 1098726249934872417776560811016192 }, { argument := 105996525975801325593878545301504, coefficient := 105996525975801325593878545301504 }, { argument := 530766980738266107648808058880, coefficient := 530766980738266107648808058880 }, { argument := 1311780686748674637536307185713152, coefficient := (-1311780686748674637536307185713152) }, { argument := 665720031113154764171588403200, coefficient := 665720031113154764171588403200 }, { argument := 127366990591938014786995435339776, coefficient := 127366990591938014786995435339776 }, { argument := 127366994870402048266893998948352, coefficient := 127366994870402048266893998948352 }, { argument := 665715752649121284273024794624, coefficient := 665715752649121284273024794624 }, { argument := 256065421246102339102334047485952, coefficient := (-256065421246102339102334047485952) }, { argument := 169522203906538768989534814208, coefficient := 169522203906538768989534814208 }, { argument := 7662095214876602183554860843008, coefficient := 7662095214876602183554860843008 }, { argument := 170426995157557144403543326720, coefficient := 170426995157557144403543326720 }, { argument := 8002044413940698096947938983936, coefficient := (-8002044413940698096947938983936) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
