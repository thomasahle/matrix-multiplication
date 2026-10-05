import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 1, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-558561431104724763946615448797184)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    57397855025, 1577493225, 2629155375, 80452154475, 2629155375, 1577493225,
    1288811964825, 82555478775, 51067035425, 80452154475, 2629155375, 82555478775,
    2629155375, 80452154475, 2629155375, 3187447445, 405638037, 80452154475,
    80452154475, 405638037, 596354851, 24432768655, 503089626785, 24432768655,
    596354851, 4830212887, 1686769665, 67413567577, 19036400505, 1686769665,
    67413551279, 1686769665, 1686769665, 69928650969, 433740771, 19036400505,
    69928650969, 4830212887, 1686769665, 433740771, 1686769665, 17621683,
    721963615, 14865789905, 721963615, 17621683, 3722078283, 37201999791,
    74403981399, 3722078283, 191029899, 1391752403, 382060055, 37319415,
    1686769665, 4689825, 13256145, 2629155375, 2629155375, 13256145,
    9596421, 433740771, 1205955, 416242953
  ]
def negativeCoefficients : Array ℕ := #[
    132350442753257344701615308800, 116398455198342873168111206400, 6062419541580357977505792000, 185510037972358954111677235200, 193997425330571455280185344000, 116398455198342873168111206400,
    2971798059282691480573339238400, 190359973605623240493681868800, 117752566636004310441892249600, 185510037972358954111677235200, 6062419541580357977505792000, 190359973605623240493681868800,
    6062419541580357977505792000, 185510037972358954111677235200, 193997425330571455280185344000, 7349753408289300246314352640, 935337631887615728208052224, 185510037972358954111677235200,
    185510037972358954111677235200, 935337631887615728208052224, 1375100664189024083904561152, 225352515195468871148754698240, 2320091397860237213245783408640, 225352515195468871148754698240,
    1375100664189024083904561152, 5568856309251422131912179712, 1944713020096987230413783040, 155445103523580390866948194304, 21947475512523141600384122880, 1944713020096987230413783040,
    155445065942951026702164164608, 1944713020096987230413783040, 1944713020096987230413783040, 80622245490306527752297119744, 2000276249242615436997033984, 21947475512523141600384122880,
    80622245490306527752297119744, 5568856309251422131912179712, 1944713020096987230413783040, 2000276249242615436997033984, 1944713020096987230413783040, 81265669112259588162322432,
    13317878036435174344716451840, 137112710915535014157604618240, 13317878036435174344716451840, 81265669112259588162322432, 4291264094300829582473822208, 171563942293693306953283928064,
    171563900366549870420686798848, 4291264094300829582473822208, 3523879657279584200539766784, 12836650196055638792810266624, 3523882027686197672217149440, 43026356092847334138839040,
    1944713020096987230413783040, 43256000762742448953753600, 30566589277373063013335040, 6062419541580357977505792000, 6062419541580357977505792000, 30566589277373063013335040,
    44255680552642972257091584, 2000276249242615436997033984, 44491886498820804638146560, 959790903309514178618720256
  ]
def negativeScales : Array ℕ := #[
    35, 30, 31, 36, 31, 30,
    40, 36, 35, 36, 31, 36,
    31, 36, 31, 31, 28, 36,
    36, 28, 29, 34, 38, 34,
    29, 32, 30, 35, 34, 30,
    35, 30, 30, 36, 28, 34,
    36, 32, 30, 28, 30, 24,
    29, 33, 29, 24, 31, 35,
    36, 31, 27, 30, 28, 25,
    30, 22, 23, 31, 31, 23,
    23, 28, 20, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35740277773018579, 30554986663138648, 31291952257303309, 36227412005108598, 31291952257303309, 30554986663138648,
    40229178931282786, 36264644911307574, 35571673258136131, 36227412005108598, 31291952257303309, 36264644911307574,
    31291952257303309, 36227412005108598, 31291952257303309, 31569754408834522, 28595617700444954, 36227412005108598,
    36227412005108598, 28595617700444954, 29151595796894609, 34508098304027116, 38872024489355301, 34508098304027116,
    29151595796894609, 32169439629848722, 30651615835428925, 35972319939767985, 34148041661526225, 30651615835428925,
    35972319590979851, 30651615835428925, 30651615835428925, 36025164622528504, 28692257819964341, 34148041661526225,
    36025164622528504, 32169439629848722, 30651615835428925, 28692257819964341, 30651615835428925, 24070848383010247,
    29427350890142419, 33791277073389239, 29427350890142419, 24070848383010247, 31793461253126315, 35114661124266427,
    36114660771697650, 31793461253126315, 27509223218110073, 30374255428149730, 28509224188566799, 25153423035631279,
    30651615835428925, 22161102659155964, 23660157952662189, 31291952257303309, 31291952257303309, 23660157952662189,
    23194065020128625, 28692257819964341, 20201744643653310, 28632850606652610
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
noncomputable def negativeCeiling : ℝ := 163782397 / 40000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 132350442753257344701615308800, coefficient := (-132350442753257344701615308800) }, { argument := 116398455198342873168111206400, coefficient := (-116398455198342873168111206400) }, { argument := 6062419541580357977505792000, coefficient := (-6062419541580357977505792000) }, { argument := 185510037972358954111677235200, coefficient := (-185510037972358954111677235200) }, { argument := 193997425330571455280185344000, coefficient := (-193997425330571455280185344000) }, { argument := 116398455198342873168111206400, coefficient := (-116398455198342873168111206400) }, { argument := 2971798059282691480573339238400, coefficient := (-2971798059282691480573339238400) }, { argument := 190359973605623240493681868800, coefficient := (-190359973605623240493681868800) }, { argument := 117752566636004310441892249600, coefficient := (-117752566636004310441892249600) }, { argument := 185510037972358954111677235200, coefficient := (-185510037972358954111677235200) }, { argument := 6062419541580357977505792000, coefficient := (-6062419541580357977505792000) }, { argument := 190359973605623240493681868800, coefficient := (-190359973605623240493681868800) }, { argument := 6062419541580357977505792000, coefficient := (-6062419541580357977505792000) }, { argument := 185510037972358954111677235200, coefficient := (-185510037972358954111677235200) }, { argument := 193997425330571455280185344000, coefficient := (-193997425330571455280185344000) }, { argument := 7349753408289300246314352640, coefficient := (-7349753408289300246314352640) }, { argument := 935337631887615728208052224, coefficient := (-935337631887615728208052224) }, { argument := 185510037972358954111677235200, coefficient := (-185510037972358954111677235200) }, { argument := 185510037972358954111677235200, coefficient := (-185510037972358954111677235200) }, { argument := 935337631887615728208052224, coefficient := (-935337631887615728208052224) }, { argument := 1375100664189024083904561152, coefficient := (-1375100664189024083904561152) }, { argument := 225352515195468871148754698240, coefficient := (-225352515195468871148754698240) }, { argument := 2320091397860237213245783408640, coefficient := (-2320091397860237213245783408640) }, { argument := 225352515195468871148754698240, coefficient := (-225352515195468871148754698240) }, { argument := 1375100664189024083904561152, coefficient := (-1375100664189024083904561152) }, { argument := 5568856309251422131912179712, coefficient := (-5568856309251422131912179712) }, { argument := 1944713020096987230413783040, coefficient := (-1944713020096987230413783040) }, { argument := 155445103523580390866948194304, coefficient := (-155445103523580390866948194304) }, { argument := 21947475512523141600384122880, coefficient := (-21947475512523141600384122880) }, { argument := 1944713020096987230413783040, coefficient := (-1944713020096987230413783040) }, { argument := 155445065942951026702164164608, coefficient := (-155445065942951026702164164608) }, { argument := 1944713020096987230413783040, coefficient := (-1944713020096987230413783040) }, { argument := 1944713020096987230413783040, coefficient := (-1944713020096987230413783040) }, { argument := 80622245490306527752297119744, coefficient := (-80622245490306527752297119744) }, { argument := 2000276249242615436997033984, coefficient := (-2000276249242615436997033984) }, { argument := 21947475512523141600384122880, coefficient := (-21947475512523141600384122880) }, { argument := 80622245490306527752297119744, coefficient := (-80622245490306527752297119744) }, { argument := 5568856309251422131912179712, coefficient := (-5568856309251422131912179712) }, { argument := 1944713020096987230413783040, coefficient := (-1944713020096987230413783040) }, { argument := 2000276249242615436997033984, coefficient := (-2000276249242615436997033984) }, { argument := 1944713020096987230413783040, coefficient := (-1944713020096987230413783040) }, { argument := 81265669112259588162322432, coefficient := (-81265669112259588162322432) }, { argument := 13317878036435174344716451840, coefficient := (-13317878036435174344716451840) }, { argument := 137112710915535014157604618240, coefficient := (-137112710915535014157604618240) }, { argument := 13317878036435174344716451840, coefficient := (-13317878036435174344716451840) }, { argument := 81265669112259588162322432, coefficient := (-81265669112259588162322432) }, { argument := 4291264094300829582473822208, coefficient := (-4291264094300829582473822208) }, { argument := 171563942293693306953283928064, coefficient := (-171563942293693306953283928064) }, { argument := 171563900366549870420686798848, coefficient := (-171563900366549870420686798848) }, { argument := 4291264094300829582473822208, coefficient := (-4291264094300829582473822208) }, { argument := 3523879657279584200539766784, coefficient := (-3523879657279584200539766784) }, { argument := 12836650196055638792810266624, coefficient := (-12836650196055638792810266624) }, { argument := 3523882027686197672217149440, coefficient := (-3523882027686197672217149440) }, { argument := 43026356092847334138839040, coefficient := (-43026356092847334138839040) }, { argument := 1944713020096987230413783040, coefficient := (-1944713020096987230413783040) }, { argument := 43256000762742448953753600, coefficient := (-43256000762742448953753600) }, { argument := 30566589277373063013335040, coefficient := (-30566589277373063013335040) }, { argument := 6062419541580357977505792000, coefficient := (-6062419541580357977505792000) }, { argument := 6062419541580357977505792000, coefficient := (-6062419541580357977505792000) }, { argument := 30566589277373063013335040, coefficient := (-30566589277373063013335040) }, { argument := 44255680552642972257091584, coefficient := (-44255680552642972257091584) }, { argument := 2000276249242615436997033984, coefficient := (-2000276249242615436997033984) }, { argument := 44491886498820804638146560, coefficient := (-44491886498820804638146560) }, { argument := 959790903309514178618720256, coefficient := (-959790903309514178618720256) }] }

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


end Parent3

namespace Parent3

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-471470432309956684545458918391808)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    82555478775, 82555478775, 416242953, 17621683, 721963615, 14865789905,
    721963615, 17621683, 13256145, 2629155375, 2629155375, 13256145,
    34315909, 1405929145, 28949169815, 1405929145, 34315909, 184026199,
    1839333323, 3678665747, 184026199, 37319415, 1686769665, 4689825,
    405638037, 80452154475, 80452154475, 405638037, 34315909, 1405929145,
    28949169815, 1405929145, 34315909, 13256145, 2629155375, 2629155375,
    13256145, 1078632491, 44191772855, 909942824185, 44191772855, 1078632491,
    1858070977, 18571333229, 37142657381, 1858070977, 34315909, 1405929145,
    28949169815, 1405929145, 34315909, 3781441573, 37795333121, 75590647769,
    3781441573, 761889675, 5550763475, 1523780375, 60670691, 3188320835,
    35239207, 2857233, 612400273, 1107653993
  ]
def negativeCoefficients : Array ℕ := #[
    190359973605623240493681868800, 190359973605623240493681868800, 959790903309514178618720256, 81265669112259588162322432, 13317878036435174344716451840, 137112710915535014157604618240,
    13317878036435174344716451840, 81265669112259588162322432, 30566589277373063013335040, 6062419541580357977505792000, 6062419541580357977505792000, 30566589277373063013335040,
    79127098872463283210682368, 12967407561792143440908124160, 133504481680915671679772917760, 12967407561792143440908124160, 79127098872463283210682368, 212167762238159038367924224,
    8482427768906686627674324992, 8482425695953821344563462144, 212167762238159038367924224, 43026356092847334138839040, 1944713020096987230413783040, 43256000762742448953753600,
    935337631887615728208052224, 185510037972358954111677235200, 185510037972358954111677235200, 935337631887615728208052224, 79127098872463283210682368, 12967407561792143440908124160,
    133504481680915671679772917760, 12967407561792143440908124160, 79127098872463283210682368, 978130856875938016426721280, 193997425330571455280185344000, 193997425330571455280185344000,
    978130856875938016426721280, 2487157188883102658757394432, 407597162009844941129085091840, 4196370599862295301718267658240, 407597162009844941129085091840, 2487157188883102658757394432,
    4284419972938308323171631104, 171290315591470510610455724032, 171290273731196521345055719424, 4284419972938308323171631104, 79127098872463283210682368, 12967407561792143440908124160,
    133504481680915671679772917760, 12967407561792143440908124160, 79127098872463283210682368, 4359705307926042175495733248, 174300209315921270381565968384, 174300166720083361176997593088,
    4359705307926042175495733248, 3513595961781686581277491200, 12799189154627460858590003200, 3513598325270771025313792000, 139897088706514178730360832, 7351767308515117394475089920,
    81256079111184268409176064, 105413291819914726584877056, 1412098888337607691543248896, 2554076216386683896212750336
  ]
def negativeScales : Array ℕ := #[
    36, 36, 28, 24, 29, 33,
    29, 24, 23, 31, 31, 23,
    25, 30, 34, 30, 25, 27,
    30, 31, 27, 25, 30, 22,
    28, 36, 36, 28, 25, 30,
    34, 30, 25, 23, 31, 31,
    23, 30, 35, 39, 35, 30,
    30, 34, 35, 30, 25, 30,
    34, 30, 25, 31, 35, 36,
    31, 29, 32, 30, 25, 31,
    25, 21, 29, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36264644911307574, 36264644911307574, 28632850606652610, 24070848383010247, 29427350890142419, 33791277073389239,
    29427350890142419, 24070848383010247, 23660157952662189, 31291952257303309, 31291952257303309, 23660157952662189,
    25032374235195611, 30388876742327768, 34752802925273451, 30388876742327768, 25032374235195611, 27455335930146138,
    30776535802248583, 31776535449679803, 27455335930146138, 25153423035631279, 30651615835428925, 22161102659155964,
    28595617700444954, 36227412005108598, 36227412005108598, 28595617700444954, 25032374235195611, 30388876742327768,
    34752802925273451, 30388876742327768, 25032374235195611, 23660157952662189, 31291952257303309, 31291952257303309,
    23660157952662189, 30006556251039880, 35363058758172034, 39726984941013510, 35363058758172034, 30006556251039880,
    30791158467230713, 34112358338397006, 35112357985828229, 30791158467230713, 25032374235195611, 30388876742327768,
    34752802925273451, 30388876742327768, 25032374235195611, 31816289182912759, 35137489053720688, 36137488701151911,
    31816289182912759, 29505006863308955, 32370039073348660, 30505007833765682, 25854496408927902, 31570149666433103,
    25070678123372250, 21446187258464497, 29189899685071248, 30044860139216519
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
noncomputable def negativeCeiling : ℝ := 3415015939 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 190359973605623240493681868800, coefficient := (-190359973605623240493681868800) }, { argument := 190359973605623240493681868800, coefficient := (-190359973605623240493681868800) }, { argument := 959790903309514178618720256, coefficient := (-959790903309514178618720256) }, { argument := 81265669112259588162322432, coefficient := (-81265669112259588162322432) }, { argument := 13317878036435174344716451840, coefficient := (-13317878036435174344716451840) }, { argument := 137112710915535014157604618240, coefficient := (-137112710915535014157604618240) }, { argument := 13317878036435174344716451840, coefficient := (-13317878036435174344716451840) }, { argument := 81265669112259588162322432, coefficient := (-81265669112259588162322432) }, { argument := 30566589277373063013335040, coefficient := (-30566589277373063013335040) }, { argument := 6062419541580357977505792000, coefficient := (-6062419541580357977505792000) }, { argument := 6062419541580357977505792000, coefficient := (-6062419541580357977505792000) }, { argument := 30566589277373063013335040, coefficient := (-30566589277373063013335040) }, { argument := 79127098872463283210682368, coefficient := (-79127098872463283210682368) }, { argument := 12967407561792143440908124160, coefficient := (-12967407561792143440908124160) }, { argument := 133504481680915671679772917760, coefficient := (-133504481680915671679772917760) }, { argument := 12967407561792143440908124160, coefficient := (-12967407561792143440908124160) }, { argument := 79127098872463283210682368, coefficient := (-79127098872463283210682368) }, { argument := 212167762238159038367924224, coefficient := (-212167762238159038367924224) }, { argument := 8482427768906686627674324992, coefficient := (-8482427768906686627674324992) }, { argument := 8482425695953821344563462144, coefficient := (-8482425695953821344563462144) }, { argument := 212167762238159038367924224, coefficient := (-212167762238159038367924224) }, { argument := 43026356092847334138839040, coefficient := (-43026356092847334138839040) }, { argument := 1944713020096987230413783040, coefficient := (-1944713020096987230413783040) }, { argument := 43256000762742448953753600, coefficient := (-43256000762742448953753600) }, { argument := 935337631887615728208052224, coefficient := (-935337631887615728208052224) }, { argument := 185510037972358954111677235200, coefficient := (-185510037972358954111677235200) }, { argument := 185510037972358954111677235200, coefficient := (-185510037972358954111677235200) }, { argument := 935337631887615728208052224, coefficient := (-935337631887615728208052224) }, { argument := 79127098872463283210682368, coefficient := (-79127098872463283210682368) }, { argument := 12967407561792143440908124160, coefficient := (-12967407561792143440908124160) }, { argument := 133504481680915671679772917760, coefficient := (-133504481680915671679772917760) }, { argument := 12967407561792143440908124160, coefficient := (-12967407561792143440908124160) }, { argument := 79127098872463283210682368, coefficient := (-79127098872463283210682368) }, { argument := 978130856875938016426721280, coefficient := (-978130856875938016426721280) }, { argument := 193997425330571455280185344000, coefficient := (-193997425330571455280185344000) }, { argument := 193997425330571455280185344000, coefficient := (-193997425330571455280185344000) }, { argument := 978130856875938016426721280, coefficient := (-978130856875938016426721280) }, { argument := 2487157188883102658757394432, coefficient := (-2487157188883102658757394432) }, { argument := 407597162009844941129085091840, coefficient := (-407597162009844941129085091840) }, { argument := 4196370599862295301718267658240, coefficient := (-4196370599862295301718267658240) }, { argument := 407597162009844941129085091840, coefficient := (-407597162009844941129085091840) }, { argument := 2487157188883102658757394432, coefficient := (-2487157188883102658757394432) }, { argument := 4284419972938308323171631104, coefficient := (-4284419972938308323171631104) }, { argument := 171290315591470510610455724032, coefficient := (-171290315591470510610455724032) }, { argument := 171290273731196521345055719424, coefficient := (-171290273731196521345055719424) }, { argument := 4284419972938308323171631104, coefficient := (-4284419972938308323171631104) }, { argument := 79127098872463283210682368, coefficient := (-79127098872463283210682368) }, { argument := 12967407561792143440908124160, coefficient := (-12967407561792143440908124160) }, { argument := 133504481680915671679772917760, coefficient := (-133504481680915671679772917760) }, { argument := 12967407561792143440908124160, coefficient := (-12967407561792143440908124160) }, { argument := 79127098872463283210682368, coefficient := (-79127098872463283210682368) }, { argument := 4359705307926042175495733248, coefficient := (-4359705307926042175495733248) }, { argument := 174300209315921270381565968384, coefficient := (-174300209315921270381565968384) }, { argument := 174300166720083361176997593088, coefficient := (-174300166720083361176997593088) }, { argument := 4359705307926042175495733248, coefficient := (-4359705307926042175495733248) }, { argument := 3513595961781686581277491200, coefficient := (-3513595961781686581277491200) }, { argument := 12799189154627460858590003200, coefficient := (-12799189154627460858590003200) }, { argument := 3513598325270771025313792000, coefficient := (-3513598325270771025313792000) }, { argument := 139897088706514178730360832, coefficient := (-139897088706514178730360832) }, { argument := 7351767308515117394475089920, coefficient := (-7351767308515117394475089920) }, { argument := 81256079111184268409176064, coefficient := (-81256079111184268409176064) }, { argument := 105413291819914726584877056, coefficient := (-105413291819914726584877056) }, { argument := 1412098888337607691543248896, coefficient := (-1412098888337607691543248896) }, { argument := 2554076216386683896212750336, coefficient := (-2554076216386683896212750336) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1
