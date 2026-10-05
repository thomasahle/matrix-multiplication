import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-382446752195869891724544185466880)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    7953687, 3187447445, 51067035425, 40488992775, 57397855025, 1577493225,
    2629155375, 80452154475, 2629155375, 1577493225, 1288811964825, 82555478775,
    51067035425, 80452154475, 2629155375, 82555478775, 2629155375, 80452154475,
    2629155375, 3187447445, 13256145, 2629155375, 2629155375, 13256145,
    34315909, 1405929145, 28949169815, 1405929145, 34315909, 108540269,
    37319415, 3694660681, 421176255, 37319415, 1847329891, 37319415,
    37319415, 1547156319, 9596421, 421176255, 1547156319, 108540269,
    37319415, 9596421, 37319415, 37319415, 1686769665, 4689825,
    1547156319, 69928650969, 194426745, 405638037, 80452154475, 80452154475,
    405638037, 9596421, 433740771, 1205955, 13256145, 2629155375,
    2629155375, 13256145, 2782371, 113994255
  ]
def negativeCoefficients : Array ℕ := #[
    586878514125562809856032768, 7349753408289300246314352640, 117752566636004310441892249600, 186722521880675025707178393600, 132350442753257344701615308800, 116398455198342873168111206400,
    6062419541580357977505792000, 185510037972358954111677235200, 193997425330571455280185344000, 116398455198342873168111206400, 2971798059282691480573339238400, 190359973605623240493681868800,
    117752566636004310441892249600, 185510037972358954111677235200, 6062419541580357977505792000, 190359973605623240493681868800, 6062419541580357977505792000, 185510037972358954111677235200,
    193997425330571455280185344000, 7349753408289300246314352640, 30566589277373063013335040, 6062419541580357977505792000, 6062419541580357977505792000, 30566589277373063013335040,
    79127098872463283210682368, 12967407561792143440908124160, 133504481680915671679772917760, 12967407561792143440908124160, 79127098872463283210682368, 250276820491823820033753088,
    43026356092847334138839040, 8519307502700555771221901312, 485583161619277056709754880, 43026356092847334138839040, 8519305429747690488111038464, 43026356092847334138839040,
    43026356092847334138839040, 1783749791163470909584441344, 44255680552642972257091584, 485583161619277056709754880, 1783749791163470909584441344, 250276820491823820033753088,
    43026356092847334138839040, 44255680552642972257091584, 43026356092847334138839040, 43026356092847334138839040, 1944713020096987230413783040, 43256000762742448953753600,
    1783749791163470909584441344, 80622245490306527752297119744, 1793270203049694098054184960, 935337631887615728208052224, 185510037972358954111677235200, 185510037972358954111677235200,
    935337631887615728208052224, 44255680552642972257091584, 2000276249242615436997033984, 44491886498820804638146560, 978130856875938016426721280, 193997425330571455280185344000,
    193997425330571455280185344000, 978130856875938016426721280, 102651371510222637678723072, 16822582782865483382799728640
  ]
def negativeScales : Array ℕ := #[
    22, 31, 35, 35, 35, 30,
    31, 36, 31, 30, 40, 36,
    35, 36, 31, 36, 31, 36,
    31, 31, 23, 31, 31, 23,
    25, 30, 34, 30, 25, 26,
    25, 31, 28, 25, 30, 25,
    25, 30, 23, 28, 30, 26,
    25, 23, 25, 25, 30, 22,
    30, 36, 27, 28, 36, 36,
    28, 23, 28, 20, 23, 31,
    31, 23, 21, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    22923192365049554, 31569754408834522, 35571673258136131, 35236810703110848, 35740277773018579, 30554986663138648,
    31291952257303309, 36227412005108598, 31291952257303309, 30554986663138648, 40229178931282786, 36264644911307574,
    35571673258136131, 36227412005108598, 31291952257303309, 36264644911307574, 31291952257303309, 36227412005108598,
    31291952257303309, 31569754408834522, 23660157952662189, 31291952257303309, 31291952257303309, 23660157952662189,
    25032374235195611, 30388876742327768, 34752802925273451, 30388876742327768, 25032374235195611, 26693655148451528,
    25153423035631279, 31782794727249851, 28649848861772002, 25153423035631279, 30782794376207327, 25153423035631279,
    25153423035631279, 30526971822753709, 23194065020128625, 28649848861772002, 30526971822753709, 26693655148451528,
    25153423035631279, 23194065020128625, 25153423035631279, 25153423035631279, 30651615835428925, 22161102659155964,
    30526971822753709, 36025164622528504, 27534651446278572, 28595617700444954, 36227412005108598, 36227412005108598,
    28595617700444954, 23194065020128625, 28692257819964341, 20201744643653310, 23660157952662189, 31291952257303309,
    31291952257303309, 23660157952662189, 21407883370287827, 26764385877726947
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
noncomputable def negativeCeiling : ℝ := 2759823213 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 586878514125562809856032768, coefficient := (-586878514125562809856032768) }, { argument := 7349753408289300246314352640, coefficient := (-7349753408289300246314352640) }, { argument := 117752566636004310441892249600, coefficient := (-117752566636004310441892249600) }, { argument := 186722521880675025707178393600, coefficient := (-186722521880675025707178393600) }, { argument := 132350442753257344701615308800, coefficient := (-132350442753257344701615308800) }, { argument := 116398455198342873168111206400, coefficient := (-116398455198342873168111206400) }, { argument := 6062419541580357977505792000, coefficient := (-6062419541580357977505792000) }, { argument := 185510037972358954111677235200, coefficient := (-185510037972358954111677235200) }, { argument := 193997425330571455280185344000, coefficient := (-193997425330571455280185344000) }, { argument := 116398455198342873168111206400, coefficient := (-116398455198342873168111206400) }, { argument := 2971798059282691480573339238400, coefficient := (-2971798059282691480573339238400) }, { argument := 190359973605623240493681868800, coefficient := (-190359973605623240493681868800) }, { argument := 117752566636004310441892249600, coefficient := (-117752566636004310441892249600) }, { argument := 185510037972358954111677235200, coefficient := (-185510037972358954111677235200) }, { argument := 6062419541580357977505792000, coefficient := (-6062419541580357977505792000) }, { argument := 190359973605623240493681868800, coefficient := (-190359973605623240493681868800) }, { argument := 6062419541580357977505792000, coefficient := (-6062419541580357977505792000) }, { argument := 185510037972358954111677235200, coefficient := (-185510037972358954111677235200) }, { argument := 193997425330571455280185344000, coefficient := (-193997425330571455280185344000) }, { argument := 7349753408289300246314352640, coefficient := (-7349753408289300246314352640) }, { argument := 30566589277373063013335040, coefficient := (-30566589277373063013335040) }, { argument := 6062419541580357977505792000, coefficient := (-6062419541580357977505792000) }, { argument := 6062419541580357977505792000, coefficient := (-6062419541580357977505792000) }, { argument := 30566589277373063013335040, coefficient := (-30566589277373063013335040) }, { argument := 79127098872463283210682368, coefficient := (-79127098872463283210682368) }, { argument := 12967407561792143440908124160, coefficient := (-12967407561792143440908124160) }, { argument := 133504481680915671679772917760, coefficient := (-133504481680915671679772917760) }, { argument := 12967407561792143440908124160, coefficient := (-12967407561792143440908124160) }, { argument := 79127098872463283210682368, coefficient := (-79127098872463283210682368) }, { argument := 250276820491823820033753088, coefficient := (-250276820491823820033753088) }, { argument := 43026356092847334138839040, coefficient := (-43026356092847334138839040) }, { argument := 8519307502700555771221901312, coefficient := (-8519307502700555771221901312) }, { argument := 485583161619277056709754880, coefficient := (-485583161619277056709754880) }, { argument := 43026356092847334138839040, coefficient := (-43026356092847334138839040) }, { argument := 8519305429747690488111038464, coefficient := (-8519305429747690488111038464) }, { argument := 43026356092847334138839040, coefficient := (-43026356092847334138839040) }, { argument := 43026356092847334138839040, coefficient := (-43026356092847334138839040) }, { argument := 1783749791163470909584441344, coefficient := (-1783749791163470909584441344) }, { argument := 44255680552642972257091584, coefficient := (-44255680552642972257091584) }, { argument := 485583161619277056709754880, coefficient := (-485583161619277056709754880) }, { argument := 1783749791163470909584441344, coefficient := (-1783749791163470909584441344) }, { argument := 250276820491823820033753088, coefficient := (-250276820491823820033753088) }, { argument := 43026356092847334138839040, coefficient := (-43026356092847334138839040) }, { argument := 44255680552642972257091584, coefficient := (-44255680552642972257091584) }, { argument := 43026356092847334138839040, coefficient := (-43026356092847334138839040) }, { argument := 43026356092847334138839040, coefficient := (-43026356092847334138839040) }, { argument := 1944713020096987230413783040, coefficient := (-1944713020096987230413783040) }, { argument := 43256000762742448953753600, coefficient := (-43256000762742448953753600) }, { argument := 1783749791163470909584441344, coefficient := (-1783749791163470909584441344) }, { argument := 80622245490306527752297119744, coefficient := (-80622245490306527752297119744) }, { argument := 1793270203049694098054184960, coefficient := (-1793270203049694098054184960) }, { argument := 935337631887615728208052224, coefficient := (-935337631887615728208052224) }, { argument := 185510037972358954111677235200, coefficient := (-185510037972358954111677235200) }, { argument := 185510037972358954111677235200, coefficient := (-185510037972358954111677235200) }, { argument := 935337631887615728208052224, coefficient := (-935337631887615728208052224) }, { argument := 44255680552642972257091584, coefficient := (-44255680552642972257091584) }, { argument := 2000276249242615436997033984, coefficient := (-2000276249242615436997033984) }, { argument := 44491886498820804638146560, coefficient := (-44491886498820804638146560) }, { argument := 978130856875938016426721280, coefficient := (-978130856875938016426721280) }, { argument := 193997425330571455280185344000, coefficient := (-193997425330571455280185344000) }, { argument := 193997425330571455280185344000, coefficient := (-193997425330571455280185344000) }, { argument := 978130856875938016426721280, coefficient := (-978130856875938016426721280) }, { argument := 102651371510222637678723072, coefficient := (-102651371510222637678723072) }, { argument := 16822582782865483382799728640, coefficient := (-16822582782865483382799728640) }] }

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


end Parent3

namespace Parent3

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1060663151390427058664506610679808)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2347229985, 113994255, 2782371, 421176255, 19036400505, 52928025,
    7953687, 1577493225, 1577493225, 7953687, 1547156319, 69928650969,
    194426745, 6498162279, 1288811964825, 1288811964825, 6498162279, 596354851,
    24432768655, 503089626785, 24432768655, 596354851, 416242953, 82555478775,
    82555478775, 416242953, 1078632491, 44191772855, 909942824185, 44191772855,
    1078632491, 563951255, 5636666635, 11273330515, 563951255, 51097269,
    525058065, 4600128963, 3465383229, 171334737, 1729928151, 3520652499,
    204565497, 525058065, 171334737, 7566502463, 51210167225, 1443756835,
    117061365, 25090152565, 45380789165, 51210167225, 25090152565, 741388645,
    741388645, 1443756835, 1443756835, 45380789165, 1443756835, 7566502463,
    117061365, 3187447445, 51067035425, 40488992775
  ]
def negativeCoefficients : Array ℕ := #[
    173195003261728438935921623040, 16822582782865483382799728640, 102651371510222637678723072, 485583161619277056709754880, 21947475512523141600384122880, 488174865750950495335219200,
    586878514125562809856032768, 116398455198342873168111206400, 116398455198342873168111206400, 586878514125562809856032768, 1783749791163470909584441344, 80622245490306527752297119744,
    1793270203049694098054184960, 14983742063768275489136836608, 2971798059282691480573339238400, 2971798059282691480573339238400, 14983742063768275489136836608, 1375100664189024083904561152,
    225352515195468871148754698240, 2320091397860237213245783408640, 225352515195468871148754698240, 1375100664189024083904561152, 959790903309514178618720256, 190359973605623240493681868800,
    190359973605623240493681868800, 959790903309514178618720256, 2487157188883102658757394432, 407597162009844941129085091840, 4196370599862295301718267658240, 407597162009844941129085091840,
    2487157188883102658757394432, 5201532235516157069665239040, 207956293689325220549435064320, 207956242868545297479620362240, 5201532235516157069665239040, 235644561027123196698034176,
    4842805874446077271757291520, 5303587605407494702406565888, 3995314846418013749199765504, 197535502773458415032205312, 3988942733425321542263242752, 4059035976344935818564993024,
    235847960591887441248387072, 4842805874446077271757291520, 197535502773458415032205312, 17447166808506746981136203776, 118082606096430483041891123200, 13316306419956954475192647680,
    17275208328592805805655326720, 231415811568441127771591147520, 418563901794863190666190520320, 118082606096430483041891123200, 231415811568441127771591147520, 13676206593469304596143800320,
    13676206593469304596143800320, 13316306419956954475192647680, 13316306419956954475192647680, 418563901794863190666190520320, 13316306419956954475192647680, 17447166808506746981136203776,
    17275208328592805805655326720, 7349753408289300246314352640, 117752566636004310441892249600, 186722521880675025707178393600
  ]
def negativeScales : Array ℕ := #[
    31, 26, 21, 28, 34, 25,
    22, 30, 30, 22, 30, 36,
    27, 32, 40, 40, 32, 29,
    34, 38, 34, 29, 28, 36,
    36, 28, 30, 35, 39, 35,
    30, 29, 32, 33, 29, 25,
    28, 32, 31, 27, 30, 31,
    27, 28, 27, 32, 35, 30,
    26, 34, 35, 35, 34, 29,
    29, 30, 30, 35, 30, 32,
    26, 31, 35, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31128312060126600, 26764385877726947, 21407883370287827, 28649848861772002, 34148041661526225, 25657528485301237,
    22923192365049554, 30554986663138648, 30554986663138648, 22923192365049554, 30526971822753709, 36025164622528504,
    27534651446278572, 32597384626619394, 40229178931282786, 40229178931282786, 32597384626619394, 29151595796894609,
    34508098304027116, 38872024489355301, 34508098304027116, 29151595796894609, 28632850606652610, 36264644911307574,
    36264644911307574, 28632850606652610, 30006556251039880, 35363058758172034, 39726984941013510, 35363058758172034,
    30006556251039880, 29070995228090153, 32392195099795340, 33392194747226563, 29070995228090153, 25606742849599528,
    28967901749185153, 32099027161171684, 31690367759654755, 27352242437181978, 30688064973782247, 31713195689149836,
    27607987592827504, 28967901749185153, 27352242437181978, 32816979438421596, 35575711219040885, 30427180630504423,
    26802689766278991, 34546402192204593, 35401362646348679, 35575711219040885, 34546402192204593, 29465654778319121,
    29465654778319121, 30427180630504423, 30427180630504423, 35401362646348679, 30427180630504423, 32816979438421596,
    26802689766278991, 31569754408834522, 35571673258136131, 35236810703110848
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
noncomputable def negativeCeiling : ℝ := 987907833 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 173195003261728438935921623040, coefficient := (-173195003261728438935921623040) }, { argument := 16822582782865483382799728640, coefficient := (-16822582782865483382799728640) }, { argument := 102651371510222637678723072, coefficient := (-102651371510222637678723072) }, { argument := 485583161619277056709754880, coefficient := (-485583161619277056709754880) }, { argument := 21947475512523141600384122880, coefficient := (-21947475512523141600384122880) }, { argument := 488174865750950495335219200, coefficient := (-488174865750950495335219200) }, { argument := 586878514125562809856032768, coefficient := (-586878514125562809856032768) }, { argument := 116398455198342873168111206400, coefficient := (-116398455198342873168111206400) }, { argument := 116398455198342873168111206400, coefficient := (-116398455198342873168111206400) }, { argument := 586878514125562809856032768, coefficient := (-586878514125562809856032768) }, { argument := 1783749791163470909584441344, coefficient := (-1783749791163470909584441344) }, { argument := 80622245490306527752297119744, coefficient := (-80622245490306527752297119744) }, { argument := 1793270203049694098054184960, coefficient := (-1793270203049694098054184960) }, { argument := 14983742063768275489136836608, coefficient := (-14983742063768275489136836608) }, { argument := 2971798059282691480573339238400, coefficient := (-2971798059282691480573339238400) }, { argument := 2971798059282691480573339238400, coefficient := (-2971798059282691480573339238400) }, { argument := 14983742063768275489136836608, coefficient := (-14983742063768275489136836608) }, { argument := 1375100664189024083904561152, coefficient := (-1375100664189024083904561152) }, { argument := 225352515195468871148754698240, coefficient := (-225352515195468871148754698240) }, { argument := 2320091397860237213245783408640, coefficient := (-2320091397860237213245783408640) }, { argument := 225352515195468871148754698240, coefficient := (-225352515195468871148754698240) }, { argument := 1375100664189024083904561152, coefficient := (-1375100664189024083904561152) }, { argument := 959790903309514178618720256, coefficient := (-959790903309514178618720256) }, { argument := 190359973605623240493681868800, coefficient := (-190359973605623240493681868800) }, { argument := 190359973605623240493681868800, coefficient := (-190359973605623240493681868800) }, { argument := 959790903309514178618720256, coefficient := (-959790903309514178618720256) }, { argument := 2487157188883102658757394432, coefficient := (-2487157188883102658757394432) }, { argument := 407597162009844941129085091840, coefficient := (-407597162009844941129085091840) }, { argument := 4196370599862295301718267658240, coefficient := (-4196370599862295301718267658240) }, { argument := 407597162009844941129085091840, coefficient := (-407597162009844941129085091840) }, { argument := 2487157188883102658757394432, coefficient := (-2487157188883102658757394432) }, { argument := 5201532235516157069665239040, coefficient := (-5201532235516157069665239040) }, { argument := 207956293689325220549435064320, coefficient := (-207956293689325220549435064320) }, { argument := 207956242868545297479620362240, coefficient := (-207956242868545297479620362240) }, { argument := 5201532235516157069665239040, coefficient := (-5201532235516157069665239040) }, { argument := 235644561027123196698034176, coefficient := (-235644561027123196698034176) }, { argument := 4842805874446077271757291520, coefficient := (-4842805874446077271757291520) }, { argument := 5303587605407494702406565888, coefficient := (-5303587605407494702406565888) }, { argument := 3995314846418013749199765504, coefficient := (-3995314846418013749199765504) }, { argument := 197535502773458415032205312, coefficient := (-197535502773458415032205312) }, { argument := 3988942733425321542263242752, coefficient := (-3988942733425321542263242752) }, { argument := 4059035976344935818564993024, coefficient := (-4059035976344935818564993024) }, { argument := 235847960591887441248387072, coefficient := (-235847960591887441248387072) }, { argument := 4842805874446077271757291520, coefficient := (-4842805874446077271757291520) }, { argument := 197535502773458415032205312, coefficient := (-197535502773458415032205312) }, { argument := 17447166808506746981136203776, coefficient := (-17447166808506746981136203776) }, { argument := 118082606096430483041891123200, coefficient := (-118082606096430483041891123200) }, { argument := 13316306419956954475192647680, coefficient := (-13316306419956954475192647680) }, { argument := 17275208328592805805655326720, coefficient := (-17275208328592805805655326720) }, { argument := 231415811568441127771591147520, coefficient := (-231415811568441127771591147520) }, { argument := 418563901794863190666190520320, coefficient := (-418563901794863190666190520320) }, { argument := 118082606096430483041891123200, coefficient := (-118082606096430483041891123200) }, { argument := 231415811568441127771591147520, coefficient := (-231415811568441127771591147520) }, { argument := 13676206593469304596143800320, coefficient := (-13676206593469304596143800320) }, { argument := 13676206593469304596143800320, coefficient := (-13676206593469304596143800320) }, { argument := 13316306419956954475192647680, coefficient := (-13316306419956954475192647680) }, { argument := 13316306419956954475192647680, coefficient := (-13316306419956954475192647680) }, { argument := 418563901794863190666190520320, coefficient := (-418563901794863190666190520320) }, { argument := 13316306419956954475192647680, coefficient := (-13316306419956954475192647680) }, { argument := 17447166808506746981136203776, coefficient := (-17447166808506746981136203776) }, { argument := 17275208328592805805655326720, coefficient := (-17275208328592805805655326720) }, { argument := 7349753408289300246314352640, coefficient := (-7349753408289300246314352640) }, { argument := 117752566636004310441892249600, coefficient := (-117752566636004310441892249600) }, { argument := 186722521880675025707178393600, coefficient := (-186722521880675025707178393600) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1
