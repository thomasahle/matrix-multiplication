import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 10, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-11098905223713831094042675581550592)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2275, 22504844465, 141225, 3125510045, 141225, 147175,
    87675, 4375, 121398078963, 2367589356489, 4735176976131, 15174832239,
    5107000337157, 8497461, 220493, 18385452438497, 13687527, 2553518388365,
    13687527, 14264201, 8497461, 424025, 322365854769, 322365778895,
    327131325515, 543585, 14105, 1177687524655, 875595, 163566828355,
    875595, 912485, 543585, 27125, 582817483785, 582817346551,
    285, 667286444184411, 355027995, 406915580387699, 4006744515, 355027995,
    26042600794764593, 355027995, 355027995, 14718446307, 91292913, 4006744515,
    14718446307, 166822911080109, 355027995, 91292913, 355027995, 2650657324493109,
    157815, 4095, 38791128993476005, 254205, 10602569544674695, 254205,
    264915, 157815, 7875, 33470414626324375
  ]
def negativeCoefficients : Array ℕ := #[
    85947069988227542889267200, 1660564425057975818811877621760, 2667664826173062581216870400, 461243871199387391906031861760, 2667664826173062581216870400, 2780057148465360137302835200,
    1656133925542384576443187200, 82641413450218791239680000, 139962455854402777462905765888, 5459289366348908961702271254528, 5459287363900652449813921529856, 139963123337154948092355674112,
    11775941025485446470325411774464, 40128125015891978287218425856, 2082497505814753364206944256, 42393966976539169908363460870144, 64637518738173306342884769792, 11776025049420107252398775336960,
    64637518738173306342884769792, 67360784707315676126847696896, 40128125015891978287218425856, 2002401447898801311737446400, 1486650105256591186832891314176, 1486649755349526224673261486080,
    754313480033572060407298785280, 2567007584590696093486940160, 133217958481752691478364160, 2715562545763911588259624386560, 4134880480568247000886149120, 754318855403265924324571217920,
    4134880480568247000886149120, 4309088580121308212819394560, 2567007584590696093486940160, 128094190847839126421504000, 2687771241266315360939425136640, 2687770608386196308075273519104,
    88203227799083344586562600960, 375648872672287082154905567232, 3274555281383617161288744960, 14660678849642322613276751429632, 36955695318472250820258693120, 3274555281383617161288744960,
    14660680904382550501457989206016, 3274555281383617161288744960, 3274555281383617161288744960, 135753706093932242886570541056, 3368114003708863365896994816, 36955695318472250820258693120,
    135753706093932242886570541056, 375651800088620140391439532032, 3274555281383617161288744960, 3368114003708863365896994816, 3274555281383617161288744960, 11937499338874041592565741912064,
    1490520532988146118798868480, 77352362989404788600340480, 43674928520074844919754255237120, 2400898343555756323095183360, 11937432062641681461090640199680, 2400898343555756323095183360,
    2502051433618824123572551680, 1490520532988146118798868480, 74377272105196912115712000, 9421084177440653398025175040000
  ]
def negativeScales : Array ℕ := #[
    11, 34, 17, 31, 17, 17,
    16, 12, 36, 41, 42, 33,
    42, 23, 17, 44, 23, 41,
    23, 23, 23, 18, 38, 38,
    38, 19, 13, 40, 19, 37,
    19, 19, 19, 14, 39, 39,
    8, 49, 28, 48, 31, 28,
    54, 28, 28, 33, 26, 31,
    33, 47, 28, 26, 28, 51,
    17, 11, 55, 17, 53, 17,
    18, 17, 12, 54
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11151650829973422, 34389516542908420, 17107635975110110, 31541444493153649, 17107635975110110, 17167173102087474,
    16419877905027552, 12095067301607054, 36820954636911702, 41106556014914685, 42106555485739090, 33820961517126636,
    42215613292943384, 23018600404704159, 17750373329876765, 44063629913081788, 23706358474870738, 41215623586853749,
    23706358474870738, 23765895602081147, 23018600404704159, 18693789801346181, 38229907984387938, 38229907644826366,
    38251078959712604, 19052146120527051, 13783919045936705, 40099093938910516, 19739904190789689, 37251089240572981,
    19739904190789689, 19799441318225700, 19052146120527051, 14727335517242487, 39084253200833232, 39084252861126823,
    8154818109052105, 49245299524456572, 28403357548942316, 48531722849232942, 31899783379412490, 28403357548942316,
    54531723051431173, 28403357548942316, 28403357548942316, 33776906336464517, 26443999533439692, 31899783379412490,
    33776906336464517, 47245310767276337, 28403357548942316, 26443999533439692, 28403357548942316, 51235271594756878,
    17267874811582488, 11999647760072134, 55106576283486721, 17955632893125710, 53235263464129387, 17955632893125710,
    18015170008642424, 17267874811582488, 12943064217429565, 54893735945118143
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
noncomputable def negativeCeiling : ℝ := 14466297161 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 85947069988227542889267200, coefficient := (-85947069988227542889267200) }, { argument := 1660564425057975818811877621760, coefficient := (-1660564425057975818811877621760) }, { argument := 2667664826173062581216870400, coefficient := (-2667664826173062581216870400) }, { argument := 461243871199387391906031861760, coefficient := (-461243871199387391906031861760) }, { argument := 2667664826173062581216870400, coefficient := (-2667664826173062581216870400) }, { argument := 2780057148465360137302835200, coefficient := (-2780057148465360137302835200) }, { argument := 1656133925542384576443187200, coefficient := (-1656133925542384576443187200) }, { argument := 82641413450218791239680000, coefficient := (-82641413450218791239680000) }, { argument := 139962455854402777462905765888, coefficient := (-139962455854402777462905765888) }, { argument := 5459289366348908961702271254528, coefficient := (-5459289366348908961702271254528) }, { argument := 5459287363900652449813921529856, coefficient := (-5459287363900652449813921529856) }, { argument := 139963123337154948092355674112, coefficient := (-139963123337154948092355674112) }, { argument := 11775941025485446470325411774464, coefficient := (-11775941025485446470325411774464) }, { argument := 40128125015891978287218425856, coefficient := (-40128125015891978287218425856) }, { argument := 2082497505814753364206944256, coefficient := (-2082497505814753364206944256) }, { argument := 42393966976539169908363460870144, coefficient := (-42393966976539169908363460870144) }, { argument := 64637518738173306342884769792, coefficient := (-64637518738173306342884769792) }, { argument := 11776025049420107252398775336960, coefficient := (-11776025049420107252398775336960) }, { argument := 64637518738173306342884769792, coefficient := (-64637518738173306342884769792) }, { argument := 67360784707315676126847696896, coefficient := (-67360784707315676126847696896) }, { argument := 40128125015891978287218425856, coefficient := (-40128125015891978287218425856) }, { argument := 2002401447898801311737446400, coefficient := (-2002401447898801311737446400) }, { argument := 1486650105256591186832891314176, coefficient := (-1486650105256591186832891314176) }, { argument := 1486649755349526224673261486080, coefficient := (-1486649755349526224673261486080) }, { argument := 754313480033572060407298785280, coefficient := (-754313480033572060407298785280) }, { argument := 2567007584590696093486940160, coefficient := (-2567007584590696093486940160) }, { argument := 133217958481752691478364160, coefficient := (-133217958481752691478364160) }, { argument := 2715562545763911588259624386560, coefficient := (-2715562545763911588259624386560) }, { argument := 4134880480568247000886149120, coefficient := (-4134880480568247000886149120) }, { argument := 754318855403265924324571217920, coefficient := (-754318855403265924324571217920) }, { argument := 4134880480568247000886149120, coefficient := (-4134880480568247000886149120) }, { argument := 4309088580121308212819394560, coefficient := (-4309088580121308212819394560) }, { argument := 2567007584590696093486940160, coefficient := (-2567007584590696093486940160) }, { argument := 128094190847839126421504000, coefficient := (-128094190847839126421504000) }, { argument := 2687771241266315360939425136640, coefficient := (-2687771241266315360939425136640) }, { argument := 2687770608386196308075273519104, coefficient := (-2687770608386196308075273519104) }, { argument := 88203227799083344586562600960, coefficient := (-88203227799083344586562600960) }, { argument := 375648872672287082154905567232, coefficient := (-375648872672287082154905567232) }, { argument := 3274555281383617161288744960, coefficient := (-3274555281383617161288744960) }, { argument := 14660678849642322613276751429632, coefficient := (-14660678849642322613276751429632) }, { argument := 36955695318472250820258693120, coefficient := (-36955695318472250820258693120) }, { argument := 3274555281383617161288744960, coefficient := (-3274555281383617161288744960) }, { argument := 14660680904382550501457989206016, coefficient := (-14660680904382550501457989206016) }, { argument := 3274555281383617161288744960, coefficient := (-3274555281383617161288744960) }, { argument := 3274555281383617161288744960, coefficient := (-3274555281383617161288744960) }, { argument := 135753706093932242886570541056, coefficient := (-135753706093932242886570541056) }, { argument := 3368114003708863365896994816, coefficient := (-3368114003708863365896994816) }, { argument := 36955695318472250820258693120, coefficient := (-36955695318472250820258693120) }, { argument := 135753706093932242886570541056, coefficient := (-135753706093932242886570541056) }, { argument := 375651800088620140391439532032, coefficient := (-375651800088620140391439532032) }, { argument := 3274555281383617161288744960, coefficient := (-3274555281383617161288744960) }, { argument := 3368114003708863365896994816, coefficient := (-3368114003708863365896994816) }, { argument := 3274555281383617161288744960, coefficient := (-3274555281383617161288744960) }, { argument := 11937499338874041592565741912064, coefficient := (-11937499338874041592565741912064) }, { argument := 1490520532988146118798868480, coefficient := (-1490520532988146118798868480) }, { argument := 77352362989404788600340480, coefficient := (-77352362989404788600340480) }, { argument := 43674928520074844919754255237120, coefficient := (-43674928520074844919754255237120) }, { argument := 2400898343555756323095183360, coefficient := (-2400898343555756323095183360) }, { argument := 11937432062641681461090640199680, coefficient := (-11937432062641681461090640199680) }, { argument := 2400898343555756323095183360, coefficient := (-2400898343555756323095183360) }, { argument := 2502051433618824123572551680, coefficient := (-2502051433618824123572551680) }, { argument := 1490520532988146118798868480, coefficient := (-1490520532988146118798868480) }, { argument := 74377272105196912115712000, coefficient := (-74377272105196912115712000) }, { argument := 9421084177440653398025175040000, coefficient := (-9421084177440653398025175040000) }] }

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

end TermShard6


end Parent2

namespace Parent2

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1230052748954899690429025903181824)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    33470425706430569, 318799160367, 277053, 7189, 1147736442947, 446271,
    159400765895, 446271, 465073, 277053, 13825, 322365854769,
    322365778895, 62005131, 9520022625, 9520020383, 1881, 525,
    7875, 13825, 525, 4375, 525, 13825,
    27475, 4375, 424025, 27125, 7875, 13825,
    525, 27125, 525, 13825, 13825, 525,
    2928278955, 57109322865, 114218603835, 366036615, 10418561059, 10521,
    273, 37514191399, 16947, 5209325275, 16947, 17661,
    10521, 525, 752986017, 14685254451, 29370498129, 94123701,
    327131325515, 543585, 14105, 1177687524655, 875595, 163566828355,
    875595, 912485, 543585, 27125
  ]
def negativeCoefficients : Array ℕ := #[
    9421087296213286305770466443264, 735100815275442276776106000384, 2616691602356967630780235776, 135796370581399517765042176, 2646500053389131643870766956544, 4214910425353438878322655232,
    735106283404588715341858734080, 4214910425353438878322655232, 4392490294575269016938479616, 2616691602356967630780235776, 130573433251345690158694400, 1486650105256591186832891314176,
    1486649755349526224673261486080, 292810952400341607398743474176, 87806710469649799531462656000, 87806689790849692903055294464, 72767662934243759283914145792, 4958484807013127474380800,
    74377272105196912115712000, 130573433251345690158694400, 4958484807013127474380800, 82641413450218791239680000, 4958484807013127474380800, 130573433251345690158694400,
    129747019116843502246297600, 82641413450218791239680000, 2002401447898801311737446400, 128094190847839126421504000, 74377272105196912115712000, 130573433251345690158694400,
    4958484807013127474380800, 128094190847839126421504000, 4958484807013127474380800, 130573433251345690158694400, 130573433251345690158694400, 4958484807013127474380800,
    3376075778707165548726190080, 131685132889188017684065812480, 131685084587541582180211752960, 3376091879255977383344209920, 24023566183961170017851015168, 99368035532543074586591232,
    5156824199293652573356032, 86501835983688635407136718848, 160059889570383754873012224, 24023772536157907560536473600, 160059889570383754873012224, 166803428907921608238170112,
    99368035532543074586591232, 4958484807013127474380800, 3472535086670227421546938368, 135447565257450532475039121408, 135447515575757055956789231616, 3472551647234719594296901632,
    754313480033572060407298785280, 2567007584590696093486940160, 133217958481752691478364160, 2715562545763911588259624386560, 4134880480568247000886149120, 754318855403265924324571217920,
    4134880480568247000886149120, 4309088580121308212819394560, 2567007584590696093486940160, 128094190847839126421504000
  ]
def negativeScales : Array ℕ := #[
    54, 38, 18, 12, 40, 18,
    37, 18, 18, 18, 13, 38,
    38, 25, 33, 33, 10, 9,
    12, 13, 9, 12, 9, 13,
    14, 12, 18, 14, 12, 13,
    9, 14, 9, 13, 13, 9,
    31, 35, 36, 28, 33, 13,
    8, 35, 14, 32, 14, 14,
    13, 9, 29, 33, 34, 26,
    38, 19, 13, 40, 19, 37,
    19, 19, 19, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    54893736422710456, 38213856873415719, 18079802463429916, 12811575389192290, 40061928529697848, 18767560533841008,
    37213867605023272, 18767560533841008, 18827097661601281, 18079802463429916, 13754991860260137, 38229907984387938,
    38229907644826366, 25885884272803755, 33148317856189282, 33148317516429306, 10877284136413052, 9036173612553486,
    12943064217429565, 13754991860260137, 9036173612553486, 12095067301607054, 9036173612553486, 13754991860260137,
    14745831860929201, 12095067301607054, 18693789801346181, 14727335517242487, 12943064217429565, 13754991860260137,
    9036173612553486, 14727335517242487, 9036173612553486, 13754991860260137, 13754991860260137, 9036173612553486,
    31447405848805486, 35733007227947319, 36733006698771722, 28447412729020287, 33278436984993259, 13360984215973970,
    8092757140919853, 35126717410826177, 14048742286056541, 32278449377075686, 14048742286056541, 14108279413033905,
    13360984215973970, 9036173612553486, 29488047833302971, 33773649212664100, 34773648683488501, 26488054713517771,
    38251078959712604, 19052146120527051, 13783919045936705, 40099093938910516, 19739904190789689, 37251089240572981,
    19739904190789689, 19799441318225700, 19052146120527051, 14727335517242487
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
noncomputable def negativeCeiling : ℝ := 3000020023 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9421087296213286305770466443264, coefficient := (-9421087296213286305770466443264) }, { argument := 735100815275442276776106000384, coefficient := (-735100815275442276776106000384) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 135796370581399517765042176, coefficient := (-135796370581399517765042176) }, { argument := 2646500053389131643870766956544, coefficient := (-2646500053389131643870766956544) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 735106283404588715341858734080, coefficient := (-735106283404588715341858734080) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 4392490294575269016938479616, coefficient := (-4392490294575269016938479616) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 130573433251345690158694400, coefficient := (-130573433251345690158694400) }, { argument := 1486650105256591186832891314176, coefficient := (-1486650105256591186832891314176) }, { argument := 1486649755349526224673261486080, coefficient := (-1486649755349526224673261486080) }, { argument := 292810952400341607398743474176, coefficient := (-292810952400341607398743474176) }, { argument := 87806710469649799531462656000, coefficient := (-87806710469649799531462656000) }, { argument := 87806689790849692903055294464, coefficient := (-87806689790849692903055294464) }, { argument := 72767662934243759283914145792, coefficient := (-72767662934243759283914145792) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 74377272105196912115712000, coefficient := (-74377272105196912115712000) }, { argument := 130573433251345690158694400, coefficient := (-130573433251345690158694400) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 82641413450218791239680000, coefficient := (-82641413450218791239680000) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 130573433251345690158694400, coefficient := (-130573433251345690158694400) }, { argument := 129747019116843502246297600, coefficient := (-129747019116843502246297600) }, { argument := 82641413450218791239680000, coefficient := (-82641413450218791239680000) }, { argument := 2002401447898801311737446400, coefficient := (-2002401447898801311737446400) }, { argument := 128094190847839126421504000, coefficient := (-128094190847839126421504000) }, { argument := 74377272105196912115712000, coefficient := (-74377272105196912115712000) }, { argument := 130573433251345690158694400, coefficient := (-130573433251345690158694400) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 128094190847839126421504000, coefficient := (-128094190847839126421504000) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 130573433251345690158694400, coefficient := (-130573433251345690158694400) }, { argument := 130573433251345690158694400, coefficient := (-130573433251345690158694400) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 3376075778707165548726190080, coefficient := (-3376075778707165548726190080) }, { argument := 131685132889188017684065812480, coefficient := (-131685132889188017684065812480) }, { argument := 131685084587541582180211752960, coefficient := (-131685084587541582180211752960) }, { argument := 3376091879255977383344209920, coefficient := (-3376091879255977383344209920) }, { argument := 24023566183961170017851015168, coefficient := (-24023566183961170017851015168) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 5156824199293652573356032, coefficient := (-5156824199293652573356032) }, { argument := 86501835983688635407136718848, coefficient := (-86501835983688635407136718848) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 24023772536157907560536473600, coefficient := (-24023772536157907560536473600) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 166803428907921608238170112, coefficient := (-166803428907921608238170112) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 3472535086670227421546938368, coefficient := (-3472535086670227421546938368) }, { argument := 135447565257450532475039121408, coefficient := (-135447565257450532475039121408) }, { argument := 135447515575757055956789231616, coefficient := (-135447515575757055956789231616) }, { argument := 3472551647234719594296901632, coefficient := (-3472551647234719594296901632) }, { argument := 754313480033572060407298785280, coefficient := (-754313480033572060407298785280) }, { argument := 2567007584590696093486940160, coefficient := (-2567007584590696093486940160) }, { argument := 133217958481752691478364160, coefficient := (-133217958481752691478364160) }, { argument := 2715562545763911588259624386560, coefficient := (-2715562545763911588259624386560) }, { argument := 4134880480568247000886149120, coefficient := (-4134880480568247000886149120) }, { argument := 754318855403265924324571217920, coefficient := (-754318855403265924324571217920) }, { argument := 4134880480568247000886149120, coefficient := (-4134880480568247000886149120) }, { argument := 4309088580121308212819394560, coefficient := (-4309088580121308212819394560) }, { argument := 2567007584590696093486940160, coefficient := (-2567007584590696093486940160) }, { argument := 128094190847839126421504000, coefficient := (-128094190847839126421504000) }] }

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

end TermShard7


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
