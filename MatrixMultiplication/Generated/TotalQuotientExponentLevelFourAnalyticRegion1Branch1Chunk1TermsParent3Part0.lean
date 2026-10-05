import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
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

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-178290916286145357030169138692096)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    191029899, 761889675, 378343263, 761889675, 51097269, 525058065,
    4600128963, 3465383229, 171334737, 1729928151, 3520652499, 204565497,
    525058065, 171334737, 37319415, 1686769665, 4689825, 60670691,
    3188320835, 35239207, 2857233, 612400273, 1107653993, 3188320835,
    612400273, 18095809, 18095809, 35239207, 35239207, 1107653993,
    35239207, 60670691, 2857233, 1391752403, 5550763475, 2756427911,
    5550763475, 3440959533, 5247931005, 62814211281, 34636344633, 1712482749,
    17290551627, 35188758423, 1720522449, 5247931005, 1712482749, 421176255,
    19036400505, 52928025, 7566502463, 51210167225, 1443756835, 117061365,
    25090152565, 45380789165, 51210167225, 25090152565, 741388645, 741388645,
    1443756835, 1443756835, 45380789165, 1443756835
  ]
def negativeCoefficients : Array ℕ := #[
    3523879657279584200539766784, 3513595961781686581277491200, 3489600672286592136332181504, 3513595961781686581277491200, 235644561027123196698034176, 4842805874446077271757291520,
    5303587605407494702406565888, 3995314846418013749199765504, 197535502773458415032205312, 3988942733425321542263242752, 4059035976344935818564993024, 235847960591887441248387072,
    4842805874446077271757291520, 197535502773458415032205312, 43026356092847334138839040, 1944713020096987230413783040, 43256000762742448953753600, 139897088706514178730360832,
    7351767308515117394475089920, 81256079111184268409176064, 105413291819914726584877056, 1412098888337607691543248896, 2554076216386683896212750336, 7351767308515117394475089920,
    1412098888337607691543248896, 83452189357432491879694336, 83452189357432491879694336, 81256079111184268409176064, 81256079111184268409176064, 2554076216386683896212750336,
    81256079111184268409176064, 139897088706514178730360832, 105413291819914726584877056, 12836650196055638792810266624, 12799189154627460858590003200, 12711780057961712345409388544,
    12799189154627460858590003200, 7934312484155267038278844416, 193614480331440722580508508160, 144839709961565801579399872512, 159731946273438596128919519232, 7897432750361397894731268096,
    159477190378265647809734639616, 162279505225168079320768315392, 7934509322443748565263056896, 193614480331440722580508508160, 7897432750361397894731268096, 485583161619277056709754880,
    21947475512523141600384122880, 488174865750950495335219200, 17447166808506746981136203776, 118082606096430483041891123200, 13316306419956954475192647680, 17275208328592805805655326720,
    231415811568441127771591147520, 418563901794863190666190520320, 118082606096430483041891123200, 231415811568441127771591147520, 13676206593469304596143800320, 13676206593469304596143800320,
    13316306419956954475192647680, 13316306419956954475192647680, 418563901794863190666190520320, 13316306419956954475192647680
  ]
def negativeScales : Array ℕ := #[
    27, 29, 28, 29, 25, 28,
    32, 31, 27, 30, 31, 27,
    28, 27, 25, 30, 22, 25,
    31, 25, 21, 29, 30, 31,
    29, 24, 24, 25, 25, 30,
    25, 25, 21, 30, 32, 31,
    32, 31, 32, 35, 35, 30,
    34, 35, 30, 32, 30, 28,
    34, 25, 32, 35, 30, 26,
    34, 35, 35, 34, 29, 29,
    30, 30, 35, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    27509223218110073, 29505006863308955, 28495120514991752, 29505006863308955, 25606742849599528, 28967901749185153,
    32099027161171684, 31690367759654755, 27352242437181978, 30688064973782247, 31713195689149836, 27607987592827504,
    28967901749185153, 27352242437181978, 25153423035631279, 30651615835428925, 22161102659155964, 25854496408927902,
    31570149666433103, 25070678123372250, 21446187258464497, 29189899685071248, 30044860139216519, 31570149666433103,
    29189899685071248, 24109152271186886, 24109152271186886, 25070678123372250, 25070678123372250, 30044860139216519,
    25070678123372250, 25854496408927902, 21446187258464497, 30374255428149730, 32370039073348660, 31360152725031546,
    32370039073348660, 31680163779560597, 32289101606831232, 35870371947239665, 35011567631302323, 30673442308925418,
    34009264845432903, 35034395560756585, 30680199570197915, 32289101606831232, 30673442308925418, 28649848861772002,
    34148041661526225, 25657528485301237, 32816979438421596, 35575711219040885, 30427180630504423, 26802689766278991,
    34546402192204593, 35401362646348679, 35575711219040885, 34546402192204593, 29465654778319121, 29465654778319121,
    30427180630504423, 30427180630504423, 35401362646348679, 30427180630504423
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
noncomputable def negativeCeiling : ℝ := 73202299 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3523879657279584200539766784, coefficient := (-3523879657279584200539766784) }, { argument := 3513595961781686581277491200, coefficient := (-3513595961781686581277491200) }, { argument := 3489600672286592136332181504, coefficient := (-3489600672286592136332181504) }, { argument := 3513595961781686581277491200, coefficient := (-3513595961781686581277491200) }, { argument := 235644561027123196698034176, coefficient := (-235644561027123196698034176) }, { argument := 4842805874446077271757291520, coefficient := (-4842805874446077271757291520) }, { argument := 5303587605407494702406565888, coefficient := (-5303587605407494702406565888) }, { argument := 3995314846418013749199765504, coefficient := (-3995314846418013749199765504) }, { argument := 197535502773458415032205312, coefficient := (-197535502773458415032205312) }, { argument := 3988942733425321542263242752, coefficient := (-3988942733425321542263242752) }, { argument := 4059035976344935818564993024, coefficient := (-4059035976344935818564993024) }, { argument := 235847960591887441248387072, coefficient := (-235847960591887441248387072) }, { argument := 4842805874446077271757291520, coefficient := (-4842805874446077271757291520) }, { argument := 197535502773458415032205312, coefficient := (-197535502773458415032205312) }, { argument := 43026356092847334138839040, coefficient := (-43026356092847334138839040) }, { argument := 1944713020096987230413783040, coefficient := (-1944713020096987230413783040) }, { argument := 43256000762742448953753600, coefficient := (-43256000762742448953753600) }, { argument := 139897088706514178730360832, coefficient := (-139897088706514178730360832) }, { argument := 7351767308515117394475089920, coefficient := (-7351767308515117394475089920) }, { argument := 81256079111184268409176064, coefficient := (-81256079111184268409176064) }, { argument := 105413291819914726584877056, coefficient := (-105413291819914726584877056) }, { argument := 1412098888337607691543248896, coefficient := (-1412098888337607691543248896) }, { argument := 2554076216386683896212750336, coefficient := (-2554076216386683896212750336) }, { argument := 7351767308515117394475089920, coefficient := (-7351767308515117394475089920) }, { argument := 1412098888337607691543248896, coefficient := (-1412098888337607691543248896) }, { argument := 83452189357432491879694336, coefficient := (-83452189357432491879694336) }, { argument := 83452189357432491879694336, coefficient := (-83452189357432491879694336) }, { argument := 81256079111184268409176064, coefficient := (-81256079111184268409176064) }, { argument := 81256079111184268409176064, coefficient := (-81256079111184268409176064) }, { argument := 2554076216386683896212750336, coefficient := (-2554076216386683896212750336) }, { argument := 81256079111184268409176064, coefficient := (-81256079111184268409176064) }, { argument := 139897088706514178730360832, coefficient := (-139897088706514178730360832) }, { argument := 105413291819914726584877056, coefficient := (-105413291819914726584877056) }, { argument := 12836650196055638792810266624, coefficient := (-12836650196055638792810266624) }, { argument := 12799189154627460858590003200, coefficient := (-12799189154627460858590003200) }, { argument := 12711780057961712345409388544, coefficient := (-12711780057961712345409388544) }, { argument := 12799189154627460858590003200, coefficient := (-12799189154627460858590003200) }, { argument := 7934312484155267038278844416, coefficient := (-7934312484155267038278844416) }, { argument := 193614480331440722580508508160, coefficient := (-193614480331440722580508508160) }, { argument := 144839709961565801579399872512, coefficient := (-144839709961565801579399872512) }, { argument := 159731946273438596128919519232, coefficient := (-159731946273438596128919519232) }, { argument := 7897432750361397894731268096, coefficient := (-7897432750361397894731268096) }, { argument := 159477190378265647809734639616, coefficient := (-159477190378265647809734639616) }, { argument := 162279505225168079320768315392, coefficient := (-162279505225168079320768315392) }, { argument := 7934509322443748565263056896, coefficient := (-7934509322443748565263056896) }, { argument := 193614480331440722580508508160, coefficient := (-193614480331440722580508508160) }, { argument := 7897432750361397894731268096, coefficient := (-7897432750361397894731268096) }, { argument := 485583161619277056709754880, coefficient := (-485583161619277056709754880) }, { argument := 21947475512523141600384122880, coefficient := (-21947475512523141600384122880) }, { argument := 488174865750950495335219200, coefficient := (-488174865750950495335219200) }, { argument := 17447166808506746981136203776, coefficient := (-17447166808506746981136203776) }, { argument := 118082606096430483041891123200, coefficient := (-118082606096430483041891123200) }, { argument := 13316306419956954475192647680, coefficient := (-13316306419956954475192647680) }, { argument := 17275208328592805805655326720, coefficient := (-17275208328592805805655326720) }, { argument := 231415811568441127771591147520, coefficient := (-231415811568441127771591147520) }, { argument := 418563901794863190666190520320, coefficient := (-418563901794863190666190520320) }, { argument := 118082606096430483041891123200, coefficient := (-118082606096430483041891123200) }, { argument := 231415811568441127771591147520, coefficient := (-231415811568441127771591147520) }, { argument := 13676206593469304596143800320, coefficient := (-13676206593469304596143800320) }, { argument := 13676206593469304596143800320, coefficient := (-13676206593469304596143800320) }, { argument := 13316306419956954475192647680, coefficient := (-13316306419956954475192647680) }, { argument := 13316306419956954475192647680, coefficient := (-13316306419956954475192647680) }, { argument := 418563901794863190666190520320, coefficient := (-418563901794863190666190520320) }, { argument := 13316306419956954475192647680, coefficient := (-13316306419956954475192647680) }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1063831920071570734472380565946368)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    7566502463, 117061365, 37319415, 1686769665, 4689825, 204144633,
    40488992775, 40488992775, 204144633, 59497853, 7374296903, 204144633,
    73559795675, 7953687, 13256145, 405638037, 13256145, 7953687,
    6498162279, 416242953, 7374296903, 405638037, 13256145, 416242953,
    13256145, 405638037, 13256145, 59497853, 382060055, 1523780375,
    756687035, 1523780375, 430119837, 10495859445, 62814196107, 69272672337,
    3424964661, 34581094803, 70377499647, 3441044061, 10495859445, 3424964661,
    75538626335, 58871452325, 29728071245, 2410384155, 516625670555, 934425590755,
    58871452325, 516625670555, 15265766315, 15265766315, 29728071245, 29728071245,
    934425590755, 29728071245, 75538626335, 2410384155, 37319415, 1686769665,
    4689825, 7953687, 1577493225, 1577493225
  ]
def negativeCoefficients : Array ℕ := #[
    17447166808506746981136203776, 17275208328592805805655326720, 43026356092847334138839040, 1944713020096987230413783040, 43256000762742448953753600, 941450949743090340810719232,
    186722521880675025707178393600, 186722521880675025707178393600, 941450949743090340810719232, 137192708403274008343085056, 17003970961648743775423430656, 941450949743090340810719232,
    169617340616386469521103257600, 586878514125562809856032768, 30566589277373063013335040, 935337631887615728208052224, 978130856875938016426721280, 586878514125562809856032768,
    14983742063768275489136836608, 959790903309514178618720256, 17003970961648743775423430656, 935337631887615728208052224, 30566589277373063013335040, 959790903309514178618720256,
    30566589277373063013335040, 935337631887615728208052224, 978130856875938016426721280, 137192708403274008343085056, 3523882027686197672217149440, 3513598325270771025313792000,
    3489603019634775515872624640, 3513598325270771025313792000, 7934310554164668326417006592, 193614433015542173515508613120, 144839674972703979770807844864, 159731907237822293150294605824,
    7897430820370799182869430272, 159477151404907106079879462912, 162279465566974163854446034944, 7934507392453149853401219072, 193614433015542173515508613120, 7897430820370799182869430272,
    174180213460165189605177425920, 135748326785858519232308838400, 137096530515379770469363220480, 177854958506438621149444177920, 2382515381659167362481095966720, 4309277432145585758266741227520,
    135748326785858519232308838400, 2382515381659167362481095966720, 140801842150930575076643307520, 140801842150930575076643307520, 137096530515379770469363220480, 137096530515379770469363220480,
    4309277432145585758266741227520, 137096530515379770469363220480, 174180213460165189605177425920, 177854958506438621149444177920, 43026356092847334138839040, 1944713020096987230413783040,
    43256000762742448953753600, 586878514125562809856032768, 116398455198342873168111206400, 116398455198342873168111206400
  ]
def negativeScales : Array ℕ := #[
    32, 26, 25, 30, 22, 27,
    35, 35, 27, 25, 32, 27,
    36, 22, 23, 28, 23, 22,
    32, 28, 32, 28, 23, 28,
    23, 28, 23, 25, 28, 30,
    29, 30, 28, 33, 35, 36,
    31, 35, 36, 31, 33, 31,
    36, 35, 34, 31, 38, 39,
    35, 38, 33, 33, 34, 34,
    39, 34, 36, 31, 25, 30,
    22, 22, 30, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32816979438421596, 26802689766278991, 25153423035631279, 30651615835428925, 22161102659155964, 27605016398448690,
    35236810703110848, 35236810703110848, 27605016398448690, 25826334274531371, 32779858357616843, 27605016398448690,
    36098198421295122, 22923192365049554, 23660157952662189, 28595617700444954, 23660157952662189, 22923192365049554,
    32597384626619394, 28632850606652610, 32779858357616843, 28595617700444954, 23660157952662189, 28632850606652610,
    23660157952662189, 28595617700444954, 23660157952662189, 25826334274531371, 28509224188566799, 30505007833765682,
    29495121485448478, 30505007833765682, 28680163428630606, 33289101254262455, 35870371598728432, 36011567278733546,
    31673441956356641, 35009264492864126, 36034395208187808, 31680199219276630, 33289101254262455, 31673441956356641,
    36136495497574896, 35776849167823344, 34791106813749348, 31166615948303240, 38910328380160000, 39765288829368267,
    35776849167823344, 38910328380160000, 33829580962192626, 33829580962192626, 34791106813749348, 34791106813749348,
    39765288829368267, 34791106813749348, 36136495497574896, 31166615948303240, 25153423035631279, 30651615835428925,
    22161102659155964, 22923192365049554, 30554986663138648, 30554986663138648
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
noncomputable def negativeCeiling : ℝ := 1579873821 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 17447166808506746981136203776, coefficient := (-17447166808506746981136203776) }, { argument := 17275208328592805805655326720, coefficient := (-17275208328592805805655326720) }, { argument := 43026356092847334138839040, coefficient := (-43026356092847334138839040) }, { argument := 1944713020096987230413783040, coefficient := (-1944713020096987230413783040) }, { argument := 43256000762742448953753600, coefficient := (-43256000762742448953753600) }, { argument := 941450949743090340810719232, coefficient := (-941450949743090340810719232) }, { argument := 186722521880675025707178393600, coefficient := (-186722521880675025707178393600) }, { argument := 186722521880675025707178393600, coefficient := (-186722521880675025707178393600) }, { argument := 941450949743090340810719232, coefficient := (-941450949743090340810719232) }, { argument := 137192708403274008343085056, coefficient := (-137192708403274008343085056) }, { argument := 17003970961648743775423430656, coefficient := (-17003970961648743775423430656) }, { argument := 941450949743090340810719232, coefficient := (-941450949743090340810719232) }, { argument := 169617340616386469521103257600, coefficient := (-169617340616386469521103257600) }, { argument := 586878514125562809856032768, coefficient := (-586878514125562809856032768) }, { argument := 30566589277373063013335040, coefficient := (-30566589277373063013335040) }, { argument := 935337631887615728208052224, coefficient := (-935337631887615728208052224) }, { argument := 978130856875938016426721280, coefficient := (-978130856875938016426721280) }, { argument := 586878514125562809856032768, coefficient := (-586878514125562809856032768) }, { argument := 14983742063768275489136836608, coefficient := (-14983742063768275489136836608) }, { argument := 959790903309514178618720256, coefficient := (-959790903309514178618720256) }, { argument := 17003970961648743775423430656, coefficient := (-17003970961648743775423430656) }, { argument := 935337631887615728208052224, coefficient := (-935337631887615728208052224) }, { argument := 30566589277373063013335040, coefficient := (-30566589277373063013335040) }, { argument := 959790903309514178618720256, coefficient := (-959790903309514178618720256) }, { argument := 30566589277373063013335040, coefficient := (-30566589277373063013335040) }, { argument := 935337631887615728208052224, coefficient := (-935337631887615728208052224) }, { argument := 978130856875938016426721280, coefficient := (-978130856875938016426721280) }, { argument := 137192708403274008343085056, coefficient := (-137192708403274008343085056) }, { argument := 3523882027686197672217149440, coefficient := (-3523882027686197672217149440) }, { argument := 3513598325270771025313792000, coefficient := (-3513598325270771025313792000) }, { argument := 3489603019634775515872624640, coefficient := (-3489603019634775515872624640) }, { argument := 3513598325270771025313792000, coefficient := (-3513598325270771025313792000) }, { argument := 7934310554164668326417006592, coefficient := (-7934310554164668326417006592) }, { argument := 193614433015542173515508613120, coefficient := (-193614433015542173515508613120) }, { argument := 144839674972703979770807844864, coefficient := (-144839674972703979770807844864) }, { argument := 159731907237822293150294605824, coefficient := (-159731907237822293150294605824) }, { argument := 7897430820370799182869430272, coefficient := (-7897430820370799182869430272) }, { argument := 159477151404907106079879462912, coefficient := (-159477151404907106079879462912) }, { argument := 162279465566974163854446034944, coefficient := (-162279465566974163854446034944) }, { argument := 7934507392453149853401219072, coefficient := (-7934507392453149853401219072) }, { argument := 193614433015542173515508613120, coefficient := (-193614433015542173515508613120) }, { argument := 7897430820370799182869430272, coefficient := (-7897430820370799182869430272) }, { argument := 174180213460165189605177425920, coefficient := (-174180213460165189605177425920) }, { argument := 135748326785858519232308838400, coefficient := (-135748326785858519232308838400) }, { argument := 137096530515379770469363220480, coefficient := (-137096530515379770469363220480) }, { argument := 177854958506438621149444177920, coefficient := (-177854958506438621149444177920) }, { argument := 2382515381659167362481095966720, coefficient := (-2382515381659167362481095966720) }, { argument := 4309277432145585758266741227520, coefficient := (-4309277432145585758266741227520) }, { argument := 135748326785858519232308838400, coefficient := (-135748326785858519232308838400) }, { argument := 2382515381659167362481095966720, coefficient := (-2382515381659167362481095966720) }, { argument := 140801842150930575076643307520, coefficient := (-140801842150930575076643307520) }, { argument := 140801842150930575076643307520, coefficient := (-140801842150930575076643307520) }, { argument := 137096530515379770469363220480, coefficient := (-137096530515379770469363220480) }, { argument := 137096530515379770469363220480, coefficient := (-137096530515379770469363220480) }, { argument := 4309277432145585758266741227520, coefficient := (-4309277432145585758266741227520) }, { argument := 137096530515379770469363220480, coefficient := (-137096530515379770469363220480) }, { argument := 174180213460165189605177425920, coefficient := (-174180213460165189605177425920) }, { argument := 177854958506438621149444177920, coefficient := (-177854958506438621149444177920) }, { argument := 43026356092847334138839040, coefficient := (-43026356092847334138839040) }, { argument := 1944713020096987230413783040, coefficient := (-1944713020096987230413783040) }, { argument := 43256000762742448953753600, coefficient := (-43256000762742448953753600) }, { argument := 586878514125562809856032768, coefficient := (-586878514125562809856032768) }, { argument := 116398455198342873168111206400, coefficient := (-116398455198342873168111206400) }, { argument := 116398455198342873168111206400, coefficient := (-116398455198342873168111206400) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1
