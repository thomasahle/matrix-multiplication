import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 3, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3

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
def constantNumerator : ℤ := (-319793849120253873883113815277568)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3891015, 255488383, 238650497, 255488383, 238650497, 371457267591,
    157669191, 2089496359033, 213331437, 7423443, 213257709, 158400873,
    372299057031, 157669191, 902241, 6594745, 9184841089, 8574630527,
    9184841089, 8574630527, 39116408346837, 8332964925, 227694646875947, 12880710975,
    409892865, 12879727935, 8815309395, 39240736241877, 8332964925, 49339515,
    14229, 170289, 254745, 73899, 14229, 295137,
    148257, 14229, 170289, 14229, 2574295017885, 157361511077475,
    43131375, 38202075, 1788103575, 486768375, 78680765602755, 1788103575,
    43131375, 43131375, 18484875, 43131375, 486768375, 18484875,
    1287137444925, 38202075, 3891015, 73478757769, 68597071479, 73478757769,
    68597071479, 417845623645815, 79273316415, 2411682037574025
  ]
def negativeCoefficients : Array ℕ := #[
    73499195281372130284677365760, 4712928815006886154026876928, 4402324641222589126805553152, 4712928815006886154026876928, 4402324641222589126805553152, 209111851488361277546299392,
    363560401835728671533432832, 2352563755983256730931822592, 491908802651961570858369024, 17117294145846331872116736, 491738797458578263630675968, 365247545660396165551620096,
    209585736814399829858844672, 363560401835728671533432832, 16643408819807779559571456, 249142422008577427398365020160, 169430412926474734334403149824, 158174014858186259418035781632,
    169430412926474734334403149824, 158174014858186259418035781632, 22020580256860909082083590144, 38429017836668327063401267200, 256361381706192895090179964928, 59401794710811707615635046400,
    1890297194573644822436904960, 59397261238988152756229898240, 40653439085033095715440558080, 22090570639582646849318682624, 38429017836668327063401267200, 1820306811851907055201812480,
    134389105369504363491360768, 3216668264005556055180312576, 2405998499357255539925975040, 2791825285740671293175365632, 134389105369504363491360768, 2787490153309396958869192704,
    2800495550603219961787711488, 134389105369504363491360768, 3216668264005556055180312576, 134389105369504363491360768, 724599630205538145990082560, 44293327665685911781874073600,
    198908359043048577957888000, 176175975152414454762700800, 8246172256327528189054156800, 2244822909200119665524736000, 44293333331224094638142914560, 8246172256327528189054156800,
    198908359043048577957888000, 198908359043048577957888000, 170492879179755923963904000, 198908359043048577957888000, 2244822909200119665524736000, 170492879179755923963904000,
    724593964667355289721241600, 176175975152414454762700800, 73499195281372130284677365760, 169430479927355053056708313088, 158174077722384219610973995008, 169430479927355053056708313088,
    158174077722384219610973995008, 235226174368710618286160609280, 365583644945425842015735644160, 2715312581438624380770425241600
  ]
def negativeScales : Array ℕ := #[
    21, 27, 27, 27, 27, 38,
    27, 40, 27, 22, 27, 27,
    38, 27, 19, 22, 33, 32,
    33, 32, 45, 32, 47, 33,
    28, 33, 33, 45, 32, 25,
    13, 17, 17, 16, 13, 18,
    17, 13, 17, 13, 41, 47,
    25, 25, 30, 28, 46, 30,
    25, 25, 24, 25, 28, 24,
    40, 25, 21, 36, 35, 36,
    35, 48, 36, 51
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    21891715115047817, 27928682459969980, 27830324101151146, 27928682459969980, 27830324101151146, 38434405296569274,
    27232325540128637, 40926292390347037, 27668521339260892, 22823657035773748, 27668022653243586, 27239005045711498,
    38437671005858519, 27232325540128637, 19783153321970993, 22652885444995578, 33096607614833513, 32997427384922505,
    33096607614833513, 32997427384922505, 45152839142218277, 32956182773091720, 47694093702453728, 33584493176786173,
    28610671636323113, 33584383067875468, 33037364059356901, 45157417343455259, 32956182773091720, 25556240198445952,
    13796546654402698, 17377625720034614, 17958694316714768, 16173267221528426, 13796546654402698, 18171025270741756,
    17177740698107733, 13796546654402698, 17377625720034614, 13796546654402698, 41227314536593270, 47161076044822163,
    25362234373190543, 25187147666632450, 30735783160476616, 28858660201351654, 46161076229356578, 30735783160476616,
    25362234373190543, 25362234373190543, 24139841951854093, 25362234373190543, 28858660201351654, 24139841951854093,
    40227303256328343, 25187147666632450, 21891715115047817, 36096608185343948, 35997427958302915, 36096608185343948,
    35997427958302915, 48569963354133538, 36206116281965622, 51098961134423467
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
noncomputable def negativeCeiling : ℝ := 591217781 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 73499195281372130284677365760, coefficient := (-73499195281372130284677365760) }, { argument := 4712928815006886154026876928, coefficient := (-4712928815006886154026876928) }, { argument := 4402324641222589126805553152, coefficient := (-4402324641222589126805553152) }, { argument := 4712928815006886154026876928, coefficient := (-4712928815006886154026876928) }, { argument := 4402324641222589126805553152, coefficient := (-4402324641222589126805553152) }, { argument := 209111851488361277546299392, coefficient := (-209111851488361277546299392) }, { argument := 363560401835728671533432832, coefficient := (-363560401835728671533432832) }, { argument := 2352563755983256730931822592, coefficient := (-2352563755983256730931822592) }, { argument := 491908802651961570858369024, coefficient := (-491908802651961570858369024) }, { argument := 17117294145846331872116736, coefficient := (-17117294145846331872116736) }, { argument := 491738797458578263630675968, coefficient := (-491738797458578263630675968) }, { argument := 365247545660396165551620096, coefficient := (-365247545660396165551620096) }, { argument := 209585736814399829858844672, coefficient := (-209585736814399829858844672) }, { argument := 363560401835728671533432832, coefficient := (-363560401835728671533432832) }, { argument := 16643408819807779559571456, coefficient := (-16643408819807779559571456) }, { argument := 249142422008577427398365020160, coefficient := (-249142422008577427398365020160) }, { argument := 169430412926474734334403149824, coefficient := (-169430412926474734334403149824) }, { argument := 158174014858186259418035781632, coefficient := (-158174014858186259418035781632) }, { argument := 169430412926474734334403149824, coefficient := (-169430412926474734334403149824) }, { argument := 158174014858186259418035781632, coefficient := (-158174014858186259418035781632) }, { argument := 22020580256860909082083590144, coefficient := (-22020580256860909082083590144) }, { argument := 38429017836668327063401267200, coefficient := (-38429017836668327063401267200) }, { argument := 256361381706192895090179964928, coefficient := (-256361381706192895090179964928) }, { argument := 59401794710811707615635046400, coefficient := (-59401794710811707615635046400) }, { argument := 1890297194573644822436904960, coefficient := (-1890297194573644822436904960) }, { argument := 59397261238988152756229898240, coefficient := (-59397261238988152756229898240) }, { argument := 40653439085033095715440558080, coefficient := (-40653439085033095715440558080) }, { argument := 22090570639582646849318682624, coefficient := (-22090570639582646849318682624) }, { argument := 38429017836668327063401267200, coefficient := (-38429017836668327063401267200) }, { argument := 1820306811851907055201812480, coefficient := (-1820306811851907055201812480) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 3216668264005556055180312576, coefficient := (-3216668264005556055180312576) }, { argument := 2405998499357255539925975040, coefficient := (-2405998499357255539925975040) }, { argument := 2791825285740671293175365632, coefficient := (-2791825285740671293175365632) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 2787490153309396958869192704, coefficient := (-2787490153309396958869192704) }, { argument := 2800495550603219961787711488, coefficient := (-2800495550603219961787711488) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 3216668264005556055180312576, coefficient := (-3216668264005556055180312576) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 724599630205538145990082560, coefficient := (-724599630205538145990082560) }, { argument := 44293327665685911781874073600, coefficient := (-44293327665685911781874073600) }, { argument := 198908359043048577957888000, coefficient := (-198908359043048577957888000) }, { argument := 176175975152414454762700800, coefficient := (-176175975152414454762700800) }, { argument := 8246172256327528189054156800, coefficient := (-8246172256327528189054156800) }, { argument := 2244822909200119665524736000, coefficient := (-2244822909200119665524736000) }, { argument := 44293333331224094638142914560, coefficient := (-44293333331224094638142914560) }, { argument := 8246172256327528189054156800, coefficient := (-8246172256327528189054156800) }, { argument := 198908359043048577957888000, coefficient := (-198908359043048577957888000) }, { argument := 198908359043048577957888000, coefficient := (-198908359043048577957888000) }, { argument := 170492879179755923963904000, coefficient := (-170492879179755923963904000) }, { argument := 198908359043048577957888000, coefficient := (-198908359043048577957888000) }, { argument := 2244822909200119665524736000, coefficient := (-2244822909200119665524736000) }, { argument := 170492879179755923963904000, coefficient := (-170492879179755923963904000) }, { argument := 724593964667355289721241600, coefficient := (-724593964667355289721241600) }, { argument := 176175975152414454762700800, coefficient := (-176175975152414454762700800) }, { argument := 73499195281372130284677365760, coefficient := (-73499195281372130284677365760) }, { argument := 169430479927355053056708313088, coefficient := (-169430479927355053056708313088) }, { argument := 158174077722384219610973995008, coefficient := (-158174077722384219610973995008) }, { argument := 169430479927355053056708313088, coefficient := (-169430479927355053056708313088) }, { argument := 158174077722384219610973995008, coefficient := (-158174077722384219610973995008) }, { argument := 235226174368710618286160609280, coefficient := (-235226174368710618286160609280) }, { argument := 365583644945425842015735644160, coefficient := (-365583644945425842015735644160) }, { argument := 2715312581438624380770425241600, coefficient := (-2715312581438624380770425241600) }] }

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
def constantNumerator : ℤ := (-495712608542103117426832260988928)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    127674816405, 3955569195, 127674785685, 85281384945, 419141472503415, 79273316415,
    474673065, 14601, 174741, 261405, 75831, 14601,
    302853, 152133, 14601, 174741, 14601, 156187590620771,
    8163413355907485, 3626884625, 3212383525, 150360274025, 40931983625, 4081708125258813,
    150360274025, 3626884625, 3626884625, 1554379125, 3626884625, 40931983625,
    1554379125, 78092348005315, 3212383525, 465, 5565, 8325,
    2415, 465, 9645, 4845, 465, 5565,
    465, 87988005, 7398844635, 3699421425, 43994895, 371924928391,
    39185479399637, 14229, 418565539677815, 14601, 465, 14229,
    8091, 14601, 227943, 279, 19592753338579, 14229,
    465, 279, 465, 7161
  ]
def negativeCoefficients : Array ℕ := #[
    588796165720222197466917765120, 18241843151503577937378017280, 588796024049227711377561354240, 393290970582980431371860705280, 235955672422737598652853780480, 365583644945425842015735644160,
    17512345097476597570684846080, 137902546032759379530350592, 3300764166332498697145810944, 2468900420909079214172405760, 2864814182099904529598251008, 137902546032759379530350592,
    2860365712873041323806949376, 2873711120553630941180854272, 137902546032759379530350592, 3300764166332498697145810944, 137902546032759379530350592, 43962898432474990726690635776,
    2297796584233517480451149660160, 16726053115561759867928576000, 14814504188068987311593881600, 693414373448003244810410393600, 188765456589911289938051072000, 2297797398993839504854830022656,
    693414373448003244810410393600, 16726053115561759867928576000, 16726053115561759867928576000, 14336616956195794172510208000, 16726053115561759867928576000, 188765456589911289938051072000,
    14336616956195794172510208000, 43962083672152966323010273280, 14814504188068987311593881600, 4391800829068770048737280, 105119877908678302456872960, 78627401939779592808038400,
    91236120449041545528606720, 4391800829068770048737280, 91094449454555456172195840, 91519462438013724241428480, 4391800829068770048737280, 105119877908678302456872960,
    4391800829068770048737280, 202886526223909549517045760, 17060574177872995065287147520, 17060570061943223618843443200, 202890642153680995960750080, 209375121113938251053268992,
    22059463802817430063880863744, 134389105369504363491360768, 235631451065392274045434593280, 137902546032759379530350592, 4391800829068770048737280, 134389105369504363491360768,
    76417334425796598848028672, 137902546032759379530350592, 2152860766409511077891014656, 84322575918120384935755776, 22059479158696606462740791296, 134389105369504363491360768,
    4391800829068770048737280, 84322575918120384935755776, 4391800829068770048737280, 135267465535318117501108224
  ]
def negativeScales : Array ℕ := #[
    36, 31, 36, 36, 48, 36,
    28, 13, 17, 17, 16, 13,
    18, 17, 13, 17, 13, 47,
    52, 31, 31, 37, 35, 51,
    37, 31, 31, 30, 31, 35,
    30, 46, 31, 8, 12, 13,
    11, 8, 13, 12, 8, 12,
    8, 26, 32, 31, 25, 38,
    45, 13, 48, 13, 8, 13,
    12, 13, 17, 8, 44, 13,
    8, 8, 8, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36893683032131241, 31881238166386031, 36893682685002486, 36311511816110716, 48574430606312448, 36206116281965622,
    28822358947452918, 13833779561266426, 17414858626233599, 17995927233034729, 16210500127727401, 13833779561266426,
    18208258176940731, 17214973604306709, 13833779561266426, 17414858626233599, 13833779561266426, 47150273161793710,
    52858093935612196, 31756083706640273, 31580996999828784, 37129632493505341, 35252509532503062, 51858094447167710,
    37129632493505341, 31756083706640273, 31756083706640273, 30533691285047920, 31756083706640273, 35252509532503062,
    30533691285047920, 46150246424212467, 31580996999828784, 8861086908132560, 12442165972229357, 13023234556845987,
    11237807473723136, 8861086908132560, 13235565522936466, 12242280950302444, 8861086908132560, 12442165972229357,
    8861086908132560, 26390803525387317, 32784652859051247, 31784652510995421, 25390832792837202, 38436220492062607,
    45155384380757414, 13796546654402698, 48572446868441632, 13833779561266426, 8861086908132560, 13796546654402698,
    12982102324703674, 13833779561266426, 17798313580599046, 8124121311829188, 44155385385035815, 13796546654402698,
    8861086908132560, 8124121311829188, 8861086908132560, 12805945352531863
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
noncomputable def negativeCeiling : ℝ := 4957774683 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 588796165720222197466917765120, coefficient := (-588796165720222197466917765120) }, { argument := 18241843151503577937378017280, coefficient := (-18241843151503577937378017280) }, { argument := 588796024049227711377561354240, coefficient := (-588796024049227711377561354240) }, { argument := 393290970582980431371860705280, coefficient := (-393290970582980431371860705280) }, { argument := 235955672422737598652853780480, coefficient := (-235955672422737598652853780480) }, { argument := 365583644945425842015735644160, coefficient := (-365583644945425842015735644160) }, { argument := 17512345097476597570684846080, coefficient := (-17512345097476597570684846080) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 3300764166332498697145810944, coefficient := (-3300764166332498697145810944) }, { argument := 2468900420909079214172405760, coefficient := (-2468900420909079214172405760) }, { argument := 2864814182099904529598251008, coefficient := (-2864814182099904529598251008) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 2860365712873041323806949376, coefficient := (-2860365712873041323806949376) }, { argument := 2873711120553630941180854272, coefficient := (-2873711120553630941180854272) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 3300764166332498697145810944, coefficient := (-3300764166332498697145810944) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 43962898432474990726690635776, coefficient := (-43962898432474990726690635776) }, { argument := 2297796584233517480451149660160, coefficient := (-2297796584233517480451149660160) }, { argument := 16726053115561759867928576000, coefficient := (-16726053115561759867928576000) }, { argument := 14814504188068987311593881600, coefficient := (-14814504188068987311593881600) }, { argument := 693414373448003244810410393600, coefficient := (-693414373448003244810410393600) }, { argument := 188765456589911289938051072000, coefficient := (-188765456589911289938051072000) }, { argument := 2297797398993839504854830022656, coefficient := (-2297797398993839504854830022656) }, { argument := 693414373448003244810410393600, coefficient := (-693414373448003244810410393600) }, { argument := 16726053115561759867928576000, coefficient := (-16726053115561759867928576000) }, { argument := 16726053115561759867928576000, coefficient := (-16726053115561759867928576000) }, { argument := 14336616956195794172510208000, coefficient := (-14336616956195794172510208000) }, { argument := 16726053115561759867928576000, coefficient := (-16726053115561759867928576000) }, { argument := 188765456589911289938051072000, coefficient := (-188765456589911289938051072000) }, { argument := 14336616956195794172510208000, coefficient := (-14336616956195794172510208000) }, { argument := 43962083672152966323010273280, coefficient := (-43962083672152966323010273280) }, { argument := 14814504188068987311593881600, coefficient := (-14814504188068987311593881600) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 105119877908678302456872960, coefficient := (-105119877908678302456872960) }, { argument := 78627401939779592808038400, coefficient := (-78627401939779592808038400) }, { argument := 91236120449041545528606720, coefficient := (-91236120449041545528606720) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 91094449454555456172195840, coefficient := (-91094449454555456172195840) }, { argument := 91519462438013724241428480, coefficient := (-91519462438013724241428480) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 105119877908678302456872960, coefficient := (-105119877908678302456872960) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 202886526223909549517045760, coefficient := (-202886526223909549517045760) }, { argument := 17060574177872995065287147520, coefficient := (-17060574177872995065287147520) }, { argument := 17060570061943223618843443200, coefficient := (-17060570061943223618843443200) }, { argument := 202890642153680995960750080, coefficient := (-202890642153680995960750080) }, { argument := 209375121113938251053268992, coefficient := (-209375121113938251053268992) }, { argument := 22059463802817430063880863744, coefficient := (-22059463802817430063880863744) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 235631451065392274045434593280, coefficient := (-235631451065392274045434593280) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 76417334425796598848028672, coefficient := (-76417334425796598848028672) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 2152860766409511077891014656, coefficient := (-2152860766409511077891014656) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 22059479158696606462740791296, coefficient := (-22059479158696606462740791296) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 135267465535318117501108224, coefficient := (-135267465535318117501108224) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3
