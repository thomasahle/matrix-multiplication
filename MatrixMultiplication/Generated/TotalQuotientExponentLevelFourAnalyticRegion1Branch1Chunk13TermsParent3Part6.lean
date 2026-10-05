import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 6, for level-four region 1, branch 1,
parent chunk 13, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent3

namespace TermShard12

/-! Directed signed-log shard 12.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 7795737257546773292300637013278720
def positiveArguments : Array ℕ := #[
    2303, 147, 217, 665, 1967, 4389,
    217, 2191, 4459, 217, 665, 217,
    257, 1025, 509, 1025, 5, 5,
    5, 5, 527, 12767, 9673, 5389,
    527, 5389, 10761, 527, 12767, 527,
    3459, 10377, 21907, 56497, 47273, 1322491,
    40355, 47273, 42661, 21907, 21907, 42661,
    1322491, 42661, 3459, 56497, 597, 8955,
    15721, 597, 4975, 597, 15721, 31243,
    4975, 482177, 30845, 8955
  ]
def positiveCoefficients : Array ℕ := #[
    44546498601159855829573173248, 45494296443737725102542815232, 8394780891403984989159686144, 205807531531194470701979402240, 152189253579646437545411084288, 169791213513235438329133006848,
    8394780891403984989159686144, 169520414129641761393998823424, 172499207349172207680474841088, 8394780891403984989159686144, 205807531531194470701979402240, 8394780891403984989159686144,
    39768823762042841331134365696, 39652766883359836930362572800, 39381967499766159995228389376, 39652766883359836930362572800, 198070406285660843983859875840, 198070406285660843983859875840,
    198070406285660843983859875840, 198070406285660843983859875840, 81549300087924425608979808256, 1975597560194556246204639870976, 1496824250000935424887403577344, 1667814717927228575357845110784,
    81549300087924425608979808256, 1667814717927228575357845110784, 1665184095343747142273684471808, 81549300087924425608979808256, 1975597560194556246204639870976, 81549300087924425608979808256,
    1070508648972032592719017672704, 802881486729024444539263254528, 847486013769525802569222324224, 1092810912492283271733997207552, 14630284869284445433826574860288, 25580696257727528830181526470656,
    780579223208773765524283719680, 14630284869284445433826574860288, 825183750249275123554242789376, 847486013769525802569222324224, 847486013769525802569222324224, 825183750249275123554242789376,
    25580696257727528830181526470656, 825183750249275123554242789376, 1070508648972032592719017672704, 1092810912492283271733997207552, 184762550863343006028694290432, 2771438262950145090430414356480,
    4865413839401365825422282981376, 184762550863343006028694290432, 3079375847722383433811571507200, 184762550863343006028694290432, 4865413839401365825422282981376, 4834620080924141991084167266304,
    3079375847722383433811571507200, 74613276790313350601254377619456, 4773032563969694322407935836160, 2771438262950145090430414356480
  ]
def positiveScales : Array ℕ := #[
    11, 7, 7, 9, 10, 12,
    7, 11, 12, 7, 9, 7,
    8, 10, 8, 10, 2, 2,
    2, 2, 9, 13, 13, 12,
    9, 12, 13, 9, 13, 9,
    11, 13, 14, 15, 15, 20,
    15, 15, 15, 14, 14, 15,
    20, 15, 11, 15, 9, 13,
    13, 9, 12, 9, 13, 14,
    12, 18, 14, 13
  ]
def negativeArguments : Array ℕ := #[
    49, 7, 1, 5, 17, 1153
  ]
def negativeCoefficients : Array ℕ := #[
    3882179963198952542083653566464, 1109194275199700726309615304704, 158456325028528675187087900672, 792281625142643375935439503360, 10775030101939949912721977245696, 91350071378946781245356174737408
  ]
def negativeScales : Array ℕ := #[
    5, 2, 0, 2, 4, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11169298695792845, 7199672344836364, 7761551232426566, 9377210530388551, 10941781241718677, 12099676554859642,
    7761551232426566, 11097373768990222, 12122504484313904, 7761551232426566, 9377210530388551, 7761551232426566,
    8005624549193878, 10001408194392808, 8991521844801183, 10001408194392808, 2321928094887362, 2321928094887362,
    2321928094887362, 2321928094887362, 9041659151637214, 13640131938763582, 13239747683556921, 12395801871389745,
    9041659151637214, 12395801871389745, 13393524530678680, 9041659151637214, 13640131938763582, 9041659151637214,
    11756139298356988, 13341101799094083, 14419104311095356, 15785886641737035, 15528728802269812, 20334826473667596,
    15300459814596738, 15528728802269812, 15380630163280721, 14419104311095356, 14419104311095356, 15380630163280721,
    20334826473667596, 15380630163280721, 11756139298356988, 15785886641737035, 9221587121264804, 13128477716873323,
    13940405368173870, 9221587121264804, 12280480810318373, 9221587121264804, 13940405368173870, 14931245368967874,
    12280480810318373, 18879203309809847, 14912749025479300, 13128477716873323
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    5614709844123661, 2807354922807594, 0, 2321928094887363, 4087462841250340, 10171176797651772
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
noncomputable def positiveFloor : ℝ := 43925946503 / 1000000000000
noncomputable def negativeCeiling : ℝ := 12036232783 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 44546498601159855829573173248, coefficient := 44546498601159855829573173248 }, { argument := 45494296443737725102542815232, coefficient := 45494296443737725102542815232 }, { argument := 3882179963198952542083653566464, coefficient := (-3882179963198952542083653566464) }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 205807531531194470701979402240, coefficient := 205807531531194470701979402240 }, { argument := 152189253579646437545411084288, coefficient := 152189253579646437545411084288 }, { argument := 169791213513235438329133006848, coefficient := 169791213513235438329133006848 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 169520414129641761393998823424, coefficient := 169520414129641761393998823424 }, { argument := 172499207349172207680474841088, coefficient := 172499207349172207680474841088 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 205807531531194470701979402240, coefficient := 205807531531194470701979402240 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 81549300087924425608979808256, coefficient := 81549300087924425608979808256 }, { argument := 1975597560194556246204639870976, coefficient := 1975597560194556246204639870976 }, { argument := 1496824250000935424887403577344, coefficient := 1496824250000935424887403577344 }, { argument := 1667814717927228575357845110784, coefficient := 1667814717927228575357845110784 }, { argument := 81549300087924425608979808256, coefficient := 81549300087924425608979808256 }, { argument := 1667814717927228575357845110784, coefficient := 1667814717927228575357845110784 }, { argument := 1665184095343747142273684471808, coefficient := 1665184095343747142273684471808 }, { argument := 81549300087924425608979808256, coefficient := 81549300087924425608979808256 }, { argument := 1975597560194556246204639870976, coefficient := 1975597560194556246204639870976 }, { argument := 81549300087924425608979808256, coefficient := 81549300087924425608979808256 }, { argument := 10775030101939949912721977245696, coefficient := (-10775030101939949912721977245696) }, { argument := 1070508648972032592719017672704, coefficient := 1070508648972032592719017672704 }, { argument := 802881486729024444539263254528, coefficient := 802881486729024444539263254528 }, { argument := 847486013769525802569222324224, coefficient := 847486013769525802569222324224 }, { argument := 1092810912492283271733997207552, coefficient := 1092810912492283271733997207552 }, { argument := 14630284869284445433826574860288, coefficient := 14630284869284445433826574860288 }, { argument := 25580696257727528830181526470656, coefficient := 25580696257727528830181526470656 }, { argument := 780579223208773765524283719680, coefficient := 780579223208773765524283719680 }, { argument := 14630284869284445433826574860288, coefficient := 14630284869284445433826574860288 }, { argument := 825183750249275123554242789376, coefficient := 825183750249275123554242789376 }, { argument := 847486013769525802569222324224, coefficient := 847486013769525802569222324224 }, { argument := 847486013769525802569222324224, coefficient := 847486013769525802569222324224 }, { argument := 825183750249275123554242789376, coefficient := 825183750249275123554242789376 }, { argument := 25580696257727528830181526470656, coefficient := 25580696257727528830181526470656 }, { argument := 825183750249275123554242789376, coefficient := 825183750249275123554242789376 }, { argument := 1070508648972032592719017672704, coefficient := 1070508648972032592719017672704 }, { argument := 1092810912492283271733997207552, coefficient := 1092810912492283271733997207552 }, { argument := 91350071378946781245356174737408, coefficient := (-91350071378946781245356174737408) }, { argument := 184762550863343006028694290432, coefficient := 184762550863343006028694290432 }, { argument := 2771438262950145090430414356480, coefficient := 2771438262950145090430414356480 }, { argument := 4865413839401365825422282981376, coefficient := 4865413839401365825422282981376 }, { argument := 184762550863343006028694290432, coefficient := 184762550863343006028694290432 }, { argument := 3079375847722383433811571507200, coefficient := 3079375847722383433811571507200 }, { argument := 184762550863343006028694290432, coefficient := 184762550863343006028694290432 }, { argument := 4865413839401365825422282981376, coefficient := 4865413839401365825422282981376 }, { argument := 4834620080924141991084167266304, coefficient := 4834620080924141991084167266304 }, { argument := 3079375847722383433811571507200, coefficient := 3079375847722383433811571507200 }, { argument := 74613276790313350601254377619456, coefficient := 74613276790313350601254377619456 }, { argument := 4773032563969694322407935836160, coefficient := 4773032563969694322407935836160 }, { argument := 2771438262950145090430414356480, coefficient := 2771438262950145090430414356480 }] }

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


end Parent3

namespace Parent3

namespace TermShard13

/-! Directed signed-log shard 13.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-58572555720528518261015630917402624)
def positiveArguments : Array ℕ := #[
    15721, 597, 30845, 597, 15721, 15721,
    597, 441, 2009, 49, 21021, 931,
    49, 931, 1813, 34251, 1813, 21021,
    34251, 441, 1813, 1813, 2009, 12582913,
    12582911, 767566573, 2810249751, 191870655, 472624955, 36962867277,
    18481433727, 945254463, 16940849, 2858349197, 230047634173, 22866830731,
    16940849, 77044153, 14040983111, 14040984247, 77043017, 38741107,
    1751027557, 4868485
  ]
def positiveCoefficients : Array ℕ := #[
    4865413839401365825422282981376, 184762550863343006028694290432, 4773032563969694322407935836160, 184762550863343006028694290432, 4865413839401365825422282981376, 4865413839401365825422282981376,
    184762550863343006028694290432, 34120722332803293826907111424, 38859711545692640191755321344, 30329530962491816735028543488, 406605274465905918103976411136, 36016318017959032372846395392,
    30329530962491816735028543488, 36016318017959032372846395392, 35068520175381163099876753408, 1325021383923861243611559493632, 35068520175381163099876753408, 406605274465905918103976411136,
    1325021383923861243611559493632, 34120722332803293826907111424, 35068520175381163099876753408, 35068520175381163099876753408, 38859711545692640191755321344, 475369012864517888518425411584,
    475368937306654162604101992448, 3624730657706316782402491383808, 13271029232615166227247525789696, 3624334200872980427077865963520, 4463816492919548679978074767360, 174552205539663990125923550625792,
    174552206375522857593850753449984, 4463837993854145185472732725248, 640007180071645969990373343232, 107985379554001317217942840016896, 1086369237082032813366637817233408, 107985555013527988239610754891776,
    640007180071645969990373343232, 727661451656561649799424638976, 132613336059850318520135043776512, 132613346789066967599968969293824, 727650722439912569965499121664, 182949705206066592275834601472,
    8268993845757917207994849820672, 183926163090828997425606164480
  ]
def positiveScales : Array ℕ := #[
    13, 9, 14, 9, 13, 13,
    9, 8, 10, 5, 14, 9,
    5, 9, 10, 15, 10, 14,
    15, 8, 10, 10, 10, 23,
    23, 29, 31, 27, 28, 35,
    34, 29, 24, 31, 37, 34,
    24, 26, 33, 33, 26, 25,
    30, 22
  ]
def negativeArguments : Array ℕ := #[
    199, 49, 3, 259, 4519, 8227,
    1683, 109
  ]
def negativeCoefficients : Array ℕ := #[
    126131234722708825448921968934912, 3882179963198952542083653566464, 950737950171172051122527404032, 20520094091194463436727883137024, 358032066401960541585225111568384, 1303620186009705410764172158828544,
    266681995023013760339868936830976, 8635869714054812797696290586624
  ]
def negativeScales : Array ℕ := #[
    7, 5, 1, 8, 12, 13,
    10, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13940405368173870, 9221587121264804, 14912749025479300, 9221587121264804, 13940405368173870, 13940405368173870,
    9221587121264804, 8784634845528344, 10972261847801237, 5614709844114682, 14359543681614753, 9862637357422660,
    5614709844114682, 9862637357422660, 10824163209679199, 15063858489490644, 10824163209679199, 14359543681614753,
    15063858489490644, 8784634845528344, 10824163209679199, 10824163209679199, 10972261847801237, 23584962615376020,
    23584962386065819, 29515716643616531, 31388051204545573, 27515558839453068, 28816120565892828, 35105357622452879,
    34105357629361353, 29816127514927813, 24014002842151850, 31412535031443750, 37743141663483205, 34412537375597972,
    24014002842151850, 26199182136746727, 33708924901583881, 33708925018306584, 26199160864351803, 25207361842742082,
    30705554642512410, 22215041466266767
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    7636624620558753, 5614709844123661, 1584962500724866, 8016808287686554, 12141787841671004, 13006150728170311,
    10716819461436938, 6768184325109843
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
noncomputable def positiveFloor : ℝ := 106387760331 / 125000000000
noncomputable def negativeCeiling : ℝ := 305376519977 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4865413839401365825422282981376, coefficient := 4865413839401365825422282981376 }, { argument := 184762550863343006028694290432, coefficient := 184762550863343006028694290432 }, { argument := 4773032563969694322407935836160, coefficient := 4773032563969694322407935836160 }, { argument := 184762550863343006028694290432, coefficient := 184762550863343006028694290432 }, { argument := 4865413839401365825422282981376, coefficient := 4865413839401365825422282981376 }, { argument := 4865413839401365825422282981376, coefficient := 4865413839401365825422282981376 }, { argument := 184762550863343006028694290432, coefficient := 184762550863343006028694290432 }, { argument := 126131234722708825448921968934912, coefficient := (-126131234722708825448921968934912) }, { argument := 34120722332803293826907111424, coefficient := 34120722332803293826907111424 }, { argument := 38859711545692640191755321344, coefficient := 38859711545692640191755321344 }, { argument := 30329530962491816735028543488, coefficient := 30329530962491816735028543488 }, { argument := 406605274465905918103976411136, coefficient := 406605274465905918103976411136 }, { argument := 36016318017959032372846395392, coefficient := 36016318017959032372846395392 }, { argument := 30329530962491816735028543488, coefficient := 30329530962491816735028543488 }, { argument := 36016318017959032372846395392, coefficient := 36016318017959032372846395392 }, { argument := 35068520175381163099876753408, coefficient := 35068520175381163099876753408 }, { argument := 1325021383923861243611559493632, coefficient := 1325021383923861243611559493632 }, { argument := 35068520175381163099876753408, coefficient := 35068520175381163099876753408 }, { argument := 406605274465905918103976411136, coefficient := 406605274465905918103976411136 }, { argument := 1325021383923861243611559493632, coefficient := 1325021383923861243611559493632 }, { argument := 34120722332803293826907111424, coefficient := 34120722332803293826907111424 }, { argument := 35068520175381163099876753408, coefficient := 35068520175381163099876753408 }, { argument := 35068520175381163099876753408, coefficient := 35068520175381163099876753408 }, { argument := 38859711545692640191755321344, coefficient := 38859711545692640191755321344 }, { argument := 3882179963198952542083653566464, coefficient := (-3882179963198952542083653566464) }, { argument := 475369012864517888518425411584, coefficient := 475369012864517888518425411584 }, { argument := 475368937306654162604101992448, coefficient := 475368937306654162604101992448 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 3624730657706316782402491383808, coefficient := 3624730657706316782402491383808 }, { argument := 13271029232615166227247525789696, coefficient := 13271029232615166227247525789696 }, { argument := 3624334200872980427077865963520, coefficient := 3624334200872980427077865963520 }, { argument := 20520094091194463436727883137024, coefficient := (-20520094091194463436727883137024) }, { argument := 4463816492919548679978074767360, coefficient := 4463816492919548679978074767360 }, { argument := 174552205539663990125923550625792, coefficient := 174552205539663990125923550625792 }, { argument := 174552206375522857593850753449984, coefficient := 174552206375522857593850753449984 }, { argument := 4463837993854145185472732725248, coefficient := 4463837993854145185472732725248 }, { argument := 358032066401960541585225111568384, coefficient := (-358032066401960541585225111568384) }, { argument := 640007180071645969990373343232, coefficient := 640007180071645969990373343232 }, { argument := 107985379554001317217942840016896, coefficient := 107985379554001317217942840016896 }, { argument := 1086369237082032813366637817233408, coefficient := 1086369237082032813366637817233408 }, { argument := 107985555013527988239610754891776, coefficient := 107985555013527988239610754891776 }, { argument := 640007180071645969990373343232, coefficient := 640007180071645969990373343232 }, { argument := 1303620186009705410764172158828544, coefficient := (-1303620186009705410764172158828544) }, { argument := 727661451656561649799424638976, coefficient := 727661451656561649799424638976 }, { argument := 132613336059850318520135043776512, coefficient := 132613336059850318520135043776512 }, { argument := 132613346789066967599968969293824, coefficient := 132613346789066967599968969293824 }, { argument := 727650722439912569965499121664, coefficient := 727650722439912569965499121664 }, { argument := 266681995023013760339868936830976, coefficient := (-266681995023013760339868936830976) }, { argument := 182949705206066592275834601472, coefficient := 182949705206066592275834601472 }, { argument := 8268993845757917207994849820672, coefficient := 8268993845757917207994849820672 }, { argument := 183926163090828997425606164480, coefficient := 183926163090828997425606164480 }, { argument := 8635869714054812797696290586624, coefficient := (-8635869714054812797696290586624) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
