import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 4, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4

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
def constantNumerator : ℤ := (-5870971360053932758849414559170560)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1313631595, 13691762425, 1313631595, 17788465, 19942673919, 722729103873,
    5781834955785, 159539266551, 130363788357, 220949017531, 130363788357, 11025915159,
    399582814953, 3196663694385, 88206146511, 2035169715051, 3449337846933, 2035169715051,
    36275, 36275, 2491027803, 4221955749, 2491027803, 9875,
    9875, 22614966684699, 3186654191, 340797467334737, 78852740939, 2508642661,
    340797626341079, 1288221907, 1288221907, 43596141379, 2373040355, 78852740939,
    43596141379, 22614785228181, 2508642661, 2373040355, 3186654191, 258492428382489,
    1313631595, 428658731, 7098646131279987, 4328070413, 2067939111784133, 8669968527,
    3885583981, 1313631595, 428658731, 40817762109915, 1054905045, 40802036727333,
    532633785, 127042417953, 215319743199, 127042417953, 36275, 36275,
    875, 875, 5804657, 428658731
  ]
def negativeCoefficients : Array ℕ := #[
    48464451680207751712121815040, 505136874744015738359093657600, 48464451680207751712121815040, 328139261319139779086909440, 183938700964617644296793751552, 6665999406883338849156159504384,
    6666001856612104759289220956160, 183936251235851734163732299776, 601196860075203998689397833728, 2037894989865961038102866690048, 601196860075203998689397833728, 101696117558253779262973673472,
    3685500961845216577822365057024, 3685502316252436251266525429760, 101694763151034105818813300736, 9385563720027547775717924143104, 31814526243066691110765135396864, 9385563720027547775717924143104,
    701660545704330772999464550400, 701660545704330772999464550400, 367610818899487795376956637184, 1246101395077275539222135046144, 367610818899487795376956637184, 191010279499111409603575808000,
    191010279499111409603575808000, 50924377767103298852043620352, 7347924289098869446732152832, 1534815346897530335800749719552, 181822041451531599288287100928, 5784536142482088713384886272,
    1534816062998432916546397405184, 5940874957143766786719612928, 5940874957143766786719612928, 100525857827459001154229239808, 5471858513158732566715432960, 181822041451531599288287100928,
    100525857827459001154229239808, 50923969163349874478193573888, 5784536142482088713384886272, 5471858513158732566715432960, 7347924289098869446732152832, 1164146404141472084477601644544,
    48464451680207751712121815040, 1976839476429526714573389824, 3996182508958445310352444882944, 39919403620802700752352968704, 1164146226656986981559745642496, 39983172636171395162500497408,
    35838186637206258502911131648, 48464451680207751712121815040, 1976839476429526714573389824, 183826858228310744592380067840, 9729781693590028932203151360, 183756037401174190904120967168,
    9825359116906237467882946560, 585879742621058673882024640512, 1985974098404407890635277729792, 585879742621058673882024640512, 701660545704330772999464550400, 701660545704330772999464550400,
    16924961474604808445886464000, 16924961474604808445886464000, 13384627764333333094334464, 1976839476429526714573389824
  ]
def negativeScales : Array ℕ := #[
    30, 33, 30, 24, 34, 39,
    42, 37, 36, 37, 36, 33,
    38, 41, 36, 40, 41, 40,
    15, 15, 31, 31, 31, 13,
    13, 44, 31, 48, 36, 31,
    48, 30, 30, 35, 31, 36,
    35, 44, 31, 31, 31, 47,
    30, 28, 52, 32, 50, 33,
    31, 30, 28, 45, 29, 45,
    28, 36, 37, 36, 15, 15,
    9, 9, 22, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30290913585820016, 33672589113414427, 30290913585820016, 24084438687327386, 34215139808512047, 39394664035703225,
    42394664565887925, 37215120594311563, 36923752232760217, 37684922559851906, 36923752232760217, 33360179354366777,
    38539703581558919, 41539704111743619, 36360160140166294, 40888286249624737, 41649456579797569, 40888286249624737,
    15146687993841470, 15146687993841470, 31214093977944126, 31975264327502248, 31214093977944126, 13269565032839191,
    13269565032839191, 44362343104196394, 31569395323371720, 48275907942516191, 36198441853164933, 31224259837320665,
    48275908615636238, 30262733985135300, 30262733985135300, 35343481399019663, 31144089488636681, 36198441853164933,
    35343481399019663, 44362331528346093, 31224259837320665, 31144089488636681, 31569395323371720, 47877115353836360,
    30290913585820016, 28675254287915937, 52656465320356002, 32011076824421686, 50877115133884626, 33013379610291107,
    31855484299632569, 30290913585820016, 28675254287915937, 45214262320329859, 29974466013348606, 45213706402964929,
    28988568720510175, 36886519323338630, 37647689653622455, 36886519323338630, 15146687993841470, 15146687993841470,
    9773139207089529, 9773139207089529, 22468779389383406, 28675254287915937
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
noncomputable def negativeCeiling : ℝ := 926112969 / 20000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 48464451680207751712121815040, coefficient := (-48464451680207751712121815040) }, { argument := 505136874744015738359093657600, coefficient := (-505136874744015738359093657600) }, { argument := 48464451680207751712121815040, coefficient := (-48464451680207751712121815040) }, { argument := 328139261319139779086909440, coefficient := (-328139261319139779086909440) }, { argument := 183938700964617644296793751552, coefficient := (-183938700964617644296793751552) }, { argument := 6665999406883338849156159504384, coefficient := (-6665999406883338849156159504384) }, { argument := 6666001856612104759289220956160, coefficient := (-6666001856612104759289220956160) }, { argument := 183936251235851734163732299776, coefficient := (-183936251235851734163732299776) }, { argument := 601196860075203998689397833728, coefficient := (-601196860075203998689397833728) }, { argument := 2037894989865961038102866690048, coefficient := (-2037894989865961038102866690048) }, { argument := 601196860075203998689397833728, coefficient := (-601196860075203998689397833728) }, { argument := 101696117558253779262973673472, coefficient := (-101696117558253779262973673472) }, { argument := 3685500961845216577822365057024, coefficient := (-3685500961845216577822365057024) }, { argument := 3685502316252436251266525429760, coefficient := (-3685502316252436251266525429760) }, { argument := 101694763151034105818813300736, coefficient := (-101694763151034105818813300736) }, { argument := 9385563720027547775717924143104, coefficient := (-9385563720027547775717924143104) }, { argument := 31814526243066691110765135396864, coefficient := (-31814526243066691110765135396864) }, { argument := 9385563720027547775717924143104, coefficient := (-9385563720027547775717924143104) }, { argument := 701660545704330772999464550400, coefficient := (-701660545704330772999464550400) }, { argument := 701660545704330772999464550400, coefficient := (-701660545704330772999464550400) }, { argument := 367610818899487795376956637184, coefficient := (-367610818899487795376956637184) }, { argument := 1246101395077275539222135046144, coefficient := (-1246101395077275539222135046144) }, { argument := 367610818899487795376956637184, coefficient := (-367610818899487795376956637184) }, { argument := 191010279499111409603575808000, coefficient := (-191010279499111409603575808000) }, { argument := 191010279499111409603575808000, coefficient := (-191010279499111409603575808000) }, { argument := 50924377767103298852043620352, coefficient := (-50924377767103298852043620352) }, { argument := 7347924289098869446732152832, coefficient := (-7347924289098869446732152832) }, { argument := 1534815346897530335800749719552, coefficient := (-1534815346897530335800749719552) }, { argument := 181822041451531599288287100928, coefficient := (-181822041451531599288287100928) }, { argument := 5784536142482088713384886272, coefficient := (-5784536142482088713384886272) }, { argument := 1534816062998432916546397405184, coefficient := (-1534816062998432916546397405184) }, { argument := 5940874957143766786719612928, coefficient := (-5940874957143766786719612928) }, { argument := 5940874957143766786719612928, coefficient := (-5940874957143766786719612928) }, { argument := 100525857827459001154229239808, coefficient := (-100525857827459001154229239808) }, { argument := 5471858513158732566715432960, coefficient := (-5471858513158732566715432960) }, { argument := 181822041451531599288287100928, coefficient := (-181822041451531599288287100928) }, { argument := 100525857827459001154229239808, coefficient := (-100525857827459001154229239808) }, { argument := 50923969163349874478193573888, coefficient := (-50923969163349874478193573888) }, { argument := 5784536142482088713384886272, coefficient := (-5784536142482088713384886272) }, { argument := 5471858513158732566715432960, coefficient := (-5471858513158732566715432960) }, { argument := 7347924289098869446732152832, coefficient := (-7347924289098869446732152832) }, { argument := 1164146404141472084477601644544, coefficient := (-1164146404141472084477601644544) }, { argument := 48464451680207751712121815040, coefficient := (-48464451680207751712121815040) }, { argument := 1976839476429526714573389824, coefficient := (-1976839476429526714573389824) }, { argument := 3996182508958445310352444882944, coefficient := (-3996182508958445310352444882944) }, { argument := 39919403620802700752352968704, coefficient := (-39919403620802700752352968704) }, { argument := 1164146226656986981559745642496, coefficient := (-1164146226656986981559745642496) }, { argument := 39983172636171395162500497408, coefficient := (-39983172636171395162500497408) }, { argument := 35838186637206258502911131648, coefficient := (-35838186637206258502911131648) }, { argument := 48464451680207751712121815040, coefficient := (-48464451680207751712121815040) }, { argument := 1976839476429526714573389824, coefficient := (-1976839476429526714573389824) }, { argument := 183826858228310744592380067840, coefficient := (-183826858228310744592380067840) }, { argument := 9729781693590028932203151360, coefficient := (-9729781693590028932203151360) }, { argument := 183756037401174190904120967168, coefficient := (-183756037401174190904120967168) }, { argument := 9825359116906237467882946560, coefficient := (-9825359116906237467882946560) }, { argument := 585879742621058673882024640512, coefficient := (-585879742621058673882024640512) }, { argument := 1985974098404407890635277729792, coefficient := (-1985974098404407890635277729792) }, { argument := 585879742621058673882024640512, coefficient := (-585879742621058673882024640512) }, { argument := 701660545704330772999464550400, coefficient := (-701660545704330772999464550400) }, { argument := 701660545704330772999464550400, coefficient := (-701660545704330772999464550400) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 13384627764333333094334464, coefficient := (-13384627764333333094334464) }, { argument := 1976839476429526714573389824, coefficient := (-1976839476429526714573389824) }] }

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
def constantNumerator : ℤ := 54755939747416940600540095972376576
def positiveArguments : Array ℕ := #[
    6851, 62392681, 509, 62388887, 257, 2406305971,
    3895
  ]
def positiveCoefficients : Array ℕ := #[
    542792141385224976853369603751936, 4714257688492443814420981743616, 39381967499766159995228389376, 4713971021957467695477929541632, 39768823762042841331134365696, 45453834659917985969473023115264,
    1205444113254139042683022213120
  ]
def positiveScales : Array ℕ := #[
    12, 25, 8, 25, 8, 31,
    11
  ]
def negativeArguments : Array ℕ := #[
    4467838265, 428658731, 5804657, 634461681, 22993101327, 183944878215,
    5075625849, 4151713005, 7036592915, 4151713005, 600166455, 21750230985,
    174001911825, 4801267695, 2491027803, 4221955749, 2491027803, 875,
    875, 4151713005, 7036592915, 4151713005, 375, 375,
    805937811, 29207453037, 233659710165, 6447416619, 63936380277, 108363530891,
    63936380277, 875, 875, 72239806287, 122436716721, 72239806287,
    9875, 9875, 375, 375, 12536559721141, 17788465,
    5804657, 341326576531623, 58608311, 100292471755185, 117403869, 52616407,
    17788465, 5804657, 4199304263205, 12545323, 4199116456411, 6334279,
    775, 775, 15
  ]
def negativeCoefficients : Array ℕ := #[
    20604267259295378801489346560, 1976839476429526714573389824, 13384627764333333094334464, 5851876126991275012021813248, 212073927820020238537212297216, 212074005756361028455461027840,
    5851798190650485093773082624, 19146396817681656009216491520, 64901114326941434334486200320, 19146396817681656009216491520, 5535558498505260146507120640, 200610472262181306724390010880,
    200610545985746918809219891200, 5535484774939648061677240320, 367610818899487795376956637184, 1246101395077275539222135046144, 367610818899487795376956637184, 16924961474604808445886464000,
    16924961474604808445886464000, 19146396817681656009216491520, 64901114326941434334486200320, 19146396817681656009216491520, 14507109835375550096474112000, 14507109835375550096474112000,
    7433464269421349339595276288, 269391205609214897601323728896, 269391304609431576686666711040, 7433365269204670254252294144, 589709021984595005083867938816, 1998954321269796177502174969856,
    589709021984595005083867938816, 16924961474604808445886464000, 16924961474604808445886464000, 333147304627660814560366952448, 1129279389288780957420059885568, 333147304627660814560366952448,
    191010279499111409603575808000, 191010279499111409603575808000, 14507109835375550096474112000, 14507109835375550096474112000, 28229822844319288422425427968, 328139261319139779086909440,
    13384627764333333094334464, 96074890179966526737705074688, 270283128402344081195270144, 28229821151544822558212751360, 270714890588290317746700288, 242650348501784941903740928,
    328139261319139779086909440, 13384627764333333094334464, 18911985114985373256835399680, 115710181351511066603945984, 18911139308377897209331449856, 116846823604472864900644864,
    14990680163221401766356582400, 14990680163221401766356582400, 9507379501711720511225274040320
  ]
def negativeScales : Array ℕ := #[
    32, 28, 22, 29, 34, 37,
    32, 31, 32, 31, 29, 34,
    37, 32, 31, 31, 31, 9,
    9, 31, 32, 31, 8, 8,
    29, 34, 37, 32, 35, 36,
    35, 9, 9, 36, 36, 36,
    13, 13, 8, 8, 43, 24,
    22, 48, 25, 46, 26, 25,
    24, 22, 41, 23, 41, 22,
    9, 9, 3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12742098869766579, 25894873467022404, 8991521844801183, 25894785736357527, 8005624549193878, 31164172952351815,
    11927407612511617
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32056929815432888, 28675254287915937, 22468779389383406, 29240957792667778, 34420482019858966, 37420482550043666,
    32240938578467295, 31951059582722450, 32712229905893342, 31951059582722450, 29160787443983795, 34340311671174969,
    37340312201359668, 32160768229783312, 31214093977944126, 31975264327502248, 31214093977944126, 9773139207089529,
    9773139207089529, 31951059582722450, 32712229905893342, 31951059582722450, 8550746785384604, 8550746785384604,
    29586093278720296, 34765617506222812, 37765618036407515, 32586074064519810, 35895918021976525, 36657088351630108,
    35895918021976525, 9773139207089529, 9773139207089529, 36072074973071698, 36833245308012083, 36072074973071698,
    13269565032839191, 13269565032839191, 8550746785384604, 8550746785384604, 43511206732059083, 24084438687327386,
    22468779389383406, 48278146079038120, 25804601926638430, 46511206645549245, 26806904712541679, 25649009399238140,
    24084438687327386, 22468779389383406, 41933287469814877, 23580646279999710, 41933222946263128, 22594748983119500,
    9598052500166958, 9598052500166958, 3906890600547867
  ]

abbrev PositiveTerm := Fin 7
abbrev NegativeTerm := Fin 57
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
noncomputable def positiveFloor : ℝ := 25855714747 / 250000000000
noncomputable def negativeCeiling : ℝ := 1065969979 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 20604267259295378801489346560, coefficient := (-20604267259295378801489346560) }, { argument := 1976839476429526714573389824, coefficient := (-1976839476429526714573389824) }, { argument := 13384627764333333094334464, coefficient := (-13384627764333333094334464) }, { argument := 5851876126991275012021813248, coefficient := (-5851876126991275012021813248) }, { argument := 212073927820020238537212297216, coefficient := (-212073927820020238537212297216) }, { argument := 212074005756361028455461027840, coefficient := (-212074005756361028455461027840) }, { argument := 5851798190650485093773082624, coefficient := (-5851798190650485093773082624) }, { argument := 19146396817681656009216491520, coefficient := (-19146396817681656009216491520) }, { argument := 64901114326941434334486200320, coefficient := (-64901114326941434334486200320) }, { argument := 19146396817681656009216491520, coefficient := (-19146396817681656009216491520) }, { argument := 5535558498505260146507120640, coefficient := (-5535558498505260146507120640) }, { argument := 200610472262181306724390010880, coefficient := (-200610472262181306724390010880) }, { argument := 200610545985746918809219891200, coefficient := (-200610545985746918809219891200) }, { argument := 5535484774939648061677240320, coefficient := (-5535484774939648061677240320) }, { argument := 367610818899487795376956637184, coefficient := (-367610818899487795376956637184) }, { argument := 1246101395077275539222135046144, coefficient := (-1246101395077275539222135046144) }, { argument := 367610818899487795376956637184, coefficient := (-367610818899487795376956637184) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 19146396817681656009216491520, coefficient := (-19146396817681656009216491520) }, { argument := 64901114326941434334486200320, coefficient := (-64901114326941434334486200320) }, { argument := 19146396817681656009216491520, coefficient := (-19146396817681656009216491520) }, { argument := 14507109835375550096474112000, coefficient := (-14507109835375550096474112000) }, { argument := 14507109835375550096474112000, coefficient := (-14507109835375550096474112000) }, { argument := 7433464269421349339595276288, coefficient := (-7433464269421349339595276288) }, { argument := 269391205609214897601323728896, coefficient := (-269391205609214897601323728896) }, { argument := 269391304609431576686666711040, coefficient := (-269391304609431576686666711040) }, { argument := 7433365269204670254252294144, coefficient := (-7433365269204670254252294144) }, { argument := 589709021984595005083867938816, coefficient := (-589709021984595005083867938816) }, { argument := 1998954321269796177502174969856, coefficient := (-1998954321269796177502174969856) }, { argument := 589709021984595005083867938816, coefficient := (-589709021984595005083867938816) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 333147304627660814560366952448, coefficient := (-333147304627660814560366952448) }, { argument := 1129279389288780957420059885568, coefficient := (-1129279389288780957420059885568) }, { argument := 333147304627660814560366952448, coefficient := (-333147304627660814560366952448) }, { argument := 191010279499111409603575808000, coefficient := (-191010279499111409603575808000) }, { argument := 191010279499111409603575808000, coefficient := (-191010279499111409603575808000) }, { argument := 14507109835375550096474112000, coefficient := (-14507109835375550096474112000) }, { argument := 14507109835375550096474112000, coefficient := (-14507109835375550096474112000) }, { argument := 28229822844319288422425427968, coefficient := (-28229822844319288422425427968) }, { argument := 328139261319139779086909440, coefficient := (-328139261319139779086909440) }, { argument := 13384627764333333094334464, coefficient := (-13384627764333333094334464) }, { argument := 96074890179966526737705074688, coefficient := (-96074890179966526737705074688) }, { argument := 270283128402344081195270144, coefficient := (-270283128402344081195270144) }, { argument := 28229821151544822558212751360, coefficient := (-28229821151544822558212751360) }, { argument := 270714890588290317746700288, coefficient := (-270714890588290317746700288) }, { argument := 242650348501784941903740928, coefficient := (-242650348501784941903740928) }, { argument := 328139261319139779086909440, coefficient := (-328139261319139779086909440) }, { argument := 13384627764333333094334464, coefficient := (-13384627764333333094334464) }, { argument := 18911985114985373256835399680, coefficient := (-18911985114985373256835399680) }, { argument := 115710181351511066603945984, coefficient := (-115710181351511066603945984) }, { argument := 18911139308377897209331449856, coefficient := (-18911139308377897209331449856) }, { argument := 116846823604472864900644864, coefficient := (-116846823604472864900644864) }, { argument := 14990680163221401766356582400, coefficient := (-14990680163221401766356582400) }, { argument := 14990680163221401766356582400, coefficient := (-14990680163221401766356582400) }, { argument := 542792141385224976853369603751936, coefficient := 542792141385224976853369603751936 }, { argument := 4714257688492443814420981743616, coefficient := 4714257688492443814420981743616 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 4713971021957467695477929541632, coefficient := 4713971021957467695477929541632 }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 9507379501711720511225274040320, coefficient := (-9507379501711720511225274040320) }, { argument := 45453834659917985969473023115264, coefficient := 45453834659917985969473023115264 }, { argument := 1205444113254139042683022213120, coefficient := 1205444113254139042683022213120 }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
