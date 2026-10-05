import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 7, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 108656920774717368098279556202364928
def positiveArguments : Array ℕ := #[
    7177, 4401, 4815, 4401, 4815, 501,
    83667, 2171, 90013, 134769, 4175, 134769,
    140447, 83667, 4175, 27931, 31535, 13515,
    355895, 31535, 13515, 31535, 31535, 1307351,
    8109, 355895, 1307351, 27931, 31535, 8109,
    31535, 3525, 102225, 90475, 5875, 3525,
    5875
  ]
def positiveCoefficients : Array ℕ := #[
    1137241044729750301817729863122944, 170255441027967455932220178432, 186271290286222063238727598080, 170255441027967455932220178432, 186271290286222063238727598080, 77525994960246939715557654528,
    1618355144795154866562266038272, 83986494540267518025187459072, 1741104636815545854445232324608, 2606811580538303347935626133504, 80756244750257228870372556800, 2606811580538303347935626133504,
    2716640073398653179199332810752, 1618355144795154866562266038272, 80756244750257228870372556800, 1080528226164998639318982459392, 1219951223089514592779496325120, 1045672476933869650953853992960,
    13768020946295950404225744240640, 1219951223089514592779496325120, 1045672476933869650953853992960, 1219951223089514592779496325120, 1219951223089514592779496325120, 50575692134368162117801404792832,
    1254806972320643581144624791552, 13768020946295950404225744240640, 50575692134368162117801404792832, 1080528226164998639318982459392, 1219951223089514592779496325120, 1254806972320643581144624791552,
    1219951223089514592779496325120, 136366832452530170906856652800, 1977319070561687478149421465600, 3500082032948274386609320755200, 113639027043775142422380544000, 2181869319240482734509706444800,
    113639027043775142422380544000
  ]
def positiveScales : Array ℕ := #[
    12, 12, 12, 12, 12, 8,
    16, 11, 16, 17, 12, 17,
    17, 16, 12, 14, 14, 13,
    18, 14, 13, 14, 14, 20,
    12, 18, 20, 14, 14, 12,
    14, 11, 16, 16, 12, 11,
    12
  ]
def negativeArguments : Array ℕ := #[
    44218660815, 743814243, 193600660953, 193600707111, 437, 6165626145,
    6165627615, 851, 46291519435, 171961458725, 2892610945, 188668160037,
    188668205019, 851, 6165626145, 6165627615, 26749, 851,
    77000465525733, 2062425, 77000490931227, 2062425, 4685747, 69,
    9, 167, 901
  ]
def negativeCoefficients : Array ℕ := #[
    407845159668237010866819563520, 109767607832008050696995733504, 892825461275251235851717312512, 892825674141454474423088185344, 16905618661490974379091165184, 28433931887746854644959150080,
    28433938666925301733219368960, 16460733959872790842799292416, 106740976475074597647149957120, 396516127455230427231630131200, 106718507614452271510968074240, 870078315765053752135749992448,
    870078523207914233036512690176, 16460733959872790842799292416, 909885820407899348638692802560, 909886037341609655463019806720, 517400907981947452707448029184, 16460733959872790842799292416,
    43347408481130732772126621696, 76090052292440843983257600, 43347422783152396717548109824, 76090052292440843983257600, 22127814580006991451140390912, 21354465677672809742009892864,
    713053462628379038341895553024, 13231103139882144378121839706112, 142769148850704336343566198505472
  ]
def negativeScales : Array ℕ := #[
    35, 29, 37, 37, 8, 32,
    32, 9, 35, 37, 31, 37,
    37, 9, 32, 32, 14, 9,
    46, 20, 46, 20, 22, 6,
    3, 7, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12809165205323695, 12103615656394545, 12233320082730821, 12103615656394545, 12233320082730821, 8968666792316714,
    16352371085669260, 11084144010615144, 16457845755226553, 17040129155751832, 12027560482248776, 17040129155751832,
    17099666282729196, 16352371085669260, 12027560482248776, 14769579606179150, 14944666312170518, 13722273891414535,
    18441092138878001, 14944666312170518, 13722273891414535, 14944666312170518, 14944666312170518, 20318215099880282,
    12985308296102858, 18441092138878001, 20318215099880282, 14769579606179150, 14944666312170518, 12985308296102858,
    14944666312170518, 11783407542145078, 16641388537300027, 16465231582147257, 12520373136339691, 11783407542145078,
    12520373136339691
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    35363936281924318, 29470367132900915, 37494292921745554, 37494293265710856, 8771489469857739, 32521600267741615,
    32521600611706917, 9733015321840403, 35430028866123530, 37323294297426971, 31429725148403493, 37457060015546416,
    37457060359511718, 9733015321840403, 32521600267741615, 32521600611706917, 14707197337615895, 9733015321840403,
    46129932401546318, 20975910242131222, 46129932877548299, 20975910242131222, 22159847629436654, 6108524456778170,
    3169925001442313, 7383704292474056, 9815383296694715
  ]

abbrev PositiveTerm := Fin 37
abbrev NegativeTerm := Fin 27
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
noncomputable def positiveFloor : ℝ := 212845778231 / 1000000000000
noncomputable def negativeCeiling : ℝ := 21027638073 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 407845159668237010866819563520, coefficient := (-407845159668237010866819563520) }, { argument := 109767607832008050696995733504, coefficient := (-109767607832008050696995733504) }, { argument := 892825461275251235851717312512, coefficient := (-892825461275251235851717312512) }, { argument := 892825674141454474423088185344, coefficient := (-892825674141454474423088185344) }, { argument := 16905618661490974379091165184, coefficient := (-16905618661490974379091165184) }, { argument := 28433931887746854644959150080, coefficient := (-28433931887746854644959150080) }, { argument := 28433938666925301733219368960, coefficient := (-28433938666925301733219368960) }, { argument := 16460733959872790842799292416, coefficient := (-16460733959872790842799292416) }, { argument := 106740976475074597647149957120, coefficient := (-106740976475074597647149957120) }, { argument := 396516127455230427231630131200, coefficient := (-396516127455230427231630131200) }, { argument := 106718507614452271510968074240, coefficient := (-106718507614452271510968074240) }, { argument := 870078315765053752135749992448, coefficient := (-870078315765053752135749992448) }, { argument := 870078523207914233036512690176, coefficient := (-870078523207914233036512690176) }, { argument := 16460733959872790842799292416, coefficient := (-16460733959872790842799292416) }, { argument := 909885820407899348638692802560, coefficient := (-909885820407899348638692802560) }, { argument := 909886037341609655463019806720, coefficient := (-909886037341609655463019806720) }, { argument := 517400907981947452707448029184, coefficient := (-517400907981947452707448029184) }, { argument := 16460733959872790842799292416, coefficient := (-16460733959872790842799292416) }, { argument := 43347408481130732772126621696, coefficient := (-43347408481130732772126621696) }, { argument := 76090052292440843983257600, coefficient := (-76090052292440843983257600) }, { argument := 43347422783152396717548109824, coefficient := (-43347422783152396717548109824) }, { argument := 76090052292440843983257600, coefficient := (-76090052292440843983257600) }, { argument := 22127814580006991451140390912, coefficient := (-22127814580006991451140390912) }, { argument := 21354465677672809742009892864, coefficient := (-21354465677672809742009892864) }, { argument := 1137241044729750301817729863122944, coefficient := 1137241044729750301817729863122944 }, { argument := 170255441027967455932220178432, coefficient := 170255441027967455932220178432 }, { argument := 186271290286222063238727598080, coefficient := 186271290286222063238727598080 }, { argument := 170255441027967455932220178432, coefficient := 170255441027967455932220178432 }, { argument := 186271290286222063238727598080, coefficient := 186271290286222063238727598080 }, { argument := 713053462628379038341895553024, coefficient := (-713053462628379038341895553024) }, { argument := 77525994960246939715557654528, coefficient := 77525994960246939715557654528 }, { argument := 1618355144795154866562266038272, coefficient := 1618355144795154866562266038272 }, { argument := 83986494540267518025187459072, coefficient := 83986494540267518025187459072 }, { argument := 1741104636815545854445232324608, coefficient := 1741104636815545854445232324608 }, { argument := 2606811580538303347935626133504, coefficient := 2606811580538303347935626133504 }, { argument := 80756244750257228870372556800, coefficient := 80756244750257228870372556800 }, { argument := 2606811580538303347935626133504, coefficient := 2606811580538303347935626133504 }, { argument := 2716640073398653179199332810752, coefficient := 2716640073398653179199332810752 }, { argument := 1618355144795154866562266038272, coefficient := 1618355144795154866562266038272 }, { argument := 80756244750257228870372556800, coefficient := 80756244750257228870372556800 }, { argument := 13231103139882144378121839706112, coefficient := (-13231103139882144378121839706112) }, { argument := 1080528226164998639318982459392, coefficient := 1080528226164998639318982459392 }, { argument := 1219951223089514592779496325120, coefficient := 1219951223089514592779496325120 }, { argument := 1045672476933869650953853992960, coefficient := 1045672476933869650953853992960 }, { argument := 13768020946295950404225744240640, coefficient := 13768020946295950404225744240640 }, { argument := 1219951223089514592779496325120, coefficient := 1219951223089514592779496325120 }, { argument := 1045672476933869650953853992960, coefficient := 1045672476933869650953853992960 }, { argument := 1219951223089514592779496325120, coefficient := 1219951223089514592779496325120 }, { argument := 1219951223089514592779496325120, coefficient := 1219951223089514592779496325120 }, { argument := 50575692134368162117801404792832, coefficient := 50575692134368162117801404792832 }, { argument := 1254806972320643581144624791552, coefficient := 1254806972320643581144624791552 }, { argument := 13768020946295950404225744240640, coefficient := 13768020946295950404225744240640 }, { argument := 50575692134368162117801404792832, coefficient := 50575692134368162117801404792832 }, { argument := 1080528226164998639318982459392, coefficient := 1080528226164998639318982459392 }, { argument := 1219951223089514592779496325120, coefficient := 1219951223089514592779496325120 }, { argument := 1254806972320643581144624791552, coefficient := 1254806972320643581144624791552 }, { argument := 1219951223089514592779496325120, coefficient := 1219951223089514592779496325120 }, { argument := 142769148850704336343566198505472, coefficient := (-142769148850704336343566198505472) }, { argument := 136366832452530170906856652800, coefficient := 136366832452530170906856652800 }, { argument := 1977319070561687478149421465600, coefficient := 1977319070561687478149421465600 }, { argument := 3500082032948274386609320755200, coefficient := 3500082032948274386609320755200 }, { argument := 113639027043775142422380544000, coefficient := 113639027043775142422380544000 }, { argument := 2181869319240482734509706444800, coefficient := 2181869319240482734509706444800 }, { argument := 113639027043775142422380544000, coefficient := 113639027043775142422380544000 }] }

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


end Parent1

namespace Parent1

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-49750190757494241391835127968956416)
def positiveArguments : Array ℕ := #[
    179775, 5875, 3525, 2879925, 184475, 102225,
    179775, 5875, 184475, 5875, 179775, 5875,
    3525, 1081, 805, 851, 69, 14789,
    26749, 805, 14789, 437, 437, 851,
    851, 26749, 851, 1081, 69, 29,
    2265972261, 2265973211, 35721830607, 129189614429, 8931820277, 2125429859,
    42239279357, 21119637905, 2125437791, 3923297, 169149983, 13971236551,
    1353200317, 3923297, 64493, 12518419, 50073677, 257971
  ]
def positiveCoefficients : Array ℕ := #[
    3477354227539519358124844646400, 3636448865400804557516177408000, 2181869319240482734509706444800, 55705851056858574815450942668800, 3568265449174539472062749081600, 1977319070561687478149421465600,
    3477354227539519358124844646400, 113639027043775142422380544000, 3568265449174539472062749081600, 113639027043775142422380544000, 3477354227539519358124844646400, 3636448865400804557516177408000,
    136366832452530170906856652800, 41819161952109252411436040192, 31141929113272847540431093760, 32921467919745581685598584832, 42708931355345619484019785728, 572121726280984027671348379648,
    1034801815963894905414896058368, 31141929113272847540431093760, 572121726280984027671348379648, 33811237322981948758182330368, 33811237322981948758182330368, 32921467919745581685598584832,
    32921467919745581685598584832, 1034801815963894905414896058368, 32921467919745581685598584832, 41819161952109252411436040192, 42708931355345619484019785728, 4595233425827331580425549119488,
    85606011651669981865172426293248, 85606047541655251674476050382848, 168691575565243833585836828393472, 610080705114362298625411550019584, 168717314828481081069943723655168, 10037058727831955941925914148864,
    398938714192128998393566612946944, 398938680691661168916303466987520, 10037096185642898063951749185536, 37054492510286060915915751424, 6390305682377362232901678137344, 65977299212685702577991761002496,
    6390307821609378972850959941632, 37054492510286060915915751424, 2436476652637696230135169024, 472932498432948329331128532992, 472932507877681295070418960384, 2436467207904730490844741632
  ]
def positiveScales : Array ℕ := #[
    17, 12, 11, 21, 17, 16,
    17, 12, 17, 12, 17, 12,
    11, 10, 9, 9, 6, 13,
    14, 9, 13, 8, 8, 9,
    9, 14, 9, 10, 6, 4,
    31, 31, 35, 36, 33, 30,
    35, 34, 30, 21, 27, 33,
    30, 21, 15, 23, 25, 17
  ]
def negativeArguments : Array ℕ := #[
    1175, 23, 29, 2161, 11959, 2581,
    995, 3
  ]
def negativeCoefficients : Array ℕ := #[
    93093090954260596672414141644800, 3644495475656159529303021715456, 4595233425827331580425549119488, 171212059193325233539648476676096, 947489595508087213281192102068224, 817951549797265021315747743268864,
    78832021701693015905576230584320, 950737950171172051122527404032
  ]
def negativeScales : Array ℕ := #[
    10, 4, 4, 11, 13, 11,
    9, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    17455832884145009, 12520373136339691, 11783407542145078, 21457599810319197, 17493065790343975, 16641388537300027,
    17455832884145009, 12520373136339691, 17493065790343975, 12520373136339691, 17455832884145009, 12520373136339691,
    11783407542145078, 10078150807734650, 9652844973000555, 9733015321676379, 6108524456778168, 13852236883273101,
    14707197337524912, 9652844973000555, 13852236883273101, 8771489469478456, 8771489469478456, 9733015321676379,
    9733015321676379, 14707197337524912, 9733015321676379, 10078150807734650, 6108524456778168, 4857980995002857,
    31077483054437414, 31077483659281536, 35056086963822367, 36910699139673593, 33056307076027811, 30985107502431572,
    35297866170005804, 34297866048856968, 30985112886488566, 21903635122959489, 27333727791236315, 33701740663749926,
    30333728274195826, 21903635122959489, 15976854959028867, 23577549034398372, 25577549063209818, 17976849366569943
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    10198445041452363, 4523561956057598, 4857980997143165, 11077483356859508, 13545809137367777, 11333714426093971,
    9958552727465983, 1584962500724866
  ]

abbrev PositiveTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 433710174443 / 500000000000
noncomputable def negativeCeiling : ℝ := 310271110467 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3477354227539519358124844646400, coefficient := 3477354227539519358124844646400 }, { argument := 3636448865400804557516177408000, coefficient := 3636448865400804557516177408000 }, { argument := 2181869319240482734509706444800, coefficient := 2181869319240482734509706444800 }, { argument := 55705851056858574815450942668800, coefficient := 55705851056858574815450942668800 }, { argument := 3568265449174539472062749081600, coefficient := 3568265449174539472062749081600 }, { argument := 1977319070561687478149421465600, coefficient := 1977319070561687478149421465600 }, { argument := 3477354227539519358124844646400, coefficient := 3477354227539519358124844646400 }, { argument := 113639027043775142422380544000, coefficient := 113639027043775142422380544000 }, { argument := 3568265449174539472062749081600, coefficient := 3568265449174539472062749081600 }, { argument := 113639027043775142422380544000, coefficient := 113639027043775142422380544000 }, { argument := 3477354227539519358124844646400, coefficient := 3477354227539519358124844646400 }, { argument := 3636448865400804557516177408000, coefficient := 3636448865400804557516177408000 }, { argument := 136366832452530170906856652800, coefficient := 136366832452530170906856652800 }, { argument := 93093090954260596672414141644800, coefficient := (-93093090954260596672414141644800) }, { argument := 41819161952109252411436040192, coefficient := 41819161952109252411436040192 }, { argument := 31141929113272847540431093760, coefficient := 31141929113272847540431093760 }, { argument := 32921467919745581685598584832, coefficient := 32921467919745581685598584832 }, { argument := 42708931355345619484019785728, coefficient := 42708931355345619484019785728 }, { argument := 572121726280984027671348379648, coefficient := 572121726280984027671348379648 }, { argument := 1034801815963894905414896058368, coefficient := 1034801815963894905414896058368 }, { argument := 31141929113272847540431093760, coefficient := 31141929113272847540431093760 }, { argument := 572121726280984027671348379648, coefficient := 572121726280984027671348379648 }, { argument := 33811237322981948758182330368, coefficient := 33811237322981948758182330368 }, { argument := 33811237322981948758182330368, coefficient := 33811237322981948758182330368 }, { argument := 32921467919745581685598584832, coefficient := 32921467919745581685598584832 }, { argument := 32921467919745581685598584832, coefficient := 32921467919745581685598584832 }, { argument := 1034801815963894905414896058368, coefficient := 1034801815963894905414896058368 }, { argument := 32921467919745581685598584832, coefficient := 32921467919745581685598584832 }, { argument := 41819161952109252411436040192, coefficient := 41819161952109252411436040192 }, { argument := 42708931355345619484019785728, coefficient := 42708931355345619484019785728 }, { argument := 3644495475656159529303021715456, coefficient := (-3644495475656159529303021715456) }, { argument := 4595233425827331580425549119488, coefficient := 4595233425827331580425549119488 }, { argument := 4595233425827331580425549119488, coefficient := (-4595233425827331580425549119488) }, { argument := 85606011651669981865172426293248, coefficient := 85606011651669981865172426293248 }, { argument := 85606047541655251674476050382848, coefficient := 85606047541655251674476050382848 }, { argument := 171212059193325233539648476676096, coefficient := (-171212059193325233539648476676096) }, { argument := 168691575565243833585836828393472, coefficient := 168691575565243833585836828393472 }, { argument := 610080705114362298625411550019584, coefficient := 610080705114362298625411550019584 }, { argument := 168717314828481081069943723655168, coefficient := 168717314828481081069943723655168 }, { argument := 947489595508087213281192102068224, coefficient := (-947489595508087213281192102068224) }, { argument := 10037058727831955941925914148864, coefficient := 10037058727831955941925914148864 }, { argument := 398938714192128998393566612946944, coefficient := 398938714192128998393566612946944 }, { argument := 398938680691661168916303466987520, coefficient := 398938680691661168916303466987520 }, { argument := 10037096185642898063951749185536, coefficient := 10037096185642898063951749185536 }, { argument := 817951549797265021315747743268864, coefficient := (-817951549797265021315747743268864) }, { argument := 37054492510286060915915751424, coefficient := 37054492510286060915915751424 }, { argument := 6390305682377362232901678137344, coefficient := 6390305682377362232901678137344 }, { argument := 65977299212685702577991761002496, coefficient := 65977299212685702577991761002496 }, { argument := 6390307821609378972850959941632, coefficient := 6390307821609378972850959941632 }, { argument := 37054492510286060915915751424, coefficient := 37054492510286060915915751424 }, { argument := 78832021701693015905576230584320, coefficient := (-78832021701693015905576230584320) }, { argument := 2436476652637696230135169024, coefficient := 2436476652637696230135169024 }, { argument := 472932498432948329331128532992, coefficient := 472932498432948329331128532992 }, { argument := 472932507877681295070418960384, coefficient := 472932507877681295070418960384 }, { argument := 2436467207904730490844741632, coefficient := 2436467207904730490844741632 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7
