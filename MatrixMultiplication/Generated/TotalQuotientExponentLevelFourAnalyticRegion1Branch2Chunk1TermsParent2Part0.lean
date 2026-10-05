import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 1, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-123929353424509879517861497536512)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2826531065, 3668751639, 176082725, 155958985, 7299886685, 1987219325,
    1834375959, 7299886685, 176082725, 176082725, 75464025, 176082725,
    1987219325, 75464025, 1413265393, 155958985, 28216425, 2362536855,
    1181268855, 14107785, 233799369, 2206747391, 10232712063, 75281911355,
    10500233947, 334402355, 10232712063, 5818600977, 10500233947, 163924034421,
    200641413, 1103374027, 10232712063, 334402355, 200641413, 334402355,
    5149796267, 5818600977, 233799369, 9207465, 770933079, 385466679,
    4603593, 129868661, 13616494879, 146772205125, 6808252633, 129868661,
    469996107, 65228151, 14168648415, 1614049779, 51349821, 14168655339,
    26368827, 26368827, 892376619, 48574155, 1614049779, 892376619,
    469992645, 51349821, 48574155, 65228151
  ]
def negativeCoefficients : Array ℕ := #[
    6517536896555587178730618880, 8459565319329431787644387328, 6496305927752757414146867200, 5753870964581013709672939520, 269318282890550028797917265920, 73315452613209690816800358400,
    8459565962659631358264999936, 269318282890550028797917265920, 6496305927752757414146867200, 6496305927752757414146867200, 5568262223788077783554457600, 6496305927752757414146867200,
    73315452613209690816800358400, 5568262223788077783554457600, 6517536253225387608110006272, 5753870964581013709672939520, 520501170650020034956492800, 43581112728891652258324807680,
    43581128500857835279991439360, 520485398683837013289861120, 1078209281134445664273432576, 40707304357103264720387833856, 23595027575765186247420542976, 173588269018171756346563624960,
    24211891041798263012058988544, 771079332541345955798056960, 23595027575765186247420542976, 13416780386219419630886191104, 24211891041798263012058988544, 377983088811767787532207521792,
    14804723184793842351322693632, 40707316587294585589820555264, 23595027575765186247420542976, 771079332541345955798056960, 14804723184793842351322693632, 771079332541345955798056960,
    23749243442273455438580154368, 13416780386219419630886191104, 1078209281134445664273432576, 21230968802829764583751680, 1777650650783738447379038208, 1777651294113938017999650816,
    21230325472630193963139072, 149728372041396548205019136, 15698749763368106757040635904, 169216831567179776840957952000, 15698761738763775108360175616, 149728372041396548205019136,
    1083737237683601288529444864, 150405875987285220368842752, 32670678897734435209299886080, 3721745399430057686999236608, 118404625777224535183982592, 32670694863391431004916809728,
    121604750798230603702468608, 121604750798230603702468608, 2057680388506902057386508288, 112004375735212398147010560, 3721745399430057686999236608, 2057680388506902057386508288,
    1083729254855103390720983040, 118404625777224535183982592, 112004375735212398147010560, 150405875987285220368842752
  ]
def negativeScales : Array ℕ := #[
    31, 31, 27, 27, 32, 30,
    30, 32, 27, 27, 26, 27,
    30, 26, 30, 27, 24, 31,
    30, 23, 27, 31, 33, 36,
    33, 28, 33, 32, 33, 37,
    27, 30, 33, 28, 27, 28,
    32, 32, 27, 23, 29, 28,
    22, 26, 33, 37, 32, 26,
    28, 25, 33, 30, 25, 33,
    24, 24, 29, 25, 30, 29,
    28, 25, 25, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31396385407011850, 31772642097093255, 27391678136301338, 27216591429743242, 32765226923735663, 30888103965944057,
    30772642206806842, 32765226923735663, 27391678136301338, 27391678136301338, 26169285714964885, 27391678136301338,
    30888103965944057, 26169285714964885, 30396385264606928, 27216591429743242, 24750031875564819, 31137689689187065,
    30137690211297030, 23749988159078591, 27800695795946228, 31039274346037137, 33252469514415263, 36131584206421663,
    33289702420614238, 28317009766609973, 33252469514415263, 32438025167571369, 33289702420614238, 37254236440589450,
    27580044172446990, 30039274779483517, 33252469514415263, 28317009766609973, 27580044172446990, 28317009766609973,
    32261868212417512, 32438025167571369, 27800695795946228, 23134372577395710, 29522030391243549, 28522030913353515,
    22134328860909696, 26952478101641564, 33664636325419953, 37094787828529347, 32664637425943092, 26952478101641564,
    28808073566788299, 25958991409854936, 33721983091302297, 30588037927531026, 25613855911690970, 33721983796324946,
    24652330059519951, 24652330059519951, 29733077473536364, 25533685562999532, 30588037927531026, 29733077473536364,
    28808062939830694, 25613855911690970, 25533685562999532, 25958991409854936
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
noncomputable def negativeCeiling : ℝ := 400702141 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6517536896555587178730618880, coefficient := (-6517536896555587178730618880) }, { argument := 8459565319329431787644387328, coefficient := (-8459565319329431787644387328) }, { argument := 6496305927752757414146867200, coefficient := (-6496305927752757414146867200) }, { argument := 5753870964581013709672939520, coefficient := (-5753870964581013709672939520) }, { argument := 269318282890550028797917265920, coefficient := (-269318282890550028797917265920) }, { argument := 73315452613209690816800358400, coefficient := (-73315452613209690816800358400) }, { argument := 8459565962659631358264999936, coefficient := (-8459565962659631358264999936) }, { argument := 269318282890550028797917265920, coefficient := (-269318282890550028797917265920) }, { argument := 6496305927752757414146867200, coefficient := (-6496305927752757414146867200) }, { argument := 6496305927752757414146867200, coefficient := (-6496305927752757414146867200) }, { argument := 5568262223788077783554457600, coefficient := (-5568262223788077783554457600) }, { argument := 6496305927752757414146867200, coefficient := (-6496305927752757414146867200) }, { argument := 73315452613209690816800358400, coefficient := (-73315452613209690816800358400) }, { argument := 5568262223788077783554457600, coefficient := (-5568262223788077783554457600) }, { argument := 6517536253225387608110006272, coefficient := (-6517536253225387608110006272) }, { argument := 5753870964581013709672939520, coefficient := (-5753870964581013709672939520) }, { argument := 520501170650020034956492800, coefficient := (-520501170650020034956492800) }, { argument := 43581112728891652258324807680, coefficient := (-43581112728891652258324807680) }, { argument := 43581128500857835279991439360, coefficient := (-43581128500857835279991439360) }, { argument := 520485398683837013289861120, coefficient := (-520485398683837013289861120) }, { argument := 1078209281134445664273432576, coefficient := (-1078209281134445664273432576) }, { argument := 40707304357103264720387833856, coefficient := (-40707304357103264720387833856) }, { argument := 23595027575765186247420542976, coefficient := (-23595027575765186247420542976) }, { argument := 173588269018171756346563624960, coefficient := (-173588269018171756346563624960) }, { argument := 24211891041798263012058988544, coefficient := (-24211891041798263012058988544) }, { argument := 771079332541345955798056960, coefficient := (-771079332541345955798056960) }, { argument := 23595027575765186247420542976, coefficient := (-23595027575765186247420542976) }, { argument := 13416780386219419630886191104, coefficient := (-13416780386219419630886191104) }, { argument := 24211891041798263012058988544, coefficient := (-24211891041798263012058988544) }, { argument := 377983088811767787532207521792, coefficient := (-377983088811767787532207521792) }, { argument := 14804723184793842351322693632, coefficient := (-14804723184793842351322693632) }, { argument := 40707316587294585589820555264, coefficient := (-40707316587294585589820555264) }, { argument := 23595027575765186247420542976, coefficient := (-23595027575765186247420542976) }, { argument := 771079332541345955798056960, coefficient := (-771079332541345955798056960) }, { argument := 14804723184793842351322693632, coefficient := (-14804723184793842351322693632) }, { argument := 771079332541345955798056960, coefficient := (-771079332541345955798056960) }, { argument := 23749243442273455438580154368, coefficient := (-23749243442273455438580154368) }, { argument := 13416780386219419630886191104, coefficient := (-13416780386219419630886191104) }, { argument := 1078209281134445664273432576, coefficient := (-1078209281134445664273432576) }, { argument := 21230968802829764583751680, coefficient := (-21230968802829764583751680) }, { argument := 1777650650783738447379038208, coefficient := (-1777650650783738447379038208) }, { argument := 1777651294113938017999650816, coefficient := (-1777651294113938017999650816) }, { argument := 21230325472630193963139072, coefficient := (-21230325472630193963139072) }, { argument := 149728372041396548205019136, coefficient := (-149728372041396548205019136) }, { argument := 15698749763368106757040635904, coefficient := (-15698749763368106757040635904) }, { argument := 169216831567179776840957952000, coefficient := (-169216831567179776840957952000) }, { argument := 15698761738763775108360175616, coefficient := (-15698761738763775108360175616) }, { argument := 149728372041396548205019136, coefficient := (-149728372041396548205019136) }, { argument := 1083737237683601288529444864, coefficient := (-1083737237683601288529444864) }, { argument := 150405875987285220368842752, coefficient := (-150405875987285220368842752) }, { argument := 32670678897734435209299886080, coefficient := (-32670678897734435209299886080) }, { argument := 3721745399430057686999236608, coefficient := (-3721745399430057686999236608) }, { argument := 118404625777224535183982592, coefficient := (-118404625777224535183982592) }, { argument := 32670694863391431004916809728, coefficient := (-32670694863391431004916809728) }, { argument := 121604750798230603702468608, coefficient := (-121604750798230603702468608) }, { argument := 121604750798230603702468608, coefficient := (-121604750798230603702468608) }, { argument := 2057680388506902057386508288, coefficient := (-2057680388506902057386508288) }, { argument := 112004375735212398147010560, coefficient := (-112004375735212398147010560) }, { argument := 3721745399430057686999236608, coefficient := (-3721745399430057686999236608) }, { argument := 2057680388506902057386508288, coefficient := (-2057680388506902057386508288) }, { argument := 1083729254855103390720983040, coefficient := (-1083729254855103390720983040) }, { argument := 118404625777224535183982592, coefficient := (-118404625777224535183982592) }, { argument := 112004375735212398147010560, coefficient := (-112004375735212398147010560) }, { argument := 150405875987285220368842752, coefficient := (-150405875987285220368842752) }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2055041170179961509807567786737664)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    9821818825, 25749269325, 4816310135, 4265874691, 199670457311, 54355500095,
    12874637529, 199670457311, 4816310135, 4816310135, 2064132915, 4816310135,
    54355500095, 2064132915, 2455453273, 4265874691, 28190033887, 759727284469,
    179059704957, 138950573755, 183741004433, 5851624345, 179059704957, 101818263603,
    183741004433, 2868466253919, 3510974607, 379863646323, 179059704957, 5851624345,
    3510974607, 5851624345, 90115014913, 101818263603, 28190033887, 92965695,
    7783937217, 3891970017, 46481439, 3213558569, 336935820091, 3631831373625,
    168468038557, 3213558569, 554417783, 6839053989, 381845231959, 169230208281,
    5383936119, 381845416599, 2764723953, 2764723953, 93564079041, 5092912545,
    169230208281, 93564079041, 277207449, 5383936119, 5092912545, 6839053989,
    102237031, 10719368309, 115544076375, 5359688243
  ]
def negativeCoefficients : Array ℕ := #[
    22647572275389707705542246400, 59373772665411862048171622400, 22211310109989625123611607040, 19672874668847953680913137664, 920817456274141315838869766144, 250670499812740054966473850880,
    59373785884809833870279049216, 920817456274141315838869766144, 22211310109989625123611607040, 22211310109989625123611607040, 19038265808562535820238520320, 22211310109989625123611607040,
    250670499812740054966473850880, 19038265808562535820238520320, 22647559055991735883434819584, 19672874668847953680913137664, 32500896283918042865663475712, 875905923900873526540704415744,
    825767137813930143218430640128, 160199104559599263016686714880, 847355821155470800557474578432, 26985854176925821673804922880, 825767137813930143218430640128, 469553862678509297124205658112,
    847355821155470800557474578432, 13228465717529037784499173195776, 518128400196975776137054519296, 875905933328312669710892138496, 825767137813930143218430640128, 26985854176925821673804922880,
    518128400196975776137054519296, 26985854176925821673804922880, 831164308649315307553191624704, 469553862678509297124205658112, 32500896283918042865663475712, 428728595824884923529953280,
    35897074431955492518041223168, 35897087423075006427992948736, 428715604705371013578227712, 3704980780513706075796537344, 388460552655257620392303394816, 4187216491758086818426257408000,
    388460848982601498957933707264, 3704980780513706075796537344, 40908811811657752771467149312, 15769784830170677375850774528, 880475158714241541300675411968, 390218292712521229534350016512,
    12414511462049256657584652288, 880475584465094762517126709248, 12750038798861398729411264512, 12750038798861398729411264512, 215744077570207352184511660032, 11743456788424972513931427840,
    390218292712521229534350016512, 215744077570207352184511660032, 40908598936231142163241500672, 12414511462049256657584652288, 11743456788424972513931427840, 15769784830170677375850774528,
    117871271607056857097568256, 12358590239247232978946883584, 133213250382673441342881792000, 12358599666686376149134606336
  ]
def negativeScales : Array ℕ := #[
    33, 34, 32, 31, 37, 35,
    33, 37, 32, 32, 30, 32,
    35, 30, 31, 31, 34, 39,
    37, 37, 37, 32, 37, 36,
    37, 41, 31, 38, 37, 32,
    31, 32, 36, 36, 34, 26,
    32, 31, 25, 31, 38, 41,
    37, 31, 29, 32, 38, 37,
    32, 38, 31, 31, 36, 32,
    37, 36, 28, 32, 32, 32,
    26, 33, 36, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33193343064558096, 34583812443069951, 32165281148039979, 31990194461713996, 37538829935162701, 35661706974188096,
    33583812764281775, 37538829935162701, 32165281148039979, 32165281148039979, 30942888735943444, 32165281148039979,
    35661706974188096, 30942888735943444, 31193342222456116, 31990194461713996, 34714466161135798, 39466690678169585,
    37381649757973167, 37015780835491143, 37418882664172153, 32446190010167915, 37381649757973167, 36567205411131461,
    37418882664172153, 41383416684147355, 31709224416091463, 38466690693697416, 37381649757973167, 32446190010167915,
    31709224416091463, 32446190010167915, 36391048455975418, 36567205411131461, 34714466161135798, 26470195113941550,
    32857852929799456, 31857853451909441, 25470151397455536, 31581524620571668, 38293682855184749, 41723834358450490,
    37293683955707887, 31581524620571668, 29046398291888704, 32671149632384007, 38474197052887967, 37300196162143424,
    32326014146299155, 38474197750498218, 31364488294113792, 31364488294113792, 36445235707998191, 32245843797615172,
    37300196162143424, 36445235707998191, 28046390784578964, 32326014146299155, 32245843797615172, 32671149632384007,
    26607342604730956, 33319500839340481, 36749652342703838, 32319501939863619
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
noncomputable def negativeCeiling : ℝ := 492189561 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 22647572275389707705542246400, coefficient := (-22647572275389707705542246400) }, { argument := 59373772665411862048171622400, coefficient := (-59373772665411862048171622400) }, { argument := 22211310109989625123611607040, coefficient := (-22211310109989625123611607040) }, { argument := 19672874668847953680913137664, coefficient := (-19672874668847953680913137664) }, { argument := 920817456274141315838869766144, coefficient := (-920817456274141315838869766144) }, { argument := 250670499812740054966473850880, coefficient := (-250670499812740054966473850880) }, { argument := 59373785884809833870279049216, coefficient := (-59373785884809833870279049216) }, { argument := 920817456274141315838869766144, coefficient := (-920817456274141315838869766144) }, { argument := 22211310109989625123611607040, coefficient := (-22211310109989625123611607040) }, { argument := 22211310109989625123611607040, coefficient := (-22211310109989625123611607040) }, { argument := 19038265808562535820238520320, coefficient := (-19038265808562535820238520320) }, { argument := 22211310109989625123611607040, coefficient := (-22211310109989625123611607040) }, { argument := 250670499812740054966473850880, coefficient := (-250670499812740054966473850880) }, { argument := 19038265808562535820238520320, coefficient := (-19038265808562535820238520320) }, { argument := 22647559055991735883434819584, coefficient := (-22647559055991735883434819584) }, { argument := 19672874668847953680913137664, coefficient := (-19672874668847953680913137664) }, { argument := 32500896283918042865663475712, coefficient := (-32500896283918042865663475712) }, { argument := 875905923900873526540704415744, coefficient := (-875905923900873526540704415744) }, { argument := 825767137813930143218430640128, coefficient := (-825767137813930143218430640128) }, { argument := 160199104559599263016686714880, coefficient := (-160199104559599263016686714880) }, { argument := 847355821155470800557474578432, coefficient := (-847355821155470800557474578432) }, { argument := 26985854176925821673804922880, coefficient := (-26985854176925821673804922880) }, { argument := 825767137813930143218430640128, coefficient := (-825767137813930143218430640128) }, { argument := 469553862678509297124205658112, coefficient := (-469553862678509297124205658112) }, { argument := 847355821155470800557474578432, coefficient := (-847355821155470800557474578432) }, { argument := 13228465717529037784499173195776, coefficient := (-13228465717529037784499173195776) }, { argument := 518128400196975776137054519296, coefficient := (-518128400196975776137054519296) }, { argument := 875905933328312669710892138496, coefficient := (-875905933328312669710892138496) }, { argument := 825767137813930143218430640128, coefficient := (-825767137813930143218430640128) }, { argument := 26985854176925821673804922880, coefficient := (-26985854176925821673804922880) }, { argument := 518128400196975776137054519296, coefficient := (-518128400196975776137054519296) }, { argument := 26985854176925821673804922880, coefficient := (-26985854176925821673804922880) }, { argument := 831164308649315307553191624704, coefficient := (-831164308649315307553191624704) }, { argument := 469553862678509297124205658112, coefficient := (-469553862678509297124205658112) }, { argument := 32500896283918042865663475712, coefficient := (-32500896283918042865663475712) }, { argument := 428728595824884923529953280, coefficient := (-428728595824884923529953280) }, { argument := 35897074431955492518041223168, coefficient := (-35897074431955492518041223168) }, { argument := 35897087423075006427992948736, coefficient := (-35897087423075006427992948736) }, { argument := 428715604705371013578227712, coefficient := (-428715604705371013578227712) }, { argument := 3704980780513706075796537344, coefficient := (-3704980780513706075796537344) }, { argument := 388460552655257620392303394816, coefficient := (-388460552655257620392303394816) }, { argument := 4187216491758086818426257408000, coefficient := (-4187216491758086818426257408000) }, { argument := 388460848982601498957933707264, coefficient := (-388460848982601498957933707264) }, { argument := 3704980780513706075796537344, coefficient := (-3704980780513706075796537344) }, { argument := 40908811811657752771467149312, coefficient := (-40908811811657752771467149312) }, { argument := 15769784830170677375850774528, coefficient := (-15769784830170677375850774528) }, { argument := 880475158714241541300675411968, coefficient := (-880475158714241541300675411968) }, { argument := 390218292712521229534350016512, coefficient := (-390218292712521229534350016512) }, { argument := 12414511462049256657584652288, coefficient := (-12414511462049256657584652288) }, { argument := 880475584465094762517126709248, coefficient := (-880475584465094762517126709248) }, { argument := 12750038798861398729411264512, coefficient := (-12750038798861398729411264512) }, { argument := 12750038798861398729411264512, coefficient := (-12750038798861398729411264512) }, { argument := 215744077570207352184511660032, coefficient := (-215744077570207352184511660032) }, { argument := 11743456788424972513931427840, coefficient := (-11743456788424972513931427840) }, { argument := 390218292712521229534350016512, coefficient := (-390218292712521229534350016512) }, { argument := 215744077570207352184511660032, coefficient := (-215744077570207352184511660032) }, { argument := 40908598936231142163241500672, coefficient := (-40908598936231142163241500672) }, { argument := 12414511462049256657584652288, coefficient := (-12414511462049256657584652288) }, { argument := 11743456788424972513931427840, coefficient := (-11743456788424972513931427840) }, { argument := 15769784830170677375850774528, coefficient := (-15769784830170677375850774528) }, { argument := 117871271607056857097568256, coefficient := (-117871271607056857097568256) }, { argument := 12358590239247232978946883584, coefficient := (-12358590239247232978946883584) }, { argument := 133213250382673441342881792000, coefficient := (-133213250382673441342881792000) }, { argument := 12358599666686376149134606336, coefficient := (-12358599666686376149134606336) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1
