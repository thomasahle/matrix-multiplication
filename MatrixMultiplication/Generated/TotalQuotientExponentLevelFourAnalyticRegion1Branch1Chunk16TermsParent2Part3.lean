import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 16, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16

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
def constantNumerator : ℤ := (-58371961190973019024787236716544)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    818762241, 3445599, 3109443, 1596741, 1596741, 3109443,
    96392733, 3109443, 20736531, 4117911, 20440467, 1941133869,
    121160799, 17770629807, 38342025, 4601043, 121160799, 240787917,
    38342025, 3716109063, 237720555, 1941135153, 121160799, 4601043,
    237720555, 4601043, 121160799, 121160799, 20440467, 227099173,
    5493795, 3693576799, 57483855, 2545905, 7387150901, 2545905,
    4957815, 93662505, 4957815, 57483855, 93662505, 28387509,
    4957815, 4957815, 5493795, 4042353, 1911120687, 72544617453,
    7644487991, 4042353, 4566773173, 89064371119, 178128676901, 570849369,
    92753, 10841025, 2968095, 188508613, 3676425439, 7352848181,
    23563689, 92753, 10841025, 2968095
  ]
def negativeCoefficients : Array ℕ := #[
    7551748758471950832110665728, 2033922653876145834833215488, 114718198465575298611019776, 117818690315996252627533824, 117818690315996252627533824, 114718198465575298611019776,
    3556264152432834256941613056, 114718198465575298611019776, 191260740166772201040642048, 151924100670626746809188352, 188530031748052828695822336, 17903799847126321555310641152,
    1117511125459582083863150592, 163905130039181781503947309056, 707285522442773470799462400, 42437131346566408247967744, 1117511125459582083863150592, 1110438270235154349155155968,
    707285522442773470799462400, 17137528208788401197470973952, 1096292559786298879739166720, 17903811689936016876842778624, 1117511125459582083863150592, 42437131346566408247967744,
    1096292559786298879739166720, 42437131346566408247967744, 1117511125459582083863150592, 1117511125459582083863150592, 188530031748052828695822336, 261827520230130638387150848,
    50671315179212583060111360, 8516808240968043214193819648, 530194980777614588604579840, 46963657970977516006932480, 8516805131538745289527525376, 46963657970977516006932480,
    45727772234899160322539520, 1727768259037541246781358080, 45727772234899160322539520, 530194980777614588604579840, 1727768259037541246781358080, 261828556706563279942582272,
    45727772234899160322539520, 45727772234899160322539520, 50671315179212583060111360, 149136502493184054207184896, 17626977103530488461415940096, 167276499010081782076859744256,
    17626989193065385768813330432, 149136502493184054207184896, 5265130997813344682112974848, 205368457514760174517813772288, 205368382186327828020252901376, 5265156107290793514633265152,
    3504109267084865620047560704, 12798823274987973875702169600, 3504108086493244902636257280, 217335633731309833749004288, 8477259897413535832293244928, 8477256787984237907626950656,
    217336670207742475304435712, 3504109267084865620047560704, 12798823274987973875702169600, 3504108086493244902636257280
  ]
def negativeScales : Array ℕ := #[
    29, 21, 21, 20, 20, 21,
    26, 21, 24, 21, 24, 30,
    26, 34, 25, 22, 26, 27,
    25, 31, 27, 30, 26, 22,
    27, 22, 26, 26, 24, 27,
    22, 31, 25, 21, 32, 21,
    22, 26, 22, 25, 26, 24,
    22, 22, 22, 21, 30, 36,
    32, 21, 32, 36, 37, 29,
    16, 23, 21, 27, 31, 32,
    24, 16, 23, 21
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29608869329984609, 21716323379415823, 21568224740323199, 20606698888142346, 20606698888142346, 21568224740323199,
    26522421050708350, 21568224740323199, 24305671231087330, 21973481234220725, 24284924821880791, 30854252471846282,
    26852347758100888, 34048775761547716, 25192423197887119, 22133529508833551, 26852347758100888, 27843187758524074,
    25192423197887119, 31791145698102488, 27824691414446617, 30854253426144137, 26852347758100888, 22133529508833551,
    27824691414446617, 22133529508833551, 26852347758100888, 26852347758100888, 24284924821880791, 27758747211734560,
    22389371646829086, 31782371429753937, 25776653480108848, 21279747155654583, 32782370903035598, 21279747155654583,
    22241273007839948, 26480968287586576, 22241273007839948, 25776653480108848, 26480968287586576, 24758752922809000,
    22241273007839948, 22241273007839948, 22389371646829086, 21946763890300079, 30831771742383466, 36078149524407017,
    32831772731861490, 21946763890300079, 32088527988279976, 36374129367267441, 37374128838091846, 29088534868494776,
    16501106324519055, 23369997831651248, 21501105838451461, 27490055201152773, 31775656580530071, 32775656051354471,
    24490062081367573, 16501106324519055, 23369997831651248, 21501105838451461
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
noncomputable def negativeCeiling : ℝ := 78596353 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7551748758471950832110665728, coefficient := (-7551748758471950832110665728) }, { argument := 2033922653876145834833215488, coefficient := (-2033922653876145834833215488) }, { argument := 114718198465575298611019776, coefficient := (-114718198465575298611019776) }, { argument := 117818690315996252627533824, coefficient := (-117818690315996252627533824) }, { argument := 117818690315996252627533824, coefficient := (-117818690315996252627533824) }, { argument := 114718198465575298611019776, coefficient := (-114718198465575298611019776) }, { argument := 3556264152432834256941613056, coefficient := (-3556264152432834256941613056) }, { argument := 114718198465575298611019776, coefficient := (-114718198465575298611019776) }, { argument := 191260740166772201040642048, coefficient := (-191260740166772201040642048) }, { argument := 151924100670626746809188352, coefficient := (-151924100670626746809188352) }, { argument := 188530031748052828695822336, coefficient := (-188530031748052828695822336) }, { argument := 17903799847126321555310641152, coefficient := (-17903799847126321555310641152) }, { argument := 1117511125459582083863150592, coefficient := (-1117511125459582083863150592) }, { argument := 163905130039181781503947309056, coefficient := (-163905130039181781503947309056) }, { argument := 707285522442773470799462400, coefficient := (-707285522442773470799462400) }, { argument := 42437131346566408247967744, coefficient := (-42437131346566408247967744) }, { argument := 1117511125459582083863150592, coefficient := (-1117511125459582083863150592) }, { argument := 1110438270235154349155155968, coefficient := (-1110438270235154349155155968) }, { argument := 707285522442773470799462400, coefficient := (-707285522442773470799462400) }, { argument := 17137528208788401197470973952, coefficient := (-17137528208788401197470973952) }, { argument := 1096292559786298879739166720, coefficient := (-1096292559786298879739166720) }, { argument := 17903811689936016876842778624, coefficient := (-17903811689936016876842778624) }, { argument := 1117511125459582083863150592, coefficient := (-1117511125459582083863150592) }, { argument := 42437131346566408247967744, coefficient := (-42437131346566408247967744) }, { argument := 1096292559786298879739166720, coefficient := (-1096292559786298879739166720) }, { argument := 42437131346566408247967744, coefficient := (-42437131346566408247967744) }, { argument := 1117511125459582083863150592, coefficient := (-1117511125459582083863150592) }, { argument := 1117511125459582083863150592, coefficient := (-1117511125459582083863150592) }, { argument := 188530031748052828695822336, coefficient := (-188530031748052828695822336) }, { argument := 261827520230130638387150848, coefficient := (-261827520230130638387150848) }, { argument := 50671315179212583060111360, coefficient := (-50671315179212583060111360) }, { argument := 8516808240968043214193819648, coefficient := (-8516808240968043214193819648) }, { argument := 530194980777614588604579840, coefficient := (-530194980777614588604579840) }, { argument := 46963657970977516006932480, coefficient := (-46963657970977516006932480) }, { argument := 8516805131538745289527525376, coefficient := (-8516805131538745289527525376) }, { argument := 46963657970977516006932480, coefficient := (-46963657970977516006932480) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 1727768259037541246781358080, coefficient := (-1727768259037541246781358080) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 530194980777614588604579840, coefficient := (-530194980777614588604579840) }, { argument := 1727768259037541246781358080, coefficient := (-1727768259037541246781358080) }, { argument := 261828556706563279942582272, coefficient := (-261828556706563279942582272) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 50671315179212583060111360, coefficient := (-50671315179212583060111360) }, { argument := 149136502493184054207184896, coefficient := (-149136502493184054207184896) }, { argument := 17626977103530488461415940096, coefficient := (-17626977103530488461415940096) }, { argument := 167276499010081782076859744256, coefficient := (-167276499010081782076859744256) }, { argument := 17626989193065385768813330432, coefficient := (-17626989193065385768813330432) }, { argument := 149136502493184054207184896, coefficient := (-149136502493184054207184896) }, { argument := 5265130997813344682112974848, coefficient := (-5265130997813344682112974848) }, { argument := 205368457514760174517813772288, coefficient := (-205368457514760174517813772288) }, { argument := 205368382186327828020252901376, coefficient := (-205368382186327828020252901376) }, { argument := 5265156107290793514633265152, coefficient := (-5265156107290793514633265152) }, { argument := 3504109267084865620047560704, coefficient := (-3504109267084865620047560704) }, { argument := 12798823274987973875702169600, coefficient := (-12798823274987973875702169600) }, { argument := 3504108086493244902636257280, coefficient := (-3504108086493244902636257280) }, { argument := 217335633731309833749004288, coefficient := (-217335633731309833749004288) }, { argument := 8477259897413535832293244928, coefficient := (-8477259897413535832293244928) }, { argument := 8477256787984237907626950656, coefficient := (-8477256787984237907626950656) }, { argument := 217336670207742475304435712, coefficient := (-217336670207742475304435712) }, { argument := 3504109267084865620047560704, coefficient := (-3504109267084865620047560704) }, { argument := 12798823274987973875702169600, coefficient := (-12798823274987973875702169600) }, { argument := 3504108086493244902636257280, coefficient := (-3504108086493244902636257280) }] }

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
def constantNumerator : ℤ := 5123439074472161832172316704899072
def positiveArguments : Array ℕ := #[
    757, 1, 1, 1, 1, 1829,
    44309, 33571, 18703, 1829, 18703, 37347,
    1829, 44309, 1829, 81, 243, 513,
    1323, 1107, 30969, 945, 1107, 999,
    513, 513, 999, 30969, 999, 81,
    1323, 387, 5805, 10191, 387, 3225,
    387, 10191, 20253, 3225, 312567, 19995,
    5805, 10191, 387, 19995, 387, 10191,
    10191, 387, 27, 123, 3, 1287,
    57, 3, 57, 111, 2097, 111
  ]
def positiveCoefficients : Array ℕ := #[
    59975719023298103558312770404352, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 35378005185202508168601534464,
    857060706260873665632895238144, 649357579044523456384976551936, 723537267336077102544947511296, 35378005185202508168601534464, 723537267336077102544947511296, 722396041362360892604024881152,
    35378005185202508168601534464, 857060706260873665632895238144, 35378005185202508168601534464, 401092572728463209067316248576, 300819429546347406800487186432, 317531620076700040511625363456,
    409448667993639525922885337088, 5481598493955663857253322063872, 9584441269157235433337744523264, 292463334281171089944918097920, 5481598493955663857253322063872, 309175524811523723656056274944,
    317531620076700040511625363456, 317531620076700040511625363456, 309175524811523723656056274944, 9584441269157235433337744523264, 309175524811523723656056274944, 401092572728463209067316248576,
    409448667993639525922885337088, 29942674700215135399122567168, 449140120503227030986838507520, 788490433772331898843560935424, 29942674700215135399122567168, 499044578336918923318709452800,
    29942674700215135399122567168, 788490433772331898843560935424, 783499987988962709610373840896, 499044578336918923318709452800, 12091850133103545512012330041344, 773519096422224331143999651840,
    449140120503227030986838507520, 788490433772331898843560935424, 29942674700215135399122567168, 773519096422224331143999651840, 29942674700215135399122567168, 788490433772331898843560935424,
    788490433772331898843560935424, 29942674700215135399122567168, 4178047632588158427784544256, 4758332026003180431643508736, 3713820117856140824697372672, 49788400955008887931099152384,
    4410161389954167229328130048, 3713820117856140824697372672, 4410161389954167229328130048, 4294104511271162828556337152, 162247516398840152278966468608, 4294104511271162828556337152
  ]
def positiveScales : Array ℕ := #[
    9, 0, 0, 0, 0, 10,
    15, 15, 14, 10, 14, 15,
    10, 15, 10, 6, 7, 9,
    10, 10, 14, 9, 10, 9,
    9, 9, 9, 14, 9, 6,
    10, 8, 12, 13, 8, 11,
    8, 13, 14, 11, 18, 14,
    12, 13, 8, 14, 8, 13,
    13, 8, 4, 6, 1, 10,
    5, 1, 5, 6, 11, 6
  ]
def negativeArguments : Array ℕ := #[
    1, 59, 27, 129
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 4674461588341595918019093069824, 34226566206162193840410986545152, 20440865928680199099134339186688
  ]
def negativeScales : Array ℕ := #[
    0, 5, 4, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9564149489985604, 0, 0, 0, 0, 10836839359665486,
    15435312146876110, 15034927891668423, 14190982079501248, 10836839359665486, 14190982079501248, 15188704738790182,
    10836839359665486, 15435312146876110, 10836839359665486, 6339850002884624, 7924812503187618, 9002815015607054,
    10369597346278676, 10112439506781552, 14918537177804473, 9884170518905654, 10112439506781552, 9964340866974576,
    9002815015607054, 9002815015607054, 9964340866974576, 14918537177804473, 9964340866974576, 6339850002884624,
    10369597346278676, 8596189756144093, 12503080351752909, 13315008003600356, 8596189756144093, 11655083445196472,
    8596189756144093, 13315008003600356, 14305848004314880, 11655083445196472, 18253805944874600, 14287351660697491,
    12503080351752909, 13315008003600356, 8596189756144093, 14287351660697491, 8596189756144093, 13315008003600356,
    13315008003600356, 8596189756144093, 4754887502147955, 6942514504772358, 1584962500720924, 10329796338220701,
    5832890014087662, 1584962500720924, 5832890014087662, 6794415866314396, 11034111146096592, 6794415866314396
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 5882643052550791, 4754887502413606, 7011227255423255
  ]

abbrev PositiveTerm := Fin 60
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 4242465247 / 250000000000
noncomputable def negativeCeiling : ℝ := 1003762239 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 59975719023298103558312770404352, coefficient := 59975719023298103558312770404352 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 35378005185202508168601534464, coefficient := 35378005185202508168601534464 }, { argument := 857060706260873665632895238144, coefficient := 857060706260873665632895238144 }, { argument := 649357579044523456384976551936, coefficient := 649357579044523456384976551936 }, { argument := 723537267336077102544947511296, coefficient := 723537267336077102544947511296 }, { argument := 35378005185202508168601534464, coefficient := 35378005185202508168601534464 }, { argument := 723537267336077102544947511296, coefficient := 723537267336077102544947511296 }, { argument := 722396041362360892604024881152, coefficient := 722396041362360892604024881152 }, { argument := 35378005185202508168601534464, coefficient := 35378005185202508168601534464 }, { argument := 857060706260873665632895238144, coefficient := 857060706260873665632895238144 }, { argument := 35378005185202508168601534464, coefficient := 35378005185202508168601534464 }, { argument := 4674461588341595918019093069824, coefficient := (-4674461588341595918019093069824) }, { argument := 401092572728463209067316248576, coefficient := 401092572728463209067316248576 }, { argument := 300819429546347406800487186432, coefficient := 300819429546347406800487186432 }, { argument := 317531620076700040511625363456, coefficient := 317531620076700040511625363456 }, { argument := 409448667993639525922885337088, coefficient := 409448667993639525922885337088 }, { argument := 5481598493955663857253322063872, coefficient := 5481598493955663857253322063872 }, { argument := 9584441269157235433337744523264, coefficient := 9584441269157235433337744523264 }, { argument := 292463334281171089944918097920, coefficient := 292463334281171089944918097920 }, { argument := 5481598493955663857253322063872, coefficient := 5481598493955663857253322063872 }, { argument := 309175524811523723656056274944, coefficient := 309175524811523723656056274944 }, { argument := 317531620076700040511625363456, coefficient := 317531620076700040511625363456 }, { argument := 317531620076700040511625363456, coefficient := 317531620076700040511625363456 }, { argument := 309175524811523723656056274944, coefficient := 309175524811523723656056274944 }, { argument := 9584441269157235433337744523264, coefficient := 9584441269157235433337744523264 }, { argument := 309175524811523723656056274944, coefficient := 309175524811523723656056274944 }, { argument := 401092572728463209067316248576, coefficient := 401092572728463209067316248576 }, { argument := 409448667993639525922885337088, coefficient := 409448667993639525922885337088 }, { argument := 34226566206162193840410986545152, coefficient := (-34226566206162193840410986545152) }, { argument := 29942674700215135399122567168, coefficient := 29942674700215135399122567168 }, { argument := 449140120503227030986838507520, coefficient := 449140120503227030986838507520 }, { argument := 788490433772331898843560935424, coefficient := 788490433772331898843560935424 }, { argument := 29942674700215135399122567168, coefficient := 29942674700215135399122567168 }, { argument := 499044578336918923318709452800, coefficient := 499044578336918923318709452800 }, { argument := 29942674700215135399122567168, coefficient := 29942674700215135399122567168 }, { argument := 788490433772331898843560935424, coefficient := 788490433772331898843560935424 }, { argument := 783499987988962709610373840896, coefficient := 783499987988962709610373840896 }, { argument := 499044578336918923318709452800, coefficient := 499044578336918923318709452800 }, { argument := 12091850133103545512012330041344, coefficient := 12091850133103545512012330041344 }, { argument := 773519096422224331143999651840, coefficient := 773519096422224331143999651840 }, { argument := 449140120503227030986838507520, coefficient := 449140120503227030986838507520 }, { argument := 788490433772331898843560935424, coefficient := 788490433772331898843560935424 }, { argument := 29942674700215135399122567168, coefficient := 29942674700215135399122567168 }, { argument := 773519096422224331143999651840, coefficient := 773519096422224331143999651840 }, { argument := 29942674700215135399122567168, coefficient := 29942674700215135399122567168 }, { argument := 788490433772331898843560935424, coefficient := 788490433772331898843560935424 }, { argument := 788490433772331898843560935424, coefficient := 788490433772331898843560935424 }, { argument := 29942674700215135399122567168, coefficient := 29942674700215135399122567168 }, { argument := 20440865928680199099134339186688, coefficient := (-20440865928680199099134339186688) }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4758332026003180431643508736, coefficient := 4758332026003180431643508736 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 49788400955008887931099152384, coefficient := 49788400955008887931099152384 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 162247516398840152278966468608, coefficient := 162247516398840152278966468608 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16
