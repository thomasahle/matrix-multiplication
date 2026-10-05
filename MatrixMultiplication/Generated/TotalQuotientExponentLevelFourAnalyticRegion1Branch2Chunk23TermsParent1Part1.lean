import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 23, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk23

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 243988148401286058395672732762112
def positiveArguments : Array ℕ := #[
    37, 5, 21, 91, 3, 3,
    7, 91, 91, 3, 1123, 45,
    21, 91, 7, 45, 7, 91,
    91, 3, 7, 133
  ]
def positiveCoefficients : Array ℕ := #[
    2931442013027780490961126162432, 193428131138340667952988160, 3249592603124123221610201088, 7040783973435600313488769024, 232113757366008801543585792, 3713820117856140824697372672,
    270799383593676935134183424, 7040783973435600313488769024, 7040783973435600313488769024, 3713820117856140824697372672, 86887916507342628044482281472, 6963412720980264046307573760,
    3249592603124123221610201088, 7040783973435600313488769024, 270799383593676935134183424, 6963412720980264046307573760, 270799383593676935134183424, 7040783973435600313488769024,
    7040783973435600313488769024, 232113757366008801543585792, 4332790137498830962146934784, 5145188288279861767549485056
  ]
def positiveScales : Array ℕ := #[
    5, 2, 4, 6, 1, 1,
    2, 6, 6, 1, 10, 5,
    4, 6, 2, 5, 2, 6,
    6, 1, 2, 7
  ]
def negativeArguments : Array ℕ := #[
    27, 17076716881, 61090827147, 4269177801, 2313, 2313,
    91, 27, 27, 91, 5622051057, 20112516459,
    1405512297, 897, 897, 3, 2313, 2313,
    1123, 45, 103744203, 59826485, 103744203, 59826485,
    1135377, 91, 315845565, 1129916655, 78961365, 27,
    27, 7, 27, 27, 45, 7,
    57, 57, 91, 91, 50865, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1044511908147039606946136064, 19688114120187663023243001856, 70432928351996052803495657472, 19688107575052281370172719104, 44739926732298196497526161408, 44739926732298196497526161408,
    3520391986717800156744384512, 1044511908147039606946136064, 1044511908147039606946136064, 3520391986717800156744384512, 12963567127225908821716107264, 46376305474680508257788755968,
    12963562817605324601322110976, 8675251681554578957691518976, 8675251681554578957691518976, 1856910058928070412348686336, 44739926732298196497526161408, 44739926732298196497526161408,
    43443958253671314022241140736, 3481706360490132023153786880, 1913742761871970685889282048, 1103603857624623384111349760, 1913742761871970685889282048, 1103603857624623384111349760,
    21446665160884356695162093568, 3520391986717800156744384512, 728290288046399372006522880, 2605410419925871250437570560, 728290045932883404568657920, 1044511908147039606946136064,
    1044511908147039606946136064, 135399691796838467567091712, 1044511908147039606946136064, 1044511908147039606946136064, 3481706360490132023153786880, 135399691796838467567091712,
    1102540347488541807332032512, 1102540347488541807332032512, 3520391986717800156744384512, 3520391986717800156744384512, 240203171151164503794647040, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    4, 33, 35, 31, 11, 11,
    6, 4, 4, 6, 32, 34,
    30, 9, 9, 1, 11, 11,
    10, 5, 26, 25, 26, 25,
    20, 6, 28, 30, 26, 4,
    4, 2, 4, 4, 5, 2,
    5, 5, 6, 6, 15, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5209453365628949, 2321928094887362, 4392317422778759, 6507794640198673, 1584962500720924, 1584962500720924,
    2807354922011143, 6507794640198673, 6507794640198673, 1584962500720924, 10133142212400601, 5491853096329661,
    4392317422778759, 6507794640198673, 2807354922011143, 5491853096329661, 2807354922011143, 6507794640198673,
    6507794640198673, 1584962500720924, 2807354922011143, 7055282435501189
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4754887502413606, 33991311602816402, 35830236724158497, 31991311123205252, 11175549550636191, 11175549550636191,
    6507794640199048, 4754887502413606, 4754887502413606, 6507794640199048, 32388449409687131, 34227374550446732,
    30388448930076140, 9808964175693987, 9808964175693987, 1584962500724866, 11175549550636191, 11175549550636191,
    10133142212400602, 5491853096329881, 26628455483167676, 25834280967961518, 26628455483167676, 25834280967961518,
    20114739990823223, 6507794640199048, 28234644073608092, 30073569214367696, 26234643593997100, 4754887502413606,
    4754887502413606, 2807354922807594, 4754887502413606, 4754887502413606, 5491853096329881, 2807354922807594,
    5832890015409720, 5832890015409720, 6507794640199048, 6507794640199048, 15634385664648197, 0
  ]

abbrev PositiveTerm := Fin 22
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 19975879 / 100000000000
noncomputable def negativeCeiling : ℝ := 58683557 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1044511908147039606946136064, coefficient := (-1044511908147039606946136064) }, { argument := 19688114120187663023243001856, coefficient := (-19688114120187663023243001856) }, { argument := 70432928351996052803495657472, coefficient := (-70432928351996052803495657472) }, { argument := 19688107575052281370172719104, coefficient := (-19688107575052281370172719104) }, { argument := 44739926732298196497526161408, coefficient := (-44739926732298196497526161408) }, { argument := 44739926732298196497526161408, coefficient := (-44739926732298196497526161408) }, { argument := 3520391986717800156744384512, coefficient := (-3520391986717800156744384512) }, { argument := 1044511908147039606946136064, coefficient := (-1044511908147039606946136064) }, { argument := 1044511908147039606946136064, coefficient := (-1044511908147039606946136064) }, { argument := 3520391986717800156744384512, coefficient := (-3520391986717800156744384512) }, { argument := 12963567127225908821716107264, coefficient := (-12963567127225908821716107264) }, { argument := 46376305474680508257788755968, coefficient := (-46376305474680508257788755968) }, { argument := 12963562817605324601322110976, coefficient := (-12963562817605324601322110976) }, { argument := 8675251681554578957691518976, coefficient := (-8675251681554578957691518976) }, { argument := 8675251681554578957691518976, coefficient := (-8675251681554578957691518976) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 44739926732298196497526161408, coefficient := (-44739926732298196497526161408) }, { argument := 44739926732298196497526161408, coefficient := (-44739926732298196497526161408) }, { argument := 43443958253671314022241140736, coefficient := (-43443958253671314022241140736) }, { argument := 3481706360490132023153786880, coefficient := (-3481706360490132023153786880) }, { argument := 1913742761871970685889282048, coefficient := (-1913742761871970685889282048) }, { argument := 1103603857624623384111349760, coefficient := (-1103603857624623384111349760) }, { argument := 1913742761871970685889282048, coefficient := (-1913742761871970685889282048) }, { argument := 1103603857624623384111349760, coefficient := (-1103603857624623384111349760) }, { argument := 21446665160884356695162093568, coefficient := (-21446665160884356695162093568) }, { argument := 3520391986717800156744384512, coefficient := (-3520391986717800156744384512) }, { argument := 728290288046399372006522880, coefficient := (-728290288046399372006522880) }, { argument := 2605410419925871250437570560, coefficient := (-2605410419925871250437570560) }, { argument := 728290045932883404568657920, coefficient := (-728290045932883404568657920) }, { argument := 1044511908147039606946136064, coefficient := (-1044511908147039606946136064) }, { argument := 1044511908147039606946136064, coefficient := (-1044511908147039606946136064) }, { argument := 135399691796838467567091712, coefficient := (-135399691796838467567091712) }, { argument := 1044511908147039606946136064, coefficient := (-1044511908147039606946136064) }, { argument := 1044511908147039606946136064, coefficient := (-1044511908147039606946136064) }, { argument := 3481706360490132023153786880, coefficient := (-3481706360490132023153786880) }, { argument := 135399691796838467567091712, coefficient := (-135399691796838467567091712) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 3520391986717800156744384512, coefficient := (-3520391986717800156744384512) }, { argument := 3520391986717800156744384512, coefficient := (-3520391986717800156744384512) }, { argument := 240203171151164503794647040, coefficient := (-240203171151164503794647040) }, { argument := 2931442013027780490961126162432, coefficient := 2931442013027780490961126162432 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 3249592603124123221610201088, coefficient := 3249592603124123221610201088 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 270799383593676935134183424, coefficient := 270799383593676935134183424 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 86887916507342628044482281472, coefficient := 86887916507342628044482281472 }, { argument := 6963412720980264046307573760, coefficient := 6963412720980264046307573760 }, { argument := 3249592603124123221610201088, coefficient := 3249592603124123221610201088 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 270799383593676935134183424, coefficient := 270799383593676935134183424 }, { argument := 6963412720980264046307573760, coefficient := 6963412720980264046307573760 }, { argument := 270799383593676935134183424, coefficient := 270799383593676935134183424 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 4332790137498830962146934784, coefficient := 4332790137498830962146934784 }, { argument := 5145188288279861767549485056, coefficient := 5145188288279861767549485056 }] }

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


end Parent1

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-78563685353341076325556864155648)
def positiveArguments : Array ℕ := #[
    203, 2093, 63, 203, 63, 63,
    5397, 63, 2093, 5397, 7, 63,
    63, 133, 105, 1869, 105, 3325,
    5677, 105, 5677, 5677, 1869, 105,
    483, 541, 483, 541, 3, 1,
    7, 7, 21056371, 75327777, 5264091, 13823,
    510465, 4083719, 110585, 6573, 1049361, 41884179,
    1049361, 26289
  ]
def positiveCoefficients : Array ℕ := #[
    3926591062108315559445659648, 40484507847254701802560421888, 4874388904686184832415301632, 3926591062108315559445659648, 4874388904686184832415301632, 4874388904686184832415301632,
    208786324750724916988455419904, 4874388904686184832415301632, 40484507847254701802560421888, 208786324750724916988455419904, 4332790137498830962146934784, 4874388904686184832415301632,
    4874388904686184832415301632, 5145188288279861767549485056, 8123981507810308054025502720, 144606870839023483361653948416, 8123981507810308054025502720, 128629707206996544188737126400,
    219618300094471994393822756864, 8123981507810308054025502720, 219618300094471994393822756864, 219618300094471994393822756864, 144606870839023483361653948416, 8123981507810308054025502720,
    149481259743709668194069250048, 167431390313347682180106551296, 149481259743709668194069250048, 167431390313347682180106551296, 475368975085586025561263702016, 158456325028528675187087900672,
    277298568799925181577403826176, 277298568799925181577403826176, 198871801322536788515914514432, 711450738667757909452819267584, 198871735209406028340881522688, 8355490802266509540981735424,
    308557159254790840833194065920, 308557083696927114918870646784, 8355566360130235455305154560, 248320919135217423916990464, 39643737718644590168713986048, 395584886144225307593873031168,
    39643737718644590168713986048, 248292584936320206045708288
  ]
def positiveScales : Array ℕ := #[
    7, 11, 5, 7, 5, 5,
    12, 5, 11, 12, 2, 5,
    5, 7, 6, 10, 6, 11,
    12, 6, 12, 12, 10, 6,
    8, 9, 8, 9, 1, 0,
    2, 2, 24, 26, 22, 13,
    18, 21, 16, 12, 20, 25,
    20, 14
  ]
def negativeArguments : Array ℕ := #[
    7, 7, 1, 3, 1, 7,
    7, 1, 3
  ]
def negativeCoefficients : Array ℕ := #[
    554597137599850363154807652352, 1109194275199700726309615304704, 633825300114114700748351602688, 475368975085586025561263702016, 158456325028528675187087900672, 554597137599850363154807652352,
    1109194275199700726309615304704, 633825300114114700748351602688, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    2, 2, 0, 1, 0, 2,
    2, 0, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7665335917183229, 11031356596255709, 5977279922488012, 7665335917183229, 5977279922488012, 5977279922488012,
    12397941971972637, 5977279922488012, 11031356596255709, 12397941971972637, 2807354922011143, 5977279922488012,
    5977279922488012, 7055282435501189, 6714245517659862, 10868050853594526, 6714245517659862, 11699138625271509,
    12470913026274870, 6714245517659862, 12470913026274870, 12470913026274870, 10868050853594526, 6714245517659862,
    8915879378478017, 9079484783826815, 8915879378478017, 9079484783826815, 1584962500720924, 0,
    2807354922011143, 2807354922011143, 24327753477999572, 26166678618759176, 22327752998388580, 13754783136752719,
    18961452519858368, 21961452166578712, 16754796182840014, 12682336269708427, 20001079646967427, 25319902058767568,
    20001079646967427, 14682171644268551
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2807354922807594, 2807354922807594, 0, 1584962500724866, 0, 2807354922807594,
    2807354922807594, 0, 1584962500724866
  ]

abbrev PositiveTerm := Fin 44
abbrev NegativeTerm := Fin 9
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
noncomputable def positiveFloor : ℝ := 961018591 / 1000000000000
noncomputable def negativeCeiling : ℝ := 130585153 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3926591062108315559445659648, coefficient := 3926591062108315559445659648 }, { argument := 40484507847254701802560421888, coefficient := 40484507847254701802560421888 }, { argument := 4874388904686184832415301632, coefficient := 4874388904686184832415301632 }, { argument := 3926591062108315559445659648, coefficient := 3926591062108315559445659648 }, { argument := 4874388904686184832415301632, coefficient := 4874388904686184832415301632 }, { argument := 4874388904686184832415301632, coefficient := 4874388904686184832415301632 }, { argument := 208786324750724916988455419904, coefficient := 208786324750724916988455419904 }, { argument := 4874388904686184832415301632, coefficient := 4874388904686184832415301632 }, { argument := 40484507847254701802560421888, coefficient := 40484507847254701802560421888 }, { argument := 208786324750724916988455419904, coefficient := 208786324750724916988455419904 }, { argument := 4332790137498830962146934784, coefficient := 4332790137498830962146934784 }, { argument := 4874388904686184832415301632, coefficient := 4874388904686184832415301632 }, { argument := 4874388904686184832415301632, coefficient := 4874388904686184832415301632 }, { argument := 5145188288279861767549485056, coefficient := 5145188288279861767549485056 }, { argument := 554597137599850363154807652352, coefficient := (-554597137599850363154807652352) }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 144606870839023483361653948416, coefficient := 144606870839023483361653948416 }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 128629707206996544188737126400, coefficient := 128629707206996544188737126400 }, { argument := 219618300094471994393822756864, coefficient := 219618300094471994393822756864 }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 219618300094471994393822756864, coefficient := 219618300094471994393822756864 }, { argument := 219618300094471994393822756864, coefficient := 219618300094471994393822756864 }, { argument := 144606870839023483361653948416, coefficient := 144606870839023483361653948416 }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 149481259743709668194069250048, coefficient := 149481259743709668194069250048 }, { argument := 167431390313347682180106551296, coefficient := 167431390313347682180106551296 }, { argument := 149481259743709668194069250048, coefficient := 149481259743709668194069250048 }, { argument := 167431390313347682180106551296, coefficient := 167431390313347682180106551296 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 277298568799925181577403826176, coefficient := 277298568799925181577403826176 }, { argument := 277298568799925181577403826176, coefficient := 277298568799925181577403826176 }, { argument := 554597137599850363154807652352, coefficient := (-554597137599850363154807652352) }, { argument := 198871801322536788515914514432, coefficient := 198871801322536788515914514432 }, { argument := 711450738667757909452819267584, coefficient := 711450738667757909452819267584 }, { argument := 198871735209406028340881522688, coefficient := 198871735209406028340881522688 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 8355490802266509540981735424, coefficient := 8355490802266509540981735424 }, { argument := 308557159254790840833194065920, coefficient := 308557159254790840833194065920 }, { argument := 308557083696927114918870646784, coefficient := 308557083696927114918870646784 }, { argument := 8355566360130235455305154560, coefficient := 8355566360130235455305154560 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 248320919135217423916990464, coefficient := 248320919135217423916990464 }, { argument := 39643737718644590168713986048, coefficient := 39643737718644590168713986048 }, { argument := 395584886144225307593873031168, coefficient := 395584886144225307593873031168 }, { argument := 39643737718644590168713986048, coefficient := 39643737718644590168713986048 }, { argument := 248292584936320206045708288, coefficient := 248292584936320206045708288 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk23
