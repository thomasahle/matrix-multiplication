import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 1,
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

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1140308591621917458853112617893888)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4562098335, 4107, 4107, 4551, 131095839, 5371020795,
    110593477365, 5371020795, 131095839, 35369924949, 143049, 5379545826495,
    1496781, 66291, 1344886949547, 66291, 129093, 2438811,
    129093, 1496781, 2438811, 141481671489, 129093, 129093,
    143049, 8723621341, 258843930695, 69775646929, 1140508683, 4551,
    173532112737, 47619, 2109, 43383044085, 2109, 4107,
    77589, 4107, 47619, 77589, 4562098335, 4107,
    4107, 4551, 17450855609, 517781007555, 139580239221, 51548000255,
    51547992065, 5493103167, 54829428705, 130438717, 70865613155643, 41278075,
    4953369, 130438717, 259226311, 41278075, 4000671029, 255924065,
    7018179282517, 130438717, 4953369, 255924065
  ]
def negativeCoefficients : Array ℕ := #[
    5259741276552591418809384960, 155158073161165063141195776, 155158073161165063141195776, 171931918908318042940243968, 1209145695580615755706662912, 198155692039874029039323709440,
    2040089573173745188228395171840, 198155692039874029039323709440, 1209145695580615755706662912, 163114988360129341170590416896, 5404238424064159025391992832, 6202194068384099565541911429120,
    56546787412768883460808900608, 5008806344254586413777944576, 6202196341591359748329846079488, 5008806344254586413777944576, 4876995650984728876573261824, 184271349191260837012146487296,
    4876995650984728876573261824, 56546787412768883460808900608, 184271349191260837012146487296, 163117261567389523958525067264, 4876995650984728876573261824, 4876995650984728876573261824,
    5404238424064159025391992832, 160922410273377921512878637056, 596853468070459643756428656640, 160891687684597603106614673408, 5259667947286133909521170432, 171931918908318042940243968,
    200068904514347034301339533312, 1798994956382157083447918592, 159351534597953308090957824, 200068977843613491810627747840, 159351534597953308090957824, 155158073161165063141195776,
    5862459088629966439767343104, 155158073161165063141195776, 1798994956382157083447918592, 5862459088629966439767343104, 5259741276552591418809384960, 155158073161165063141195776,
    155158073161165063141195776, 171931918908318042940243968, 160955733643240919127474307072, 596960858287159801384984903680, 160925059416058954464620445696, 59430798013468731593593978880,
    59430788571041608863517245440, 197909899008071131679686656, 31607013719651222662718423040, 1203084814901013671718158336, 319150349001135533956874108928, 761446085380388399821619200,
    45686765122823303989297152, 1203084814901013671718158336, 1195470354047209787719942144, 761446085380388399821619200, 18449838648766810927677833216, 1180241432339602019723509760,
    31607069601562896172614418432, 1203084814901013671718158336, 45686765122823303989297152, 1180241432339602019723509760
  ]
def negativeScales : Array ℕ := #[
    32, 12, 12, 12, 26, 32,
    36, 32, 26, 35, 17, 42,
    20, 16, 40, 16, 16, 21,
    16, 20, 21, 37, 16, 16,
    17, 33, 37, 36, 30, 12,
    37, 15, 11, 35, 11, 12,
    16, 12, 15, 16, 32, 12,
    12, 12, 34, 38, 37, 35,
    35, 32, 35, 26, 46, 25,
    22, 26, 27, 25, 31, 27,
    42, 26, 22, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32087050397937468, 12003869231979056, 12003869231979056, 12151967870968190, 26966046667679686, 32322549161177958,
    36686475343937075, 32322549161177958, 26966046667679686, 35041804106679196, 17126149886812459, 42290621515608320,
    20513431719694343, 16016525395637961, 40290622044379946, 16016525395637961, 16978051264435663, 21217746527569812,
    16978051264435663, 20513431719694343, 21217746527569812, 37041824212262516, 16978051264435663, 16978051264435663,
    17126149886812459, 33022280003456273, 37913291539951451, 36022004544258602, 30087030284304312, 12151967870968190,
    37336411707137963, 15539249703850609, 11042343379793692, 35336412235914536, 11042343379793692, 12003869231979056,
    16243564511725543, 12003869231979056, 15539249703850609, 16243564511725543, 32087050397937468, 12003869231979056,
    12003869231979056, 12151967870968190, 34022578721847238, 38913551096810877, 37022303753246894, 35585197409872209,
    35585197180655299, 32354974241623043, 35674231390470791, 26958796927050616, 46010150977161336, 25298872356564039,
    22239978667510471, 26958796927050616, 27949636926041265, 25298872356564039, 31897594860423681, 27931140579617666,
    42674233941185843, 26958796927050616, 22239978667510471, 27931140579617666
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
noncomputable def negativeCeiling : ℝ := 8767859077 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5259741276552591418809384960, coefficient := (-5259741276552591418809384960) }, { argument := 155158073161165063141195776, coefficient := (-155158073161165063141195776) }, { argument := 155158073161165063141195776, coefficient := (-155158073161165063141195776) }, { argument := 171931918908318042940243968, coefficient := (-171931918908318042940243968) }, { argument := 1209145695580615755706662912, coefficient := (-1209145695580615755706662912) }, { argument := 198155692039874029039323709440, coefficient := (-198155692039874029039323709440) }, { argument := 2040089573173745188228395171840, coefficient := (-2040089573173745188228395171840) }, { argument := 198155692039874029039323709440, coefficient := (-198155692039874029039323709440) }, { argument := 1209145695580615755706662912, coefficient := (-1209145695580615755706662912) }, { argument := 163114988360129341170590416896, coefficient := (-163114988360129341170590416896) }, { argument := 5404238424064159025391992832, coefficient := (-5404238424064159025391992832) }, { argument := 6202194068384099565541911429120, coefficient := (-6202194068384099565541911429120) }, { argument := 56546787412768883460808900608, coefficient := (-56546787412768883460808900608) }, { argument := 5008806344254586413777944576, coefficient := (-5008806344254586413777944576) }, { argument := 6202196341591359748329846079488, coefficient := (-6202196341591359748329846079488) }, { argument := 5008806344254586413777944576, coefficient := (-5008806344254586413777944576) }, { argument := 4876995650984728876573261824, coefficient := (-4876995650984728876573261824) }, { argument := 184271349191260837012146487296, coefficient := (-184271349191260837012146487296) }, { argument := 4876995650984728876573261824, coefficient := (-4876995650984728876573261824) }, { argument := 56546787412768883460808900608, coefficient := (-56546787412768883460808900608) }, { argument := 184271349191260837012146487296, coefficient := (-184271349191260837012146487296) }, { argument := 163117261567389523958525067264, coefficient := (-163117261567389523958525067264) }, { argument := 4876995650984728876573261824, coefficient := (-4876995650984728876573261824) }, { argument := 4876995650984728876573261824, coefficient := (-4876995650984728876573261824) }, { argument := 5404238424064159025391992832, coefficient := (-5404238424064159025391992832) }, { argument := 160922410273377921512878637056, coefficient := (-160922410273377921512878637056) }, { argument := 596853468070459643756428656640, coefficient := (-596853468070459643756428656640) }, { argument := 160891687684597603106614673408, coefficient := (-160891687684597603106614673408) }, { argument := 5259667947286133909521170432, coefficient := (-5259667947286133909521170432) }, { argument := 171931918908318042940243968, coefficient := (-171931918908318042940243968) }, { argument := 200068904514347034301339533312, coefficient := (-200068904514347034301339533312) }, { argument := 1798994956382157083447918592, coefficient := (-1798994956382157083447918592) }, { argument := 159351534597953308090957824, coefficient := (-159351534597953308090957824) }, { argument := 200068977843613491810627747840, coefficient := (-200068977843613491810627747840) }, { argument := 159351534597953308090957824, coefficient := (-159351534597953308090957824) }, { argument := 155158073161165063141195776, coefficient := (-155158073161165063141195776) }, { argument := 5862459088629966439767343104, coefficient := (-5862459088629966439767343104) }, { argument := 155158073161165063141195776, coefficient := (-155158073161165063141195776) }, { argument := 1798994956382157083447918592, coefficient := (-1798994956382157083447918592) }, { argument := 5862459088629966439767343104, coefficient := (-5862459088629966439767343104) }, { argument := 5259741276552591418809384960, coefficient := (-5259741276552591418809384960) }, { argument := 155158073161165063141195776, coefficient := (-155158073161165063141195776) }, { argument := 155158073161165063141195776, coefficient := (-155158073161165063141195776) }, { argument := 171931918908318042940243968, coefficient := (-171931918908318042940243968) }, { argument := 160955733643240919127474307072, coefficient := (-160955733643240919127474307072) }, { argument := 596960858287159801384984903680, coefficient := (-596960858287159801384984903680) }, { argument := 160925059416058954464620445696, coefficient := (-160925059416058954464620445696) }, { argument := 59430798013468731593593978880, coefficient := (-59430798013468731593593978880) }, { argument := 59430788571041608863517245440, coefficient := (-59430788571041608863517245440) }, { argument := 197909899008071131679686656, coefficient := (-197909899008071131679686656) }, { argument := 31607013719651222662718423040, coefficient := (-31607013719651222662718423040) }, { argument := 1203084814901013671718158336, coefficient := (-1203084814901013671718158336) }, { argument := 319150349001135533956874108928, coefficient := (-319150349001135533956874108928) }, { argument := 761446085380388399821619200, coefficient := (-761446085380388399821619200) }, { argument := 45686765122823303989297152, coefficient := (-45686765122823303989297152) }, { argument := 1203084814901013671718158336, coefficient := (-1203084814901013671718158336) }, { argument := 1195470354047209787719942144, coefficient := (-1195470354047209787719942144) }, { argument := 761446085380388399821619200, coefficient := (-761446085380388399821619200) }, { argument := 18449838648766810927677833216, coefficient := (-18449838648766810927677833216) }, { argument := 1180241432339602019723509760, coefficient := (-1180241432339602019723509760) }, { argument := 31607069601562896172614418432, coefficient := (-31607069601562896172614418432) }, { argument := 1203084814901013671718158336, coefficient := (-1203084814901013671718158336) }, { argument := 45686765122823303989297152, coefficient := (-45686765122823303989297152) }, { argument := 1180241432339602019723509760, coefficient := (-1180241432339602019723509760) }] }

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

end TermShard10


end Parent3

namespace Parent3

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 106675647086638533811936863283314688
def positiveArguments : Array ℕ := #[
    6931, 2303, 1715, 1813, 147, 31507,
    56987, 1715, 31507, 931, 931, 1813,
    1813, 56987, 1813
  ]
def positiveCoefficients : Array ℕ := #[
    1098260788772732247721706239557632, 44546498601159855829573173248, 33172924490225424553937469440, 35068520175381163099876753408, 45494296443737725102542815232, 609434012777569942519479795712,
    1102288890918061964463693627392, 33172924490225424553937469440, 609434012777569942519479795712, 36016318017959032372846395392, 36016318017959032372846395392, 35068520175381163099876753408,
    35068520175381163099876753408, 1102288890918061964463693627392, 35068520175381163099876753408
  ]
def positiveScales : Array ℕ := #[
    12, 11, 10, 10, 7, 14,
    15, 10, 14, 9, 9, 10,
    10, 15, 10
  ]
def negativeArguments : Array ℕ := #[
    4953369, 130438717, 130438717, 5493103167, 20173192304025, 5781,
    388075000912893, 60489, 2679, 776150136344385, 2679, 5217,
    98559, 5217, 60489, 98559, 5043343194315, 5217,
    5217, 5781, 10594395388541, 38499252588025, 5296865319877, 1509518655,
    369, 229809652221, 3861, 171, 57452434113, 171,
    333, 6291, 333, 3861, 6291, 6038158851,
    333, 333, 369, 20714986587, 38414089735, 20711040919,
    25744640003, 25744635901, 854114511, 25342497985, 6831613127, 51548000255,
    51547992065
  ]
def negativeCoefficients : Array ℕ := #[
    45686765122823303989297152, 1203084814901013671718158336, 1203084814901013671718158336, 197909899008071131679686656, 11356497667910043456818380800, 218400005099755351843012608,
    436933607375777452457283551232, 2285209809458415754650058752, 202419516921724472439865344, 436933683103016493807430533120, 202419516921724472439865344, 197092687529047512638816256,
    7446907490962389801866625024, 197092687529047512638816256, 2285209809458415754650058752, 7446907490962389801866625024, 11356599265309280500312965120, 197092687529047512638816256,
    197092687529047512638816256, 218400005099755351843012608, 23856457562024474394039943168, 86692609804735996876763955200, 23854960680829760299432148992, 6961426075818815804009349120,
    223046813718899082733289472, 264952490011811552889925533696, 2333831294766041621770272768, 206726315154101588874756096, 264952587123542807429253169152, 206726315154101588874756096,
    201286148965835757588578304, 7605352331195632138076553216, 201286148965835757588578304, 2333831294766041621770272768, 7605352331195632138076553216, 6961523187550070343336984576,
    201286148965835757588578304, 201286148965835757588578304, 223046813718899082733289472, 191062028030357550529612087296, 708614882166058170103638261760, 191025635666459637820059287552,
    59363098175640762892058361856, 59363088717072739097485770752, 7877815897029290817264549888, 29217910907362187706483343360, 7876313685272726775321853952, 59430798013468731593593978880,
    59430788571041608863517245440
  ]
def negativeScales : Array ℕ := #[
    22, 26, 26, 32, 44, 12,
    48, 15, 11, 49, 11, 12,
    16, 12, 15, 16, 42, 12,
    12, 12, 43, 45, 42, 30,
    8, 37, 11, 7, 35, 7,
    8, 12, 8, 11, 12, 32,
    8, 8, 8, 34, 35, 34,
    34, 34, 29, 34, 32, 35,
    35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12758847803091420, 11169298695792845, 10743992861047947, 10824163209679199, 7199672344836364, 14943384770867824,
    15798345225549727, 10743992861047947, 14943384770867824, 9862637357422660, 9862637357422660, 10824163209679199,
    10824163209679199, 15798345225549727, 10824163209679199
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    22239978667510471, 26958796927050616, 26958796927050616, 32354974241623043, 44197504634629204, 12497103357017124,
    48463328828744073, 15884385193190574, 11387478865842383, 49463329078785042, 11387478865842383, 12349004718027745,
    16588699997778354, 12349004718027745, 15884385193190574, 16588699997778354, 42197517541197118, 12349004718027745,
    12349004718027745, 12497103357017124, 43268366490444201, 45129895671602561, 42268275965234234, 30491441440125638,
    8527477006061059, 37741648437749969, 11914758844619001, 7417852514885912, 35741648966533783, 7417852514885912,
    8379378367071265, 12619073646827253, 8379378367071265, 11914758844619001, 12619073646827253, 32491461565547407,
    8379378367071265, 8379378367071265, 8527477006061059, 34269955835042791, 35160916516655879, 34269681012858937,
    34583553045405338, 34583552815534750, 29669854263847217, 34560839685388633, 32669579131736786, 35585197409872209,
    35585197180655299
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 49
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
noncomputable def positiveFloor : ℝ := 16935366019 / 100000000000
noncomputable def negativeCeiling : ℝ := 1422163217 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 45686765122823303989297152, coefficient := (-45686765122823303989297152) }, { argument := 1203084814901013671718158336, coefficient := (-1203084814901013671718158336) }, { argument := 1203084814901013671718158336, coefficient := (-1203084814901013671718158336) }, { argument := 197909899008071131679686656, coefficient := (-197909899008071131679686656) }, { argument := 11356497667910043456818380800, coefficient := (-11356497667910043456818380800) }, { argument := 218400005099755351843012608, coefficient := (-218400005099755351843012608) }, { argument := 436933607375777452457283551232, coefficient := (-436933607375777452457283551232) }, { argument := 2285209809458415754650058752, coefficient := (-2285209809458415754650058752) }, { argument := 202419516921724472439865344, coefficient := (-202419516921724472439865344) }, { argument := 436933683103016493807430533120, coefficient := (-436933683103016493807430533120) }, { argument := 202419516921724472439865344, coefficient := (-202419516921724472439865344) }, { argument := 197092687529047512638816256, coefficient := (-197092687529047512638816256) }, { argument := 7446907490962389801866625024, coefficient := (-7446907490962389801866625024) }, { argument := 197092687529047512638816256, coefficient := (-197092687529047512638816256) }, { argument := 2285209809458415754650058752, coefficient := (-2285209809458415754650058752) }, { argument := 7446907490962389801866625024, coefficient := (-7446907490962389801866625024) }, { argument := 11356599265309280500312965120, coefficient := (-11356599265309280500312965120) }, { argument := 197092687529047512638816256, coefficient := (-197092687529047512638816256) }, { argument := 197092687529047512638816256, coefficient := (-197092687529047512638816256) }, { argument := 218400005099755351843012608, coefficient := (-218400005099755351843012608) }, { argument := 23856457562024474394039943168, coefficient := (-23856457562024474394039943168) }, { argument := 86692609804735996876763955200, coefficient := (-86692609804735996876763955200) }, { argument := 23854960680829760299432148992, coefficient := (-23854960680829760299432148992) }, { argument := 6961426075818815804009349120, coefficient := (-6961426075818815804009349120) }, { argument := 223046813718899082733289472, coefficient := (-223046813718899082733289472) }, { argument := 264952490011811552889925533696, coefficient := (-264952490011811552889925533696) }, { argument := 2333831294766041621770272768, coefficient := (-2333831294766041621770272768) }, { argument := 206726315154101588874756096, coefficient := (-206726315154101588874756096) }, { argument := 264952587123542807429253169152, coefficient := (-264952587123542807429253169152) }, { argument := 206726315154101588874756096, coefficient := (-206726315154101588874756096) }, { argument := 201286148965835757588578304, coefficient := (-201286148965835757588578304) }, { argument := 7605352331195632138076553216, coefficient := (-7605352331195632138076553216) }, { argument := 201286148965835757588578304, coefficient := (-201286148965835757588578304) }, { argument := 2333831294766041621770272768, coefficient := (-2333831294766041621770272768) }, { argument := 7605352331195632138076553216, coefficient := (-7605352331195632138076553216) }, { argument := 6961523187550070343336984576, coefficient := (-6961523187550070343336984576) }, { argument := 201286148965835757588578304, coefficient := (-201286148965835757588578304) }, { argument := 201286148965835757588578304, coefficient := (-201286148965835757588578304) }, { argument := 223046813718899082733289472, coefficient := (-223046813718899082733289472) }, { argument := 191062028030357550529612087296, coefficient := (-191062028030357550529612087296) }, { argument := 708614882166058170103638261760, coefficient := (-708614882166058170103638261760) }, { argument := 191025635666459637820059287552, coefficient := (-191025635666459637820059287552) }, { argument := 59363098175640762892058361856, coefficient := (-59363098175640762892058361856) }, { argument := 59363088717072739097485770752, coefficient := (-59363088717072739097485770752) }, { argument := 7877815897029290817264549888, coefficient := (-7877815897029290817264549888) }, { argument := 29217910907362187706483343360, coefficient := (-29217910907362187706483343360) }, { argument := 7876313685272726775321853952, coefficient := (-7876313685272726775321853952) }, { argument := 59430798013468731593593978880, coefficient := (-59430798013468731593593978880) }, { argument := 59430788571041608863517245440, coefficient := (-59430788571041608863517245440) }, { argument := 1098260788772732247721706239557632, coefficient := 1098260788772732247721706239557632 }, { argument := 44546498601159855829573173248, coefficient := 44546498601159855829573173248 }, { argument := 33172924490225424553937469440, coefficient := 33172924490225424553937469440 }, { argument := 35068520175381163099876753408, coefficient := 35068520175381163099876753408 }, { argument := 45494296443737725102542815232, coefficient := 45494296443737725102542815232 }, { argument := 609434012777569942519479795712, coefficient := 609434012777569942519479795712 }, { argument := 1102288890918061964463693627392, coefficient := 1102288890918061964463693627392 }, { argument := 33172924490225424553937469440, coefficient := 33172924490225424553937469440 }, { argument := 609434012777569942519479795712, coefficient := 609434012777569942519479795712 }, { argument := 36016318017959032372846395392, coefficient := 36016318017959032372846395392 }, { argument := 36016318017959032372846395392, coefficient := 36016318017959032372846395392 }, { argument := 35068520175381163099876753408, coefficient := 35068520175381163099876753408 }, { argument := 35068520175381163099876753408, coefficient := 35068520175381163099876753408 }, { argument := 1102288890918061964463693627392, coefficient := 1102288890918061964463693627392 }, { argument := 35068520175381163099876753408, coefficient := 35068520175381163099876753408 }] }

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

end TermShard11


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
