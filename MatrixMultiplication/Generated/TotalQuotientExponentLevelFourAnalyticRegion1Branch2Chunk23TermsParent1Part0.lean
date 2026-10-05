import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
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

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-59611976279328668598570961600512)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    11693, 1135377, 91, 41908755, 3, 7,
    91, 91, 3, 1123, 45, 1135377,
    91, 7, 45, 7, 91, 91,
    50865, 15065117, 19, 254156771, 299, 9,
    2033253685, 9, 9, 771, 9, 299,
    771, 120521419, 9, 9, 19, 315845565,
    5622051057, 315845565, 12261609535, 17076716881, 631691025, 17076716881,
    17076716881, 5622051057, 315845565, 7478243, 276161565, 2209291979,
    59826485, 5622051057, 20112516459, 1405512297, 12967965, 7478243,
    12967965, 7478243, 315845565, 1129916655, 78961365, 57,
    57, 11693, 15065117, 19
  ]
def negativeCoefficients : Array ℕ := #[
    220874525136779045934989312, 21446665160884356695162093568, 3520391986717800156744384512, 197908499950795658197708308480, 1856910058928070412348686336, 135399691796838467567091712,
    3520391986717800156744384512, 3520391986717800156744384512, 1856910058928070412348686336, 43443958253671314022241140736, 3481706360490132023153786880, 21446665160884356695162093568,
    3520391986717800156744384512, 135399691796838467567091712, 3481706360490132023153786880, 135399691796838467567091712, 3520391986717800156744384512, 3520391986717800156744384512,
    240203171151164503794647040, 2223218861915928152900632576, 1470053796651389076442710016, 37506919273899245044643135488, 11567002242072771943588691968, 1392682544196052809261514752,
    37506910364121857442929704960, 1392682544196052809261514752, 1392682544196052809261514752, 59653235643064261996701548544, 1392682544196052809261514752, 11567002242072771943588691968,
    59653235643064261996701548544, 2223227771693315754614063104, 1392682544196052809261514752, 1392682544196052809261514752, 1470053796651389076442710016, 1456580576092798744013045760,
    12963567127225908821716107264, 728290288046399372006522880, 14136673313993861307207516160, 19688114120187663023243001856, 1456580333979282776575180800, 19688114120187663023243001856,
    19688114120187663023243001856, 12963567127225908821716107264, 728290288046399372006522880, 1103593877936079507243925504, 40754253700400841037782712320, 40754243720712297160915288064,
    1103603857624623384111349760, 12963567127225908821716107264, 46376305474680508257788755968, 12963562817605324601322110976, 1913733852094583084175851520, 1103593877936079507243925504,
    1913733852094583084175851520, 1103593877936079507243925504, 728290288046399372006522880, 2605410419925871250437570560, 728290045932883404568657920, 1102540347488541807332032512,
    1102540347488541807332032512, 220874525136779045934989312, 2223218861915928152900632576, 1470053796651389076442710016
  ]
def negativeScales : Array ℕ := #[
    13, 20, 6, 25, 1, 2,
    6, 6, 1, 10, 5, 20,
    6, 2, 5, 2, 6, 6,
    15, 23, 4, 27, 8, 3,
    30, 3, 3, 9, 3, 8,
    9, 26, 3, 3, 4, 28,
    32, 28, 33, 33, 29, 33,
    33, 32, 28, 22, 28, 31,
    25, 32, 34, 30, 23, 22,
    23, 22, 28, 30, 26, 5,
    5, 13, 23, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13513357500168823, 20114739990823223, 6507794640199048, 25320748327603114, 1584962500724866, 2807354922807594,
    6507794640199048, 6507794640199048, 1584962500724866, 10133142212400602, 5491853096329881, 20114739990823223,
    6507794640199048, 2807354922807594, 5491853096329881, 2807354922807594, 6507794640199048, 6507794640199048,
    15634385664648197, 23844708543134205, 4247927513443586, 27921143431639467, 8224001674198106, 3169925001442313,
    30921143088926847, 3169925001442313, 3169925001442313, 9590587049919383, 3169925001442313, 8224001674198106,
    9590587049919383, 26844714324870993, 3169925001442313, 3169925001442313, 4247927513443586, 28234644073608092,
    32388449409687131, 28234644073608092, 33513429317442008, 33991311602816402, 29234643833802616, 33991311602816402,
    33991311602816402, 32388449409687131, 28234644073608092, 22834267921873894, 28040937304464723, 31040936951185061,
    25834280967961518, 32388449409687131, 34227374550446732, 30388448930076140, 23628448766422962, 22834267921873894,
    23628448766422962, 22834267921873894, 28234644073608092, 30073569214367696, 26234643593997100, 5832890015409720,
    5832890015409720, 13513357500168823, 23844708543134205, 4247927513443586
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
noncomputable def negativeCeiling : ℝ := 56693027 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 220874525136779045934989312, coefficient := (-220874525136779045934989312) }, { argument := 21446665160884356695162093568, coefficient := (-21446665160884356695162093568) }, { argument := 3520391986717800156744384512, coefficient := (-3520391986717800156744384512) }, { argument := 197908499950795658197708308480, coefficient := (-197908499950795658197708308480) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 135399691796838467567091712, coefficient := (-135399691796838467567091712) }, { argument := 3520391986717800156744384512, coefficient := (-3520391986717800156744384512) }, { argument := 3520391986717800156744384512, coefficient := (-3520391986717800156744384512) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 43443958253671314022241140736, coefficient := (-43443958253671314022241140736) }, { argument := 3481706360490132023153786880, coefficient := (-3481706360490132023153786880) }, { argument := 21446665160884356695162093568, coefficient := (-21446665160884356695162093568) }, { argument := 3520391986717800156744384512, coefficient := (-3520391986717800156744384512) }, { argument := 135399691796838467567091712, coefficient := (-135399691796838467567091712) }, { argument := 3481706360490132023153786880, coefficient := (-3481706360490132023153786880) }, { argument := 135399691796838467567091712, coefficient := (-135399691796838467567091712) }, { argument := 3520391986717800156744384512, coefficient := (-3520391986717800156744384512) }, { argument := 3520391986717800156744384512, coefficient := (-3520391986717800156744384512) }, { argument := 240203171151164503794647040, coefficient := (-240203171151164503794647040) }, { argument := 2223218861915928152900632576, coefficient := (-2223218861915928152900632576) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 37506919273899245044643135488, coefficient := (-37506919273899245044643135488) }, { argument := 11567002242072771943588691968, coefficient := (-11567002242072771943588691968) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 37506910364121857442929704960, coefficient := (-37506910364121857442929704960) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 59653235643064261996701548544, coefficient := (-59653235643064261996701548544) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 11567002242072771943588691968, coefficient := (-11567002242072771943588691968) }, { argument := 59653235643064261996701548544, coefficient := (-59653235643064261996701548544) }, { argument := 2223227771693315754614063104, coefficient := (-2223227771693315754614063104) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 1456580576092798744013045760, coefficient := (-1456580576092798744013045760) }, { argument := 12963567127225908821716107264, coefficient := (-12963567127225908821716107264) }, { argument := 728290288046399372006522880, coefficient := (-728290288046399372006522880) }, { argument := 14136673313993861307207516160, coefficient := (-14136673313993861307207516160) }, { argument := 19688114120187663023243001856, coefficient := (-19688114120187663023243001856) }, { argument := 1456580333979282776575180800, coefficient := (-1456580333979282776575180800) }, { argument := 19688114120187663023243001856, coefficient := (-19688114120187663023243001856) }, { argument := 19688114120187663023243001856, coefficient := (-19688114120187663023243001856) }, { argument := 12963567127225908821716107264, coefficient := (-12963567127225908821716107264) }, { argument := 728290288046399372006522880, coefficient := (-728290288046399372006522880) }, { argument := 1103593877936079507243925504, coefficient := (-1103593877936079507243925504) }, { argument := 40754253700400841037782712320, coefficient := (-40754253700400841037782712320) }, { argument := 40754243720712297160915288064, coefficient := (-40754243720712297160915288064) }, { argument := 1103603857624623384111349760, coefficient := (-1103603857624623384111349760) }, { argument := 12963567127225908821716107264, coefficient := (-12963567127225908821716107264) }, { argument := 46376305474680508257788755968, coefficient := (-46376305474680508257788755968) }, { argument := 12963562817605324601322110976, coefficient := (-12963562817605324601322110976) }, { argument := 1913733852094583084175851520, coefficient := (-1913733852094583084175851520) }, { argument := 1103593877936079507243925504, coefficient := (-1103593877936079507243925504) }, { argument := 1913733852094583084175851520, coefficient := (-1913733852094583084175851520) }, { argument := 1103593877936079507243925504, coefficient := (-1103593877936079507243925504) }, { argument := 728290288046399372006522880, coefficient := (-728290288046399372006522880) }, { argument := 2605410419925871250437570560, coefficient := (-2605410419925871250437570560) }, { argument := 728290045932883404568657920, coefficient := (-728290045932883404568657920) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 220874525136779045934989312, coefficient := (-220874525136779045934989312) }, { argument := 2223218861915928152900632576, coefficient := (-2223218861915928152900632576) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }] }

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


end Parent1

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-107330949703341258398435414900736)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    254156771, 299, 9, 2033253685, 9, 9,
    771, 9, 299, 771, 120521419, 9,
    9, 19, 12261609535, 20112516459, 1129916655, 35780694075,
    61090827147, 6130803105, 61090827147, 61090827147, 20112516459, 1129916655,
    252256227, 276161565, 252256227, 276161565, 17076716881, 61090827147,
    4269177801, 897, 897, 1135377, 27, 27,
    91, 631691025, 1405512297, 78961365, 6130803105, 4269177801,
    78961365, 4269177801, 4269177801, 1405512297, 78961365, 2018049333,
    2209291979, 2018049333, 2209291979, 41908755, 27, 27,
    3, 7, 7478243, 276161565, 2209291979, 59826485,
    17076716881, 61090827147, 4269177801, 27
  ]
def negativeCoefficients : Array ℕ := #[
    37506919273899245044643135488, 11567002242072771943588691968, 1392682544196052809261514752, 37506910364121857442929704960, 1392682544196052809261514752, 1392682544196052809261514752,
    59653235643064261996701548544, 1392682544196052809261514752, 11567002242072771943588691968, 59653235643064261996701548544, 2223227771693315754614063104, 1392682544196052809261514752,
    1392682544196052809261514752, 1470053796651389076442710016, 14136673313993861307207516160, 46376305474680508257788755968, 2605410419925871250437570560, 82504663297652589597189734400,
    70432928351996052803495657472, 14136669480529858489441320960, 70432928351996052803495657472, 70432928351996052803495657472, 46376305474680508257788755968, 2605410419925871250437570560,
    37226448483748651076111302656, 40754253700400841037782712320, 37226448483748651076111302656, 40754253700400841037782712320, 19688114120187663023243001856, 70432928351996052803495657472,
    19688107575052281370172719104, 8675251681554578957691518976, 8675251681554578957691518976, 21446665160884356695162093568, 1044511908147039606946136064, 1044511908147039606946136064,
    3520391986717800156744384512, 1456580333979282776575180800, 12963562817605324601322110976, 728290045932883404568657920, 14136669480529858489441320960, 19688107575052281370172719104,
    1456580091865766809137315840, 19688107575052281370172719104, 19688107575052281370172719104, 12963562817605324601322110976, 728290045932883404568657920, 37226439573971263474397872128,
    40754243720712297160915288064, 37226439573971263474397872128, 40754243720712297160915288064, 197908499950795658197708308480, 1044511908147039606946136064, 1044511908147039606946136064,
    1856910058928070412348686336, 135399691796838467567091712, 1103593877936079507243925504, 40754253700400841037782712320, 40754243720712297160915288064, 1103603857624623384111349760,
    19688114120187663023243001856, 70432928351996052803495657472, 19688107575052281370172719104, 1044511908147039606946136064
  ]
def negativeScales : Array ℕ := #[
    27, 8, 3, 30, 3, 3,
    9, 3, 8, 9, 26, 3,
    3, 4, 33, 34, 30, 35,
    35, 32, 35, 35, 34, 30,
    27, 28, 27, 28, 33, 35,
    31, 9, 9, 20, 4, 4,
    6, 29, 30, 26, 32, 31,
    26, 31, 31, 30, 26, 30,
    31, 30, 31, 25, 4, 4,
    1, 2, 22, 28, 31, 25,
    33, 35, 31, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    27921143431639467, 8224001674198106, 3169925001442313, 30921143088926847, 3169925001442313, 3169925001442313,
    9590587049919383, 3169925001442313, 8224001674198106, 9590587049919383, 26844714324870993, 3169925001442313,
    3169925001442313, 4247927513443586, 33513429317442008, 34227374550446732, 30073569214367696, 35058462321977488,
    35830236724158497, 32513428926224065, 35830236724158497, 35830236724158497, 34227374550446732, 30073569214367696,
    27910314647360639, 28040937304464723, 27910314647360639, 28040937304464723, 33991311602816402, 35830236724158497,
    31991311123205252, 9808964175693987, 9808964175693987, 20114739990823223, 4754887502413606, 4754887502413606,
    6507794640199048, 29234643833802616, 30388448930076140, 26234643593997100, 32513428926224065, 31991311123205252,
    26234643593997100, 31991311123205252, 31991311123205252, 30388448930076140, 26234643593997100, 30910314302065966,
    31040936951185061, 30910314302065966, 31040936951185061, 25320748327603114, 4754887502413606, 4754887502413606,
    1584962500724866, 2807354922807594, 22834267921873894, 28040937304464723, 31040936951185061, 25834280967961518,
    33991311602816402, 35830236724158497, 31991311123205252, 4754887502413606
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
noncomputable def negativeCeiling : ℝ := 112146763 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 37506919273899245044643135488, coefficient := (-37506919273899245044643135488) }, { argument := 11567002242072771943588691968, coefficient := (-11567002242072771943588691968) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 37506910364121857442929704960, coefficient := (-37506910364121857442929704960) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 59653235643064261996701548544, coefficient := (-59653235643064261996701548544) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 11567002242072771943588691968, coefficient := (-11567002242072771943588691968) }, { argument := 59653235643064261996701548544, coefficient := (-59653235643064261996701548544) }, { argument := 2223227771693315754614063104, coefficient := (-2223227771693315754614063104) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 14136673313993861307207516160, coefficient := (-14136673313993861307207516160) }, { argument := 46376305474680508257788755968, coefficient := (-46376305474680508257788755968) }, { argument := 2605410419925871250437570560, coefficient := (-2605410419925871250437570560) }, { argument := 82504663297652589597189734400, coefficient := (-82504663297652589597189734400) }, { argument := 70432928351996052803495657472, coefficient := (-70432928351996052803495657472) }, { argument := 14136669480529858489441320960, coefficient := (-14136669480529858489441320960) }, { argument := 70432928351996052803495657472, coefficient := (-70432928351996052803495657472) }, { argument := 70432928351996052803495657472, coefficient := (-70432928351996052803495657472) }, { argument := 46376305474680508257788755968, coefficient := (-46376305474680508257788755968) }, { argument := 2605410419925871250437570560, coefficient := (-2605410419925871250437570560) }, { argument := 37226448483748651076111302656, coefficient := (-37226448483748651076111302656) }, { argument := 40754253700400841037782712320, coefficient := (-40754253700400841037782712320) }, { argument := 37226448483748651076111302656, coefficient := (-37226448483748651076111302656) }, { argument := 40754253700400841037782712320, coefficient := (-40754253700400841037782712320) }, { argument := 19688114120187663023243001856, coefficient := (-19688114120187663023243001856) }, { argument := 70432928351996052803495657472, coefficient := (-70432928351996052803495657472) }, { argument := 19688107575052281370172719104, coefficient := (-19688107575052281370172719104) }, { argument := 8675251681554578957691518976, coefficient := (-8675251681554578957691518976) }, { argument := 8675251681554578957691518976, coefficient := (-8675251681554578957691518976) }, { argument := 21446665160884356695162093568, coefficient := (-21446665160884356695162093568) }, { argument := 1044511908147039606946136064, coefficient := (-1044511908147039606946136064) }, { argument := 1044511908147039606946136064, coefficient := (-1044511908147039606946136064) }, { argument := 3520391986717800156744384512, coefficient := (-3520391986717800156744384512) }, { argument := 1456580333979282776575180800, coefficient := (-1456580333979282776575180800) }, { argument := 12963562817605324601322110976, coefficient := (-12963562817605324601322110976) }, { argument := 728290045932883404568657920, coefficient := (-728290045932883404568657920) }, { argument := 14136669480529858489441320960, coefficient := (-14136669480529858489441320960) }, { argument := 19688107575052281370172719104, coefficient := (-19688107575052281370172719104) }, { argument := 1456580091865766809137315840, coefficient := (-1456580091865766809137315840) }, { argument := 19688107575052281370172719104, coefficient := (-19688107575052281370172719104) }, { argument := 19688107575052281370172719104, coefficient := (-19688107575052281370172719104) }, { argument := 12963562817605324601322110976, coefficient := (-12963562817605324601322110976) }, { argument := 728290045932883404568657920, coefficient := (-728290045932883404568657920) }, { argument := 37226439573971263474397872128, coefficient := (-37226439573971263474397872128) }, { argument := 40754243720712297160915288064, coefficient := (-40754243720712297160915288064) }, { argument := 37226439573971263474397872128, coefficient := (-37226439573971263474397872128) }, { argument := 40754243720712297160915288064, coefficient := (-40754243720712297160915288064) }, { argument := 197908499950795658197708308480, coefficient := (-197908499950795658197708308480) }, { argument := 1044511908147039606946136064, coefficient := (-1044511908147039606946136064) }, { argument := 1044511908147039606946136064, coefficient := (-1044511908147039606946136064) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 135399691796838467567091712, coefficient := (-135399691796838467567091712) }, { argument := 1103593877936079507243925504, coefficient := (-1103593877936079507243925504) }, { argument := 40754253700400841037782712320, coefficient := (-40754253700400841037782712320) }, { argument := 40754243720712297160915288064, coefficient := (-40754243720712297160915288064) }, { argument := 1103603857624623384111349760, coefficient := (-1103603857624623384111349760) }, { argument := 19688114120187663023243001856, coefficient := (-19688114120187663023243001856) }, { argument := 70432928351996052803495657472, coefficient := (-70432928351996052803495657472) }, { argument := 19688107575052281370172719104, coefficient := (-19688107575052281370172719104) }, { argument := 1044511908147039606946136064, coefficient := (-1044511908147039606946136064) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk23
