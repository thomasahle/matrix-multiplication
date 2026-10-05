import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 14, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14

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
def constantNumerator : ℤ := (-127813879950920993502798096105472)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    9509, 10537, 9509, 37925, 18833, 37925,
    9596421, 433740771, 1205955, 9509, 37925, 18833,
    37925, 495815085, 22409939835, 62307675, 2710749, 475439907,
    118859991, 677673, 9596421, 433740771, 1205955, 2710749,
    475439907, 118859991, 677673, 693129, 327693591, 12438987429,
    1310775263, 693129, 10537, 42025, 20869, 42025,
    252705753, 11421840303, 31756815, 5278827, 925856661, 231464193,
    1319679, 252705753, 11421840303, 31756815, 163643637, 28701556491,
    7175389983, 40910049, 7087803, 3350931237, 127198677903, 13403734141,
    7087803, 5278827, 925856661, 231464193, 1319679, 14153247,
    6691291713, 253996098147, 26765185209, 14153247
  ]
def negativeCoefficients : Array ℕ := #[
    179619931542429825348141056, 199038302519989806466859008, 179619931542429825348141056, 179095748862831294729420800, 177872655943768056619073536, 179095748862831294729420800,
    22127840276321486128545792, 1000138124621307718498516992, 22245943249410402319073280, 179619931542429825348141056, 179095748862831294729420800, 177872655943768056619073536,
    179095748862831294729420800, 571635873804971724987432960, 25836901552717116061211688960, 574686867276435393242726400, 100008986102128186667040768, 17540636573714540730645479424,
    17540638676643365133534363648, 100006883173303783778156544, 22127840276321486128545792, 1000138124621307718498516992, 22245943249410402319073280, 100008986102128186667040768,
    17540636573714540730645479424, 17540638676643365133534363648, 100006883173303783778156544, 12785973273066227802046464, 1511219951942962915011723264, 14341176102428335121790664704,
    1511220988419395556567154688, 12785973273066227802046464, 199038302519989806466859008, 198457451442596840105574400, 197102132262013251929243648, 198457451442596840105574400,
    582699793943132468051705856, 26336970615027769920460947456, 585809838901140594402263040, 97377170678387971228434432, 17079040874406263342996914176, 17079042921994855524757143552,
    97375123089795789468205056, 582699793943132468051705856, 26336970615027769920460947456, 585809838901140594402263040, 3018692291030027108081467392, 529450267106594163632904339456,
    529450330581840521267471450112, 3018628815783669473514356736, 261493775971741562145079296, 30906885468768983487659114496, 293300182223856918297267142656, 30906906666383767189147615232,
    261493775971741562145079296, 97377170678387971228434432, 17079040874406263342996914176, 17079042921994855524757143552, 97375123089795789468205056, 261081325220997490280497152,
    30858136438061145974271639552, 292837563639907617164306153472, 30858157602241206042161577984, 261081325220997490280497152
  ]
def negativeScales : Array ℕ := #[
    13, 13, 13, 15, 14, 15,
    23, 28, 20, 13, 15, 14,
    15, 28, 34, 25, 21, 28,
    26, 19, 23, 28, 20, 21,
    28, 26, 19, 19, 28, 33,
    30, 19, 13, 15, 14, 15,
    27, 33, 24, 22, 29, 27,
    20, 27, 33, 24, 27, 34,
    32, 25, 22, 31, 36, 33,
    22, 22, 29, 27, 20, 23,
    32, 37, 34, 23
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13215077914822828, 13363176553811964, 13215077914822828, 15210861560021759, 14200975211704646, 15210861560021759,
    23194065020128625, 28692257819964341, 20201744643653310, 13215077914822828, 15210861560021759, 14200975211704646,
    15210861560021759, 28885226928024954, 34383419724457157, 25892906552050300, 21370260103296661, 28824687764016880,
    26824687936980093, 19370229766853884, 23194065020128625, 28692257819964341, 20201744643653310, 21370260103296661,
    28824687764016880, 26824687936980093, 19370229766853884, 19402764355429489, 28287772216163475, 33534149999405926,
    30287773205641476, 19402764355429489, 13363176553811964, 15358960199010894, 14349073850693780, 15358960199010894,
    27912883273077072, 33411076067360029, 24920562897395069, 22331785955482024, 29786213615628785, 27786213788591997,
    20331755619039247, 27912883273077072, 33411076067360029, 24920562897395069, 27285982265868899, 34740409925711307,
    32740410098674518, 25285951929426122, 22756907075443343, 31641914935933328, 36888292722692984, 33641915925411329,
    22756907075443343, 22331785955482024, 29786213615628785, 27786213788591997, 20331755619039247, 23754629734719690,
    32639637595221273, 37886015381838274, 34639638584699274, 23754629734719690
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
noncomputable def negativeCeiling : ℝ := 416852981 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 179619931542429825348141056, coefficient := (-179619931542429825348141056) }, { argument := 199038302519989806466859008, coefficient := (-199038302519989806466859008) }, { argument := 179619931542429825348141056, coefficient := (-179619931542429825348141056) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 177872655943768056619073536, coefficient := (-177872655943768056619073536) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 22127840276321486128545792, coefficient := (-22127840276321486128545792) }, { argument := 1000138124621307718498516992, coefficient := (-1000138124621307718498516992) }, { argument := 22245943249410402319073280, coefficient := (-22245943249410402319073280) }, { argument := 179619931542429825348141056, coefficient := (-179619931542429825348141056) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 177872655943768056619073536, coefficient := (-177872655943768056619073536) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 571635873804971724987432960, coefficient := (-571635873804971724987432960) }, { argument := 25836901552717116061211688960, coefficient := (-25836901552717116061211688960) }, { argument := 574686867276435393242726400, coefficient := (-574686867276435393242726400) }, { argument := 100008986102128186667040768, coefficient := (-100008986102128186667040768) }, { argument := 17540636573714540730645479424, coefficient := (-17540636573714540730645479424) }, { argument := 17540638676643365133534363648, coefficient := (-17540638676643365133534363648) }, { argument := 100006883173303783778156544, coefficient := (-100006883173303783778156544) }, { argument := 22127840276321486128545792, coefficient := (-22127840276321486128545792) }, { argument := 1000138124621307718498516992, coefficient := (-1000138124621307718498516992) }, { argument := 22245943249410402319073280, coefficient := (-22245943249410402319073280) }, { argument := 100008986102128186667040768, coefficient := (-100008986102128186667040768) }, { argument := 17540636573714540730645479424, coefficient := (-17540636573714540730645479424) }, { argument := 17540638676643365133534363648, coefficient := (-17540638676643365133534363648) }, { argument := 100006883173303783778156544, coefficient := (-100006883173303783778156544) }, { argument := 12785973273066227802046464, coefficient := (-12785973273066227802046464) }, { argument := 1511219951942962915011723264, coefficient := (-1511219951942962915011723264) }, { argument := 14341176102428335121790664704, coefficient := (-14341176102428335121790664704) }, { argument := 1511220988419395556567154688, coefficient := (-1511220988419395556567154688) }, { argument := 12785973273066227802046464, coefficient := (-12785973273066227802046464) }, { argument := 199038302519989806466859008, coefficient := (-199038302519989806466859008) }, { argument := 198457451442596840105574400, coefficient := (-198457451442596840105574400) }, { argument := 197102132262013251929243648, coefficient := (-197102132262013251929243648) }, { argument := 198457451442596840105574400, coefficient := (-198457451442596840105574400) }, { argument := 582699793943132468051705856, coefficient := (-582699793943132468051705856) }, { argument := 26336970615027769920460947456, coefficient := (-26336970615027769920460947456) }, { argument := 585809838901140594402263040, coefficient := (-585809838901140594402263040) }, { argument := 97377170678387971228434432, coefficient := (-97377170678387971228434432) }, { argument := 17079040874406263342996914176, coefficient := (-17079040874406263342996914176) }, { argument := 17079042921994855524757143552, coefficient := (-17079042921994855524757143552) }, { argument := 97375123089795789468205056, coefficient := (-97375123089795789468205056) }, { argument := 582699793943132468051705856, coefficient := (-582699793943132468051705856) }, { argument := 26336970615027769920460947456, coefficient := (-26336970615027769920460947456) }, { argument := 585809838901140594402263040, coefficient := (-585809838901140594402263040) }, { argument := 3018692291030027108081467392, coefficient := (-3018692291030027108081467392) }, { argument := 529450267106594163632904339456, coefficient := (-529450267106594163632904339456) }, { argument := 529450330581840521267471450112, coefficient := (-529450330581840521267471450112) }, { argument := 3018628815783669473514356736, coefficient := (-3018628815783669473514356736) }, { argument := 261493775971741562145079296, coefficient := (-261493775971741562145079296) }, { argument := 30906885468768983487659114496, coefficient := (-30906885468768983487659114496) }, { argument := 293300182223856918297267142656, coefficient := (-293300182223856918297267142656) }, { argument := 30906906666383767189147615232, coefficient := (-30906906666383767189147615232) }, { argument := 261493775971741562145079296, coefficient := (-261493775971741562145079296) }, { argument := 97377170678387971228434432, coefficient := (-97377170678387971228434432) }, { argument := 17079040874406263342996914176, coefficient := (-17079040874406263342996914176) }, { argument := 17079042921994855524757143552, coefficient := (-17079042921994855524757143552) }, { argument := 97375123089795789468205056, coefficient := (-97375123089795789468205056) }, { argument := 261081325220997490280497152, coefficient := (-261081325220997490280497152) }, { argument := 30858136438061145974271639552, coefficient := (-30858136438061145974271639552) }, { argument := 292837563639907617164306153472, coefficient := (-292837563639907617164306153472) }, { argument := 30858157602241206042161577984, coefficient := (-30858157602241206042161577984) }, { argument := 261081325220997490280497152, coefficient := (-261081325220997490280497152) }] }

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
def constantNumerator : ℤ := (-17128422062203796379453276291072)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1196035, 42025, 20512905, 439725, 19475, 41025795,
    19475, 37925, 716475, 37925, 439725, 716475,
    149505, 37925, 37925, 42025, 15141453, 16791609,
    535518939, 7087803, 693129, 7087803, 14153247, 474771,
    16791609, 693129, 1747701, 603230697, 5647275, 14564025,
    12186225, 340917075, 2412625851, 12186225, 10997325, 5647275,
    5647275, 10997325, 340917075, 10997325, 1747683, 14564025,
    474771, 400050891, 31756815, 12458282709, 10049625, 1205955,
    31756815, 63111645, 10049625, 974009655, 62307675, 1600204463,
    31756815, 1205955, 62307675, 1205955, 31756815, 31756815,
    474771, 6990879, 1226134497, 306533661
  ]
def negativeCoefficients : Array ℕ := #[
    1412028899084749028290723840, 198457451442596840105574400, 48434727519144579826125373440, 2076542601679854741592473600, 183936174507772681073459200, 48434709810270269064955822080,
    183936174507772681073459200, 179095748862831294729420800, 6766915051628058108965683200, 179095748862831294729420800, 2076542601679854741592473600, 6766915051628058108965683200,
    1412034802042852615347240960, 179095748862831294729420800, 179095748862831294729420800, 198457451442596840105574400, 34913813549387713930592256, 309750513808797970301190144,
    1234822601794684609445756928, 261493775971741562145079296, 12785973273066227802046464, 261493775971741562145079296, 261081325220997490280497152, 35031916522476630121119744,
    309750513808797970301190144, 12785973273066227802046464, 257915144514930056550678528, 22255284569928864393754312704, 104173836638858108102246400, 134329420929053876237107200,
    1798369390397129445133516800, 3144405016441322368244121600, 22252545809506356847190212608, 1798369390397129445133516800, 101432419885203947362713600, 104173836638858108102246400,
    104173836638858108102246400, 101432419885203947362713600, 3144405016441322368244121600, 101432419885203947362713600, 257912488183783442375245824, 134329420929053876237107200,
    35031916522476630121119744, 1844909100684118949797822464, 585809838901140594402263040, 14363422045677745524109737984, 370765720823506705317888000, 22245943249410402319073280,
    585809838901140594402263040, 582102181692905527349084160, 370765720823506705317888000, 8983653415553567469852426240, 574686867276435393242726400, 1844910137160551591353253888,
    585809838901140594402263040, 22245943249410402319073280, 574686867276435393242726400, 22245943249410402319073280, 585809838901140594402263040, 585809838901140594402263040,
    35031916522476630121119744, 128958955763270556491710464, 22618189266105591994779697152, 22618191977776970830083784704
  ]
def negativeScales : Array ℕ := #[
    20, 15, 24, 18, 14, 25,
    14, 15, 19, 15, 18, 19,
    17, 15, 15, 15, 23, 24,
    28, 22, 19, 22, 23, 18,
    24, 19, 20, 29, 22, 23,
    23, 28, 31, 23, 23, 22,
    22, 23, 28, 23, 20, 23,
    18, 28, 24, 33, 23, 20,
    24, 25, 23, 29, 25, 30,
    24, 20, 25, 20, 24, 24,
    18, 22, 30, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    20189828177578928, 15358960199010894, 24290028482324614, 18746242032099458, 14249335707836394, 25290027954841316,
    14249335707836394, 15210861560021759, 19450556839768293, 15210861560021759, 18746242032099458, 19450556839768293,
    17189834208723607, 15210861560021759, 15210861560021759, 15358960199010894, 23852000321487339, 24001237142556879,
    28996362379230506, 22756907075443343, 19402764355429489, 22756907075443343, 23754629734719690, 18856872291268380,
    24001237142556879, 19402764355429489, 20737026956439974, 29168134604951556, 22429123455907472, 23795905787173233,
    23538747947082891, 28344845618479691, 31167957054347492, 23538747947082891, 23390649308092819, 22429123455907472,
    22429123455907472, 23390649308092819, 28344845618479691, 23390649308092819, 20737012097694363, 23795905787173233,
    18856872291268380, 28575608297909707, 24920562897395069, 33536386165072939, 23260638332706879, 20201744643653310,
    24920562897395069, 25911402897174510, 23260638332706879, 29859360834452284, 25892906552050300, 30575609108420636,
    24920562897395069, 20201744643653310, 25892906552050300, 20201744643653310, 24920562897395069, 24920562897395069,
    18856872291268380, 22737042434137255, 30191470093628594, 28191470266591804
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
noncomputable def negativeCeiling : ℝ := 10299809 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1412028899084749028290723840, coefficient := (-1412028899084749028290723840) }, { argument := 198457451442596840105574400, coefficient := (-198457451442596840105574400) }, { argument := 48434727519144579826125373440, coefficient := (-48434727519144579826125373440) }, { argument := 2076542601679854741592473600, coefficient := (-2076542601679854741592473600) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 48434709810270269064955822080, coefficient := (-48434709810270269064955822080) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 6766915051628058108965683200, coefficient := (-6766915051628058108965683200) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 2076542601679854741592473600, coefficient := (-2076542601679854741592473600) }, { argument := 6766915051628058108965683200, coefficient := (-6766915051628058108965683200) }, { argument := 1412034802042852615347240960, coefficient := (-1412034802042852615347240960) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 198457451442596840105574400, coefficient := (-198457451442596840105574400) }, { argument := 34913813549387713930592256, coefficient := (-34913813549387713930592256) }, { argument := 309750513808797970301190144, coefficient := (-309750513808797970301190144) }, { argument := 1234822601794684609445756928, coefficient := (-1234822601794684609445756928) }, { argument := 261493775971741562145079296, coefficient := (-261493775971741562145079296) }, { argument := 12785973273066227802046464, coefficient := (-12785973273066227802046464) }, { argument := 261493775971741562145079296, coefficient := (-261493775971741562145079296) }, { argument := 261081325220997490280497152, coefficient := (-261081325220997490280497152) }, { argument := 35031916522476630121119744, coefficient := (-35031916522476630121119744) }, { argument := 309750513808797970301190144, coefficient := (-309750513808797970301190144) }, { argument := 12785973273066227802046464, coefficient := (-12785973273066227802046464) }, { argument := 257915144514930056550678528, coefficient := (-257915144514930056550678528) }, { argument := 22255284569928864393754312704, coefficient := (-22255284569928864393754312704) }, { argument := 104173836638858108102246400, coefficient := (-104173836638858108102246400) }, { argument := 134329420929053876237107200, coefficient := (-134329420929053876237107200) }, { argument := 1798369390397129445133516800, coefficient := (-1798369390397129445133516800) }, { argument := 3144405016441322368244121600, coefficient := (-3144405016441322368244121600) }, { argument := 22252545809506356847190212608, coefficient := (-22252545809506356847190212608) }, { argument := 1798369390397129445133516800, coefficient := (-1798369390397129445133516800) }, { argument := 101432419885203947362713600, coefficient := (-101432419885203947362713600) }, { argument := 104173836638858108102246400, coefficient := (-104173836638858108102246400) }, { argument := 104173836638858108102246400, coefficient := (-104173836638858108102246400) }, { argument := 101432419885203947362713600, coefficient := (-101432419885203947362713600) }, { argument := 3144405016441322368244121600, coefficient := (-3144405016441322368244121600) }, { argument := 101432419885203947362713600, coefficient := (-101432419885203947362713600) }, { argument := 257912488183783442375245824, coefficient := (-257912488183783442375245824) }, { argument := 134329420929053876237107200, coefficient := (-134329420929053876237107200) }, { argument := 35031916522476630121119744, coefficient := (-35031916522476630121119744) }, { argument := 1844909100684118949797822464, coefficient := (-1844909100684118949797822464) }, { argument := 585809838901140594402263040, coefficient := (-585809838901140594402263040) }, { argument := 14363422045677745524109737984, coefficient := (-14363422045677745524109737984) }, { argument := 370765720823506705317888000, coefficient := (-370765720823506705317888000) }, { argument := 22245943249410402319073280, coefficient := (-22245943249410402319073280) }, { argument := 585809838901140594402263040, coefficient := (-585809838901140594402263040) }, { argument := 582102181692905527349084160, coefficient := (-582102181692905527349084160) }, { argument := 370765720823506705317888000, coefficient := (-370765720823506705317888000) }, { argument := 8983653415553567469852426240, coefficient := (-8983653415553567469852426240) }, { argument := 574686867276435393242726400, coefficient := (-574686867276435393242726400) }, { argument := 1844910137160551591353253888, coefficient := (-1844910137160551591353253888) }, { argument := 585809838901140594402263040, coefficient := (-585809838901140594402263040) }, { argument := 22245943249410402319073280, coefficient := (-22245943249410402319073280) }, { argument := 574686867276435393242726400, coefficient := (-574686867276435393242726400) }, { argument := 22245943249410402319073280, coefficient := (-22245943249410402319073280) }, { argument := 585809838901140594402263040, coefficient := (-585809838901140594402263040) }, { argument := 585809838901140594402263040, coefficient := (-585809838901140594402263040) }, { argument := 35031916522476630121119744, coefficient := (-35031916522476630121119744) }, { argument := 128958955763270556491710464, coefficient := (-128958955763270556491710464) }, { argument := 22618189266105591994779697152, coefficient := (-22618189266105591994779697152) }, { argument := 22618191977776970830083784704, coefficient := (-22618191977776970830083784704) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14
