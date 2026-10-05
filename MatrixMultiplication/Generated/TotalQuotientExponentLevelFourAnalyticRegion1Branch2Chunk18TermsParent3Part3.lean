import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 18, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 12687962741253333175023515048345600
def positiveArguments : Array ℕ := #[
    1715, 31, 371, 555
  ]
def positiveCoefficients : Array ℕ := #[
    135876298711963338972927874826240, 599627206528856070654263296, 14352367330464877562111721472, 10735261278177907071390842880
  ]
def positiveScales : Array ℕ := #[
    10, 4, 8, 9
  ]
def negativeArguments : Array ℕ := #[
    870619843, 34749907177, 870619843, 21811107, 678004327, 25037797785,
    200302333231, 5424083665, 3167479809, 11331449883, 791869689, 678004327,
    25037797785, 200302333231, 5424083665, 3167479809, 11331449883, 791869689,
    643, 643, 3167479809, 11331449883, 791869689, 323,
    323, 3068913, 41790747, 26477286837, 657654387, 19795617,
    26477280369, 19795617, 19795617, 1695824523, 19795617, 657654387,
    1695824523, 196412049, 19795617, 19795617, 41790747, 3663657315,
    19742247, 1109115, 13215237765, 59966151, 915914025, 59966151,
    59966151, 19742247, 1109115, 31, 31, 3817219257,
    13655849859, 954304497, 371, 371, 31, 31
  ]
def negativeCoefficients : Array ℕ := #[
    16060101429314190255522316288, 160255661069820441178572587008, 16060101429314190255522316288, 100585977198323729304649728, 25013944602073365873755684864, 923731695818373776368855941120,
    923731469619786258523906637824, 25014170800660883718704988160, 7303711174408176559265415168, 26128544496970880254388207616, 7303708746355487857245683712, 25013944602073365873755684864,
    923731695818373776368855941120, 923731469619786258523906637824, 25014170800660883718704988160, 233718757581061649896493285376, 836113423903068168140422643712, 233718679883375611431861878784,
    6218714416097652474688569344, 6218714416097652474688569344, 7303711174408176559265415168, 26128544496970880254388207616, 7303708746355487857245683712, 6247728635768403574881517568,
    6247728635768403574881517568, 905783243127683218856214528, 96362901819768152883462144, 30526233378021104297718054912, 758223885371333624004083712, 91291170145043513258016768,
    30526225920924812500631814144, 91291170145043513258016768, 91291170145043513258016768, 3910305121212697151218384896, 91291170145043513258016768, 758223885371333624004083712,
    3910305121212697151218384896, 905790700223975015942455296, 91291170145043513258016768, 91291170145043513258016768, 96362901819768152883462144, 8447818607947362245416058880,
    364180177848960174262321152, 20459560553312369340579840, 30472263615522051269622497280, 553090120291211051173675008, 8447815806348106050777907200, 553090120291211051173675008,
    553090120291211051173675008, 364180177848960174262321152, 20459560553312369340579840, 299813603264428035327131648, 299813603264428035327131648, 8801908338389340981678833664,
    31488245932246958255288352768, 8801905412274562289501208576, 7176183665232438781055860736, 7176183665232438781055860736, 299813603264428035327131648, 299813603264428035327131648
  ]
def negativeScales : Array ℕ := #[
    29, 35, 29, 24, 29, 34,
    37, 32, 31, 33, 29, 29,
    34, 37, 32, 31, 33, 29,
    9, 9, 31, 33, 29, 8,
    8, 21, 25, 34, 29, 24,
    34, 24, 24, 30, 24, 29,
    30, 27, 24, 24, 25, 31,
    24, 20, 33, 25, 29, 25,
    25, 24, 20, 4, 4, 31,
    33, 29, 8, 8, 4, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10743992861047947, 4954196309696329, 8535275376620750, 9116343961237468
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    29697467661295501, 35016290073027449, 29697467661295501, 24378559658531374, 29336719239719401, 34543388623590196,
    37543388270310535, 32336732285806700, 31560688276969518, 33399613417727297, 29560687797358527, 29336719239719401,
    34543388623590196, 37543388270310535, 32336732285806700, 31560688276969518, 33399613417727297, 29560687797358527,
    9328674927327948, 9328674927327948, 31560688276969518, 33399613417727297, 29560687797358527, 8335390354693926,
    8335390354693926, 21549296317036804, 25316680210944693, 34624036243712819, 29292754371699213, 24238677698943420,
    34624035891284237, 24238677698943420, 24238677698943420, 30659339747443115, 24238677698943420, 29292754371699213,
    30659339747443115, 27549308194350318, 24238677698943420, 24238677698943420, 25316680210944693, 31770637419706612,
    24234782866329446, 20080977530250411, 33621483330677515, 25837645040224812, 29770636941257175, 25837645040224812,
    25837645040224812, 24234782866329446, 20080977530250411, 4954196321574415, 4954196321574415, 31829874910956773,
    33668800050576809, 29829874431345771, 8535275376621650, 8535275376621650, 4954196321574415, 4954196321574415
  ]

abbrev PositiveTerm := Fin 4
abbrev NegativeTerm := Fin 60
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
noncomputable def positiveFloor : ℝ := 17575041469 / 1000000000000
noncomputable def negativeCeiling : ℝ := 2331557503 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 16060101429314190255522316288, coefficient := (-16060101429314190255522316288) }, { argument := 160255661069820441178572587008, coefficient := (-160255661069820441178572587008) }, { argument := 16060101429314190255522316288, coefficient := (-16060101429314190255522316288) }, { argument := 100585977198323729304649728, coefficient := (-100585977198323729304649728) }, { argument := 25013944602073365873755684864, coefficient := (-25013944602073365873755684864) }, { argument := 923731695818373776368855941120, coefficient := (-923731695818373776368855941120) }, { argument := 923731469619786258523906637824, coefficient := (-923731469619786258523906637824) }, { argument := 25014170800660883718704988160, coefficient := (-25014170800660883718704988160) }, { argument := 7303711174408176559265415168, coefficient := (-7303711174408176559265415168) }, { argument := 26128544496970880254388207616, coefficient := (-26128544496970880254388207616) }, { argument := 7303708746355487857245683712, coefficient := (-7303708746355487857245683712) }, { argument := 25013944602073365873755684864, coefficient := (-25013944602073365873755684864) }, { argument := 923731695818373776368855941120, coefficient := (-923731695818373776368855941120) }, { argument := 923731469619786258523906637824, coefficient := (-923731469619786258523906637824) }, { argument := 25014170800660883718704988160, coefficient := (-25014170800660883718704988160) }, { argument := 233718757581061649896493285376, coefficient := (-233718757581061649896493285376) }, { argument := 836113423903068168140422643712, coefficient := (-836113423903068168140422643712) }, { argument := 233718679883375611431861878784, coefficient := (-233718679883375611431861878784) }, { argument := 6218714416097652474688569344, coefficient := (-6218714416097652474688569344) }, { argument := 6218714416097652474688569344, coefficient := (-6218714416097652474688569344) }, { argument := 7303711174408176559265415168, coefficient := (-7303711174408176559265415168) }, { argument := 26128544496970880254388207616, coefficient := (-26128544496970880254388207616) }, { argument := 7303708746355487857245683712, coefficient := (-7303708746355487857245683712) }, { argument := 6247728635768403574881517568, coefficient := (-6247728635768403574881517568) }, { argument := 6247728635768403574881517568, coefficient := (-6247728635768403574881517568) }, { argument := 905783243127683218856214528, coefficient := (-905783243127683218856214528) }, { argument := 96362901819768152883462144, coefficient := (-96362901819768152883462144) }, { argument := 30526233378021104297718054912, coefficient := (-30526233378021104297718054912) }, { argument := 758223885371333624004083712, coefficient := (-758223885371333624004083712) }, { argument := 91291170145043513258016768, coefficient := (-91291170145043513258016768) }, { argument := 30526225920924812500631814144, coefficient := (-30526225920924812500631814144) }, { argument := 91291170145043513258016768, coefficient := (-91291170145043513258016768) }, { argument := 91291170145043513258016768, coefficient := (-91291170145043513258016768) }, { argument := 3910305121212697151218384896, coefficient := (-3910305121212697151218384896) }, { argument := 91291170145043513258016768, coefficient := (-91291170145043513258016768) }, { argument := 758223885371333624004083712, coefficient := (-758223885371333624004083712) }, { argument := 3910305121212697151218384896, coefficient := (-3910305121212697151218384896) }, { argument := 905790700223975015942455296, coefficient := (-905790700223975015942455296) }, { argument := 91291170145043513258016768, coefficient := (-91291170145043513258016768) }, { argument := 91291170145043513258016768, coefficient := (-91291170145043513258016768) }, { argument := 96362901819768152883462144, coefficient := (-96362901819768152883462144) }, { argument := 8447818607947362245416058880, coefficient := (-8447818607947362245416058880) }, { argument := 364180177848960174262321152, coefficient := (-364180177848960174262321152) }, { argument := 20459560553312369340579840, coefficient := (-20459560553312369340579840) }, { argument := 30472263615522051269622497280, coefficient := (-30472263615522051269622497280) }, { argument := 553090120291211051173675008, coefficient := (-553090120291211051173675008) }, { argument := 8447815806348106050777907200, coefficient := (-8447815806348106050777907200) }, { argument := 553090120291211051173675008, coefficient := (-553090120291211051173675008) }, { argument := 553090120291211051173675008, coefficient := (-553090120291211051173675008) }, { argument := 364180177848960174262321152, coefficient := (-364180177848960174262321152) }, { argument := 20459560553312369340579840, coefficient := (-20459560553312369340579840) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 8801908338389340981678833664, coefficient := (-8801908338389340981678833664) }, { argument := 31488245932246958255288352768, coefficient := (-31488245932246958255288352768) }, { argument := 8801905412274562289501208576, coefficient := (-8801905412274562289501208576) }, { argument := 7176183665232438781055860736, coefficient := (-7176183665232438781055860736) }, { argument := 7176183665232438781055860736, coefficient := (-7176183665232438781055860736) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 135876298711963338972927874826240, coefficient := 135876298711963338972927874826240 }, { argument := 599627206528856070654263296, coefficient := 599627206528856070654263296 }, { argument := 14352367330464877562111721472, coefficient := 14352367330464877562111721472 }, { argument := 10735261278177907071390842880, coefficient := 10735261278177907071390842880 }] }

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


end Parent3

namespace Parent3

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1431003983938413675042490497892352)
def positiveArguments : Array ℕ := #[
    161, 31, 643, 323, 31, 371,
    31, 2385, 1855, 265, 2491, 29415,
    2067, 1855, 29415, 265, 2067, 2067,
    2067, 2067, 2067, 2385, 2491, 2705,
    11361, 49231, 1623, 1623, 3787, 49231,
    49231, 1623, 607543, 24345, 11361, 49231,
    3787, 24345, 3787, 49231, 49231, 1623,
    513, 9747, 14877, 153387, 4617, 14877,
    4617, 4617, 395523, 4617, 153387, 395523,
    513, 4617, 4617, 9747, 195, 3471
  ]
def positiveCoefficients : Array ℕ := #[
    12456771645309139016172437504, 599627206528856070654263296, 12437428832195304949377138688, 12495457271536807149763035136, 599627206528856070654263296, 14352367330464877562111721472,
    599627206528856070654263296, 92265218552988498613575352320, 71761836652324387810558607360, 82013527602656443212066979840, 96365894933121320774178701312, 1137937695486858149567429345280,
    2558822061202881028216489771008, 71761836652324387810558607360, 1137937695486858149567429345280, 82013527602656443212066979840, 79963189412590032131765305344, 79963189412590032131765305344,
    79963189412590032131765305344, 2558822061202881028216489771008, 79963189412590032131765305344, 92265218552988498613575352320, 96365894933121320774178701312, 104644618945842301362566594560,
    1758029598290150662891118788608, 3809064129628659769597424041984, 125573542735010761635079913472, 2009176683760172186161278615552, 146502466524179221907593232384, 3809064129628659769597424041984,
    3809064129628659769597424041984, 2009176683760172186161278615552, 47006362830472361772064914276352, 3767206282050322849052397404160, 1758029598290150662891118788608, 3809064129628659769597424041984,
    146502466524179221907593232384, 3767206282050322849052397404160, 146502466524179221907593232384, 3809064129628659769597424041984, 3809064129628659769597424041984, 125573542735010761635079913472,
    317531620076700040511625363456, 377068798841081298107555119104, 287763030694509411713660485632, 2966936075091666003530499489792, 357223072586287545575578533888, 287763030694509411713660485632,
    357223072586287545575578533888, 357223072586287545575578533888, 15301054942445983202153947201536, 357223072586287545575578533888, 2966936075091666003530499489792, 15301054942445983202153947201536,
    317531620076700040511625363456, 357223072586287545575578533888, 357223072586287545575578533888, 377068798841081298107555119104, 7543697114395286050166538240, 134277808636236091692964380672
  ]
def positiveScales : Array ℕ := #[
    7, 4, 9, 8, 4, 8,
    4, 11, 10, 8, 11, 14,
    11, 10, 14, 8, 11, 11,
    11, 11, 11, 11, 11, 11,
    13, 15, 10, 10, 11, 15,
    15, 10, 19, 14, 13, 15,
    11, 14, 11, 15, 15, 10,
    9, 13, 13, 17, 12, 13,
    12, 12, 18, 12, 17, 18,
    9, 12, 12, 13, 7, 11
  ]
def negativeArguments : Array ℕ := #[
    1, 53, 541, 513
  ]
def negativeCoefficients : Array ℕ := #[
    79228162514264337593543950336, 8398185226512019784915658735616, 85724871840434013276214554263552, 40644047369817605185488046522368
  ]
def negativeScales : Array ℕ := #[
    0, 5, 9, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7330916878114616, 4954196309696329, 9328674927327946, 8335390354693924, 4954196309696329, 8535275376620750,
    4954196309696329, 11219773550892873, 10857203471385268, 8049848549450561, 11282509306240836, 14844264415704613,
    11013322673425447, 10857203471385268, 14844264415704613, 8049848549450561, 11013322673425447, 11013322673425447,
    11013322673425447, 11013322673425447, 11013322673425447, 11219773550892873, 11282509306240836, 11401412878714176,
    13471802206605568, 15587279424025264, 10664447284546067, 10664447284546067, 11886839705671529, 15587279424025264,
    15587279424025264, 10664447284546067, 19212626996227416, 14571337880156333, 13471802206605568, 15587279424025264,
    11886839705671529, 14571337880156333, 11886839705671529, 15587279424025264, 15587279424025264, 10664447284546067,
    9002815015607054, 13250742529050639, 13860796010603119, 17226816689805158, 12172740017049366, 13860796010603119,
    12172740017049366, 12172740017049366, 18593402065521795, 12172740017049366, 17226816689805158, 18593402065521795,
    9002815015607054, 12172740017049366, 12172740017049366, 13250742529050639, 7607330313749179, 11761135649810892
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 5727920454700926, 9079484783826816, 9002815015607055
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
noncomputable def positiveFloor : ℝ := 27592863273 / 1000000000000
noncomputable def negativeCeiling : ℝ := 7008019 / 488281250

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 12456771645309139016172437504, coefficient := 12456771645309139016172437504 }, { argument := 599627206528856070654263296, coefficient := 599627206528856070654263296 }, { argument := 12437428832195304949377138688, coefficient := 12437428832195304949377138688 }, { argument := 12495457271536807149763035136, coefficient := 12495457271536807149763035136 }, { argument := 599627206528856070654263296, coefficient := 599627206528856070654263296 }, { argument := 14352367330464877562111721472, coefficient := 14352367330464877562111721472 }, { argument := 599627206528856070654263296, coefficient := 599627206528856070654263296 }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 92265218552988498613575352320, coefficient := 92265218552988498613575352320 }, { argument := 71761836652324387810558607360, coefficient := 71761836652324387810558607360 }, { argument := 82013527602656443212066979840, coefficient := 82013527602656443212066979840 }, { argument := 96365894933121320774178701312, coefficient := 96365894933121320774178701312 }, { argument := 1137937695486858149567429345280, coefficient := 1137937695486858149567429345280 }, { argument := 2558822061202881028216489771008, coefficient := 2558822061202881028216489771008 }, { argument := 71761836652324387810558607360, coefficient := 71761836652324387810558607360 }, { argument := 1137937695486858149567429345280, coefficient := 1137937695486858149567429345280 }, { argument := 82013527602656443212066979840, coefficient := 82013527602656443212066979840 }, { argument := 79963189412590032131765305344, coefficient := 79963189412590032131765305344 }, { argument := 79963189412590032131765305344, coefficient := 79963189412590032131765305344 }, { argument := 79963189412590032131765305344, coefficient := 79963189412590032131765305344 }, { argument := 2558822061202881028216489771008, coefficient := 2558822061202881028216489771008 }, { argument := 79963189412590032131765305344, coefficient := 79963189412590032131765305344 }, { argument := 92265218552988498613575352320, coefficient := 92265218552988498613575352320 }, { argument := 96365894933121320774178701312, coefficient := 96365894933121320774178701312 }, { argument := 8398185226512019784915658735616, coefficient := (-8398185226512019784915658735616) }, { argument := 104644618945842301362566594560, coefficient := 104644618945842301362566594560 }, { argument := 1758029598290150662891118788608, coefficient := 1758029598290150662891118788608 }, { argument := 3809064129628659769597424041984, coefficient := 3809064129628659769597424041984 }, { argument := 125573542735010761635079913472, coefficient := 125573542735010761635079913472 }, { argument := 2009176683760172186161278615552, coefficient := 2009176683760172186161278615552 }, { argument := 146502466524179221907593232384, coefficient := 146502466524179221907593232384 }, { argument := 3809064129628659769597424041984, coefficient := 3809064129628659769597424041984 }, { argument := 3809064129628659769597424041984, coefficient := 3809064129628659769597424041984 }, { argument := 2009176683760172186161278615552, coefficient := 2009176683760172186161278615552 }, { argument := 47006362830472361772064914276352, coefficient := 47006362830472361772064914276352 }, { argument := 3767206282050322849052397404160, coefficient := 3767206282050322849052397404160 }, { argument := 1758029598290150662891118788608, coefficient := 1758029598290150662891118788608 }, { argument := 3809064129628659769597424041984, coefficient := 3809064129628659769597424041984 }, { argument := 146502466524179221907593232384, coefficient := 146502466524179221907593232384 }, { argument := 3767206282050322849052397404160, coefficient := 3767206282050322849052397404160 }, { argument := 146502466524179221907593232384, coefficient := 146502466524179221907593232384 }, { argument := 3809064129628659769597424041984, coefficient := 3809064129628659769597424041984 }, { argument := 3809064129628659769597424041984, coefficient := 3809064129628659769597424041984 }, { argument := 125573542735010761635079913472, coefficient := 125573542735010761635079913472 }, { argument := 85724871840434013276214554263552, coefficient := (-85724871840434013276214554263552) }, { argument := 317531620076700040511625363456, coefficient := 317531620076700040511625363456 }, { argument := 377068798841081298107555119104, coefficient := 377068798841081298107555119104 }, { argument := 287763030694509411713660485632, coefficient := 287763030694509411713660485632 }, { argument := 2966936075091666003530499489792, coefficient := 2966936075091666003530499489792 }, { argument := 357223072586287545575578533888, coefficient := 357223072586287545575578533888 }, { argument := 287763030694509411713660485632, coefficient := 287763030694509411713660485632 }, { argument := 357223072586287545575578533888, coefficient := 357223072586287545575578533888 }, { argument := 357223072586287545575578533888, coefficient := 357223072586287545575578533888 }, { argument := 15301054942445983202153947201536, coefficient := 15301054942445983202153947201536 }, { argument := 357223072586287545575578533888, coefficient := 357223072586287545575578533888 }, { argument := 2966936075091666003530499489792, coefficient := 2966936075091666003530499489792 }, { argument := 15301054942445983202153947201536, coefficient := 15301054942445983202153947201536 }, { argument := 317531620076700040511625363456, coefficient := 317531620076700040511625363456 }, { argument := 357223072586287545575578533888, coefficient := 357223072586287545575578533888 }, { argument := 357223072586287545575578533888, coefficient := 357223072586287545575578533888 }, { argument := 377068798841081298107555119104, coefficient := 377068798841081298107555119104 }, { argument := 40644047369817605185488046522368, coefficient := (-40644047369817605185488046522368) }, { argument := 7543697114395286050166538240, coefficient := 7543697114395286050166538240 }, { argument := 134277808636236091692964380672, coefficient := 134277808636236091692964380672 }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18
