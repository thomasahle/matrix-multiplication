import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 8, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-227246012103709060034930887622656)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    54653127163, 82555, 7315, 54653127163, 7315, 7315,
    303259, 1881, 82555, 303259, 1422411269, 7315,
    1881, 7315, 40873688624229, 148274366027799, 10219675000545, 2415,
    7245, 15295, 39445, 33005, 923335, 28175,
    33005, 29785, 15295, 15295, 29785, 923335,
    29785, 2415, 39445, 100119, 300357, 634087,
    1635277, 1368293, 38278831, 1168055, 1368293, 1234801,
    634087, 634087, 1234801, 38278831, 1234801, 100119,
    1635277, 45179829, 21359862891, 810803364129, 85439510163, 45179829,
    621, 1863, 3933, 10143, 8487, 237429,
    7245, 8487, 7659, 3933
  ]
def negativeCoefficients : Array ℕ := #[
    252043062400941192399240036352, 1559419859973214242466693120, 138176443288765818952744960, 252043062400941192399240036352, 138176443288765818952744960, 138176443288765818952744960,
    5728400548914262951440941056, 142124341668444842351394816, 1559419859973214242466693120, 5728400548914262951440941056, 6559714161700858212883890176, 138176443288765818952744960,
    142124341668444842351394816, 138176443288765818952744960, 23009841107166925712888168448, 83471047448924013443351052288, 23012662262151017752858460160, 182472240898083091057213440,
    136854180673562318292910080, 144457190710982447086960640, 186273745916793155454238720, 2493787292273802244448583680, 4360326256460443863387996160, 133052675654852253895884800,
    2493787292273802244448583680, 140655685692272382689935360, 144457190710982447086960640, 144457190710982447086960640, 140655685692272382689935360, 4360326256460443863387996160,
    140655685692272382689935360, 182472240898083091057213440, 186273745916793155454238720, 7564777758374816146400477184, 5673583318781112109800357888, 5988782392046729449233711104,
    7722377295007624816117153792, 103385296031122487334139854848, 180766668517831544165028069376, 5515983782148303440083681280, 103385296031122487334139854848, 5831182855413920779517034496,
    5988782392046729449233711104, 5988782392046729449233711104, 5831182855413920779517034496, 180766668517831544165028069376, 5831182855413920779517034496, 7564777758374816146400477184,
    7722377295007624816117153792, 1666841485713921875355107328, 197009962099901410137423740928, 1869585269023799799336621047808, 197010097219995907050675634176, 1666841485713921875355107328,
    187685733495171179373133824, 140764300121378384529850368, 148584539017010517003730944, 191595852942987245610074112, 2565038357767339451432828928, 4484907006645027973770510336,
    136854180673562318292910080, 2565038357767339451432828928, 144674419569194450766790656, 148584539017010517003730944
  ]
def negativeScales : Array ℕ := #[
    35, 16, 12, 35, 12, 12,
    18, 10, 16, 18, 30, 12,
    10, 12, 45, 47, 43, 11,
    12, 13, 15, 15, 19, 14,
    15, 14, 13, 13, 14, 19,
    14, 11, 15, 16, 18, 19,
    20, 20, 25, 20, 20, 20,
    19, 19, 20, 25, 20, 16,
    20, 25, 34, 39, 36, 25,
    9, 10, 11, 13, 13, 17,
    12, 13, 12, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35669584995829904, 16333067975145349, 12836642150365173, 35669584995829904, 12836642150365173, 12836642150365173,
    18210190936147628, 10877284136413052, 16333067975145349, 18210190936147628, 30405691513009289, 12836642150365173,
    10877284136413052, 12836642150365173, 45216237678013808, 47075262531737193, 43216414550891737, 11237807473723136,
    12822769975464802, 13900772490874059, 15267554817117188, 15010396977620064, 19816494649918742, 14782127990393705,
    15010396977620064, 14862298340817341, 13900772490874059, 13900772490874059, 14862298340817341, 19816494649918742,
    14862298340817341, 11237807473723136, 15267554817117188, 16611356260852633, 18196318761566070, 19274321273567343,
    20641103604255928, 20383945764741845, 25190043436139583, 20155676777068724, 20383945764741845, 20235847125752708,
    19274321273567343, 19274321273567343, 20235847125752708, 25190043436139583, 20235847125752708, 16611356260852633,
    20641103604255928, 25429175474532665, 34314183335266637, 39560561118510096, 36314184324744638, 25429175474532665,
    9278449458220482, 10863411961174251, 11941414479953564, 13308196801614534, 13051038962117409, 17857136635498825,
    12822769975464802, 13051038962117409, 12902940327731866, 11941414479953564
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
noncomputable def negativeCeiling : ℝ := 1536135951 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 252043062400941192399240036352, coefficient := (-252043062400941192399240036352) }, { argument := 1559419859973214242466693120, coefficient := (-1559419859973214242466693120) }, { argument := 138176443288765818952744960, coefficient := (-138176443288765818952744960) }, { argument := 252043062400941192399240036352, coefficient := (-252043062400941192399240036352) }, { argument := 138176443288765818952744960, coefficient := (-138176443288765818952744960) }, { argument := 138176443288765818952744960, coefficient := (-138176443288765818952744960) }, { argument := 5728400548914262951440941056, coefficient := (-5728400548914262951440941056) }, { argument := 142124341668444842351394816, coefficient := (-142124341668444842351394816) }, { argument := 1559419859973214242466693120, coefficient := (-1559419859973214242466693120) }, { argument := 5728400548914262951440941056, coefficient := (-5728400548914262951440941056) }, { argument := 6559714161700858212883890176, coefficient := (-6559714161700858212883890176) }, { argument := 138176443288765818952744960, coefficient := (-138176443288765818952744960) }, { argument := 142124341668444842351394816, coefficient := (-142124341668444842351394816) }, { argument := 138176443288765818952744960, coefficient := (-138176443288765818952744960) }, { argument := 23009841107166925712888168448, coefficient := (-23009841107166925712888168448) }, { argument := 83471047448924013443351052288, coefficient := (-83471047448924013443351052288) }, { argument := 23012662262151017752858460160, coefficient := (-23012662262151017752858460160) }, { argument := 182472240898083091057213440, coefficient := (-182472240898083091057213440) }, { argument := 136854180673562318292910080, coefficient := (-136854180673562318292910080) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 186273745916793155454238720, coefficient := (-186273745916793155454238720) }, { argument := 2493787292273802244448583680, coefficient := (-2493787292273802244448583680) }, { argument := 4360326256460443863387996160, coefficient := (-4360326256460443863387996160) }, { argument := 133052675654852253895884800, coefficient := (-133052675654852253895884800) }, { argument := 2493787292273802244448583680, coefficient := (-2493787292273802244448583680) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 4360326256460443863387996160, coefficient := (-4360326256460443863387996160) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 182472240898083091057213440, coefficient := (-182472240898083091057213440) }, { argument := 186273745916793155454238720, coefficient := (-186273745916793155454238720) }, { argument := 7564777758374816146400477184, coefficient := (-7564777758374816146400477184) }, { argument := 5673583318781112109800357888, coefficient := (-5673583318781112109800357888) }, { argument := 5988782392046729449233711104, coefficient := (-5988782392046729449233711104) }, { argument := 7722377295007624816117153792, coefficient := (-7722377295007624816117153792) }, { argument := 103385296031122487334139854848, coefficient := (-103385296031122487334139854848) }, { argument := 180766668517831544165028069376, coefficient := (-180766668517831544165028069376) }, { argument := 5515983782148303440083681280, coefficient := (-5515983782148303440083681280) }, { argument := 103385296031122487334139854848, coefficient := (-103385296031122487334139854848) }, { argument := 5831182855413920779517034496, coefficient := (-5831182855413920779517034496) }, { argument := 5988782392046729449233711104, coefficient := (-5988782392046729449233711104) }, { argument := 5988782392046729449233711104, coefficient := (-5988782392046729449233711104) }, { argument := 5831182855413920779517034496, coefficient := (-5831182855413920779517034496) }, { argument := 180766668517831544165028069376, coefficient := (-180766668517831544165028069376) }, { argument := 5831182855413920779517034496, coefficient := (-5831182855413920779517034496) }, { argument := 7564777758374816146400477184, coefficient := (-7564777758374816146400477184) }, { argument := 7722377295007624816117153792, coefficient := (-7722377295007624816117153792) }, { argument := 1666841485713921875355107328, coefficient := (-1666841485713921875355107328) }, { argument := 197009962099901410137423740928, coefficient := (-197009962099901410137423740928) }, { argument := 1869585269023799799336621047808, coefficient := (-1869585269023799799336621047808) }, { argument := 197010097219995907050675634176, coefficient := (-197010097219995907050675634176) }, { argument := 1666841485713921875355107328, coefficient := (-1666841485713921875355107328) }, { argument := 187685733495171179373133824, coefficient := (-187685733495171179373133824) }, { argument := 140764300121378384529850368, coefficient := (-140764300121378384529850368) }, { argument := 148584539017010517003730944, coefficient := (-148584539017010517003730944) }, { argument := 191595852942987245610074112, coefficient := (-191595852942987245610074112) }, { argument := 2565038357767339451432828928, coefficient := (-2565038357767339451432828928) }, { argument := 4484907006645027973770510336, coefficient := (-4484907006645027973770510336) }, { argument := 136854180673562318292910080, coefficient := (-136854180673562318292910080) }, { argument := 2565038357767339451432828928, coefficient := (-2565038357767339451432828928) }, { argument := 144674419569194450766790656, coefficient := (-144674419569194450766790656) }, { argument := 148584539017010517003730944, coefficient := (-148584539017010517003730944) }] }

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


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-357474355198953258974796681576448)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3933, 7659, 237429, 7659, 621, 10143,
    1476465, 698034735, 26496841965, 2792140855, 1476465, 115317667,
    18865, 4431322077, 212905, 18865, 4431322077, 18865,
    18865, 782089, 4851, 212905, 782089, 115317667,
    18865, 4851, 18865, 27255, 81765, 172615,
    445165, 372485, 10420495, 317975, 372485, 336145,
    172615, 172615, 336145, 10420495, 336145, 27255,
    445165, 885879, 418820841, 15898105179, 1675284513, 885879,
    100119, 300357, 634087, 1635277, 1368293, 38278831,
    1168055, 1368293, 1234801, 634087, 634087, 1234801,
    38278831, 1234801, 100119, 1635277
  ]
def negativeCoefficients : Array ℕ := #[
    148584539017010517003730944, 144674419569194450766790656, 4484907006645027973770510336, 144674419569194450766790656, 187685733495171179373133824, 191595852942987245610074112,
    1743102207282532680109916160, 206023489777674677267894108160, 1955121849959529201920649461760, 206023631079734281883059486720, 1743102207282532680109916160, 8508941961305046111892799488,
    178174887398671713912750080, 326973857050392205447007305728, 2010830872070723628443893760, 178174887398671713912750080, 326973857050392205447007305728, 178174887398671713912750080,
    178174887398671713912750080, 7386621760442075911068581888, 183265598467205191453114368, 2010830872070723628443893760, 7386621760442075911068581888, 8508941961305046111892799488,
    178174887398671713912750080, 183265598467205191453114368, 178174887398671713912750080, 2059329575849794884788551680, 1544497181887346163591413760, 1630302580881087617124270080,
    2102232275346665611554979840, 28144170869947196758776872960, 49209396322910723601093099520, 1501594482390475436824985600, 28144170869947196758776872960, 1587399881384216890357841920,
    1630302580881087617124270080, 1630302580881087617124270080, 1587399881384216890357841920, 49209396322910723601093099520, 1587399881384216890357841920, 2059329575849794884788551680,
    2102232275346665611554979840, 1045861324369519608065949696, 123614093866604806360736464896, 1173073109975717521152389677056, 123614178647840569129835692032, 1045861324369519608065949696,
    7564777758374816146400477184, 5673583318781112109800357888, 5988782392046729449233711104, 7722377295007624816117153792, 103385296031122487334139854848, 180766668517831544165028069376,
    5515983782148303440083681280, 103385296031122487334139854848, 5831182855413920779517034496, 5988782392046729449233711104, 5988782392046729449233711104, 5831182855413920779517034496,
    180766668517831544165028069376, 5831182855413920779517034496, 7564777758374816146400477184, 7722377295007624816117153792
  ]
def negativeScales : Array ℕ := #[
    11, 12, 17, 12, 9, 13,
    20, 29, 34, 31, 20, 26,
    14, 32, 17, 14, 32, 14,
    14, 19, 12, 17, 19, 26,
    14, 12, 14, 14, 16, 17,
    18, 18, 23, 18, 18, 18,
    17, 17, 18, 23, 18, 14,
    18, 19, 28, 33, 30, 19,
    16, 18, 19, 20, 20, 25,
    20, 20, 20, 19, 19, 20,
    25, 20, 16, 20
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11941414479953564, 12902940327731866, 17857136635498825, 12902940327731866, 9278449458220482, 13308196801614534,
    20493715726727574, 29378723587461350, 34625101370714141, 31378724576939351, 20493715726727574, 26781038314509347,
    14203424479697473, 32045090042467562, 17699850305889104, 14203424479697473, 32045090042467562, 14203424479697473,
    14203424479697473, 19576973266822201, 12244066464194818, 17699850305889104, 19576973266822201, 26781038314509347,
    14203424479697473, 12244066464194818, 14203424479697473, 14734233300001342, 16319195800563791, 17397198312565070,
    18763980643541010, 18506822803739902, 23312920475137304, 18278553816066445, 18506822803739902, 18358724164750430,
    17397198312565070, 17397198312565070, 18358724164750430, 23312920475137304, 18358724164750430, 14734233300001342,
    18763980643541010, 19756750132821590, 28641757993312392, 33888135780062040, 30641758982790393, 19756750132821590,
    16611356260852633, 18196318761566070, 19274321273567343, 20641103604255928, 20383945764741845, 25190043436139583,
    20155676777068724, 20383945764741845, 20235847125752708, 19274321273567343, 19274321273567343, 20235847125752708,
    25190043436139583, 20235847125752708, 16611356260852633, 20641103604255928
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
noncomputable def negativeCeiling : ℝ := 504946193 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 148584539017010517003730944, coefficient := (-148584539017010517003730944) }, { argument := 144674419569194450766790656, coefficient := (-144674419569194450766790656) }, { argument := 4484907006645027973770510336, coefficient := (-4484907006645027973770510336) }, { argument := 144674419569194450766790656, coefficient := (-144674419569194450766790656) }, { argument := 187685733495171179373133824, coefficient := (-187685733495171179373133824) }, { argument := 191595852942987245610074112, coefficient := (-191595852942987245610074112) }, { argument := 1743102207282532680109916160, coefficient := (-1743102207282532680109916160) }, { argument := 206023489777674677267894108160, coefficient := (-206023489777674677267894108160) }, { argument := 1955121849959529201920649461760, coefficient := (-1955121849959529201920649461760) }, { argument := 206023631079734281883059486720, coefficient := (-206023631079734281883059486720) }, { argument := 1743102207282532680109916160, coefficient := (-1743102207282532680109916160) }, { argument := 8508941961305046111892799488, coefficient := (-8508941961305046111892799488) }, { argument := 178174887398671713912750080, coefficient := (-178174887398671713912750080) }, { argument := 326973857050392205447007305728, coefficient := (-326973857050392205447007305728) }, { argument := 2010830872070723628443893760, coefficient := (-2010830872070723628443893760) }, { argument := 178174887398671713912750080, coefficient := (-178174887398671713912750080) }, { argument := 326973857050392205447007305728, coefficient := (-326973857050392205447007305728) }, { argument := 178174887398671713912750080, coefficient := (-178174887398671713912750080) }, { argument := 178174887398671713912750080, coefficient := (-178174887398671713912750080) }, { argument := 7386621760442075911068581888, coefficient := (-7386621760442075911068581888) }, { argument := 183265598467205191453114368, coefficient := (-183265598467205191453114368) }, { argument := 2010830872070723628443893760, coefficient := (-2010830872070723628443893760) }, { argument := 7386621760442075911068581888, coefficient := (-7386621760442075911068581888) }, { argument := 8508941961305046111892799488, coefficient := (-8508941961305046111892799488) }, { argument := 178174887398671713912750080, coefficient := (-178174887398671713912750080) }, { argument := 183265598467205191453114368, coefficient := (-183265598467205191453114368) }, { argument := 178174887398671713912750080, coefficient := (-178174887398671713912750080) }, { argument := 2059329575849794884788551680, coefficient := (-2059329575849794884788551680) }, { argument := 1544497181887346163591413760, coefficient := (-1544497181887346163591413760) }, { argument := 1630302580881087617124270080, coefficient := (-1630302580881087617124270080) }, { argument := 2102232275346665611554979840, coefficient := (-2102232275346665611554979840) }, { argument := 28144170869947196758776872960, coefficient := (-28144170869947196758776872960) }, { argument := 49209396322910723601093099520, coefficient := (-49209396322910723601093099520) }, { argument := 1501594482390475436824985600, coefficient := (-1501594482390475436824985600) }, { argument := 28144170869947196758776872960, coefficient := (-28144170869947196758776872960) }, { argument := 1587399881384216890357841920, coefficient := (-1587399881384216890357841920) }, { argument := 1630302580881087617124270080, coefficient := (-1630302580881087617124270080) }, { argument := 1630302580881087617124270080, coefficient := (-1630302580881087617124270080) }, { argument := 1587399881384216890357841920, coefficient := (-1587399881384216890357841920) }, { argument := 49209396322910723601093099520, coefficient := (-49209396322910723601093099520) }, { argument := 1587399881384216890357841920, coefficient := (-1587399881384216890357841920) }, { argument := 2059329575849794884788551680, coefficient := (-2059329575849794884788551680) }, { argument := 2102232275346665611554979840, coefficient := (-2102232275346665611554979840) }, { argument := 1045861324369519608065949696, coefficient := (-1045861324369519608065949696) }, { argument := 123614093866604806360736464896, coefficient := (-123614093866604806360736464896) }, { argument := 1173073109975717521152389677056, coefficient := (-1173073109975717521152389677056) }, { argument := 123614178647840569129835692032, coefficient := (-123614178647840569129835692032) }, { argument := 1045861324369519608065949696, coefficient := (-1045861324369519608065949696) }, { argument := 7564777758374816146400477184, coefficient := (-7564777758374816146400477184) }, { argument := 5673583318781112109800357888, coefficient := (-5673583318781112109800357888) }, { argument := 5988782392046729449233711104, coefficient := (-5988782392046729449233711104) }, { argument := 7722377295007624816117153792, coefficient := (-7722377295007624816117153792) }, { argument := 103385296031122487334139854848, coefficient := (-103385296031122487334139854848) }, { argument := 180766668517831544165028069376, coefficient := (-180766668517831544165028069376) }, { argument := 5515983782148303440083681280, coefficient := (-5515983782148303440083681280) }, { argument := 103385296031122487334139854848, coefficient := (-103385296031122487334139854848) }, { argument := 5831182855413920779517034496, coefficient := (-5831182855413920779517034496) }, { argument := 5988782392046729449233711104, coefficient := (-5988782392046729449233711104) }, { argument := 5988782392046729449233711104, coefficient := (-5988782392046729449233711104) }, { argument := 5831182855413920779517034496, coefficient := (-5831182855413920779517034496) }, { argument := 180766668517831544165028069376, coefficient := (-180766668517831544165028069376) }, { argument := 5831182855413920779517034496, coefficient := (-5831182855413920779517034496) }, { argument := 7564777758374816146400477184, coefficient := (-7564777758374816146400477184) }, { argument := 7722377295007624816117153792, coefficient := (-7722377295007624816117153792) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
