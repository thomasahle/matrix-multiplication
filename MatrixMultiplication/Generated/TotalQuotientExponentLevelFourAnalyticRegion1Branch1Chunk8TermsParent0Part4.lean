import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
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

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-248960421684876140775364016209920)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    590557, 3663, 160765, 590557, 729719603, 14245,
    3663, 14245, 35041505073, 129966903933, 17517362985, 12926842875,
    12926846981, 2415, 7245, 15295, 39445, 33005,
    923335, 28175, 33005, 29785, 15295, 15295,
    29785, 923335, 29785, 2415, 39445, 1476465,
    698034735, 26496841965, 2792140855, 1476465, 621, 1863,
    3933, 10143, 8487, 237429, 7245, 8487,
    7659, 3933, 3933, 7659, 237429, 7659,
    621, 10143, 46361001, 21918290679, 832000837701, 87673222847,
    46361001, 730068787, 7315, 28064772301, 82555, 7315,
    28064772301, 7315, 7315, 303259
  ]
def negativeCoefficients : Array ℕ := #[
    5577653166048098136929337344, 138384227414012083342147584, 1518382495237077025559674880, 5577653166048098136929337344, 6730475381054968371267764224, 134540221096956192138199040,
    138384227414012083342147584, 134540221096956192138199040, 161600419009806484720154836992, 599366553726111591455294226432, 161569155915283905559532666880, 59614540549045198031683584000,
    59614559484627989694538317824, 182472240898083091057213440, 136854180673562318292910080, 144457190710982447086960640, 186273745916793155454238720, 2493787292273802244448583680,
    4360326256460443863387996160, 133052675654852253895884800, 2493787292273802244448583680, 140655685692272382689935360, 144457190710982447086960640, 144457190710982447086960640,
    140655685692272382689935360, 4360326256460443863387996160, 140655685692272382689935360, 182472240898083091057213440, 186273745916793155454238720, 54471943977579146253434880,
    6438234055552333664621690880, 61097557811235287560020295680, 6438238471241696308845608960, 54471943977579146253434880, 187685733495171179373133824, 140764300121378384529850368,
    148584539017010517003730944, 191595852942987245610074112, 2565038357767339451432828928, 4484907006645027973770510336, 136854180673562318292910080, 2565038357767339451432828928,
    144674419569194450766790656, 148584539017010517003730944, 148584539017010517003730944, 144674419569194450766790656, 4484907006645027973770510336, 144674419569194450766790656,
    187685733495171179373133824, 191595852942987245610074112, 1710419040895985192357855232, 202160549344343277069121093632, 1918463315272788029384637284352, 202160687996989264097752121344,
    1710419040895985192357855232, 6733696034996285469303504896, 138176443288765818952744960, 258851836061739863255923294208, 1559419859973214242466693120, 138176443288765818952744960,
    258851836061739863255923294208, 138176443288765818952744960, 138176443288765818952744960, 5728400548914262951440941056
  ]
def negativeScales : Array ℕ := #[
    19, 11, 17, 19, 29, 13,
    11, 13, 35, 36, 34, 33,
    33, 11, 12, 13, 15, 15,
    19, 14, 15, 14, 13, 13,
    14, 19, 14, 11, 15, 20,
    29, 34, 31, 20, 9, 10,
    11, 13, 13, 17, 12, 13,
    12, 11, 11, 12, 17, 12,
    9, 13, 25, 34, 39, 36,
    25, 29, 12, 34, 16, 12,
    34, 12, 12, 18
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19171716788332992, 11838809987105390, 17294593827330713, 19171716788332992, 29442766969568483, 13798168001833534,
    11838809987105390, 13798168001833534, 35028345690557042, 36919353337702177, 34028066560867425, 33589650917394809,
    33589651375643197, 11237807473723136, 12822769975464802, 13900772490874059, 15267554817117188, 15010396977620064,
    19816494649918742, 14782127990393705, 15010396977620064, 14862298340817341, 13900772490874059, 13900772490874059,
    14862298340817341, 19816494649918742, 14862298340817341, 11237807473723136, 15267554817117188, 20493715726727574,
    29378723587461350, 34625101370714141, 31378724576939351, 20493715726727574, 9278449458220482, 10863411961174251,
    11941414479953564, 13308196801614534, 13051038962117409, 17857136635498825, 12822769975464802, 13051038962117409,
    12902940327731866, 11941414479953564, 11941414479953564, 12902940327731866, 17857136635498825, 12902940327731866,
    9278449458220482, 13308196801614534, 25466408380731704, 34351416241465613, 39597794024712565, 36351417230943614,
    25466408380731704, 29443457160062142, 12836642150365173, 34708041303234980, 16333067975145349, 12836642150365173,
    34708041303234980, 12836642150365173, 12836642150365173, 18210190936147628
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
noncomputable def negativeCeiling : ℝ := 14388637 / 8000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5577653166048098136929337344, coefficient := (-5577653166048098136929337344) }, { argument := 138384227414012083342147584, coefficient := (-138384227414012083342147584) }, { argument := 1518382495237077025559674880, coefficient := (-1518382495237077025559674880) }, { argument := 5577653166048098136929337344, coefficient := (-5577653166048098136929337344) }, { argument := 6730475381054968371267764224, coefficient := (-6730475381054968371267764224) }, { argument := 134540221096956192138199040, coefficient := (-134540221096956192138199040) }, { argument := 138384227414012083342147584, coefficient := (-138384227414012083342147584) }, { argument := 134540221096956192138199040, coefficient := (-134540221096956192138199040) }, { argument := 161600419009806484720154836992, coefficient := (-161600419009806484720154836992) }, { argument := 599366553726111591455294226432, coefficient := (-599366553726111591455294226432) }, { argument := 161569155915283905559532666880, coefficient := (-161569155915283905559532666880) }, { argument := 59614540549045198031683584000, coefficient := (-59614540549045198031683584000) }, { argument := 59614559484627989694538317824, coefficient := (-59614559484627989694538317824) }, { argument := 182472240898083091057213440, coefficient := (-182472240898083091057213440) }, { argument := 136854180673562318292910080, coefficient := (-136854180673562318292910080) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 186273745916793155454238720, coefficient := (-186273745916793155454238720) }, { argument := 2493787292273802244448583680, coefficient := (-2493787292273802244448583680) }, { argument := 4360326256460443863387996160, coefficient := (-4360326256460443863387996160) }, { argument := 133052675654852253895884800, coefficient := (-133052675654852253895884800) }, { argument := 2493787292273802244448583680, coefficient := (-2493787292273802244448583680) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 4360326256460443863387996160, coefficient := (-4360326256460443863387996160) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 182472240898083091057213440, coefficient := (-182472240898083091057213440) }, { argument := 186273745916793155454238720, coefficient := (-186273745916793155454238720) }, { argument := 54471943977579146253434880, coefficient := (-54471943977579146253434880) }, { argument := 6438234055552333664621690880, coefficient := (-6438234055552333664621690880) }, { argument := 61097557811235287560020295680, coefficient := (-61097557811235287560020295680) }, { argument := 6438238471241696308845608960, coefficient := (-6438238471241696308845608960) }, { argument := 54471943977579146253434880, coefficient := (-54471943977579146253434880) }, { argument := 187685733495171179373133824, coefficient := (-187685733495171179373133824) }, { argument := 140764300121378384529850368, coefficient := (-140764300121378384529850368) }, { argument := 148584539017010517003730944, coefficient := (-148584539017010517003730944) }, { argument := 191595852942987245610074112, coefficient := (-191595852942987245610074112) }, { argument := 2565038357767339451432828928, coefficient := (-2565038357767339451432828928) }, { argument := 4484907006645027973770510336, coefficient := (-4484907006645027973770510336) }, { argument := 136854180673562318292910080, coefficient := (-136854180673562318292910080) }, { argument := 2565038357767339451432828928, coefficient := (-2565038357767339451432828928) }, { argument := 144674419569194450766790656, coefficient := (-144674419569194450766790656) }, { argument := 148584539017010517003730944, coefficient := (-148584539017010517003730944) }, { argument := 148584539017010517003730944, coefficient := (-148584539017010517003730944) }, { argument := 144674419569194450766790656, coefficient := (-144674419569194450766790656) }, { argument := 4484907006645027973770510336, coefficient := (-4484907006645027973770510336) }, { argument := 144674419569194450766790656, coefficient := (-144674419569194450766790656) }, { argument := 187685733495171179373133824, coefficient := (-187685733495171179373133824) }, { argument := 191595852942987245610074112, coefficient := (-191595852942987245610074112) }, { argument := 1710419040895985192357855232, coefficient := (-1710419040895985192357855232) }, { argument := 202160549344343277069121093632, coefficient := (-202160549344343277069121093632) }, { argument := 1918463315272788029384637284352, coefficient := (-1918463315272788029384637284352) }, { argument := 202160687996989264097752121344, coefficient := (-202160687996989264097752121344) }, { argument := 1710419040895985192357855232, coefficient := (-1710419040895985192357855232) }, { argument := 6733696034996285469303504896, coefficient := (-6733696034996285469303504896) }, { argument := 138176443288765818952744960, coefficient := (-138176443288765818952744960) }, { argument := 258851836061739863255923294208, coefficient := (-258851836061739863255923294208) }, { argument := 1559419859973214242466693120, coefficient := (-1559419859973214242466693120) }, { argument := 138176443288765818952744960, coefficient := (-138176443288765818952744960) }, { argument := 258851836061739863255923294208, coefficient := (-258851836061739863255923294208) }, { argument := 138176443288765818952744960, coefficient := (-138176443288765818952744960) }, { argument := 138176443288765818952744960, coefficient := (-138176443288765818952744960) }, { argument := 5728400548914262951440941056, coefficient := (-5728400548914262951440941056) }] }

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

end TermShard8


end Parent0

namespace Parent0

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-214200296996208937720729162481664)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1881, 82555, 303259, 730068787, 7315, 1881,
    7315, 1476465, 698034735, 26496841965, 2792140855, 1476465,
    1422411269, 7315, 54653127163, 82555, 7315, 54653127163,
    7315, 7315, 303259, 1881, 82555, 303259,
    1422411269, 7315, 1881, 7315, 1730971087, 3210086611,
    1730635915, 2415, 7245, 15295, 39445, 33005,
    923335, 28175, 33005, 29785, 15295, 15295,
    29785, 923335, 29785, 2415, 39445, 45179829,
    21359862891, 810803364129, 85439510163, 45179829, 1421712901, 14245,
    54652451323, 160765, 14245, 54652451323, 14245, 14245,
    590557, 3663, 160765, 590557
  ]
def negativeCoefficients : Array ℕ := #[
    142124341668444842351394816, 1559419859973214242466693120, 5728400548914262951440941056, 6733696034996285469303504896, 138176443288765818952744960, 142124341668444842351394816,
    138176443288765818952744960, 54471943977579146253434880, 6438234055552333664621690880, 61097557811235287560020295680, 6438238471241696308845608960, 54471943977579146253434880,
    6559714161700858212883890176, 138176443288765818952744960, 252043062400941192399240036352, 1559419859973214242466693120, 138176443288765818952744960, 252043062400941192399240036352,
    138176443288765818952744960, 138176443288765818952744960, 5728400548914262951440941056, 142124341668444842351394816, 1559419859973214242466693120, 5728400548914262951440941056,
    6559714161700858212883890176, 138176443288765818952744960, 142124341668444842351394816, 138176443288765818952744960, 7982695160219957670757531648, 29607823083779314372667506688,
    7981149452193789326298972160, 182472240898083091057213440, 136854180673562318292910080, 144457190710982447086960640, 186273745916793155454238720, 2493787292273802244448583680,
    4360326256460443863387996160, 133052675654852253895884800, 2493787292273802244448583680, 140655685692272382689935360, 144457190710982447086960640, 144457190710982447086960640,
    140655685692272382689935360, 4360326256460443863387996160, 140655685692272382689935360, 182472240898083091057213440, 186273745916793155454238720, 1666841485713921875355107328,
    197009962099901410137423740928, 1869585269023799799336621047808, 197010097219995907050675634176, 1666841485713921875355107328, 6556493507759541114848149504, 134540221096956192138199040,
    252039945639062498433398996992, 1518382495237077025559674880, 134540221096956192138199040, 252039945639062498433398996992, 134540221096956192138199040, 134540221096956192138199040,
    5577653166048098136929337344, 138384227414012083342147584, 1518382495237077025559674880, 5577653166048098136929337344
  ]
def negativeScales : Array ℕ := #[
    10, 16, 18, 29, 12, 10,
    12, 20, 29, 34, 31, 20,
    30, 12, 35, 16, 12, 35,
    12, 12, 18, 10, 16, 18,
    30, 12, 10, 12, 30, 31,
    30, 11, 12, 13, 15, 15,
    19, 14, 15, 14, 13, 13,
    14, 19, 14, 11, 15, 25,
    34, 39, 36, 25, 30, 13,
    35, 17, 13, 35, 13, 13,
    19, 11, 17, 19
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    10877284136413052, 16333067975145349, 18210190936147628, 29443457160062142, 12836642150365173, 10877284136413052,
    12836642150365173, 20493715726727574, 29378723587461350, 34625101370714141, 31378724576939351, 20493715726727574,
    30405691513009289, 12836642150365173, 35669584995829904, 16333067975145349, 12836642150365173, 35669584995829904,
    12836642150365173, 12836642150365173, 18210190936147628, 10877284136413052, 16333067975145349, 18210190936147628,
    30405691513009289, 12836642150365173, 10877284136413052, 12836642150365173, 30688934481120788, 31579965077061198,
    30688655101639455, 11237807473723136, 12822769975464802, 13900772490874059, 15267554817117188, 15010396977620064,
    19816494649918742, 14782127990393705, 15010396977620064, 14862298340817341, 13900772490874059, 13900772490874059,
    14862298340817341, 19816494649918742, 14862298340817341, 11237807473723136, 15267554817117188, 25429175474532665,
    34314183335266637, 39560561118510096, 36314184324744638, 25429175474532665, 30404983012247478, 13798168001833534,
    35669567155367765, 17294593827330713, 13798168001833534, 35669567155367765, 13798168001833534, 13798168001833534,
    19171716788332992, 11838809987105390, 17294593827330713, 19171716788332992
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
noncomputable def negativeCeiling : ℝ := 1560135507 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 142124341668444842351394816, coefficient := (-142124341668444842351394816) }, { argument := 1559419859973214242466693120, coefficient := (-1559419859973214242466693120) }, { argument := 5728400548914262951440941056, coefficient := (-5728400548914262951440941056) }, { argument := 6733696034996285469303504896, coefficient := (-6733696034996285469303504896) }, { argument := 138176443288765818952744960, coefficient := (-138176443288765818952744960) }, { argument := 142124341668444842351394816, coefficient := (-142124341668444842351394816) }, { argument := 138176443288765818952744960, coefficient := (-138176443288765818952744960) }, { argument := 54471943977579146253434880, coefficient := (-54471943977579146253434880) }, { argument := 6438234055552333664621690880, coefficient := (-6438234055552333664621690880) }, { argument := 61097557811235287560020295680, coefficient := (-61097557811235287560020295680) }, { argument := 6438238471241696308845608960, coefficient := (-6438238471241696308845608960) }, { argument := 54471943977579146253434880, coefficient := (-54471943977579146253434880) }, { argument := 6559714161700858212883890176, coefficient := (-6559714161700858212883890176) }, { argument := 138176443288765818952744960, coefficient := (-138176443288765818952744960) }, { argument := 252043062400941192399240036352, coefficient := (-252043062400941192399240036352) }, { argument := 1559419859973214242466693120, coefficient := (-1559419859973214242466693120) }, { argument := 138176443288765818952744960, coefficient := (-138176443288765818952744960) }, { argument := 252043062400941192399240036352, coefficient := (-252043062400941192399240036352) }, { argument := 138176443288765818952744960, coefficient := (-138176443288765818952744960) }, { argument := 138176443288765818952744960, coefficient := (-138176443288765818952744960) }, { argument := 5728400548914262951440941056, coefficient := (-5728400548914262951440941056) }, { argument := 142124341668444842351394816, coefficient := (-142124341668444842351394816) }, { argument := 1559419859973214242466693120, coefficient := (-1559419859973214242466693120) }, { argument := 5728400548914262951440941056, coefficient := (-5728400548914262951440941056) }, { argument := 6559714161700858212883890176, coefficient := (-6559714161700858212883890176) }, { argument := 138176443288765818952744960, coefficient := (-138176443288765818952744960) }, { argument := 142124341668444842351394816, coefficient := (-142124341668444842351394816) }, { argument := 138176443288765818952744960, coefficient := (-138176443288765818952744960) }, { argument := 7982695160219957670757531648, coefficient := (-7982695160219957670757531648) }, { argument := 29607823083779314372667506688, coefficient := (-29607823083779314372667506688) }, { argument := 7981149452193789326298972160, coefficient := (-7981149452193789326298972160) }, { argument := 182472240898083091057213440, coefficient := (-182472240898083091057213440) }, { argument := 136854180673562318292910080, coefficient := (-136854180673562318292910080) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 186273745916793155454238720, coefficient := (-186273745916793155454238720) }, { argument := 2493787292273802244448583680, coefficient := (-2493787292273802244448583680) }, { argument := 4360326256460443863387996160, coefficient := (-4360326256460443863387996160) }, { argument := 133052675654852253895884800, coefficient := (-133052675654852253895884800) }, { argument := 2493787292273802244448583680, coefficient := (-2493787292273802244448583680) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 4360326256460443863387996160, coefficient := (-4360326256460443863387996160) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 182472240898083091057213440, coefficient := (-182472240898083091057213440) }, { argument := 186273745916793155454238720, coefficient := (-186273745916793155454238720) }, { argument := 1666841485713921875355107328, coefficient := (-1666841485713921875355107328) }, { argument := 197009962099901410137423740928, coefficient := (-197009962099901410137423740928) }, { argument := 1869585269023799799336621047808, coefficient := (-1869585269023799799336621047808) }, { argument := 197010097219995907050675634176, coefficient := (-197010097219995907050675634176) }, { argument := 1666841485713921875355107328, coefficient := (-1666841485713921875355107328) }, { argument := 6556493507759541114848149504, coefficient := (-6556493507759541114848149504) }, { argument := 134540221096956192138199040, coefficient := (-134540221096956192138199040) }, { argument := 252039945639062498433398996992, coefficient := (-252039945639062498433398996992) }, { argument := 1518382495237077025559674880, coefficient := (-1518382495237077025559674880) }, { argument := 134540221096956192138199040, coefficient := (-134540221096956192138199040) }, { argument := 252039945639062498433398996992, coefficient := (-252039945639062498433398996992) }, { argument := 134540221096956192138199040, coefficient := (-134540221096956192138199040) }, { argument := 134540221096956192138199040, coefficient := (-134540221096956192138199040) }, { argument := 5577653166048098136929337344, coefficient := (-5577653166048098136929337344) }, { argument := 138384227414012083342147584, coefficient := (-138384227414012083342147584) }, { argument := 1518382495237077025559674880, coefficient := (-1518382495237077025559674880) }, { argument := 5577653166048098136929337344, coefficient := (-5577653166048098136929337344) }] }

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

end TermShard9


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
