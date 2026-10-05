import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 20, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 503867596507867951165432611733504
def positiveArguments : Array ℕ := #[
    297, 21, 105, 87, 1563, 585,
    21, 2343, 2343, 1677, 87, 61,
    67, 61, 67, 1, 583, 10125049815,
    10125049897, 216604697, 6281930617, 1732794303
  ]
def positiveCoefficients : Array ℕ := #[
    188246114133892066122260425998336, 3249592603124123221610201088, 64991852062482464432204021760, 3365649481807127622381993984, 60465633793845292802104098816, 90524365372743432601998458880,
    3249592603124123221610201088, 90640422251426437002770251776, 90640422251426437002770251776, 64875795183799460031432228864, 3365649481807127622381993984, 37757171198204098384423288832,
    41470991316060239209120661504, 37757171198204098384423288832, 41470991316060239209120661504, 158456325028528675187087900672, 92380037491632217634072246091776, 95628391767483003880096640532480,
    95628392541951107070718455578624, 16366188178318963072161957281792, 59331157186866860575688820260864, 16365779476389336635847292747776
  ]
def positiveScales : Array ℕ := #[
    8, 4, 6, 6, 10, 9,
    4, 11, 11, 10, 6, 5,
    6, 5, 6, 0, 9, 33,
    33, 27, 32, 30
  ]
def negativeArguments : Array ℕ := #[
    868071841, 105, 87, 6299186849, 585, 1736099357,
    2343, 2343, 1677, 87, 42465887513017803, 562036535,
    42465887868944949, 562036535, 865109799, 562036535, 562036937, 105,
    87, 42465887818613301, 562036937, 42465888174538187, 562036937, 6277478481,
    585, 1730177377, 562036535, 562036937, 2343, 2343,
    1677, 87, 3, 1, 1, 583,
    1207, 581
  ]
def negativeCoefficients : Array ℕ := #[
    8198706733322695767339850268672, 32495926031241232216102010880, 1682824740903563811190996992, 29747068845050852911409637883904, 45262182686371716300999229440, 8198497414428342570315753193472,
    45320211125713218501385125888, 45320211125713218501385125888, 32437897591899730015716114432, 1682824740903563811190996992, 23906169397448047086897815617536, 10367744121219500986660290560,
    23906169597817217348978331353088, 10367744121219500986660290560, 8170731037599391428043717214208, 10367744121219500986660290560, 10367751536810618617900040192, 32495926031241232216102010880,
    1682824740903563811190996992, 23906169569483018451760460070912, 10367751536810618617900040192, 23906169769850916446946243641344, 10367751536810618617900040192, 29644553975609852957081286475776,
    45262182686371716300999229440, 8170531654564118188753149755392, 10367744121219500986660290560, 10367751536810618617900040192, 45320211125713218501385125888, 45320211125713218501385125888,
    32437897591899730015716114432, 1682824740903563811190996992, 475368975085586025561263702016, 158456325028528675187087900672, 158456325028528675187087900672, 92380037491632217634072246091776,
    191256784309434110950815096111104, 92063124841575160283698070290432
  ]
def negativeScales : Array ℕ := #[
    29, 6, 6, 32, 9, 30,
    11, 11, 10, 6, 55, 29,
    55, 29, 29, 29, 29, 6,
    6, 55, 29, 55, 29, 32,
    9, 30, 29, 29, 11, 11,
    10, 6, 1, 0, 0, 9,
    10, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8214319120800765, 4392317422778759, 6714245517659862, 6442943495848725, 10610102062999199, 9192292814470766,
    4392317422778759, 11194141238863135, 11194141238863135, 10711666973558447, 6442943495848725, 5930737337099561,
    6066089190457772, 5930737337099561, 6066089190457772, 0, 9187352073200496, 33237209954913025,
    33237209966597016, 27690489286737465, 32548560862709454, 30690453258824125
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    29693239203173130, 6714245517766967, 6442943495848765, 32552518459643026, 9192292814470767, 30693202369658271,
    11194141238863136, 11194141238863136, 10711666973659367, 6442943495848765, 55237153919987635, 29066088674509728,
    55237153932079560, 29066088674509728, 29688308009151618, 29066088674509728, 29066089706405633, 6714245517766967,
    6442943495848765, 55237153930369641, 29066089706405633, 55237153942461489, 29066089706405633, 32547538031979246,
    9192292814470767, 30688272803926411, 29066088674509728, 29066089706405633, 11194141238863136, 11194141238863136,
    10711666973659367, 6442943495848765, 1584962500724866, 0, 0, 9187352073200497,
    10237209960755022, 9182394353404529
  ]

abbrev PositiveTerm := Fin 22
abbrev NegativeTerm := Fin 38
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
noncomputable def positiveFloor : ℝ := 140161301531 / 1000000000000
noncomputable def negativeCeiling : ℝ := 142793951113 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8198706733322695767339850268672, coefficient := (-8198706733322695767339850268672) }, { argument := 32495926031241232216102010880, coefficient := (-32495926031241232216102010880) }, { argument := 1682824740903563811190996992, coefficient := (-1682824740903563811190996992) }, { argument := 29747068845050852911409637883904, coefficient := (-29747068845050852911409637883904) }, { argument := 45262182686371716300999229440, coefficient := (-45262182686371716300999229440) }, { argument := 8198497414428342570315753193472, coefficient := (-8198497414428342570315753193472) }, { argument := 45320211125713218501385125888, coefficient := (-45320211125713218501385125888) }, { argument := 45320211125713218501385125888, coefficient := (-45320211125713218501385125888) }, { argument := 32437897591899730015716114432, coefficient := (-32437897591899730015716114432) }, { argument := 1682824740903563811190996992, coefficient := (-1682824740903563811190996992) }, { argument := 23906169397448047086897815617536, coefficient := (-23906169397448047086897815617536) }, { argument := 10367744121219500986660290560, coefficient := (-10367744121219500986660290560) }, { argument := 23906169597817217348978331353088, coefficient := (-23906169597817217348978331353088) }, { argument := 10367744121219500986660290560, coefficient := (-10367744121219500986660290560) }, { argument := 8170731037599391428043717214208, coefficient := (-8170731037599391428043717214208) }, { argument := 10367744121219500986660290560, coefficient := (-10367744121219500986660290560) }, { argument := 10367751536810618617900040192, coefficient := (-10367751536810618617900040192) }, { argument := 32495926031241232216102010880, coefficient := (-32495926031241232216102010880) }, { argument := 1682824740903563811190996992, coefficient := (-1682824740903563811190996992) }, { argument := 23906169569483018451760460070912, coefficient := (-23906169569483018451760460070912) }, { argument := 10367751536810618617900040192, coefficient := (-10367751536810618617900040192) }, { argument := 23906169769850916446946243641344, coefficient := (-23906169769850916446946243641344) }, { argument := 10367751536810618617900040192, coefficient := (-10367751536810618617900040192) }, { argument := 29644553975609852957081286475776, coefficient := (-29644553975609852957081286475776) }, { argument := 45262182686371716300999229440, coefficient := (-45262182686371716300999229440) }, { argument := 8170531654564118188753149755392, coefficient := (-8170531654564118188753149755392) }, { argument := 10367744121219500986660290560, coefficient := (-10367744121219500986660290560) }, { argument := 10367751536810618617900040192, coefficient := (-10367751536810618617900040192) }, { argument := 45320211125713218501385125888, coefficient := (-45320211125713218501385125888) }, { argument := 45320211125713218501385125888, coefficient := (-45320211125713218501385125888) }, { argument := 32437897591899730015716114432, coefficient := (-32437897591899730015716114432) }, { argument := 1682824740903563811190996992, coefficient := (-1682824740903563811190996992) }, { argument := 188246114133892066122260425998336, coefficient := 188246114133892066122260425998336 }, { argument := 3249592603124123221610201088, coefficient := 3249592603124123221610201088 }, { argument := 64991852062482464432204021760, coefficient := 64991852062482464432204021760 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 60465633793845292802104098816, coefficient := 60465633793845292802104098816 }, { argument := 90524365372743432601998458880, coefficient := 90524365372743432601998458880 }, { argument := 3249592603124123221610201088, coefficient := 3249592603124123221610201088 }, { argument := 90640422251426437002770251776, coefficient := 90640422251426437002770251776 }, { argument := 90640422251426437002770251776, coefficient := 90640422251426437002770251776 }, { argument := 64875795183799460031432228864, coefficient := 64875795183799460031432228864 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 37757171198204098384423288832, coefficient := 37757171198204098384423288832 }, { argument := 41470991316060239209120661504, coefficient := 41470991316060239209120661504 }, { argument := 37757171198204098384423288832, coefficient := 37757171198204098384423288832 }, { argument := 41470991316060239209120661504, coefficient := 41470991316060239209120661504 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 92380037491632217634072246091776, coefficient := 92380037491632217634072246091776 }, { argument := 92380037491632217634072246091776, coefficient := (-92380037491632217634072246091776) }, { argument := 95628391767483003880096640532480, coefficient := 95628391767483003880096640532480 }, { argument := 95628392541951107070718455578624, coefficient := 95628392541951107070718455578624 }, { argument := 191256784309434110950815096111104, coefficient := (-191256784309434110950815096111104) }, { argument := 16366188178318963072161957281792, coefficient := 16366188178318963072161957281792 }, { argument := 59331157186866860575688820260864, coefficient := 59331157186866860575688820260864 }, { argument := 16365779476389336635847292747776, coefficient := 16365779476389336635847292747776 }, { argument := 92063124841575160283698070290432, coefficient := (-92063124841575160283698070290432) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20
