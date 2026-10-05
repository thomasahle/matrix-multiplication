import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 18, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-10898704480174672302665619109576704)
def positiveArguments : Array ℕ := #[
    3369, 174065, 3369, 88717, 88717, 3369,
    243, 1107, 27, 11583, 513, 27,
    513, 999, 18873, 999, 11583, 18873,
    243, 999, 999, 1107, 7, 35,
    29, 521, 195, 7, 781, 781,
    559, 29, 649271, 75887175, 20776665, 92052593,
    1795273379, 3590545441, 11506629, 865833, 409343607, 15538356933,
    1637375551, 865833, 1284039, 225208377, 56302101, 321003,
    355423, 16064473, 44665
  ]
def positiveCoefficients : Array ℕ := #[
    130331874761013942066723422208, 3366906764659526836723688407040, 130331874761013942066723422208, 3432072702040033807757050118144, 3432072702040033807757050118144, 130331874761013942066723422208,
    75204857386586851700121796608, 85649976468057247769583157248, 66848762121410534844552708096, 896191217190159982759784742912, 79382905019175010127906340864, 66848762121410534844552708096,
    79382905019175010127906340864, 77293881202880930914014068736, 2920455295179122741021396434944, 77293881202880930914014068736, 896191217190159982759784742912, 2920455295179122741021396434944,
    75204857386586851700121796608, 77293881202880930914014068736, 77293881202880930914014068736, 85649976468057247769583157248, 541598767187353870268366848, 10831975343747077405367336960,
    560941580301187937063665664, 10077605632307548800350683136, 15087394228790572100333076480, 541598767187353870268366848, 15106737041904406167128375296, 15106737041904406167128375296,
    10812632530633243338572038144, 560941580301187937063665664, 196230118956752474722663399424, 716734103399326537039321497600, 196230052843621714547630407680, 434706079844440922910755913728,
    16955877665155467158646389997568, 16955871445798809219323643559936, 434708152963326902685004726272, 65420491823399576388960780288, 7732282118695057130338425765888, 73377815979264377441483508154368,
    7732287421912617392950000746496, 65420491823399576388960780288, 24254810945189825482195992576, 4254065964825084404569177325568, 4254066474840664554490860404736, 24254300929609675560512913408,
    1678437662440977910787473408, 75862328860164378054998622208, 1687395991658981627757854720
  ]
def positiveScales : Array ℕ := #[
    11, 17, 11, 16, 16, 11,
    7, 10, 4, 13, 9, 4,
    9, 9, 14, 9, 13, 14,
    7, 9, 9, 10, 2, 5,
    4, 9, 7, 2, 9, 9,
    9, 4, 19, 26, 24, 26,
    30, 31, 23, 19, 28, 33,
    30, 19, 20, 27, 25, 18,
    18, 23, 15
  ]
def negativeArguments : Array ℕ := #[
    1123, 27, 1, 7, 439, 1123,
    27, 1
  ]
def negativeCoefficients : Array ℕ := #[
    88973226503518851117549856227328, 8556641551540548460102746636288, 79228162514264337593543950336, 1109194275199700726309615304704, 34781163343762044203565794197504, 88973226503518851117549856227328,
    8556641551540548460102746636288, 79228162514264337593543950336
  ]
def negativeScales : Array ℕ := #[
    10, 4, 0, 2, 8, 10,
    4, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11718104713114918, 17409266617674837, 11718104713114918, 16436922960577701, 16436922960577701, 11718104713114918,
    7924812503187618, 10112439506781552, 4754887502147955, 13499721339662996, 9002815015607054, 4754887502147955,
    9002815015607054, 9964340866974576, 14204036147538904, 9964340866974576, 13499721339662996, 14204036147538904,
    7924812503187618, 9964340866974576, 9964340866974576, 10112439506781552, 2807354922011143, 5129283016944966,
    4857980995002857, 9025139562278508, 7607330313749179, 2807354922011143, 9609178738141526, 9609178738141526,
    9126704472843189, 4857980995002857, 19308461246576377, 26177352753708849, 24308460760508782, 26455955025173485,
    30741556404149365, 31741555874973770, 23455961905388285, 19723729262307861, 28608737123049180, 33855114906173124,
    30608738112527181, 19723729262307861, 20292257591295385, 27746685250942725, 25746685423905934, 18292227254852608,
    18439177517965153, 23937370317221351, 15446857141489837
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    10133142212400602, 4754887502413606, 0, 2807354922807594, 8778077129945769, 10133142212400602,
    4754887502413606, 0
  ]

abbrev PositiveTerm := Fin 51
abbrev NegativeTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 55074869297 / 1000000000000
noncomputable def negativeCeiling : ℝ := 26396724643 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 130331874761013942066723422208, coefficient := 130331874761013942066723422208 }, { argument := 3366906764659526836723688407040, coefficient := 3366906764659526836723688407040 }, { argument := 130331874761013942066723422208, coefficient := 130331874761013942066723422208 }, { argument := 3432072702040033807757050118144, coefficient := 3432072702040033807757050118144 }, { argument := 3432072702040033807757050118144, coefficient := 3432072702040033807757050118144 }, { argument := 130331874761013942066723422208, coefficient := 130331874761013942066723422208 }, { argument := 88973226503518851117549856227328, coefficient := (-88973226503518851117549856227328) }, { argument := 75204857386586851700121796608, coefficient := 75204857386586851700121796608 }, { argument := 85649976468057247769583157248, coefficient := 85649976468057247769583157248 }, { argument := 66848762121410534844552708096, coefficient := 66848762121410534844552708096 }, { argument := 896191217190159982759784742912, coefficient := 896191217190159982759784742912 }, { argument := 79382905019175010127906340864, coefficient := 79382905019175010127906340864 }, { argument := 66848762121410534844552708096, coefficient := 66848762121410534844552708096 }, { argument := 79382905019175010127906340864, coefficient := 79382905019175010127906340864 }, { argument := 77293881202880930914014068736, coefficient := 77293881202880930914014068736 }, { argument := 2920455295179122741021396434944, coefficient := 2920455295179122741021396434944 }, { argument := 77293881202880930914014068736, coefficient := 77293881202880930914014068736 }, { argument := 896191217190159982759784742912, coefficient := 896191217190159982759784742912 }, { argument := 2920455295179122741021396434944, coefficient := 2920455295179122741021396434944 }, { argument := 75204857386586851700121796608, coefficient := 75204857386586851700121796608 }, { argument := 77293881202880930914014068736, coefficient := 77293881202880930914014068736 }, { argument := 77293881202880930914014068736, coefficient := 77293881202880930914014068736 }, { argument := 85649976468057247769583157248, coefficient := 85649976468057247769583157248 }, { argument := 8556641551540548460102746636288, coefficient := (-8556641551540548460102746636288) }, { argument := 541598767187353870268366848, coefficient := 541598767187353870268366848 }, { argument := 10831975343747077405367336960, coefficient := 10831975343747077405367336960 }, { argument := 560941580301187937063665664, coefficient := 560941580301187937063665664 }, { argument := 10077605632307548800350683136, coefficient := 10077605632307548800350683136 }, { argument := 15087394228790572100333076480, coefficient := 15087394228790572100333076480 }, { argument := 541598767187353870268366848, coefficient := 541598767187353870268366848 }, { argument := 15106737041904406167128375296, coefficient := 15106737041904406167128375296 }, { argument := 15106737041904406167128375296, coefficient := 15106737041904406167128375296 }, { argument := 10812632530633243338572038144, coefficient := 10812632530633243338572038144 }, { argument := 560941580301187937063665664, coefficient := 560941580301187937063665664 }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 196230118956752474722663399424, coefficient := 196230118956752474722663399424 }, { argument := 716734103399326537039321497600, coefficient := 716734103399326537039321497600 }, { argument := 196230052843621714547630407680, coefficient := 196230052843621714547630407680 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 434706079844440922910755913728, coefficient := 434706079844440922910755913728 }, { argument := 16955877665155467158646389997568, coefficient := 16955877665155467158646389997568 }, { argument := 16955871445798809219323643559936, coefficient := 16955871445798809219323643559936 }, { argument := 434708152963326902685004726272, coefficient := 434708152963326902685004726272 }, { argument := 34781163343762044203565794197504, coefficient := (-34781163343762044203565794197504) }, { argument := 65420491823399576388960780288, coefficient := 65420491823399576388960780288 }, { argument := 7732282118695057130338425765888, coefficient := 7732282118695057130338425765888 }, { argument := 73377815979264377441483508154368, coefficient := 73377815979264377441483508154368 }, { argument := 7732287421912617392950000746496, coefficient := 7732287421912617392950000746496 }, { argument := 65420491823399576388960780288, coefficient := 65420491823399576388960780288 }, { argument := 88973226503518851117549856227328, coefficient := (-88973226503518851117549856227328) }, { argument := 24254810945189825482195992576, coefficient := 24254810945189825482195992576 }, { argument := 4254065964825084404569177325568, coefficient := 4254065964825084404569177325568 }, { argument := 4254066474840664554490860404736, coefficient := 4254066474840664554490860404736 }, { argument := 24254300929609675560512913408, coefficient := 24254300929609675560512913408 }, { argument := 8556641551540548460102746636288, coefficient := (-8556641551540548460102746636288) }, { argument := 1678437662440977910787473408, coefficient := 1678437662440977910787473408 }, { argument := 75862328860164378054998622208, coefficient := 75862328860164378054998622208 }, { argument := 1687395991658981627757854720, coefficient := 1687395991658981627757854720 }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18
