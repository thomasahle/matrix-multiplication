import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 3, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk3

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
def constantNumerator : ℤ := 3642045923654532920499171753984
def positiveArguments : Array ℕ := #[
    11, 8386841, 8390375, 3394075, 12086731, 1696781,
    2046561, 73450857, 73450967, 2046559, 101353, 2603653,
    439805, 2601377, 100529
  ]
def positiveCoefficients : Array ℕ := #[
    1743019575313815427057966907392, 158422947342227752534717497344, 158489702714829597839458304000, 256449056325532657258804019200, 913247573789784156214097084416, 256410295141441263210890002432,
    19329222143096367956373798912, 693723730469702520463838674944, 693724769390328751785785688064, 19329203253630436477792944128, 957252020276574302687461376, 24590807320446000739150462976,
    265845810047805992090824867840, 24569311108215978114137718784, 949469560312805127375290368
  ]
def positiveScales : Array ℕ := #[
    3, 22, 23, 21, 23, 20,
    20, 26, 26, 20, 16, 21,
    18, 21, 16
  ]
def negativeArguments : Array ℕ := #[
    425009137189, 10918296050149, 118034229553535, 5454376871983, 421554529817, 3085500825553,
    55400338626575, 27700210303169, 3085498289421, 3085500825553, 10997480837977, 1542408156779,
    425009137189, 425201449435, 425201449435, 10922728334875, 118084281898625, 5456589084625,
    421743843815, 10997480837977, 197282810454161, 197283107999567, 10997469138151, 55400338626575,
    197282810454161, 1731002319931, 10918296050149, 10922728334875, 1542408156779, 1731002319931,
    55392156086063, 771203443075, 27700210303169, 197283107999567, 55392156086063, 118034229553535,
    118084281898625, 3085498289421, 10997469138151, 771203443075, 5454376871983, 5456589084625,
    421554529817, 421743843815, 1, 9, 9, 1
  ]
def negativeCoefficients : Array ℕ := #[
    239258873984179551724371968, 6146454252871474338477375488, 66447364029282976555513937920, 6141082412050222590975803392, 237314102925023230667259904, 1736982546026481072824385536,
    62375236098710616536829132800, 62375328399718141217222950912, 1736981118311089802525540352, 1736982546026481072824385536, 6191031325490923411890765824, 1736597200030779493471748096,
    239258873984179551724371968, 239367136154107599619358720, 239367136154107599619358720, 6148949407351526031097856000, 66475540994620019489898496000, 6143573142057766466093056000,
    237420677231379333020385280, 6191031325490923411890765824, 222120697911990918084992958464, 222121032918335814935729143808, 6191024739074421674435674112, 62375236098710616536829132800,
    222120697911990918084992958464, 62365931224149725610097246208, 6146454252871474338477375488, 6148949407351526031097856000, 1736597200030779493471748096, 62365931224149725610097246208,
    62366023377110419739940749312, 1736595769429706761935257600, 62375328399718141217222950912, 222121032918335814935729143808, 62366023377110419739940749312, 66447364029282976555513937920,
    66475540994620019489898496000, 1736981118311089802525540352, 6191024739074421674435674112, 1736595769429706761935257600, 6141082412050222590975803392, 6143573142057766466093056000,
    237314102925023230667259904, 237420677231379333020385280, 316912650057057350374175801344, 1426106925256758076683791106048, 1426106925256758076683791106048, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    38, 43, 46, 42, 38, 41,
    45, 44, 41, 41, 43, 40,
    38, 38, 38, 43, 46, 42,
    38, 43, 47, 47, 43, 45,
    47, 40, 43, 43, 40, 40,
    45, 39, 44, 47, 45, 46,
    46, 41, 43, 39, 42, 42,
    38, 38, 0, 3, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3459431618637292, 22999696073192418, 23000303861342093, 21694587014263425, 23526920767541022, 20694368940563456,
    20964770237033723, 26130275987973855, 26130278148552263, 20964768827160549, 16629029266951434, 21312105756484683,
    18746504480240692, 21310844063805739, 16617252215850361
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    38628702901577851, 43311812955011962, 46746198625895194, 42310551525838917, 38616928305561775, 41488641819238389,
    45654960028126526, 44654962162981890, 41488640633412564, 41488641819238389, 43322238321032474, 40488321724811342,
    38628702901577851, 38629355558537888, 38629355558537888, 43312398498544084, 46746810270200539, 42311136542466121,
    38617576053450968, 43322238321032474, 47487258585787790, 47487260761684195, 43322236786200072, 45654960028126526,
    47487258585787790, 40654744796912865, 43311812955011962, 43312398498544084, 40488321724811342, 40654744796912865,
    45654746928662022, 39488320536325075, 44654962162981890, 47487260761684195, 45654746928662022, 46746198625895194,
    46746810270200539, 41488640633412564, 43322236786200072, 39488320536325075, 42310551525838917, 42311136542466121,
    38616928305561775, 38617576053450968, 0, 3169925001442313, 3169925001442313, 0
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 1068921039 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1077428041 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 239258873984179551724371968, coefficient := (-239258873984179551724371968) }, { argument := 6146454252871474338477375488, coefficient := (-6146454252871474338477375488) }, { argument := 66447364029282976555513937920, coefficient := (-66447364029282976555513937920) }, { argument := 6141082412050222590975803392, coefficient := (-6141082412050222590975803392) }, { argument := 237314102925023230667259904, coefficient := (-237314102925023230667259904) }, { argument := 1736982546026481072824385536, coefficient := (-1736982546026481072824385536) }, { argument := 62375236098710616536829132800, coefficient := (-62375236098710616536829132800) }, { argument := 62375328399718141217222950912, coefficient := (-62375328399718141217222950912) }, { argument := 1736981118311089802525540352, coefficient := (-1736981118311089802525540352) }, { argument := 1736982546026481072824385536, coefficient := (-1736982546026481072824385536) }, { argument := 6191031325490923411890765824, coefficient := (-6191031325490923411890765824) }, { argument := 1736597200030779493471748096, coefficient := (-1736597200030779493471748096) }, { argument := 239258873984179551724371968, coefficient := (-239258873984179551724371968) }, { argument := 239367136154107599619358720, coefficient := (-239367136154107599619358720) }, { argument := 239367136154107599619358720, coefficient := (-239367136154107599619358720) }, { argument := 6148949407351526031097856000, coefficient := (-6148949407351526031097856000) }, { argument := 66475540994620019489898496000, coefficient := (-66475540994620019489898496000) }, { argument := 6143573142057766466093056000, coefficient := (-6143573142057766466093056000) }, { argument := 237420677231379333020385280, coefficient := (-237420677231379333020385280) }, { argument := 6191031325490923411890765824, coefficient := (-6191031325490923411890765824) }, { argument := 222120697911990918084992958464, coefficient := (-222120697911990918084992958464) }, { argument := 222121032918335814935729143808, coefficient := (-222121032918335814935729143808) }, { argument := 6191024739074421674435674112, coefficient := (-6191024739074421674435674112) }, { argument := 62375236098710616536829132800, coefficient := (-62375236098710616536829132800) }, { argument := 222120697911990918084992958464, coefficient := (-222120697911990918084992958464) }, { argument := 62365931224149725610097246208, coefficient := (-62365931224149725610097246208) }, { argument := 6146454252871474338477375488, coefficient := (-6146454252871474338477375488) }, { argument := 6148949407351526031097856000, coefficient := (-6148949407351526031097856000) }, { argument := 1736597200030779493471748096, coefficient := (-1736597200030779493471748096) }, { argument := 62365931224149725610097246208, coefficient := (-62365931224149725610097246208) }, { argument := 62366023377110419739940749312, coefficient := (-62366023377110419739940749312) }, { argument := 1736595769429706761935257600, coefficient := (-1736595769429706761935257600) }, { argument := 62375328399718141217222950912, coefficient := (-62375328399718141217222950912) }, { argument := 222121032918335814935729143808, coefficient := (-222121032918335814935729143808) }, { argument := 62366023377110419739940749312, coefficient := (-62366023377110419739940749312) }, { argument := 66447364029282976555513937920, coefficient := (-66447364029282976555513937920) }, { argument := 66475540994620019489898496000, coefficient := (-66475540994620019489898496000) }, { argument := 1736981118311089802525540352, coefficient := (-1736981118311089802525540352) }, { argument := 6191024739074421674435674112, coefficient := (-6191024739074421674435674112) }, { argument := 1736595769429706761935257600, coefficient := (-1736595769429706761935257600) }, { argument := 6141082412050222590975803392, coefficient := (-6141082412050222590975803392) }, { argument := 6143573142057766466093056000, coefficient := (-6143573142057766466093056000) }, { argument := 237314102925023230667259904, coefficient := (-237314102925023230667259904) }, { argument := 237420677231379333020385280, coefficient := (-237420677231379333020385280) }, { argument := 1743019575313815427057966907392, coefficient := 1743019575313815427057966907392 }, { argument := 158422947342227752534717497344, coefficient := 158422947342227752534717497344 }, { argument := 158489702714829597839458304000, coefficient := 158489702714829597839458304000 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 256449056325532657258804019200, coefficient := 256449056325532657258804019200 }, { argument := 913247573789784156214097084416, coefficient := 913247573789784156214097084416 }, { argument := 256410295141441263210890002432, coefficient := 256410295141441263210890002432 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 19329222143096367956373798912, coefficient := 19329222143096367956373798912 }, { argument := 693723730469702520463838674944, coefficient := 693723730469702520463838674944 }, { argument := 693724769390328751785785688064, coefficient := 693724769390328751785785688064 }, { argument := 19329203253630436477792944128, coefficient := 19329203253630436477792944128 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 957252020276574302687461376, coefficient := 957252020276574302687461376 }, { argument := 24590807320446000739150462976, coefficient := 24590807320446000739150462976 }, { argument := 265845810047805992090824867840, coefficient := 265845810047805992090824867840 }, { argument := 24569311108215978114137718784, coefficient := 24569311108215978114137718784 }, { argument := 949469560312805127375290368, coefficient := 949469560312805127375290368 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk3
