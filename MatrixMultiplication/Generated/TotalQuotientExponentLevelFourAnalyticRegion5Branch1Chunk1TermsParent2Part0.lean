import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 1, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 11283257500837902841102657912832
def positiveArguments : Array ℕ := #[
    1, 229429, 8159191, 4079579, 114719, 72421
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 2166895639596599663466119168, 77061380211463326801562959872, 77061068535275457404978855936, 2166980642193291317079965696, 683997006111805152042156032
  ]
def positiveScales : Array ℕ := #[
    0, 17, 22, 21, 16, 16
  ]
def negativeArguments : Array ℕ := #[
    38506216215, 1886061703433, 58940539529, 601792267, 326809555, 46266783397,
    512442031557, 5773560263, 653422345, 1369397821485, 67074073792307, 2096104327091,
    21401557993, 46266783397, 816216709407, 18080935934887, 814907703393, 11563019949,
    38506216215, 1369397821485, 684696141465, 19253863365, 684696141465, 33536901254983,
    1048047924679, 10700735717, 512442031557, 18080935934887, 50066389335905, 9025963385921,
    256139620423, 1886061703433, 67074073792307, 33536901254983, 943067844763, 19253863365,
    943067844763, 29471425819, 300907937, 5773560263, 814907703393, 9025963385921,
    101699841003, 11543456373, 58940539529, 2096104327091, 1048047924679, 29471425819,
    653422345, 11563019949, 256139620423, 11543456373, 163306395, 601792267,
    21401557993, 10700735717, 300907937, 1
  ]
def negativeCoefficients : Array ℕ := #[
    10838536312332609430487040, 530879174048663858522882048, 530889183719640779632672768, 10840925717662584147017728, 735909695059558808944640, 26045883558295081387556864,
    288479217796135644020342784, 26001803849047902884200448, 735688157364388920033280, 385451219910113437585244160, 18879673358578434794577723392, 18880029332833423727653814272,
    385536194409691440964698112, 26045883558295081387556864, 918978317084734404289363968, 10178662042358362990910111744, 917504507335515369721823232, 26037606166797005831012352,
    10838536312332609430487040, 385451219910113437585244160, 385449660945473801897902080, 10838961484507055527034880, 385449660945473801897902080, 18879596999387819807338397696,
    18879952972203064234539483136, 385534635101370858713645056, 288479217796135644020342784, 10178662042358362990910111744, 112739486178483966345415229440, 10162331335373388995524296704,
    288387574772960771757309952, 530879174048663858522882048, 18879673358578434794577723392, 18879596999387819807338397696, 530899999282467945951789056, 10838961484507055527034880,
    530899999282467945951789056, 530910009346102459572944896, 10841350983568197488214016, 26001803849047902884200448, 917504507335515369721823232, 10162331335373388995524296704,
    916030732089498980346494976, 25993552910005188641685504, 530889183719640779632672768, 18880029332833423727653814272, 18879952972203064234539483136, 530910009346102459572944896,
    735688157364388920033280, 26037606166797005831012352, 288387574772960771757309952, 25993552910005188641685504, 735466619669219031121920, 10840925717662584147017728,
    385536194409691440964698112, 385534635101370858713645056, 10841350983568197488214016, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    35, 40, 35, 29, 28, 35,
    38, 32, 29, 40, 45, 40,
    34, 35, 39, 44, 39, 33,
    35, 40, 39, 34, 39, 44,
    39, 33, 38, 44, 45, 43,
    37, 40, 45, 44, 39, 34,
    39, 34, 28, 32, 39, 43,
    36, 33, 35, 40, 39, 34,
    29, 33, 37, 33, 27, 29,
    34, 33, 28, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 17807688235019656, 22959994681771336, 21959988846752641, 16807744827694036, 16144120477449985
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    35164372313606774, 40778514014322966, 35778541215929983, 29164690327331415, 28283874923578815, 35429257750856470,
    38898597861388793, 32426814084430279, 29283440550375457, 40316678761072526, 45930820468886993, 40930847670497304,
    34316996774797167, 35429257750856470, 39570161289193851, 44039534592354744, 39567845712435119, 33428799188965577,
    35164372313606774, 40316678761072526, 39316672926053757, 34164428906281208, 39316672926053757, 44930814633867467,
    39930841835477777, 33316990939778398, 38898597861388793, 44039534592354744, 45508907649113267, 43037218064876863,
    37898139478455486, 40778514014322966, 45930820468886993, 44930814633867467, 39778570606997892, 34164428906281208,
    39778570606997892, 34778597808604909, 28164746920005849, 32426814084430279, 39567845712435119, 43037218064876863,
    36565526467458388, 33426356213201712, 35778541215929983, 40930847670497304, 39930841835477777, 34778597808604909,
    29283440550375457, 33428799188965577, 37898139478455486, 33426356213201712, 27283006046349644, 29164690327331415,
    34316996774797167, 33316990939778398, 28164746920005849, 0
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 58
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
noncomputable def positiveFloor : ℝ := 5337897 / 125000000000
noncomputable def negativeCeiling : ℝ := 83396979 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 10838536312332609430487040, coefficient := (-10838536312332609430487040) }, { argument := 530879174048663858522882048, coefficient := (-530879174048663858522882048) }, { argument := 530889183719640779632672768, coefficient := (-530889183719640779632672768) }, { argument := 10840925717662584147017728, coefficient := (-10840925717662584147017728) }, { argument := 735909695059558808944640, coefficient := (-735909695059558808944640) }, { argument := 26045883558295081387556864, coefficient := (-26045883558295081387556864) }, { argument := 288479217796135644020342784, coefficient := (-288479217796135644020342784) }, { argument := 26001803849047902884200448, coefficient := (-26001803849047902884200448) }, { argument := 735688157364388920033280, coefficient := (-735688157364388920033280) }, { argument := 385451219910113437585244160, coefficient := (-385451219910113437585244160) }, { argument := 18879673358578434794577723392, coefficient := (-18879673358578434794577723392) }, { argument := 18880029332833423727653814272, coefficient := (-18880029332833423727653814272) }, { argument := 385536194409691440964698112, coefficient := (-385536194409691440964698112) }, { argument := 26045883558295081387556864, coefficient := (-26045883558295081387556864) }, { argument := 918978317084734404289363968, coefficient := (-918978317084734404289363968) }, { argument := 10178662042358362990910111744, coefficient := (-10178662042358362990910111744) }, { argument := 917504507335515369721823232, coefficient := (-917504507335515369721823232) }, { argument := 26037606166797005831012352, coefficient := (-26037606166797005831012352) }, { argument := 10838536312332609430487040, coefficient := (-10838536312332609430487040) }, { argument := 385451219910113437585244160, coefficient := (-385451219910113437585244160) }, { argument := 385449660945473801897902080, coefficient := (-385449660945473801897902080) }, { argument := 10838961484507055527034880, coefficient := (-10838961484507055527034880) }, { argument := 385449660945473801897902080, coefficient := (-385449660945473801897902080) }, { argument := 18879596999387819807338397696, coefficient := (-18879596999387819807338397696) }, { argument := 18879952972203064234539483136, coefficient := (-18879952972203064234539483136) }, { argument := 385534635101370858713645056, coefficient := (-385534635101370858713645056) }, { argument := 288479217796135644020342784, coefficient := (-288479217796135644020342784) }, { argument := 10178662042358362990910111744, coefficient := (-10178662042358362990910111744) }, { argument := 112739486178483966345415229440, coefficient := (-112739486178483966345415229440) }, { argument := 10162331335373388995524296704, coefficient := (-10162331335373388995524296704) }, { argument := 288387574772960771757309952, coefficient := (-288387574772960771757309952) }, { argument := 530879174048663858522882048, coefficient := (-530879174048663858522882048) }, { argument := 18879673358578434794577723392, coefficient := (-18879673358578434794577723392) }, { argument := 18879596999387819807338397696, coefficient := (-18879596999387819807338397696) }, { argument := 530899999282467945951789056, coefficient := (-530899999282467945951789056) }, { argument := 10838961484507055527034880, coefficient := (-10838961484507055527034880) }, { argument := 530899999282467945951789056, coefficient := (-530899999282467945951789056) }, { argument := 530910009346102459572944896, coefficient := (-530910009346102459572944896) }, { argument := 10841350983568197488214016, coefficient := (-10841350983568197488214016) }, { argument := 26001803849047902884200448, coefficient := (-26001803849047902884200448) }, { argument := 917504507335515369721823232, coefficient := (-917504507335515369721823232) }, { argument := 10162331335373388995524296704, coefficient := (-10162331335373388995524296704) }, { argument := 916030732089498980346494976, coefficient := (-916030732089498980346494976) }, { argument := 25993552910005188641685504, coefficient := (-25993552910005188641685504) }, { argument := 530889183719640779632672768, coefficient := (-530889183719640779632672768) }, { argument := 18880029332833423727653814272, coefficient := (-18880029332833423727653814272) }, { argument := 18879952972203064234539483136, coefficient := (-18879952972203064234539483136) }, { argument := 530910009346102459572944896, coefficient := (-530910009346102459572944896) }, { argument := 735688157364388920033280, coefficient := (-735688157364388920033280) }, { argument := 26037606166797005831012352, coefficient := (-26037606166797005831012352) }, { argument := 288387574772960771757309952, coefficient := (-288387574772960771757309952) }, { argument := 25993552910005188641685504, coefficient := (-25993552910005188641685504) }, { argument := 735466619669219031121920, coefficient := (-735466619669219031121920) }, { argument := 10840925717662584147017728, coefficient := (-10840925717662584147017728) }, { argument := 385536194409691440964698112, coefficient := (-385536194409691440964698112) }, { argument := 385534635101370858713645056, coefficient := (-385534635101370858713645056) }, { argument := 10841350983568197488214016, coefficient := (-10841350983568197488214016) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 2166895639596599663466119168, coefficient := 2166895639596599663466119168 }, { argument := 77061380211463326801562959872, coefficient := 77061380211463326801562959872 }, { argument := 77061068535275457404978855936, coefficient := 77061068535275457404978855936 }, { argument := 2166980642193291317079965696, coefficient := 2166980642193291317079965696 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 683997006111805152042156032, coefficient := 683997006111805152042156032 }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-10818560092266206145940721500160)
def positiveArguments : Array ℕ := #[
    2555335, 7075761, 1275617, 36199, 167835, 8220677,
    256901, 2623
  ]
def positiveCoefficients : Array ℕ := #[
    24134456713007409704279736320, 267314692697569629495254581248, 24095723863114912874237001728, 683779777253593148362326016, 1585156757304853808881336320, 77642099062594772812781584384,
    77643562996204462402797830144, 1585506212424586162627149824
  ]
def positiveScales : Array ℕ := #[
    21, 22, 20, 15, 17, 22,
    17, 11
  ]
def negativeArguments : Array ℕ := #[
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    316912650057057350374175801344, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    21285081007711035, 22754453887837745, 20282763798784799, 15143662222853289, 17356684078540342, 22970825777932037,
    17970852979538410, 11357002092264983
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 24843847 / 200000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 24134456713007409704279736320, coefficient := 24134456713007409704279736320 }, { argument := 267314692697569629495254581248, coefficient := 267314692697569629495254581248 }, { argument := 24095723863114912874237001728, coefficient := 24095723863114912874237001728 }, { argument := 683779777253593148362326016, coefficient := 683779777253593148362326016 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 1585156757304853808881336320, coefficient := 1585156757304853808881336320 }, { argument := 77642099062594772812781584384, coefficient := 77642099062594772812781584384 }, { argument := 77643562996204462402797830144, coefficient := 77643562996204462402797830144 }, { argument := 1585506212424586162627149824, coefficient := 1585506212424586162627149824 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk1
