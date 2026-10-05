import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 5, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk5

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
def constantNumerator : ℤ := (-138943364869551632720717869481984)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    928965694957, 12709467235829, 50852206487567, 57179380387, 114573272151, 4755103997427,
    52693758713129, 4755129787717, 14319404905, 114573272151, 2033250794367, 2033312686089,
    114450097305, 3191389838873, 21842909227237, 174792627610203, 785715199513, 2033250794367,
    166832817313001, 1847567685141997, 166833747824069, 4065856921703, 4755103997427, 166832817313001,
    41709252427885, 296932819127, 928965694957, 3191389838873, 464533194237, 464533194237,
    12710939428929, 25429048605387, 228742207323, 2033312686089, 41709252427885, 923806596444195,
    20854742527143, 1016495169071, 52693758713129, 1847567685141997, 923806596444195, 13162097626921,
    12709467235829, 21842909227237, 12710939428929, 114450097305, 296932819127, 13162097626921,
    2375475450847, 114432093077, 4755129787717, 166833747824069, 20854742527143, 2375475450847,
    50852206487567, 174792627610203, 25429048605387, 14319404905, 4065856921703, 1016495169071,
    114432093077, 57179380387, 785715199513, 228742207323
  ]
def negativeCoefficients : Array ℕ := #[
    261480597353019940947361792, 14309587976839253052197175296, 14313623636773391277020413952, 257513036204169047364861952, 32249509110366376669741056, 1338442786932512073147482112,
    14831974506574911951941402624, 1338450046253789184211812352, 32244433297162626337341440, 32249509110366376669741056, 1144618439982748273427349504, 1144653281924765338218528768,
    32214838473457188030382080, 898296380571401879382130688, 49185858928236060968826699776, 49199750785776256347084423168, 884636669936520430052442112, 1144618439982748273427349504,
    46959263367750083583364038656, 520044071146704223019343020032, 46959525283331277891005579264, 1144436982345211420677767168, 1338442786932512073147482112, 46959263367750083583364038656,
    46960443423031210396604170240, 1337266533574428087384276992, 261480597353019940947361792, 898296380571401879382130688, 261508940058372429991378944, 261508940058372429991378944,
    14311245518913397406035869696, 14315281727950890522843807744, 257540829915941885341335552, 1144653281924765338218528768, 46960443423031210396604170240, 520056880438560347133931683840,
    46960705337074425431498686464, 1144471816163016232669282304, 14831974506574911951941402624, 520044071146704223019343020032, 520056880438560347133931683840, 14819204492003876320212680704,
    14309587976839253052197175296, 49185858928236060968826699776, 14311245518913397406035869696, 32214838473457188030382080, 1337266533574428087384276992, 14819204492003876320212680704,
    1337273794407788773338251264, 32209770733800194689728512, 1338450046253789184211812352, 46959525283331277891005579264, 46960705337074425431498686464, 1337273794407788773338251264,
    14313623636773391277020413952, 49199750785776256347084423168, 14315281727950890522843807744, 32244433297162626337341440, 1144436982345211420677767168, 1144471816163016232669282304,
    32209770733800194689728512, 257513036204169047364861952, 884636669936520430052442112, 257540829915941885341335552
  ]
def negativeScales : Array ℕ := #[
    39, 43, 45, 35, 36, 42,
    45, 42, 33, 36, 40, 40,
    36, 41, 44, 47, 39, 40,
    47, 50, 47, 41, 42, 47,
    45, 38, 39, 41, 38, 38,
    43, 44, 37, 40, 45, 49,
    44, 39, 45, 50, 49, 43,
    43, 44, 43, 36, 38, 43,
    41, 36, 42, 47, 44, 41,
    45, 47, 44, 33, 41, 39,
    36, 35, 39, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    39756834365463823, 43530968789265873, 45531375607808181, 35734775935609685, 36737479572908249, 42112614032821776,
    45582697326201490, 42112621857555495, 33737252486446885, 36737479572908249, 40886925319637531, 40886969234302308,
    36735927733393299, 41537321988023847, 44312230253172157, 47312637664666042, 39515215513105716, 40886925319637531,
    47245396434458736, 50714548641493835, 47245404481076789, 41886696589438850, 42112614032821776, 47245396434458736,
    45245432687976987, 38111345602814940, 39756834365463823, 41537321988023847, 38756990735248699, 38756990735248699,
    43531135893255596, 44531542720025109, 37734931639131057, 40886969234302308, 45245432687976987, 49714584176317362,
    44245440734345591, 39886740500825259, 45582697326201490, 50714548641493835, 49714584176317362, 43581454661426815,
    43530968789265873, 44312230253172157, 43531135893255596, 36735927733393299, 38111345602814940, 43581454661426815,
    41111353436062525, 36735700764134082, 42112621857555495, 47245404481076789, 44245440734345591, 41111353436062525,
    45531375607808181, 47312637664666042, 44531542720025109, 33737252486446885, 41886696589438850, 39886740500825259,
    36735700764134082, 35734775935609685, 39515215513105716, 37734931639131057
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
noncomputable def negativeCeiling : ℝ := 1679279237 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 261480597353019940947361792, coefficient := (-261480597353019940947361792) }, { argument := 14309587976839253052197175296, coefficient := (-14309587976839253052197175296) }, { argument := 14313623636773391277020413952, coefficient := (-14313623636773391277020413952) }, { argument := 257513036204169047364861952, coefficient := (-257513036204169047364861952) }, { argument := 32249509110366376669741056, coefficient := (-32249509110366376669741056) }, { argument := 1338442786932512073147482112, coefficient := (-1338442786932512073147482112) }, { argument := 14831974506574911951941402624, coefficient := (-14831974506574911951941402624) }, { argument := 1338450046253789184211812352, coefficient := (-1338450046253789184211812352) }, { argument := 32244433297162626337341440, coefficient := (-32244433297162626337341440) }, { argument := 32249509110366376669741056, coefficient := (-32249509110366376669741056) }, { argument := 1144618439982748273427349504, coefficient := (-1144618439982748273427349504) }, { argument := 1144653281924765338218528768, coefficient := (-1144653281924765338218528768) }, { argument := 32214838473457188030382080, coefficient := (-32214838473457188030382080) }, { argument := 898296380571401879382130688, coefficient := (-898296380571401879382130688) }, { argument := 49185858928236060968826699776, coefficient := (-49185858928236060968826699776) }, { argument := 49199750785776256347084423168, coefficient := (-49199750785776256347084423168) }, { argument := 884636669936520430052442112, coefficient := (-884636669936520430052442112) }, { argument := 1144618439982748273427349504, coefficient := (-1144618439982748273427349504) }, { argument := 46959263367750083583364038656, coefficient := (-46959263367750083583364038656) }, { argument := 520044071146704223019343020032, coefficient := (-520044071146704223019343020032) }, { argument := 46959525283331277891005579264, coefficient := (-46959525283331277891005579264) }, { argument := 1144436982345211420677767168, coefficient := (-1144436982345211420677767168) }, { argument := 1338442786932512073147482112, coefficient := (-1338442786932512073147482112) }, { argument := 46959263367750083583364038656, coefficient := (-46959263367750083583364038656) }, { argument := 46960443423031210396604170240, coefficient := (-46960443423031210396604170240) }, { argument := 1337266533574428087384276992, coefficient := (-1337266533574428087384276992) }, { argument := 261480597353019940947361792, coefficient := (-261480597353019940947361792) }, { argument := 898296380571401879382130688, coefficient := (-898296380571401879382130688) }, { argument := 261508940058372429991378944, coefficient := (-261508940058372429991378944) }, { argument := 261508940058372429991378944, coefficient := (-261508940058372429991378944) }, { argument := 14311245518913397406035869696, coefficient := (-14311245518913397406035869696) }, { argument := 14315281727950890522843807744, coefficient := (-14315281727950890522843807744) }, { argument := 257540829915941885341335552, coefficient := (-257540829915941885341335552) }, { argument := 1144653281924765338218528768, coefficient := (-1144653281924765338218528768) }, { argument := 46960443423031210396604170240, coefficient := (-46960443423031210396604170240) }, { argument := 520056880438560347133931683840, coefficient := (-520056880438560347133931683840) }, { argument := 46960705337074425431498686464, coefficient := (-46960705337074425431498686464) }, { argument := 1144471816163016232669282304, coefficient := (-1144471816163016232669282304) }, { argument := 14831974506574911951941402624, coefficient := (-14831974506574911951941402624) }, { argument := 520044071146704223019343020032, coefficient := (-520044071146704223019343020032) }, { argument := 520056880438560347133931683840, coefficient := (-520056880438560347133931683840) }, { argument := 14819204492003876320212680704, coefficient := (-14819204492003876320212680704) }, { argument := 14309587976839253052197175296, coefficient := (-14309587976839253052197175296) }, { argument := 49185858928236060968826699776, coefficient := (-49185858928236060968826699776) }, { argument := 14311245518913397406035869696, coefficient := (-14311245518913397406035869696) }, { argument := 32214838473457188030382080, coefficient := (-32214838473457188030382080) }, { argument := 1337266533574428087384276992, coefficient := (-1337266533574428087384276992) }, { argument := 14819204492003876320212680704, coefficient := (-14819204492003876320212680704) }, { argument := 1337273794407788773338251264, coefficient := (-1337273794407788773338251264) }, { argument := 32209770733800194689728512, coefficient := (-32209770733800194689728512) }, { argument := 1338450046253789184211812352, coefficient := (-1338450046253789184211812352) }, { argument := 46959525283331277891005579264, coefficient := (-46959525283331277891005579264) }, { argument := 46960705337074425431498686464, coefficient := (-46960705337074425431498686464) }, { argument := 1337273794407788773338251264, coefficient := (-1337273794407788773338251264) }, { argument := 14313623636773391277020413952, coefficient := (-14313623636773391277020413952) }, { argument := 49199750785776256347084423168, coefficient := (-49199750785776256347084423168) }, { argument := 14315281727950890522843807744, coefficient := (-14315281727950890522843807744) }, { argument := 32244433297162626337341440, coefficient := (-32244433297162626337341440) }, { argument := 1144436982345211420677767168, coefficient := (-1144436982345211420677767168) }, { argument := 1144471816163016232669282304, coefficient := (-1144471816163016232669282304) }, { argument := 32209770733800194689728512, coefficient := (-32209770733800194689728512) }, { argument := 257513036204169047364861952, coefficient := (-257513036204169047364861952) }, { argument := 884636669936520430052442112, coefficient := (-884636669936520430052442112) }, { argument := 257540829915941885341335552, coefficient := (-257540829915941885341335552) }] }

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

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 124108099535872325645087981699072
def positiveArguments : Array ℕ := #[
    9, 3085551, 10605757, 771477, 465163, 130496419,
    65249823, 3718087, 498423, 20454875, 226528825, 20454989,
    62293, 300969, 1029763, 16480859, 74099
  ]
def positiveCoefficients : Array ℕ := #[
    2852213850513516153367582212096, 58284410494339666635059625984, 200337085529040479250691391488, 58291154033677204488424783872, 35146722564337484424615559168, 1232503830440227088375635509248,
    1232534308593507529065844703232, 35116338858386701127310639104, 4707472138982674352692002816, 193190832222576468280999936000, 2139504261167686716850857574400, 193191908922134562560108658688,
    4706726005078380948748238848, 2842571835965588500641742848, 155613384847977422854119489536, 155657312301001076293897289728, 2799381072113262725517279232
  ]
def positiveScales : Array ℕ := #[
    3, 21, 23, 19, 18, 26,
    25, 21, 18, 24, 27, 24,
    15, 18, 19, 23, 16
  ]
def negativeArguments : Array ℕ := #[
    1, 1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    316912650057057350374175801344, 2535301200456458802993406410752, 2535301200456458802993406410752, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    0, 0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 21557096709910023, 23338344263030901, 19557263620888503, 18827376820879042, 26959434976160770,
    25959470651616940, 21826129097717403, 18927011117846505, 24285941385136780, 27755119398929320, 24285949425605194,
    15926782432692176, 18199255370559777, 19973880907651264, 23974288102537513, 16177166452380480
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0, 0, 0
  ]

abbrev PositiveTerm := Fin 17
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
noncomputable def positiveFloor : ℝ := 76378501 / 40000000000
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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2852213850513516153367582212096, coefficient := 2852213850513516153367582212096 }, { argument := 58284410494339666635059625984, coefficient := 58284410494339666635059625984 }, { argument := 200337085529040479250691391488, coefficient := 200337085529040479250691391488 }, { argument := 58291154033677204488424783872, coefficient := 58291154033677204488424783872 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 35146722564337484424615559168, coefficient := 35146722564337484424615559168 }, { argument := 1232503830440227088375635509248, coefficient := 1232503830440227088375635509248 }, { argument := 1232534308593507529065844703232, coefficient := 1232534308593507529065844703232 }, { argument := 35116338858386701127310639104, coefficient := 35116338858386701127310639104 }, { argument := 2535301200456458802993406410752, coefficient := (-2535301200456458802993406410752) }, { argument := 4707472138982674352692002816, coefficient := 4707472138982674352692002816 }, { argument := 193190832222576468280999936000, coefficient := 193190832222576468280999936000 }, { argument := 2139504261167686716850857574400, coefficient := 2139504261167686716850857574400 }, { argument := 193191908922134562560108658688, coefficient := 193191908922134562560108658688 }, { argument := 4706726005078380948748238848, coefficient := 4706726005078380948748238848 }, { argument := 2535301200456458802993406410752, coefficient := (-2535301200456458802993406410752) }, { argument := 2842571835965588500641742848, coefficient := 2842571835965588500641742848 }, { argument := 155613384847977422854119489536, coefficient := 155613384847977422854119489536 }, { argument := 155657312301001076293897289728, coefficient := 155657312301001076293897289728 }, { argument := 2799381072113262725517279232, coefficient := 2799381072113262725517279232 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk5
