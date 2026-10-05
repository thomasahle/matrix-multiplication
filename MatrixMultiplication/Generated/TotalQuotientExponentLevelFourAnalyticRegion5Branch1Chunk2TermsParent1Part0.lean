import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 2, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk2

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
def constantNumerator : ℤ := (-1635808724277423629737236889600)
def positiveArguments : Array ℕ := #[
    17, 6199723, 21151929, 1550695, 1998439, 73499125,
    36749379, 999311, 72421, 2555335, 7075761, 1275617,
    36199
  ]
def positiveCoefficients : Array ℕ := #[
    1346878762742493739090247155712, 117109456393104181732764024832, 399548642230553807261150478336, 117167201490456711754437099520, 18874722703319061822426841088, 694179608840492824534188032000,
    694176142623494398214601179136, 18876451089451792112575053824, 1367994012223610304084312064, 48268913426014819408559472640, 534629385395139258990509162496, 48191447726229825748474003456,
    1367559554507186296724652032
  ]
def positiveScales : Array ℕ := #[
    4, 22, 24, 20, 20, 26,
    25, 19, 16, 21, 22, 20,
    15
  ]
def negativeArguments : Array ℕ := #[
    112241078659, 990148808321, 43867771810955, 1977116182567, 3506420861, 439699218605,
    16324445472279, 8162178044511, 219870992959, 112241078659, 382976905437, 3509168621,
    382976905437, 844534928887, 149665960717145, 6745444575161, 47856898717, 16324445472279,
    600231650939061, 300114330852293, 8162968910037, 990148808321, 844534928887, 990637382051,
    3509168621, 990637382051, 10972352198663, 61815319169, 14032223087, 8162178044511,
    300114330852293, 150056418117533, 4081462108497, 43867771810955, 149665960717145, 10972352198663,
    219870992959, 8162968910037, 4081462108497, 109946189093, 1977116182567, 6745444575161,
    61815319169, 3506420861, 47856898717, 14032223087, 1, 9,
    1
  ]
def negativeCoefficients : Array ℕ := #[
    126372220006083732717961216, 4459233804195796269154697216, 49390720195347721624664145920, 4452069851538459369842671616, 126332125464029870002536448, 123764327316536016376954880,
    4594922909124105311851905024, 4594897749973922914272018432, 123776365244966668712542208, 126372220006083732717961216, 431193662154394720888946688, 126431123951326698435248128,
    431193662154394720888946688, 15213788764147446152647671808, 168508891228945378571693588480, 15189390837571706649132924928, 431056622457977536212107264, 4594922909124105311851905024,
    168950189969070796567285334016, 168949348574366563252270268416, 4595342967684947135686508544, 4459233804195796269154697216, 15213788764147446152647671808, 4461434144664167282477367296,
    126431123951326698435248128, 4461434144664167282477367296, 49415081273276529298896846848, 4454263174004746855261405184, 126391029331585742147682304, 4594897749973922914272018432,
    168949348574366563252270268416, 168948507179668240911766126592, 4595317807738472028992176128, 49390720195347721624664145920, 168508891228945378571693588480, 49415081273276529298896846848,
    123776365244966668712542208, 4595342967684947135686508544, 4595317807738472028992176128, 123788404057510222896300032, 4452069851538459369842671616, 15189390837571706649132924928,
    4454263174004746855261405184, 126332125464029870002536448, 431056622457977536212107264, 126391029331585742147682304, 633825300114114700748351602688, 1426106925256758076683791106048,
    633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    36, 39, 45, 40, 31, 38,
    43, 42, 37, 36, 38, 31,
    38, 39, 47, 42, 35, 43,
    49, 48, 42, 39, 39, 39,
    31, 39, 43, 35, 33, 42,
    48, 47, 41, 45, 47, 43,
    37, 42, 41, 36, 40, 42,
    35, 31, 35, 33, 0, 3,
    0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4087462841250339, 22563772327492314, 24334285903529847, 20564483525680179, 20930442105724341, 26131223739117342,
    25131216535352646, 19930574209382787, 16144120477449985, 21285081007711035, 22754453887837745, 20282763798784799,
    15143662222853289
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36707809822570079, 39848854407914086, 45318226662506851, 40846534791856617, 31707352021201592, 38677726012524839,
    43892099222787412, 42892091323398504, 37677866329330948, 36707809822570079, 38478466440046890, 31708482127216619,
    38478466440046890, 39619366136057114, 47088739467731083, 42617050669339202, 35478007857438987, 43892099222787412,
    49092512724415053, 48092505539581523, 42892231105031683, 39848854407914086, 39619366136057114, 39849566108084533,
    31708482127216619, 39849566108084533, 43318938070268508, 35847245363895423, 33708024538283700, 42892091323398504,
    48092505539581523, 47092498354712261, 41892223206114860, 45318226662506851, 47088739467731083, 43318938070268508,
    37677866329330948, 42892231105031683, 41892223206114860, 36678006642795061, 40846534791856617, 42617050669339202,
    35847245363895423, 31707352021201592, 35478007857438987, 33708024538283700, 0, 3169925001442313,
    0
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 49
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
noncomputable def positiveFloor : ℝ := 85281801 / 100000000000
noncomputable def negativeCeiling : ℝ := 101165789 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 126372220006083732717961216, coefficient := (-126372220006083732717961216) }, { argument := 4459233804195796269154697216, coefficient := (-4459233804195796269154697216) }, { argument := 49390720195347721624664145920, coefficient := (-49390720195347721624664145920) }, { argument := 4452069851538459369842671616, coefficient := (-4452069851538459369842671616) }, { argument := 126332125464029870002536448, coefficient := (-126332125464029870002536448) }, { argument := 123764327316536016376954880, coefficient := (-123764327316536016376954880) }, { argument := 4594922909124105311851905024, coefficient := (-4594922909124105311851905024) }, { argument := 4594897749973922914272018432, coefficient := (-4594897749973922914272018432) }, { argument := 123776365244966668712542208, coefficient := (-123776365244966668712542208) }, { argument := 126372220006083732717961216, coefficient := (-126372220006083732717961216) }, { argument := 431193662154394720888946688, coefficient := (-431193662154394720888946688) }, { argument := 126431123951326698435248128, coefficient := (-126431123951326698435248128) }, { argument := 431193662154394720888946688, coefficient := (-431193662154394720888946688) }, { argument := 15213788764147446152647671808, coefficient := (-15213788764147446152647671808) }, { argument := 168508891228945378571693588480, coefficient := (-168508891228945378571693588480) }, { argument := 15189390837571706649132924928, coefficient := (-15189390837571706649132924928) }, { argument := 431056622457977536212107264, coefficient := (-431056622457977536212107264) }, { argument := 4594922909124105311851905024, coefficient := (-4594922909124105311851905024) }, { argument := 168950189969070796567285334016, coefficient := (-168950189969070796567285334016) }, { argument := 168949348574366563252270268416, coefficient := (-168949348574366563252270268416) }, { argument := 4595342967684947135686508544, coefficient := (-4595342967684947135686508544) }, { argument := 4459233804195796269154697216, coefficient := (-4459233804195796269154697216) }, { argument := 15213788764147446152647671808, coefficient := (-15213788764147446152647671808) }, { argument := 4461434144664167282477367296, coefficient := (-4461434144664167282477367296) }, { argument := 126431123951326698435248128, coefficient := (-126431123951326698435248128) }, { argument := 4461434144664167282477367296, coefficient := (-4461434144664167282477367296) }, { argument := 49415081273276529298896846848, coefficient := (-49415081273276529298896846848) }, { argument := 4454263174004746855261405184, coefficient := (-4454263174004746855261405184) }, { argument := 126391029331585742147682304, coefficient := (-126391029331585742147682304) }, { argument := 4594897749973922914272018432, coefficient := (-4594897749973922914272018432) }, { argument := 168949348574366563252270268416, coefficient := (-168949348574366563252270268416) }, { argument := 168948507179668240911766126592, coefficient := (-168948507179668240911766126592) }, { argument := 4595317807738472028992176128, coefficient := (-4595317807738472028992176128) }, { argument := 49390720195347721624664145920, coefficient := (-49390720195347721624664145920) }, { argument := 168508891228945378571693588480, coefficient := (-168508891228945378571693588480) }, { argument := 49415081273276529298896846848, coefficient := (-49415081273276529298896846848) }, { argument := 123776365244966668712542208, coefficient := (-123776365244966668712542208) }, { argument := 4595342967684947135686508544, coefficient := (-4595342967684947135686508544) }, { argument := 4595317807738472028992176128, coefficient := (-4595317807738472028992176128) }, { argument := 123788404057510222896300032, coefficient := (-123788404057510222896300032) }, { argument := 4452069851538459369842671616, coefficient := (-4452069851538459369842671616) }, { argument := 15189390837571706649132924928, coefficient := (-15189390837571706649132924928) }, { argument := 4454263174004746855261405184, coefficient := (-4454263174004746855261405184) }, { argument := 126332125464029870002536448, coefficient := (-126332125464029870002536448) }, { argument := 431056622457977536212107264, coefficient := (-431056622457977536212107264) }, { argument := 126391029331585742147682304, coefficient := (-126391029331585742147682304) }, { argument := 1346878762742493739090247155712, coefficient := 1346878762742493739090247155712 }, { argument := 117109456393104181732764024832, coefficient := 117109456393104181732764024832 }, { argument := 399548642230553807261150478336, coefficient := 399548642230553807261150478336 }, { argument := 117167201490456711754437099520, coefficient := 117167201490456711754437099520 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 18874722703319061822426841088, coefficient := 18874722703319061822426841088 }, { argument := 694179608840492824534188032000, coefficient := 694179608840492824534188032000 }, { argument := 694176142623494398214601179136, coefficient := 694176142623494398214601179136 }, { argument := 18876451089451792112575053824, coefficient := 18876451089451792112575053824 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 1367994012223610304084312064, coefficient := 1367994012223610304084312064 }, { argument := 48268913426014819408559472640, coefficient := 48268913426014819408559472640 }, { argument := 534629385395139258990509162496, coefficient := 534629385395139258990509162496 }, { argument := 48191447726229825748474003456, coefficient := 48191447726229825748474003456 }, { argument := 1367559554507186296724652032, coefficient := 1367559554507186296724652032 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk2
