import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 23, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk23

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
def constantNumerator : ℤ := (-1839070847302382040589428326400)
def positiveArguments : Array ℕ := #[
    5, 45, 801, 45, 1425, 2433,
    45, 2433, 2433, 801, 45, 483,
    541, 483, 541, 17, 19, 22020097,
    22020095, 4630673, 262860263, 74090761
  ]
def positiveCoefficients : Array ℕ := #[
    6338253001141147007483516026880, 3481706360490132023153786880, 61974373216724350012137406464, 3481706360490132023153786880, 55127017374427090366601625600, 94122128611916569025924038656,
    3481706360490132023153786880, 94122128611916569025924038656, 94122128611916569025924038656, 61974373216724350012137406464, 3481706360490132023153786880, 149481259743709668194069250048,
    167431390313347682180106551296, 149481259743709668194069250048, 167431390313347682180106551296, 1346878762742493739090247155712, 3010670175542044828554670112768, 1663791488357414815378746376192,
    1663791337241687363550099537920, 699767518986541715540521517056, 2482644991338999871177643524096, 699767452873410955365488525312
  ]
def positiveScales : Array ℕ := #[
    2, 5, 9, 5, 10, 11,
    5, 11, 11, 9, 5, 8,
    9, 8, 9, 4, 4, 24,
    24, 22, 27, 26
  ]
def negativeArguments : Array ℕ := #[
    18228837, 801, 45, 263396575, 2433, 72915341,
    2433, 2433, 801, 45, 11152654819, 2269119005,
    2659, 2269119005, 19000867, 2269119005, 2269117923, 801,
    45, 2659, 2269117923, 11152653853, 2269117923, 273997551,
    2433, 76003461, 2269119005, 2269117923, 2433, 2433,
    801, 45, 3, 1, 17, 19,
    21, 49
  ]
def negativeCoefficients : Array ℕ := #[
    344332995481976219393178206208, 30987186608362175006068703232, 1740853180245066011576893440, 1243855157482660720752669491200, 47061064305958284512962019328, 344332962425410839305661710336,
    47061064305958284512962019328, 47061064305958284512962019328, 30987186608362175006068703232, 1740853180245066011576893440, 411460338377033044073023275008, 41857857558025464421894062080,
    411460320557478268869596413952, 41857857558025464421894062080, 358916229865055628170497097728, 41857857558025464421894062080, 41857837598648376668159213568, 30987186608362175006068703232,
    1740853180245066011576893440, 411460320557478268869596413952, 41857837598648376668159213568, 411460302737923493666169552896, 41857837598648376668159213568, 1293916851230766240791575658496,
    47061064305958284512962019328, 358916196808490248082980601856, 41857857558025464421894062080, 41857837598648376668159213568, 47061064305958284512962019328, 47061064305958284512962019328,
    30987186608362175006068703232, 1740853180245066011576893440, 475368975085586025561263702016, 633825300114114700748351602688, 1346878762742493739090247155712, 3010670175542044828554670112768,
    3327582825599102178928845914112, 3882179963198952542083653566464
  ]
def negativeScales : Array ℕ := #[
    24, 9, 5, 27, 11, 26,
    11, 11, 9, 5, 33, 31,
    11, 31, 24, 31, 31, 9,
    5, 11, 31, 33, 31, 28,
    11, 26, 31, 31, 11, 11,
    9, 5, 1, 0, 4, 4,
    4, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 5491853096329661, 9645658432407524, 5491853096329661, 10476746203939458, 11248520604938428,
    5491853096329661, 11248520604938428, 11248520604938428, 9645658432407524, 5491853096329661, 8915879378478017,
    9079484783826815, 8915879378478017, 9079484783826815, 4087462841250339, 4247927513443585, 24392317488295958,
    24392317357261557, 22142790452486500, 27969720822162365, 26142790316182530
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    24119719184565272, 9645658432427781, 5491853096329881, 27972661360361265, 11248520604938430, 26119719046064037,
    11248520604938430, 11248520604938430, 9645658432427781, 5491853096329881, 33376668124338016, 31079485127792077,
    11376668061857671, 31079485127792077, 24179561913718442, 31079485127792077, 31079484439861473, 9645658432427781,
    5491853096329881, 11376668061857671, 31079484439861473, 33376667999377323, 31079484439861473, 28029587757481983,
    11248520604938430, 26179561780844692, 31079485127792077, 31079484439861473, 11248520604938430, 11248520604938430,
    9645658432427781, 5491853096329881, 1584962500724866, 0, 4087462841250340, 4247927513443586,
    4392317422778766, 5614709844123661
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
noncomputable def positiveFloor : ℝ := 2746112717 / 1000000000000
noncomputable def negativeCeiling : ℝ := 2570424323 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 344332995481976219393178206208, coefficient := (-344332995481976219393178206208) }, { argument := 30987186608362175006068703232, coefficient := (-30987186608362175006068703232) }, { argument := 1740853180245066011576893440, coefficient := (-1740853180245066011576893440) }, { argument := 1243855157482660720752669491200, coefficient := (-1243855157482660720752669491200) }, { argument := 47061064305958284512962019328, coefficient := (-47061064305958284512962019328) }, { argument := 344332962425410839305661710336, coefficient := (-344332962425410839305661710336) }, { argument := 47061064305958284512962019328, coefficient := (-47061064305958284512962019328) }, { argument := 47061064305958284512962019328, coefficient := (-47061064305958284512962019328) }, { argument := 30987186608362175006068703232, coefficient := (-30987186608362175006068703232) }, { argument := 1740853180245066011576893440, coefficient := (-1740853180245066011576893440) }, { argument := 411460338377033044073023275008, coefficient := (-411460338377033044073023275008) }, { argument := 41857857558025464421894062080, coefficient := (-41857857558025464421894062080) }, { argument := 411460320557478268869596413952, coefficient := (-411460320557478268869596413952) }, { argument := 41857857558025464421894062080, coefficient := (-41857857558025464421894062080) }, { argument := 358916229865055628170497097728, coefficient := (-358916229865055628170497097728) }, { argument := 41857857558025464421894062080, coefficient := (-41857857558025464421894062080) }, { argument := 41857837598648376668159213568, coefficient := (-41857837598648376668159213568) }, { argument := 30987186608362175006068703232, coefficient := (-30987186608362175006068703232) }, { argument := 1740853180245066011576893440, coefficient := (-1740853180245066011576893440) }, { argument := 411460320557478268869596413952, coefficient := (-411460320557478268869596413952) }, { argument := 41857837598648376668159213568, coefficient := (-41857837598648376668159213568) }, { argument := 411460302737923493666169552896, coefficient := (-411460302737923493666169552896) }, { argument := 41857837598648376668159213568, coefficient := (-41857837598648376668159213568) }, { argument := 1293916851230766240791575658496, coefficient := (-1293916851230766240791575658496) }, { argument := 47061064305958284512962019328, coefficient := (-47061064305958284512962019328) }, { argument := 358916196808490248082980601856, coefficient := (-358916196808490248082980601856) }, { argument := 41857857558025464421894062080, coefficient := (-41857857558025464421894062080) }, { argument := 41857837598648376668159213568, coefficient := (-41857837598648376668159213568) }, { argument := 47061064305958284512962019328, coefficient := (-47061064305958284512962019328) }, { argument := 47061064305958284512962019328, coefficient := (-47061064305958284512962019328) }, { argument := 30987186608362175006068703232, coefficient := (-30987186608362175006068703232) }, { argument := 1740853180245066011576893440, coefficient := (-1740853180245066011576893440) }, { argument := 6338253001141147007483516026880, coefficient := 6338253001141147007483516026880 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 61974373216724350012137406464, coefficient := 61974373216724350012137406464 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 55127017374427090366601625600, coefficient := 55127017374427090366601625600 }, { argument := 94122128611916569025924038656, coefficient := 94122128611916569025924038656 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 94122128611916569025924038656, coefficient := 94122128611916569025924038656 }, { argument := 94122128611916569025924038656, coefficient := 94122128611916569025924038656 }, { argument := 61974373216724350012137406464, coefficient := 61974373216724350012137406464 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 149481259743709668194069250048, coefficient := 149481259743709668194069250048 }, { argument := 167431390313347682180106551296, coefficient := 167431390313347682180106551296 }, { argument := 149481259743709668194069250048, coefficient := 149481259743709668194069250048 }, { argument := 167431390313347682180106551296, coefficient := 167431390313347682180106551296 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 1346878762742493739090247155712, coefficient := 1346878762742493739090247155712 }, { argument := 1346878762742493739090247155712, coefficient := (-1346878762742493739090247155712) }, { argument := 3010670175542044828554670112768, coefficient := 3010670175542044828554670112768 }, { argument := 3010670175542044828554670112768, coefficient := (-3010670175542044828554670112768) }, { argument := 1663791488357414815378746376192, coefficient := 1663791488357414815378746376192 }, { argument := 1663791337241687363550099537920, coefficient := 1663791337241687363550099537920 }, { argument := 3327582825599102178928845914112, coefficient := (-3327582825599102178928845914112) }, { argument := 699767518986541715540521517056, coefficient := 699767518986541715540521517056 }, { argument := 2482644991338999871177643524096, coefficient := 2482644991338999871177643524096 }, { argument := 699767452873410955365488525312, coefficient := 699767452873410955365488525312 }, { argument := 3882179963198952542083653566464, coefficient := (-3882179963198952542083653566464) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk23
