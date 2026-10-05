import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 8, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk8

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 2971519344167136680637397729280
def positiveArguments : Array ℕ := #[
    11, 8386541, 8390675, 27662135, 5978067, 27683737,
    1916451, 73581883, 73576429, 1920181, 34905, 1303367,
    14097197, 1305213, 18267
  ]
def positiveCoefficients : Array ℕ := #[
    1743019575313815427057966907392, 158417280502448308960461062144, 158495369554609041413714739200, 261261478337230626606725201920, 903379943460770923318528180224, 261465503458756526758537723904,
    18100367936924028878865825792, 694961236051271476731378139136, 694909724477676334641387143168, 18135596790886236432159997952, 659336808338259864736235520, 24619906542713443492957257728,
    266288522460842055590318440448, 24654776496822952953215188992, 690107748340638472948678656
  ]
def positiveScales : Array ℕ := #[
    3, 22, 23, 24, 22, 24,
    20, 26, 26, 20, 15, 20,
    23, 20, 14
  ]
def negativeArguments : Array ℕ := #[
    292713442821, 10930710410539, 118226825878913, 10946188276529, 153185920527, 2942689712875,
    226164293052985, 113073598698995, 5896744039435, 2942689712875, 5094228543351, 2945209390631,
    292713442821, 292895281659, 292895281659, 10936159275733, 118284893184639, 10951652150479,
    153283484145, 5094228543351, 195498596217161, 195484269446777, 5104191078599, 226164293052985,
    195498596217161, 226340466856099, 10930710410539, 10936159275733, 2945209390631, 226340466856099,
    113161683328283, 5901783042265, 113073598698995, 195484269446777, 113161683328283, 118226825878913,
    118284893184639, 5896744039435, 5104191078599, 5901783042265, 10946188276529, 10951652150479,
    153185920527, 153283484145, 1, 9, 9, 1
  ]
def negativeCoefficients : Array ℕ := #[
    164783019001873823434801152, 6153442916474780219152007168, 66555786121683637505785593856, 6162156180412912028297986048, 172472013650950903560142848, 1656587036796355233185792000,
    63659589119870931447222108160, 63654777120779360412305981440, 1659785891168666210648719360, 1656587036796355233185792000, 5735591442393927057118593024, 1658005489271732149128527872,
    164783019001873823434801152, 164885385167256108933316608, 164885385167256108933316608, 6156510354881941527326621696, 66588475108737390289373626368, 6165232067998564448309608448,
    172581860519368332914196480, 5735591442393927057118593024, 220111851268765334625755070464, 220095720759324633361283022848, 5746808259901566615107403776, 63659589119870931447222108160,
    220111851268765334625755070464, 63709177636999472292711890944, 6153442916474780219152007168, 6156510354881941527326621696, 1658005489271732149128527872, 63709177636999472292711890944,
    63704364358734173547104567296, 1661204244372885390323875840, 63654777120779360412305981440, 220095720759324633361283022848, 63704364358734173547104567296, 66555786121683637505785593856,
    66588475108737390289373626368, 1659785891168666210648719360, 5746808259901566615107403776, 1661204244372885390323875840, 6162156180412912028297986048, 6165232067998564448309608448,
    172472013650950903560142848, 172581860519368332914196480, 316912650057057350374175801344, 1426106925256758076683791106048, 1426106925256758076683791106048, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    38, 43, 46, 43, 37, 41,
    47, 46, 42, 41, 42, 41,
    38, 38, 38, 43, 46, 43,
    37, 42, 47, 47, 42, 47,
    47, 47, 43, 43, 41, 47,
    46, 42, 46, 47, 46, 46,
    46, 42, 42, 42, 43, 43,
    37, 37, 0, 3, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3459431618637292, 22999644466604992, 23000355444349392, 24721409174092571, 22511247635631904, 24722535368286442,
    20870005680815015, 26132847260337619, 26132740321644865, 20872810877759594, 15091146091013867, 20313811942201425,
    23748904998722517, 20315853831267546, 14156952098325733
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    38090698046582657, 43313452401467346, 46748550751393404, 43315493810037408, 37156492747555757, 41420272566316917,
    47684364502267016, 46684255445489799, 42423055710957726, 41420272566316917, 42212000823616345, 41421507345229131,
    38090698046582657, 38091593996343269, 38091593996343269, 43314171393355014, 46749259159555387, 43316213762677631,
    37157411302886038, 42212000823616345, 47474151576683120, 47474045847443251, 42214819476957093, 47684364502267016,
    47474151576683120, 47685487872042351, 43313452401467346, 43314171393355014, 41421507345229131, 47685487872042351,
    46685378871184407, 42424288024921247, 46684255445489799, 47474045847443251, 46685378871184407, 46748550751393404,
    46749259159555387, 42423055710957726, 42214819476957093, 42424288024921247, 43315493810037408, 43316213762677631,
    37156492747555757, 37157411302886038, 0, 3169925001442313, 3169925001442313, 0
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
noncomputable def positiveFloor : ℝ := 219074999 / 200000000000
noncomputable def negativeCeiling : ℝ := 547905413 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 164783019001873823434801152, coefficient := (-164783019001873823434801152) }, { argument := 6153442916474780219152007168, coefficient := (-6153442916474780219152007168) }, { argument := 66555786121683637505785593856, coefficient := (-66555786121683637505785593856) }, { argument := 6162156180412912028297986048, coefficient := (-6162156180412912028297986048) }, { argument := 172472013650950903560142848, coefficient := (-172472013650950903560142848) }, { argument := 1656587036796355233185792000, coefficient := (-1656587036796355233185792000) }, { argument := 63659589119870931447222108160, coefficient := (-63659589119870931447222108160) }, { argument := 63654777120779360412305981440, coefficient := (-63654777120779360412305981440) }, { argument := 1659785891168666210648719360, coefficient := (-1659785891168666210648719360) }, { argument := 1656587036796355233185792000, coefficient := (-1656587036796355233185792000) }, { argument := 5735591442393927057118593024, coefficient := (-5735591442393927057118593024) }, { argument := 1658005489271732149128527872, coefficient := (-1658005489271732149128527872) }, { argument := 164783019001873823434801152, coefficient := (-164783019001873823434801152) }, { argument := 164885385167256108933316608, coefficient := (-164885385167256108933316608) }, { argument := 164885385167256108933316608, coefficient := (-164885385167256108933316608) }, { argument := 6156510354881941527326621696, coefficient := (-6156510354881941527326621696) }, { argument := 66588475108737390289373626368, coefficient := (-66588475108737390289373626368) }, { argument := 6165232067998564448309608448, coefficient := (-6165232067998564448309608448) }, { argument := 172581860519368332914196480, coefficient := (-172581860519368332914196480) }, { argument := 5735591442393927057118593024, coefficient := (-5735591442393927057118593024) }, { argument := 220111851268765334625755070464, coefficient := (-220111851268765334625755070464) }, { argument := 220095720759324633361283022848, coefficient := (-220095720759324633361283022848) }, { argument := 5746808259901566615107403776, coefficient := (-5746808259901566615107403776) }, { argument := 63659589119870931447222108160, coefficient := (-63659589119870931447222108160) }, { argument := 220111851268765334625755070464, coefficient := (-220111851268765334625755070464) }, { argument := 63709177636999472292711890944, coefficient := (-63709177636999472292711890944) }, { argument := 6153442916474780219152007168, coefficient := (-6153442916474780219152007168) }, { argument := 6156510354881941527326621696, coefficient := (-6156510354881941527326621696) }, { argument := 1658005489271732149128527872, coefficient := (-1658005489271732149128527872) }, { argument := 63709177636999472292711890944, coefficient := (-63709177636999472292711890944) }, { argument := 63704364358734173547104567296, coefficient := (-63704364358734173547104567296) }, { argument := 1661204244372885390323875840, coefficient := (-1661204244372885390323875840) }, { argument := 63654777120779360412305981440, coefficient := (-63654777120779360412305981440) }, { argument := 220095720759324633361283022848, coefficient := (-220095720759324633361283022848) }, { argument := 63704364358734173547104567296, coefficient := (-63704364358734173547104567296) }, { argument := 66555786121683637505785593856, coefficient := (-66555786121683637505785593856) }, { argument := 66588475108737390289373626368, coefficient := (-66588475108737390289373626368) }, { argument := 1659785891168666210648719360, coefficient := (-1659785891168666210648719360) }, { argument := 5746808259901566615107403776, coefficient := (-5746808259901566615107403776) }, { argument := 1661204244372885390323875840, coefficient := (-1661204244372885390323875840) }, { argument := 6162156180412912028297986048, coefficient := (-6162156180412912028297986048) }, { argument := 6165232067998564448309608448, coefficient := (-6165232067998564448309608448) }, { argument := 172472013650950903560142848, coefficient := (-172472013650950903560142848) }, { argument := 172581860519368332914196480, coefficient := (-172581860519368332914196480) }, { argument := 1743019575313815427057966907392, coefficient := 1743019575313815427057966907392 }, { argument := 158417280502448308960461062144, coefficient := 158417280502448308960461062144 }, { argument := 158495369554609041413714739200, coefficient := 158495369554609041413714739200 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 261261478337230626606725201920, coefficient := 261261478337230626606725201920 }, { argument := 903379943460770923318528180224, coefficient := 903379943460770923318528180224 }, { argument := 261465503458756526758537723904, coefficient := 261465503458756526758537723904 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 18100367936924028878865825792, coefficient := 18100367936924028878865825792 }, { argument := 694961236051271476731378139136, coefficient := 694961236051271476731378139136 }, { argument := 694909724477676334641387143168, coefficient := 694909724477676334641387143168 }, { argument := 18135596790886236432159997952, coefficient := 18135596790886236432159997952 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 659336808338259864736235520, coefficient := 659336808338259864736235520 }, { argument := 24619906542713443492957257728, coefficient := 24619906542713443492957257728 }, { argument := 266288522460842055590318440448, coefficient := 266288522460842055590318440448 }, { argument := 24654776496822952953215188992, coefficient := 24654776496822952953215188992 }, { argument := 690107748340638472948678656, coefficient := 690107748340638472948678656 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk8
