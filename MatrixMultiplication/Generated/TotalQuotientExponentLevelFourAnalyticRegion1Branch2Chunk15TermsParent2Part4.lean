import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 15, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15

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
def constantNumerator : ℤ := (-459083134688850542655546714761461760)
def positiveArguments : Array ℕ := #[
    105, 3489, 1929, 6138731873, 111, 105,
    141, 111540911, 15918548067, 765, 164831282797, 785,
    25, 765, 435, 785, 12255, 15,
    7959274751, 765, 25, 15, 25, 385,
    435, 111538307, 35315697, 2894053391, 105, 93,
    4353, 1185, 1447026639, 4353, 105, 105,
    45, 105, 1185, 45, 17657905, 93
  ]
def positiveCoefficients : Array ℕ := #[
    4061990753905154027012751360, 134974149908334118097595138048, 74624572993171829696262832128, 57978683288757599155035062665216, 4294104511271162828556337152, 4061990753905154027012751360,
    5454673298101206836274266112, 526737059575146121382441517056, 75173217847550179429456262725632, 59189008128332244393614376960, 778393725208960746305782873587712, 60736433177438969737238282240,
    1934281311383406679529881600, 59189008128332244393614376960, 33656494818071276223819939840, 60736433177438969737238282240, 948184698840145954305547960320, 37138201178561408246973726720,
    75173224624146082347397144379392, 59189008128332244393614376960, 1934281311383406679529881600, 37138201178561408246973726720, 1934281311383406679529881600, 59575864390608925729520353280,
    33656494818071276223819939840, 526724762532824728826305052672, 166773663831980080864388186112, 13666780733293640141663828443136, 4061990753905154027012751360, 3597763239173136423925579776,
    168398530969039385519871492096, 45842467079786738304858193920, 13666780199666227577393919295488, 168398530969039385519871492096, 4061990753905154027012751360, 4061990753905154027012751360,
    3481706360490132023153786880, 4061990753905154027012751360, 45842467079786738304858193920, 3481706360490132023153786880, 166774197459392645134297333760, 3597763239173136423925579776
  ]
def positiveScales : Array ℕ := #[
    6, 11, 10, 32, 6, 6,
    7, 26, 33, 9, 37, 9,
    4, 9, 8, 9, 13, 3,
    32, 9, 4, 3, 4, 8,
    8, 26, 25, 31, 6, 6,
    12, 10, 30, 12, 6, 6,
    5, 6, 10, 5, 24, 6
  ]
def negativeArguments : Array ℕ := #[
    3467, 5877, 355
  ]
def negativeCoefficients : Array ℕ := #[
    4394944630991271334989070013038592, 931247822192663024074515592249344, 28125997692563839845708102369280
  ]
def negativeScales : Array ℕ := #[
    11, 12, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6714245517659862, 11768597882173550, 10913637427705176, 32515293511293338, 6794415866314396, 6714245517659862,
    7139551352398793, 26732997718305979, 33889989702113638, 9579315937579817, 37262199116701666, 9616548843778436,
    4643856189773592, 9579315937579817, 8764871590716857, 9616548843778436, 13581082863753994, 3906890595303263,
    32889989832167414, 9579315937579817, 4643856189773592, 3906890595303263, 4643856189773592, 8588714635582006,
    8764871590716857, 26732964037195568, 25073806234407887, 31430444391688795, 6714245517659862, 6539158811107971,
    12087794304787900, 10210671343785621, 30430444335357925, 12087794304787900, 6714245517659862, 6714245517659862,
    5491853096329661, 6714245517659862, 10210671343785621, 5491853096329661, 24073810850606707, 6539158811107971
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    11759472121479051, 12520864182989280, 8471675214392147
  ]

abbrev PositiveTerm := Fin 42
abbrev NegativeTerm := Fin 3
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
noncomputable def positiveFloor : ℝ := 88632770569 / 200000000000
noncomputable def negativeCeiling : ℝ := 382661399761 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 57978683288757599155035062665216, coefficient := 57978683288757599155035062665216 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 4394944630991271334989070013038592, coefficient := (-4394944630991271334989070013038592) }, { argument := 526737059575146121382441517056, coefficient := 526737059575146121382441517056 }, { argument := 75173217847550179429456262725632, coefficient := 75173217847550179429456262725632 }, { argument := 59189008128332244393614376960, coefficient := 59189008128332244393614376960 }, { argument := 778393725208960746305782873587712, coefficient := 778393725208960746305782873587712 }, { argument := 60736433177438969737238282240, coefficient := 60736433177438969737238282240 }, { argument := 1934281311383406679529881600, coefficient := 1934281311383406679529881600 }, { argument := 59189008128332244393614376960, coefficient := 59189008128332244393614376960 }, { argument := 33656494818071276223819939840, coefficient := 33656494818071276223819939840 }, { argument := 60736433177438969737238282240, coefficient := 60736433177438969737238282240 }, { argument := 948184698840145954305547960320, coefficient := 948184698840145954305547960320 }, { argument := 37138201178561408246973726720, coefficient := 37138201178561408246973726720 }, { argument := 75173224624146082347397144379392, coefficient := 75173224624146082347397144379392 }, { argument := 59189008128332244393614376960, coefficient := 59189008128332244393614376960 }, { argument := 1934281311383406679529881600, coefficient := 1934281311383406679529881600 }, { argument := 37138201178561408246973726720, coefficient := 37138201178561408246973726720 }, { argument := 1934281311383406679529881600, coefficient := 1934281311383406679529881600 }, { argument := 59575864390608925729520353280, coefficient := 59575864390608925729520353280 }, { argument := 33656494818071276223819939840, coefficient := 33656494818071276223819939840 }, { argument := 526724762532824728826305052672, coefficient := 526724762532824728826305052672 }, { argument := 931247822192663024074515592249344, coefficient := (-931247822192663024074515592249344) }, { argument := 166773663831980080864388186112, coefficient := 166773663831980080864388186112 }, { argument := 13666780733293640141663828443136, coefficient := 13666780733293640141663828443136 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 13666780199666227577393919295488, coefficient := 13666780199666227577393919295488 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 166774197459392645134297333760, coefficient := 166774197459392645134297333760 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 28125997692563839845708102369280, coefficient := (-28125997692563839845708102369280) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15
