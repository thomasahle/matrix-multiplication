import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 0, branch 2,
parent chunk 7, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 56375263552466783711800783273984
def positiveArguments : Array ℕ := #[
    7, 17, 145, 37, 9, 53,
    9, 145, 37, 53, 2395, 53,
    145, 145, 9, 53, 9, 37,
    37, 1, 12088211, 5366919, 12085301, 147933,
    49137261, 12287829, 1191255, 128485, 865117, 43158767,
    864097, 31885
  ]
def positiveCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 657655645870358271040159744, 5609415803011879370636656640, 5725472681694883771408449536, 696341272098026404630757376, 4100676380132822160603348992,
    696341272098026404630757376, 5609415803011879370636656640, 5725472681694883771408449536, 4100676380132822160603348992, 92652074815265179949481328640, 4100676380132822160603348992,
    5609415803011879370636656640, 5609415803011879370636656640, 696341272098026404630757376, 4100676380132822160603348992, 696341272098026404630757376, 5725472681694883771408449536,
    5725472681694883771408449536, 618970019642690137449562112, 114169924928512313676594675712, 405512934430020374730305961984, 114142440755582012341450964992, 11177501454565683606363045888,
    464088308812835571685562253312, 464221054534669037412519247872, 11251085369101758418082856960, 1213506515103012730563461120, 32683196196485910866696339456, 407623029445561018301141745664,
    32644661685985694561752580096, 1204581242450389101109575680
  ]
def positiveScales : Array ℕ := #[
    2, 4, 7, 5, 3, 5,
    3, 7, 5, 5, 11, 5,
    7, 7, 3, 5, 3, 5,
    5, 0, 23, 22, 23, 17,
    25, 23, 20, 16, 19, 25,
    19, 14
  ]
def negativeArguments : Array ℕ := #[
    518528327239, 145639227057, 1, 1, 3, 3
  ]
def negativeCoefficients : Array ℕ := #[
    583810995333651752745435136, 163975192176108064701677568, 158456325028528675187087900672, 633825300114114700748351602688, 950737950171172051122527404032, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    38, 37, 0, 0, 1, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 4087462841250339, 7179909090014934, 5209453365628949, 3169925001442312, 5727920454554652,
    3169925001442312, 7179909090014934, 5209453365628949, 5727920454554652, 11225809940623542, 5727920454554652,
    7179909090014934, 7179909090014934, 3169925001442312, 5727920454554652, 3169925001442312, 5209453365628949,
    5209453365628949, 0, 23527097412321653, 22355662683785039, 23526750069942171, 17174584390469447,
    25550314105716007, 23550726708676732, 20184050838829855, 16971240415127978, 19722535733080545, 25363150313365663,
    19720833746961848, 14960590259978586
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    38915631855249022, 37083608032940918, 0, 0, 1584962500724866, 1584962500724866
  ]

abbrev PositiveTerm := Fin 32
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 16205459 / 25000000000
noncomputable def negativeCeiling : ℝ := 13777177 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 583810995333651752745435136, coefficient := (-583810995333651752745435136) }, { argument := 163975192176108064701677568, coefficient := (-163975192176108064701677568) }, { argument := 1109194275199700726309615304704, coefficient := 1109194275199700726309615304704 }, { argument := 657655645870358271040159744, coefficient := 657655645870358271040159744 }, { argument := 5609415803011879370636656640, coefficient := 5609415803011879370636656640 }, { argument := 5725472681694883771408449536, coefficient := 5725472681694883771408449536 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 4100676380132822160603348992, coefficient := 4100676380132822160603348992 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 5609415803011879370636656640, coefficient := 5609415803011879370636656640 }, { argument := 5725472681694883771408449536, coefficient := 5725472681694883771408449536 }, { argument := 4100676380132822160603348992, coefficient := 4100676380132822160603348992 }, { argument := 92652074815265179949481328640, coefficient := 92652074815265179949481328640 }, { argument := 4100676380132822160603348992, coefficient := 4100676380132822160603348992 }, { argument := 5609415803011879370636656640, coefficient := 5609415803011879370636656640 }, { argument := 5609415803011879370636656640, coefficient := 5609415803011879370636656640 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 4100676380132822160603348992, coefficient := 4100676380132822160603348992 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 5725472681694883771408449536, coefficient := 5725472681694883771408449536 }, { argument := 5725472681694883771408449536, coefficient := 5725472681694883771408449536 }, { argument := 618970019642690137449562112, coefficient := 618970019642690137449562112 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 114169924928512313676594675712, coefficient := 114169924928512313676594675712 }, { argument := 405512934430020374730305961984, coefficient := 405512934430020374730305961984 }, { argument := 114142440755582012341450964992, coefficient := 114142440755582012341450964992 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 11177501454565683606363045888, coefficient := 11177501454565683606363045888 }, { argument := 464088308812835571685562253312, coefficient := 464088308812835571685562253312 }, { argument := 464221054534669037412519247872, coefficient := 464221054534669037412519247872 }, { argument := 11251085369101758418082856960, coefficient := 11251085369101758418082856960 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 1213506515103012730563461120, coefficient := 1213506515103012730563461120 }, { argument := 32683196196485910866696339456, coefficient := 32683196196485910866696339456 }, { argument := 407623029445561018301141745664, coefficient := 407623029445561018301141745664 }, { argument := 32644661685985694561752580096, coefficient := 32644661685985694561752580096 }, { argument := 1204581242450389101109575680, coefficient := 1204581242450389101109575680 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end TermShard2


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk7
