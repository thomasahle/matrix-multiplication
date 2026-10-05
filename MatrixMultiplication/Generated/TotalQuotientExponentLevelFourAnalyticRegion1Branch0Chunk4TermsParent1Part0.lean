import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 4, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk4

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    167, 223, 257, 303, 311, 359,
    1245, 1883, 1885, 7831, 8779, 15723,
    35213, 70141
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 848058251552685469601294444396544, 141501498250476106942069495300096, 345751701212249569258225799266304, 4516005263313067242832005169152, 282686083850895156533764814798848,
    4595233425827331580425549119488, 4119864450741745554864285417472, 4199092613256009892457829367808, 105373456143971568999413453946880, 113613185045455060109142024781824, 105769596956542890687381173698560,
    113850869532997853121922656632832, 328796874434197001013207393894400
  ]
def positiveScales : Array ℕ := #[
    7, 7, 8, 8, 8, 8,
    10, 10, 10, 12, 13, 13,
    15, 16
  ]
def negativeArguments : Array ℕ := #[
    9, 11, 47, 49, 123, 225,
    395, 397, 449, 493, 891, 893,
    1283, 2719095756965
  ]
def negativeCoefficients : Array ℕ := #[
    713053462628379038341895553024, 6972078301255261708231867629568, 3723723638170423866896565665792, 3882179963198952542083653566464, 38980255957018054096023623565312, 71305346262837903834189555302400,
    62590248386268826698899720765440, 62907161036325884049273896566784, 71146889937809375159002467401728, 39059484119532318433617167515648, 141184585600419049591695319498752, 141501498250476106942069495300096,
    203299465011602290265033776562176, 565372167701790313067529629597696
  ]
def negativeScales : Array ℕ := #[
    3, 3, 5, 5, 6, 7,
    8, 8, 8, 8, 9, 9,
    10, 41
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7383704292474051, 7800899899879537, 8005624549193878, 8243173983472950, 8280770770130602, 8487840033823039,
    10281930026955443, 10878817284430388, 10880348807966944, 12934980832155414, 13099840899000720, 13940588893810476,
    15103820523556800, 16097970378785121
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3169925001442313, 3459431618637364, 5554588851679165, 5614709844123661, 6942514514520450, 7813781192070436,
    8625708843075807, 8632995197156697, 8810571635541341, 8945443846028074, 9799281622158559, 9802516365801205,
    10325305455089683, 41306264097538040
  ]

abbrev PositiveTerm := Fin 14
abbrev NegativeTerm := Fin 14
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
noncomputable def positiveFloor : ℝ := 295059521141 / 1000000000000
noncomputable def negativeCeiling : ℝ := 93825821823 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9, coefficient := (-713053462628379038341895553024) }, { argument := 11, coefficient := (-6972078301255261708231867629568) }, { argument := 47, coefficient := (-3723723638170423866896565665792) }, { argument := 49, coefficient := (-3882179963198952542083653566464) }, { argument := 123, coefficient := (-38980255957018054096023623565312) }, { argument := 167, coefficient := 158456325028528675187087900672 }, { argument := 223, coefficient := 848058251552685469601294444396544 }, { argument := 225, coefficient := (-71305346262837903834189555302400) }, { argument := 257, coefficient := 141501498250476106942069495300096 }, { argument := 303, coefficient := 345751701212249569258225799266304 }, { argument := 311, coefficient := 4516005263313067242832005169152 }, { argument := 359, coefficient := 282686083850895156533764814798848 }, { argument := 395, coefficient := (-62590248386268826698899720765440) }, { argument := 397, coefficient := (-62907161036325884049273896566784) }, { argument := 449, coefficient := (-71146889937809375159002467401728) }, { argument := 493, coefficient := (-39059484119532318433617167515648) }, { argument := 891, coefficient := (-141184585600419049591695319498752) }, { argument := 893, coefficient := (-141501498250476106942069495300096) }, { argument := 1245, coefficient := 4595233425827331580425549119488 }, { argument := 1283, coefficient := (-203299465011602290265033776562176) }, { argument := 1883, coefficient := 4119864450741745554864285417472 }, { argument := 1885, coefficient := 4199092613256009892457829367808 }, { argument := 7831, coefficient := 105373456143971568999413453946880 }, { argument := 8779, coefficient := 113613185045455060109142024781824 }, { argument := 15723, coefficient := 105769596956542890687381173698560 }, { argument := 35213, coefficient := 113850869532997853121922656632832 }, { argument := 70141, coefficient := 328796874434197001013207393894400 }, { argument := 2719095756965, coefficient := (-565372167701790313067529629597696) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  rfl

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk4
