import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 8, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    1, 84275, 8221607, 4109271, 168517, 44253,
    1318493, 3511195, 20659, 23757
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 1591909741375357401536921600, 77650882664252910352879058944, 77621934557712919427719102464, 1591598065187488004952817664, 417957767932860819283378176,
    12452814302196494253483360256, 132649196662555871408826613760, 12487599253709312060127444992, 448757042134136645367103488
  ]
def positiveScales : Array ℕ := #[
    0, 16, 22, 21, 17, 15,
    20, 21, 14, 14
  ]
def negativeArguments : Array ℕ := #[
    3729421575, 111115997575, 295905958625, 1741037225, 2002121175, 3729421575,
    363830774571, 181847569563, 7457382801, 363830774571, 10840131278251, 28867665390365,
    169850179013, 195320717499, 111115997575, 10840131278251, 5418045048603, 222188484881,
    181847569563, 5418045048603, 14428451788845, 84893429589, 97623951147, 295905958625,
    28867665390365, 14428451788845, 591696047815, 7457382801, 222188484881, 591696047815,
    3481392703, 4003458369, 1741037225, 169850179013, 84893429589, 3481392703,
    2002121175, 195320717499, 97623951147, 4003458369, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    2099477701934686037606400, 62552745659208867145318400, 666320982500129703460864000, 62727476781985299221708800, 2254188044420144902963200, 2099477701934686037606400,
    102409258798992158229528576, 102371080815269643766726656, 2099066650233921607827456, 102409258798992158229528576, 3051225699086153880652742656, 32502101773775994487580917760,
    3059748811647035360298401792, 109955788818279289677938688, 62552745659208867145318400, 3051225699086153880652742656, 3050088207745628961176027136, 62540498607255417767591936,
    102371080815269643766726656, 3050088207745628961176027136, 32489985049887754217387458560, 3058608142905790715136049152, 109914797502016176393289728, 666320982500129703460864000,
    32502101773775994487580917760, 32489985049887754217387458560, 666190525114057295984066560, 2099066650233921607827456, 62540498607255417767591936, 666190525114057295984066560,
    62715195519844655407562752, 2253746702352711709360128, 62727476781985299221708800, 3059748811647035360298401792, 3058608142905790715136049152, 62715195519844655407562752,
    2254188044420144902963200, 109955788818279289677938688, 109914797502016176393289728, 2253746702352711709360128, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    31, 36, 38, 30, 30, 31,
    38, 37, 32, 38, 43, 44,
    37, 37, 36, 43, 42, 37,
    37, 42, 43, 36, 36, 38,
    44, 43, 39, 32, 37, 39,
    31, 31, 30, 37, 36, 31,
    30, 37, 36, 31, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 16362817101758934, 22970988979877623, 21970451045545589, 17362534612304307, 15433487641262925,
    20330458481146977, 21743530690202026, 14334482801711899, 14536065045722443
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    31796304743620901, 36693275582967660, 38106347791973065, 30697299903538759, 30898882151762329, 31796304743620901,
    38404476622053312, 37403938687713233, 32796022254162816, 38404476622053312, 43301447461937354, 44714519671105988,
    37305471782502276, 37507054026513217, 36693275582967660, 43301447461937354, 42300909527597276, 37692993093512619,
    37403938687713233, 42300909527597276, 43713981736764660, 36304933848162197, 36506516092173132, 38106347791973065,
    44714519671105988, 43713981736764660, 39106065302518438, 32796022254162816, 37692993093512619, 39106065302518438,
    31697017414083679, 31898599662286042, 30697299903538759, 37305471782502276, 36304933848162197, 31697017414083679,
    30898882151762329, 37507054026513217, 36506516092173132, 31898599662286042, 0, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 82721087 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1292517 / 15625000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2099477701934686037606400, coefficient := (-2099477701934686037606400) }, { argument := 62552745659208867145318400, coefficient := (-62552745659208867145318400) }, { argument := 666320982500129703460864000, coefficient := (-666320982500129703460864000) }, { argument := 62727476781985299221708800, coefficient := (-62727476781985299221708800) }, { argument := 2254188044420144902963200, coefficient := (-2254188044420144902963200) }, { argument := 2099477701934686037606400, coefficient := (-2099477701934686037606400) }, { argument := 102409258798992158229528576, coefficient := (-102409258798992158229528576) }, { argument := 102371080815269643766726656, coefficient := (-102371080815269643766726656) }, { argument := 2099066650233921607827456, coefficient := (-2099066650233921607827456) }, { argument := 102409258798992158229528576, coefficient := (-102409258798992158229528576) }, { argument := 3051225699086153880652742656, coefficient := (-3051225699086153880652742656) }, { argument := 32502101773775994487580917760, coefficient := (-32502101773775994487580917760) }, { argument := 3059748811647035360298401792, coefficient := (-3059748811647035360298401792) }, { argument := 109955788818279289677938688, coefficient := (-109955788818279289677938688) }, { argument := 62552745659208867145318400, coefficient := (-62552745659208867145318400) }, { argument := 3051225699086153880652742656, coefficient := (-3051225699086153880652742656) }, { argument := 3050088207745628961176027136, coefficient := (-3050088207745628961176027136) }, { argument := 62540498607255417767591936, coefficient := (-62540498607255417767591936) }, { argument := 102371080815269643766726656, coefficient := (-102371080815269643766726656) }, { argument := 3050088207745628961176027136, coefficient := (-3050088207745628961176027136) }, { argument := 32489985049887754217387458560, coefficient := (-32489985049887754217387458560) }, { argument := 3058608142905790715136049152, coefficient := (-3058608142905790715136049152) }, { argument := 109914797502016176393289728, coefficient := (-109914797502016176393289728) }, { argument := 666320982500129703460864000, coefficient := (-666320982500129703460864000) }, { argument := 32502101773775994487580917760, coefficient := (-32502101773775994487580917760) }, { argument := 32489985049887754217387458560, coefficient := (-32489985049887754217387458560) }, { argument := 666190525114057295984066560, coefficient := (-666190525114057295984066560) }, { argument := 2099066650233921607827456, coefficient := (-2099066650233921607827456) }, { argument := 62540498607255417767591936, coefficient := (-62540498607255417767591936) }, { argument := 666190525114057295984066560, coefficient := (-666190525114057295984066560) }, { argument := 62715195519844655407562752, coefficient := (-62715195519844655407562752) }, { argument := 2253746702352711709360128, coefficient := (-2253746702352711709360128) }, { argument := 62727476781985299221708800, coefficient := (-62727476781985299221708800) }, { argument := 3059748811647035360298401792, coefficient := (-3059748811647035360298401792) }, { argument := 3058608142905790715136049152, coefficient := (-3058608142905790715136049152) }, { argument := 62715195519844655407562752, coefficient := (-62715195519844655407562752) }, { argument := 2254188044420144902963200, coefficient := (-2254188044420144902963200) }, { argument := 109955788818279289677938688, coefficient := (-109955788818279289677938688) }, { argument := 109914797502016176393289728, coefficient := (-109914797502016176393289728) }, { argument := 2253746702352711709360128, coefficient := (-2253746702352711709360128) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 1591909741375357401536921600, coefficient := 1591909741375357401536921600 }, { argument := 77650882664252910352879058944, coefficient := 77650882664252910352879058944 }, { argument := 77621934557712919427719102464, coefficient := 77621934557712919427719102464 }, { argument := 1591598065187488004952817664, coefficient := 1591598065187488004952817664 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 417957767932860819283378176, coefficient := 417957767932860819283378176 }, { argument := 12452814302196494253483360256, coefficient := 12452814302196494253483360256 }, { argument := 132649196662555871408826613760, coefficient := 132649196662555871408826613760 }, { argument := 12487599253709312060127444992, coefficient := 12487599253709312060127444992 }, { argument := 448757042134136645367103488, coefficient := 448757042134136645367103488 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk8
