import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 0, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0

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
def constantNumerator : ℤ := (-61653867811495468765588840513536)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    24765, 555729, 77, 10530815, 3, 5,
    153, 5, 3, 2451, 157, 555729,
    153, 5, 157, 5, 153, 5,
    24765, 1020587641, 35, 5128242885, 395, 35,
    10256483325, 35, 35, 1451, 9, 395,
    1451, 1020587641, 35, 9, 35, 15609447,
    2606777649, 67640937, 3259389147, 4198941243, 254954385, 4198941243,
    4375848309, 2606777649, 130078725, 547575175, 5472988475, 10945974275,
    547575175, 2606777649, 18991734153, 5213558805, 1020587641, 547575175,
    1020587641, 547575175, 67640937, 492799489, 135281965, 35,
    35, 24765, 1020587641, 35
  ]
def negativeCoefficients : Array ℕ := #[
    233898811896533527434362880, 20994848025269320519696515072, 2978793219530446286476017664, 198921471173203611444272168960, 1856910058928070412348686336, 96714065569170333976494080,
    2959450406416612219680718848, 3094850098213450687247810560, 1856910058928070412348686336, 47409234942007297715277398016, 3036821658871948486861914112, 20994848025269320519696515072,
    2959450406416612219680718848, 96714065569170333976494080, 3036821658871948486861914112, 96714065569170333976494080, 2959450406416612219680718848, 3094850098213450687247810560,
    233898811896533527434362880, 2353314877289745175367647232, 1353996917968384675670917120, 47299692023708461815646126080, 15280822359928912768286064640, 1353996917968384675670917120,
    47299680748136146760682700800, 1353996917968384675670917120, 1353996917968384675670917120, 56132843656346461839957164032, 1392682544196052809261514752, 15280822359928912768286064640,
    56132843656346461839957164032, 2353314877289745175367647232, 1353996917968384675670917120, 1392682544196052809261514752, 1353996917968384675670917120, 1151773895764533357374865408,
    12021640037042316917600157696, 623877526872455568578052096, 15031279357833870141856677888, 19364198622541217070864924672, 1175769572641253350220759040, 19364198622541217070864924672,
    20180038465374428199005454336, 12021640037042316917600157696, 599882237377361123632742400, 1262622389292715078162841600, 50479408858343463245892812800, 50479396522083363952630169600,
    1262622389292715078162841600, 12021640037042316917600157696, 43791957429540005103487942656, 12021648123633750230024847360, 2353314877289745175367647232, 1262622389292715078162841600,
    2353314877289745175367647232, 1262622389292715078162841600, 623877526872455568578052096, 2272636513309461342695981056, 623877946535883245470351360, 1353996917968384675670917120,
    1353996917968384675670917120, 233898811896533527434362880, 2353314877289745175367647232, 1353996917968384675670917120
  ]
def negativeScales : Array ℕ := #[
    14, 19, 6, 23, 1, 2,
    7, 2, 1, 11, 7, 19,
    7, 2, 7, 2, 7, 2,
    14, 29, 5, 32, 8, 5,
    33, 5, 5, 10, 3, 8,
    10, 29, 5, 3, 5, 23,
    31, 26, 31, 31, 27, 31,
    32, 31, 26, 29, 32, 33,
    29, 31, 34, 32, 29, 29,
    29, 29, 26, 28, 27, 5,
    5, 14, 29, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14596015000526839, 19084022001866714, 6266786540694902, 23328113757836191, 1584962500724866, 2321928094887363,
    7257387842692652, 2321928094887363, 1584962500724866, 11259154768866840, 7294620748891628, 19084022001866714,
    7257387842692652, 2321928094887363, 7294620748891628, 2321928094887363, 7257387842692652, 2321928094887363,
    14596015000526839, 29926752937338929, 5129283016944967, 32255817446810077, 8625708843075807, 5129283016944967,
    33255817102892104, 5129283016944967, 5129283016944967, 10502831804067043, 3169925001442313, 8625708843075807,
    10502831804067043, 29926752937338929, 5129283016944967, 3169925001442313, 5129283016944967, 23895916095753100,
    31279620384168640, 26011393309114523, 31601954463488472, 31967378468189136, 27925663917284852, 31967378468189136,
    32026915581228575, 31279620384168640, 26954809792051575, 29028481800807505, 32349681672512688, 33349681319943911,
    29028481800807505, 31279620384168640, 34144652594208662, 32279621354625366, 29926752937338929, 29028481800807505,
    29926752937338929, 29028481800807505, 26011393309114523, 28876425521998986, 27011394279571249, 5129283016944967,
    5129283016944967, 14596015000526839, 29926752937338929, 5129283016944967
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
noncomputable def negativeCeiling : ℝ := 60559509 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 233898811896533527434362880, coefficient := (-233898811896533527434362880) }, { argument := 20994848025269320519696515072, coefficient := (-20994848025269320519696515072) }, { argument := 2978793219530446286476017664, coefficient := (-2978793219530446286476017664) }, { argument := 198921471173203611444272168960, coefficient := (-198921471173203611444272168960) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 96714065569170333976494080, coefficient := (-96714065569170333976494080) }, { argument := 2959450406416612219680718848, coefficient := (-2959450406416612219680718848) }, { argument := 3094850098213450687247810560, coefficient := (-3094850098213450687247810560) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 47409234942007297715277398016, coefficient := (-47409234942007297715277398016) }, { argument := 3036821658871948486861914112, coefficient := (-3036821658871948486861914112) }, { argument := 20994848025269320519696515072, coefficient := (-20994848025269320519696515072) }, { argument := 2959450406416612219680718848, coefficient := (-2959450406416612219680718848) }, { argument := 96714065569170333976494080, coefficient := (-96714065569170333976494080) }, { argument := 3036821658871948486861914112, coefficient := (-3036821658871948486861914112) }, { argument := 96714065569170333976494080, coefficient := (-96714065569170333976494080) }, { argument := 2959450406416612219680718848, coefficient := (-2959450406416612219680718848) }, { argument := 3094850098213450687247810560, coefficient := (-3094850098213450687247810560) }, { argument := 233898811896533527434362880, coefficient := (-233898811896533527434362880) }, { argument := 2353314877289745175367647232, coefficient := (-2353314877289745175367647232) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 47299692023708461815646126080, coefficient := (-47299692023708461815646126080) }, { argument := 15280822359928912768286064640, coefficient := (-15280822359928912768286064640) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 47299680748136146760682700800, coefficient := (-47299680748136146760682700800) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 56132843656346461839957164032, coefficient := (-56132843656346461839957164032) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 15280822359928912768286064640, coefficient := (-15280822359928912768286064640) }, { argument := 56132843656346461839957164032, coefficient := (-56132843656346461839957164032) }, { argument := 2353314877289745175367647232, coefficient := (-2353314877289745175367647232) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 1151773895764533357374865408, coefficient := (-1151773895764533357374865408) }, { argument := 12021640037042316917600157696, coefficient := (-12021640037042316917600157696) }, { argument := 623877526872455568578052096, coefficient := (-623877526872455568578052096) }, { argument := 15031279357833870141856677888, coefficient := (-15031279357833870141856677888) }, { argument := 19364198622541217070864924672, coefficient := (-19364198622541217070864924672) }, { argument := 1175769572641253350220759040, coefficient := (-1175769572641253350220759040) }, { argument := 19364198622541217070864924672, coefficient := (-19364198622541217070864924672) }, { argument := 20180038465374428199005454336, coefficient := (-20180038465374428199005454336) }, { argument := 12021640037042316917600157696, coefficient := (-12021640037042316917600157696) }, { argument := 599882237377361123632742400, coefficient := (-599882237377361123632742400) }, { argument := 1262622389292715078162841600, coefficient := (-1262622389292715078162841600) }, { argument := 50479408858343463245892812800, coefficient := (-50479408858343463245892812800) }, { argument := 50479396522083363952630169600, coefficient := (-50479396522083363952630169600) }, { argument := 1262622389292715078162841600, coefficient := (-1262622389292715078162841600) }, { argument := 12021640037042316917600157696, coefficient := (-12021640037042316917600157696) }, { argument := 43791957429540005103487942656, coefficient := (-43791957429540005103487942656) }, { argument := 12021648123633750230024847360, coefficient := (-12021648123633750230024847360) }, { argument := 2353314877289745175367647232, coefficient := (-2353314877289745175367647232) }, { argument := 1262622389292715078162841600, coefficient := (-1262622389292715078162841600) }, { argument := 2353314877289745175367647232, coefficient := (-2353314877289745175367647232) }, { argument := 1262622389292715078162841600, coefficient := (-1262622389292715078162841600) }, { argument := 623877526872455568578052096, coefficient := (-623877526872455568578052096) }, { argument := 2272636513309461342695981056, coefficient := (-2272636513309461342695981056) }, { argument := 623877946535883245470351360, coefficient := (-623877946535883245470351360) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 233898811896533527434362880, coefficient := (-233898811896533527434362880) }, { argument := 2353314877289745175367647232, coefficient := (-2353314877289745175367647232) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }] }

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
def constantNumerator : ℤ := (-115885388123318231306268208791552)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5128242885, 395, 35, 10256483325, 35, 35,
    1451, 9, 395, 1451, 1020587641, 35,
    9, 35, 3259389147, 18991734153, 492799489, 20432224967,
    30591475971, 819586215, 30591475971, 31880336173, 18991734153, 947691325,
    5128242885, 5472988475, 5128242885, 5472988475, 4198941243, 30591475971,
    8397888135, 395, 395, 555729, 35, 35,
    77, 254954385, 5213558805, 135281965, 819586215, 8397888135,
    260157625, 8397888135, 8751702505, 5213558805, 260157625, 10256483325,
    10945974275, 10256483325, 10945974275, 10530815, 35, 35,
    3, 5, 547575175, 5472988475, 10945974275, 547575175,
    4198941243, 30591475971, 8397888135, 35
  ]
def negativeCoefficients : Array ℕ := #[
    47299692023708461815646126080, 15280822359928912768286064640, 1353996917968384675670917120, 47299680748136146760682700800, 1353996917968384675670917120, 1353996917968384675670917120,
    56132843656346461839957164032, 1392682544196052809261514752, 15280822359928912768286064640, 56132843656346461839957164032, 2353314877289745175367647232, 1353996917968384675670917120,
    1392682544196052809261514752, 1353996917968384675670917120, 15031279357833870141856677888, 43791957429540005103487942656, 2272636513309461342695981056, 94227006205676897208702599168,
    70539141009259050136756027392, 15118697154445292418304573440, 70539141009259050136756027392, 73511050295894499584896925696, 43791957429540005103487942656, 2185227416643712829515366400,
    47299692023708461815646126080, 50479408858343463245892812800, 47299692023708461815646126080, 50479408858343463245892812800, 19364198622541217070864924672, 70539141009259050136756027392,
    19364211648248376119022059520, 15280822359928912768286064640, 15280822359928912768286064640, 20994848025269320519696515072, 1353996917968384675670917120, 1353996917968384675670917120,
    2978793219530446286476017664, 1175769572641253350220759040, 12021648123633750230024847360, 623877946535883245470351360, 15118697154445292418304573440, 19364211648248376119022059520,
    1199765281799775472058368000, 19364211648248376119022059520, 20180052039872223440021749760, 12021648123633750230024847360, 599882640899887736029184000, 47299680748136146760682700800,
    50479396522083363952630169600, 47299680748136146760682700800, 50479396522083363952630169600, 198921471173203611444272168960, 1353996917968384675670917120, 1353996917968384675670917120,
    1856910058928070412348686336, 96714065569170333976494080, 1262622389292715078162841600, 50479408858343463245892812800, 50479396522083363952630169600, 1262622389292715078162841600,
    19364198622541217070864924672, 70539141009259050136756027392, 19364211648248376119022059520, 1353996917968384675670917120
  ]
def negativeScales : Array ℕ := #[
    32, 8, 5, 33, 5, 5,
    10, 3, 8, 10, 29, 5,
    3, 5, 31, 34, 28, 34,
    34, 29, 34, 34, 34, 29,
    32, 32, 32, 32, 31, 34,
    32, 8, 8, 19, 5, 5,
    6, 27, 32, 27, 29, 32,
    27, 32, 33, 32, 27, 33,
    33, 33, 33, 23, 5, 5,
    1, 2, 29, 32, 33, 29,
    31, 34, 32, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32255817446810077, 8625708843075807, 5129283016944967, 33255817102892104, 5129283016944967, 5129283016944967,
    10502831804067043, 3169925001442313, 8625708843075807, 10502831804067043, 29926752937338929, 5129283016944967,
    3169925001442313, 5129283016944967, 31601954463488472, 34144652594208662, 28876425521998986, 34250127263765960,
    34832410665524617, 29610320478303799, 34832410665524617, 34891947795046392, 34144652594208662, 29819841991751165,
    32255817446810077, 32349681672512688, 32255817446810077, 32349681672512688, 31967378468189136, 34832410665524617,
    32967379438646086, 8625708843075807, 8625708843075807, 19084022001866714, 5129283016944967, 5129283016944967,
    6266786540694902, 27925663917284852, 32279621354625366, 27011394279571249, 29610320478303799, 32967379438646086,
    27954810762508485, 32967379438646086, 33026916551685302, 32279621354625366, 27954810762508485, 33255817102892104,
    33349681319943911, 33255817102892104, 33349681319943911, 23328113757836191, 5129283016944967, 5129283016944967,
    1584962500724866, 2321928094887363, 29028481800807505, 32349681672512688, 33349681319943911, 29028481800807505,
    31967378468189136, 34832410665524617, 32967379438646086, 5129283016944967
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
noncomputable def negativeCeiling : ℝ := 311055873 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 47299692023708461815646126080, coefficient := (-47299692023708461815646126080) }, { argument := 15280822359928912768286064640, coefficient := (-15280822359928912768286064640) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 47299680748136146760682700800, coefficient := (-47299680748136146760682700800) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 56132843656346461839957164032, coefficient := (-56132843656346461839957164032) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 15280822359928912768286064640, coefficient := (-15280822359928912768286064640) }, { argument := 56132843656346461839957164032, coefficient := (-56132843656346461839957164032) }, { argument := 2353314877289745175367647232, coefficient := (-2353314877289745175367647232) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 15031279357833870141856677888, coefficient := (-15031279357833870141856677888) }, { argument := 43791957429540005103487942656, coefficient := (-43791957429540005103487942656) }, { argument := 2272636513309461342695981056, coefficient := (-2272636513309461342695981056) }, { argument := 94227006205676897208702599168, coefficient := (-94227006205676897208702599168) }, { argument := 70539141009259050136756027392, coefficient := (-70539141009259050136756027392) }, { argument := 15118697154445292418304573440, coefficient := (-15118697154445292418304573440) }, { argument := 70539141009259050136756027392, coefficient := (-70539141009259050136756027392) }, { argument := 73511050295894499584896925696, coefficient := (-73511050295894499584896925696) }, { argument := 43791957429540005103487942656, coefficient := (-43791957429540005103487942656) }, { argument := 2185227416643712829515366400, coefficient := (-2185227416643712829515366400) }, { argument := 47299692023708461815646126080, coefficient := (-47299692023708461815646126080) }, { argument := 50479408858343463245892812800, coefficient := (-50479408858343463245892812800) }, { argument := 47299692023708461815646126080, coefficient := (-47299692023708461815646126080) }, { argument := 50479408858343463245892812800, coefficient := (-50479408858343463245892812800) }, { argument := 19364198622541217070864924672, coefficient := (-19364198622541217070864924672) }, { argument := 70539141009259050136756027392, coefficient := (-70539141009259050136756027392) }, { argument := 19364211648248376119022059520, coefficient := (-19364211648248376119022059520) }, { argument := 15280822359928912768286064640, coefficient := (-15280822359928912768286064640) }, { argument := 15280822359928912768286064640, coefficient := (-15280822359928912768286064640) }, { argument := 20994848025269320519696515072, coefficient := (-20994848025269320519696515072) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 2978793219530446286476017664, coefficient := (-2978793219530446286476017664) }, { argument := 1175769572641253350220759040, coefficient := (-1175769572641253350220759040) }, { argument := 12021648123633750230024847360, coefficient := (-12021648123633750230024847360) }, { argument := 623877946535883245470351360, coefficient := (-623877946535883245470351360) }, { argument := 15118697154445292418304573440, coefficient := (-15118697154445292418304573440) }, { argument := 19364211648248376119022059520, coefficient := (-19364211648248376119022059520) }, { argument := 1199765281799775472058368000, coefficient := (-1199765281799775472058368000) }, { argument := 19364211648248376119022059520, coefficient := (-19364211648248376119022059520) }, { argument := 20180052039872223440021749760, coefficient := (-20180052039872223440021749760) }, { argument := 12021648123633750230024847360, coefficient := (-12021648123633750230024847360) }, { argument := 599882640899887736029184000, coefficient := (-599882640899887736029184000) }, { argument := 47299680748136146760682700800, coefficient := (-47299680748136146760682700800) }, { argument := 50479396522083363952630169600, coefficient := (-50479396522083363952630169600) }, { argument := 47299680748136146760682700800, coefficient := (-47299680748136146760682700800) }, { argument := 50479396522083363952630169600, coefficient := (-50479396522083363952630169600) }, { argument := 198921471173203611444272168960, coefficient := (-198921471173203611444272168960) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 96714065569170333976494080, coefficient := (-96714065569170333976494080) }, { argument := 1262622389292715078162841600, coefficient := (-1262622389292715078162841600) }, { argument := 50479408858343463245892812800, coefficient := (-50479408858343463245892812800) }, { argument := 50479396522083363952630169600, coefficient := (-50479396522083363952630169600) }, { argument := 1262622389292715078162841600, coefficient := (-1262622389292715078162841600) }, { argument := 19364198622541217070864924672, coefficient := (-19364198622541217070864924672) }, { argument := 70539141009259050136756027392, coefficient := (-70539141009259050136756027392) }, { argument := 19364211648248376119022059520, coefficient := (-19364211648248376119022059520) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0
