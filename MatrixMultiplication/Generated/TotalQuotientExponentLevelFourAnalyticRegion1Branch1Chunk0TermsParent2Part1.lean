import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 256289453940399718847443049119744
def positiveArguments : Array ℕ := #[
    5, 3, 2445, 2675, 2445, 2675,
    21, 3507, 91, 3773, 5649, 175,
    5649, 5887, 3507, 175, 31, 35,
    15, 395
  ]
def positiveCoefficients : Array ℕ := #[
    3169126500570573503741758013440, 475368975085586025561263702016, 189172712253297173258022420480, 206968100318024514709697331200, 189172712253297173258022420480, 206968100318024514709697331200,
    6499185206248246443220402176, 135670491180432144502225895424, 7040783973435600313488769024, 145960867756991868037324865536, 218535102560097286653286023168, 6769984589841923378354585600,
    218535102560097286653286023168, 227742281602282302447848259584, 135670491180432144502225895424, 6769984589841923378354585600, 4797017652230848565234106368, 5415987671873538702683668480,
    4642275147320176030871715840, 61123289439715651073144258560
  ]
def positiveScales : Array ℕ := #[
    2, 1, 11, 11, 11, 11,
    4, 11, 6, 11, 12, 7,
    12, 12, 11, 7, 4, 5,
    3, 8
  ]
def negativeArguments : Array ℕ := #[
    35, 4375848309, 31880336173, 8751702505, 1451, 1451,
    153, 9, 9, 5, 2606777649, 18991734153,
    5213558805, 395, 395, 3, 1451, 1451,
    2451, 157, 1020587641, 547575175, 1020587641, 547575175,
    555729, 153, 130078725, 947691325, 260157625, 35,
    35, 5, 9, 9, 157, 5,
    35, 35, 153, 5, 24765, 3,
    5, 7
  ]
def negativeCoefficients : Array ℕ := #[
    1353996917968384675670917120, 20180038465374428199005454336, 73511050295894499584896925696, 20180052039872223440021749760, 56132843656346461839957164032, 56132843656346461839957164032,
    2959450406416612219680718848, 1392682544196052809261514752, 1392682544196052809261514752, 3094850098213450687247810560, 12021640037042316917600157696, 43791957429540005103487942656,
    12021648123633750230024847360, 15280822359928912768286064640, 15280822359928912768286064640, 1856910058928070412348686336, 56132843656346461839957164032, 56132843656346461839957164032,
    47409234942007297715277398016, 3036821658871948486861914112, 2353314877289745175367647232, 1262622389292715078162841600, 2353314877289745175367647232, 1262622389292715078162841600,
    20994848025269320519696515072, 2959450406416612219680718848, 599882237377361123632742400, 2185227416643712829515366400, 599882640899887736029184000, 1353996917968384675670917120,
    1353996917968384675670917120, 96714065569170333976494080, 1392682544196052809261514752, 1392682544196052809261514752, 3036821658871948486861914112, 96714065569170333976494080,
    1353996917968384675670917120, 1353996917968384675670917120, 2959450406416612219680718848, 3094850098213450687247810560, 233898811896533527434362880, 475368975085586025561263702016,
    792281625142643375935439503360, 1109194275199700726309615304704
  ]
def negativeScales : Array ℕ := #[
    5, 32, 34, 33, 10, 10,
    7, 3, 3, 2, 31, 34,
    32, 8, 8, 1, 10, 10,
    11, 7, 29, 29, 29, 29,
    19, 7, 26, 29, 27, 5,
    5, 2, 3, 3, 7, 2,
    5, 5, 7, 2, 14, 1,
    2, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 1584962500720924, 11255618749839595, 11385323176175871, 11255618749839595, 11385323176175871,
    4392317422778759, 11776021715228447, 6507794640198673, 11881496384617007, 12463779785335379, 7451211111832325,
    12463779785335379, 12523316912312711, 11776021715228447, 7451211111832325, 4954196309696329, 5129283016944966,
    3906890595303263, 8625708843063759
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    5129283016944967, 32026915581228575, 34891947795046392, 33026916551685302, 10502831804067043, 10502831804067043,
    7257387842692652, 3169925001442313, 3169925001442313, 2321928094887363, 31279620384168640, 34144652594208662,
    32279621354625366, 8625708843075807, 8625708843075807, 1584962500724866, 10502831804067043, 10502831804067043,
    11259154768866840, 7294620748891628, 29926752937338929, 29028481800807505, 29926752937338929, 29028481800807505,
    19084022001866714, 7257387842692652, 26954809792051575, 29819841991751165, 27954810762508485, 5129283016944967,
    5129283016944967, 2321928094887363, 3169925001442313, 3169925001442313, 7294620748891628, 2321928094887363,
    5129283016944967, 5129283016944967, 7257387842692652, 2321928094887363, 14596015000526839, 1584962500724866,
    2321928094887363, 2807354922807594
  ]

abbrev PositiveTerm := Fin 20
abbrev NegativeTerm := Fin 44
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
noncomputable def positiveFloor : ℝ := 93541789 / 250000000000
noncomputable def negativeCeiling : ℝ := 2989497 / 15625000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 20180038465374428199005454336, coefficient := (-20180038465374428199005454336) }, { argument := 73511050295894499584896925696, coefficient := (-73511050295894499584896925696) }, { argument := 20180052039872223440021749760, coefficient := (-20180052039872223440021749760) }, { argument := 56132843656346461839957164032, coefficient := (-56132843656346461839957164032) }, { argument := 56132843656346461839957164032, coefficient := (-56132843656346461839957164032) }, { argument := 2959450406416612219680718848, coefficient := (-2959450406416612219680718848) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 3094850098213450687247810560, coefficient := (-3094850098213450687247810560) }, { argument := 12021640037042316917600157696, coefficient := (-12021640037042316917600157696) }, { argument := 43791957429540005103487942656, coefficient := (-43791957429540005103487942656) }, { argument := 12021648123633750230024847360, coefficient := (-12021648123633750230024847360) }, { argument := 15280822359928912768286064640, coefficient := (-15280822359928912768286064640) }, { argument := 15280822359928912768286064640, coefficient := (-15280822359928912768286064640) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 56132843656346461839957164032, coefficient := (-56132843656346461839957164032) }, { argument := 56132843656346461839957164032, coefficient := (-56132843656346461839957164032) }, { argument := 47409234942007297715277398016, coefficient := (-47409234942007297715277398016) }, { argument := 3036821658871948486861914112, coefficient := (-3036821658871948486861914112) }, { argument := 2353314877289745175367647232, coefficient := (-2353314877289745175367647232) }, { argument := 1262622389292715078162841600, coefficient := (-1262622389292715078162841600) }, { argument := 2353314877289745175367647232, coefficient := (-2353314877289745175367647232) }, { argument := 1262622389292715078162841600, coefficient := (-1262622389292715078162841600) }, { argument := 20994848025269320519696515072, coefficient := (-20994848025269320519696515072) }, { argument := 2959450406416612219680718848, coefficient := (-2959450406416612219680718848) }, { argument := 599882237377361123632742400, coefficient := (-599882237377361123632742400) }, { argument := 2185227416643712829515366400, coefficient := (-2185227416643712829515366400) }, { argument := 599882640899887736029184000, coefficient := (-599882640899887736029184000) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 96714065569170333976494080, coefficient := (-96714065569170333976494080) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 3036821658871948486861914112, coefficient := (-3036821658871948486861914112) }, { argument := 96714065569170333976494080, coefficient := (-96714065569170333976494080) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 1353996917968384675670917120, coefficient := (-1353996917968384675670917120) }, { argument := 2959450406416612219680718848, coefficient := (-2959450406416612219680718848) }, { argument := 3094850098213450687247810560, coefficient := (-3094850098213450687247810560) }, { argument := 233898811896533527434362880, coefficient := (-233898811896533527434362880) }, { argument := 3169126500570573503741758013440, coefficient := 3169126500570573503741758013440 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 6499185206248246443220402176, coefficient := 6499185206248246443220402176 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 145960867756991868037324865536, coefficient := 145960867756991868037324865536 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 6769984589841923378354585600, coefficient := 6769984589841923378354585600 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 227742281602282302447848259584, coefficient := 227742281602282302447848259584 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 6769984589841923378354585600, coefficient := 6769984589841923378354585600 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 4797017652230848565234106368, coefficient := 4797017652230848565234106368 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 61123289439715651073144258560, coefficient := 61123289439715651073144258560 }] }

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

namespace Parent2

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-70170534528399648280532041596928)
def positiveArguments : Array ℕ := #[
    35, 15, 35, 35, 1451, 9,
    395, 1451, 31, 35, 9, 35,
    3, 87, 77, 5, 3, 5,
    153, 5, 3, 2451, 157, 87,
    153, 5, 157, 5, 153, 5,
    3, 1, 1, 1, 5203149, 37907653,
    10406305, 1023505, 10229885, 20459765, 1023505, 12477,
    511185, 10525695, 511185, 12477
  ]
def positiveCoefficients : Array ℕ := #[
    5415987671873538702683668480, 4642275147320176030871715840, 5415987671873538702683668480, 5415987671873538702683668480, 224531374625385847359828656128, 5570730176784211237046059008,
    61123289439715651073144258560, 224531374625385847359828656128, 4797017652230848565234106368, 5415987671873538702683668480, 5570730176784211237046059008, 5415987671873538702683668480,
    232113757366008801543585792, 3365649481807127622381993984, 5957586439060892572952035328, 193428131138340667952988160, 3713820117856140824697372672, 193428131138340667952988160,
    5918900812833224439361437696, 6189700196426901374495621120, 3713820117856140824697372672, 94818469884014595430554796032, 6073643317743896973723828224, 3365649481807127622381993984,
    5918900812833224439361437696, 193428131138340667952988160, 6073643317743896973723828224, 193428131138340667952988160, 5918900812833224439361437696, 6189700196426901374495621120,
    232113757366008801543585792, 158456325028528675187087900672, 316912650057057350374175801344, 316912650057057350374175801344, 196569411543813692991977029632, 716055319885811819975595261952,
    196569543770075213342043013120, 9666731414098992448887848960, 386474128380887524215284039680, 386474033933557866822379765760, 9666731414098992448887848960, 235683866427058253325139968,
    38624046568731513417011036160, 397649514215268882220591349760, 38624046568731513417011036160, 235683866427058253325139968
  ]
def positiveScales : Array ℕ := #[
    5, 3, 5, 5, 10, 3,
    8, 10, 4, 5, 3, 5,
    1, 6, 6, 2, 1, 2,
    7, 2, 1, 11, 7, 6,
    7, 2, 7, 2, 7, 2,
    1, 0, 0, 0, 22, 25,
    23, 19, 23, 24, 19, 13,
    18, 23, 18, 13
  ]
def negativeArguments : Array ℕ := #[
    1, 1, 1, 1, 7, 5,
    3
  ]
def negativeCoefficients : Array ℕ := #[
    633825300114114700748351602688, 158456325028528675187087900672, 158456325028528675187087900672, 633825300114114700748351602688, 1109194275199700726309615304704, 792281625142643375935439503360,
    475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    0, 0, 0, 0, 2, 2,
    1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5129283016944966, 3906890595303263, 5129283016944966, 5129283016944966, 10502831804066725, 3169925001442312,
    8625708843063759, 10502831804066725, 4954196309696329, 5129283016944966, 3169925001442312, 5129283016944966,
    1584962500720924, 6442943495848725, 6266786540694901, 2321928094887362, 1584962500720924, 2321928094887362,
    7257387842692651, 2321928094887362, 1584962500720924, 11259154768866839, 7294620748891626, 6442943495848725,
    7257387842692651, 2321928094887362, 7294620748891626, 2321928094887362, 7257387842692651, 2321928094887362,
    1584962500720924, 0, 0, 0, 22310953590973430, 25175985801013453,
    23310954561430156, 19965086718690982, 23286286591224177, 24286286238655400, 19965086718690982, 13606983470367085,
    18963485976693339, 23327412160206294, 18963485976693339, 13606983470367085
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0, 0, 0, 2807354922807594, 2321928094887363,
    1584962500724866
  ]

abbrev PositiveTerm := Fin 46
abbrev NegativeTerm := Fin 7
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
noncomputable def positiveFloor : ℝ := 762943471 / 1000000000000
noncomputable def negativeCeiling : ℝ := 68695093 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 224531374625385847359828656128, coefficient := 224531374625385847359828656128 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 61123289439715651073144258560, coefficient := 61123289439715651073144258560 }, { argument := 224531374625385847359828656128, coefficient := 224531374625385847359828656128 }, { argument := 4797017652230848565234106368, coefficient := 4797017652230848565234106368 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 5957586439060892572952035328, coefficient := 5957586439060892572952035328 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 6189700196426901374495621120, coefficient := 6189700196426901374495621120 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 94818469884014595430554796032, coefficient := 94818469884014595430554796032 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 6189700196426901374495621120, coefficient := 6189700196426901374495621120 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 196569411543813692991977029632, coefficient := 196569411543813692991977029632 }, { argument := 716055319885811819975595261952, coefficient := 716055319885811819975595261952 }, { argument := 196569543770075213342043013120, coefficient := 196569543770075213342043013120 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 9666731414098992448887848960, coefficient := 9666731414098992448887848960 }, { argument := 386474128380887524215284039680, coefficient := 386474128380887524215284039680 }, { argument := 386474033933557866822379765760, coefficient := 386474033933557866822379765760 }, { argument := 9666731414098992448887848960, coefficient := 9666731414098992448887848960 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 235683866427058253325139968, coefficient := 235683866427058253325139968 }, { argument := 38624046568731513417011036160, coefficient := 38624046568731513417011036160 }, { argument := 397649514215268882220591349760, coefficient := 397649514215268882220591349760 }, { argument := 38624046568731513417011036160, coefficient := 38624046568731513417011036160 }, { argument := 235683866427058253325139968, coefficient := 235683866427058253325139968 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end TermShard3


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0
