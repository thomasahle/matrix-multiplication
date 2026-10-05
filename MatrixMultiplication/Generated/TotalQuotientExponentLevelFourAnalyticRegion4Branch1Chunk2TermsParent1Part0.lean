import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 2, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk2

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
def constantNumerator : ℤ := 29654161677219193575025886101504
def positiveArguments : Array ℕ := #[
    5, 454261, 16322963, 16322537, 454671, 96357
  ]
def positiveCoefficients : Array ℕ := #[
    792281625142643375935439503360, 4290373841749695808837517312, 154166026744642705292573802496, 154162003288399300354851733504, 4294246182265648917912748032, 1820132268759481615424421888
  ]
def positiveScales : Array ℕ := #[
    2, 18, 23, 23, 18, 16
  ]
def negativeArguments : Array ℕ := #[
    68458099045, 3742150300567, 3743202432885, 67424084879, 2977777971, 123563326215,
    2727041071425, 123563363703, 5954397021, 2456254142715, 134470365765841, 134508329064635,
    2418927037817, 123563326215, 154812919317, 13631807462847, 2477006751849, 123538373259,
    68458099045, 2456254142715, 614046444423, 17130975713, 614046444423, 134466860600821,
    67252411546051, 2418859446377, 2727041071425, 13631807462847, 150011527875219, 54527229605331,
    2726488889481, 3742150300567, 134470365765841, 134466860600821, 3745523809699, 17130975713,
    3745523809699, 1873288359461, 67489144463, 123563363703, 2477006751849, 54527229605331,
    619251698655, 30884602683, 3743202432885, 134508329064635, 67252411546051, 1873288359461,
    5954397021, 123538373259, 2726488889481, 30884602683, 1488309579, 67424084879,
    2418927037817, 2418859446377, 67489144463, 1
  ]
def negativeCoefficients : Array ℕ := #[
    19269241834347156754923520, 1053321668699870675391741952, 1053617817619576253904322560, 18978192721053818367770624, 1676339970073458955517952, 69559968737316629989294080,
    767593822068354260454604800, 69559989841184483847438336, 1676013762811974465355776, 691374077616156943885271040, 37850043072213489348505501696, 37860728790857390173517250560,
    680867431634316180378877952, 69559968737316629989294080, 2788861622992719448457084928, 30696101505032047847911981056, 2788861671155339763464011776, 69545921471898705941495808,
    19269241834347156754923520, 691374077616156943885271040, 691354834572900195423485952, 19287763959389954257190912, 691354834572900195423485952, 37849056455971117842433048576,
    37859741947320315798892838912, 680848406335316340676493312, 767593822068354260454604800, 30696101505032047847911981056, 337795930520057530987485069312, 30696101366514271158924214272,
    767438396668526815699009536, 1053321668699870675391741952, 37850043072213489348505501696, 37849056455971117842433048576, 1054271227104233560729452544, 19287763959389954257190912,
    1054271227104233560729452544, 1054567594703255920634232832, 18996505365945023335497728, 69559989841184483847438336, 2788861671155339763464011776, 30696101366514271158924214272,
    2788861719311204679029882880, 69545942567322310498320384, 1053617817619576253904322560, 37860728790857390173517250560, 37859741947320315798892838912, 1054567594703255920634232832,
    1676013762811974465355776, 69545921471898705941495808, 767438396668526815699009536, 69545942567322310498320384, 1675687616349084944695296, 18978192721053818367770624,
    680867431634316180378877952, 680848406335316340676493312, 18996505365945023335497728, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    35, 41, 41, 35, 31, 36,
    41, 36, 32, 41, 46, 46,
    41, 36, 37, 43, 41, 36,
    35, 41, 39, 33, 39, 46,
    45, 41, 41, 43, 47, 45,
    41, 41, 46, 46, 41, 33,
    41, 40, 35, 36, 41, 45,
    39, 34, 41, 46, 45, 40,
    32, 36, 41, 34, 30, 35,
    41, 41, 35, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 18793161924366751, 23960399627458571, 23960361975219848, 18794463462889884, 16556101856640700
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    35994502202483728, 41767004643443740, 41767410210462995, 35972544999504271, 31471589041728140, 36846459658049772,
    41310473567209176, 36846460095750397, 32471308273266676, 41159596979269199, 46934281606776073, 46934688846991448,
    41137504392560199, 36846459658049772, 37171734914835287, 43632042097585429, 41171734939750103, 36846168284035023,
    35994502202483728, 41159596979269199, 39159556824119719, 33995888295041685, 39159556824119719, 46934244000343122,
    45934651242511185, 41137464079150081, 41310473567209176, 43632042097585429, 47092066699606684, 45632042091075191,
    41310181415094597, 41767004643443740, 46934281606776073, 46934244000343122, 41768304631981413, 33995888295041685,
    41768304631981413, 40768710132929930, 35973936429694159, 36846460095750397, 41171734939750103, 45632042091075191,
    39171734964661423, 34846168721648886, 41767410210462995, 46934688846991448, 45934651242511185, 40768710132929930,
    32471308273266676, 36846168284035023, 41310181415094597, 34846168721648886, 30471027502498119, 35972544999504271,
    41137504392560199, 41137464079150081, 35973936429694159, 0
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 58
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
noncomputable def positiveFloor : ℝ := 113374079 / 1000000000000
noncomputable def negativeCeiling : ℝ := 441686799 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 19269241834347156754923520, coefficient := (-19269241834347156754923520) }, { argument := 1053321668699870675391741952, coefficient := (-1053321668699870675391741952) }, { argument := 1053617817619576253904322560, coefficient := (-1053617817619576253904322560) }, { argument := 18978192721053818367770624, coefficient := (-18978192721053818367770624) }, { argument := 1676339970073458955517952, coefficient := (-1676339970073458955517952) }, { argument := 69559968737316629989294080, coefficient := (-69559968737316629989294080) }, { argument := 767593822068354260454604800, coefficient := (-767593822068354260454604800) }, { argument := 69559989841184483847438336, coefficient := (-69559989841184483847438336) }, { argument := 1676013762811974465355776, coefficient := (-1676013762811974465355776) }, { argument := 691374077616156943885271040, coefficient := (-691374077616156943885271040) }, { argument := 37850043072213489348505501696, coefficient := (-37850043072213489348505501696) }, { argument := 37860728790857390173517250560, coefficient := (-37860728790857390173517250560) }, { argument := 680867431634316180378877952, coefficient := (-680867431634316180378877952) }, { argument := 69559968737316629989294080, coefficient := (-69559968737316629989294080) }, { argument := 2788861622992719448457084928, coefficient := (-2788861622992719448457084928) }, { argument := 30696101505032047847911981056, coefficient := (-30696101505032047847911981056) }, { argument := 2788861671155339763464011776, coefficient := (-2788861671155339763464011776) }, { argument := 69545921471898705941495808, coefficient := (-69545921471898705941495808) }, { argument := 19269241834347156754923520, coefficient := (-19269241834347156754923520) }, { argument := 691374077616156943885271040, coefficient := (-691374077616156943885271040) }, { argument := 691354834572900195423485952, coefficient := (-691354834572900195423485952) }, { argument := 19287763959389954257190912, coefficient := (-19287763959389954257190912) }, { argument := 691354834572900195423485952, coefficient := (-691354834572900195423485952) }, { argument := 37849056455971117842433048576, coefficient := (-37849056455971117842433048576) }, { argument := 37859741947320315798892838912, coefficient := (-37859741947320315798892838912) }, { argument := 680848406335316340676493312, coefficient := (-680848406335316340676493312) }, { argument := 767593822068354260454604800, coefficient := (-767593822068354260454604800) }, { argument := 30696101505032047847911981056, coefficient := (-30696101505032047847911981056) }, { argument := 337795930520057530987485069312, coefficient := (-337795930520057530987485069312) }, { argument := 30696101366514271158924214272, coefficient := (-30696101366514271158924214272) }, { argument := 767438396668526815699009536, coefficient := (-767438396668526815699009536) }, { argument := 1053321668699870675391741952, coefficient := (-1053321668699870675391741952) }, { argument := 37850043072213489348505501696, coefficient := (-37850043072213489348505501696) }, { argument := 37849056455971117842433048576, coefficient := (-37849056455971117842433048576) }, { argument := 1054271227104233560729452544, coefficient := (-1054271227104233560729452544) }, { argument := 19287763959389954257190912, coefficient := (-19287763959389954257190912) }, { argument := 1054271227104233560729452544, coefficient := (-1054271227104233560729452544) }, { argument := 1054567594703255920634232832, coefficient := (-1054567594703255920634232832) }, { argument := 18996505365945023335497728, coefficient := (-18996505365945023335497728) }, { argument := 69559989841184483847438336, coefficient := (-69559989841184483847438336) }, { argument := 2788861671155339763464011776, coefficient := (-2788861671155339763464011776) }, { argument := 30696101366514271158924214272, coefficient := (-30696101366514271158924214272) }, { argument := 2788861719311204679029882880, coefficient := (-2788861719311204679029882880) }, { argument := 69545942567322310498320384, coefficient := (-69545942567322310498320384) }, { argument := 1053617817619576253904322560, coefficient := (-1053617817619576253904322560) }, { argument := 37860728790857390173517250560, coefficient := (-37860728790857390173517250560) }, { argument := 37859741947320315798892838912, coefficient := (-37859741947320315798892838912) }, { argument := 1054567594703255920634232832, coefficient := (-1054567594703255920634232832) }, { argument := 1676013762811974465355776, coefficient := (-1676013762811974465355776) }, { argument := 69545921471898705941495808, coefficient := (-69545921471898705941495808) }, { argument := 767438396668526815699009536, coefficient := (-767438396668526815699009536) }, { argument := 69545942567322310498320384, coefficient := (-69545942567322310498320384) }, { argument := 1675687616349084944695296, coefficient := (-1675687616349084944695296) }, { argument := 18978192721053818367770624, coefficient := (-18978192721053818367770624) }, { argument := 680867431634316180378877952, coefficient := (-680867431634316180378877952) }, { argument := 680848406335316340676493312, coefficient := (-680848406335316340676493312) }, { argument := 18996505365945023335497728, coefficient := (-18996505365945023335497728) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 4290373841749695808837517312, coefficient := 4290373841749695808837517312 }, { argument := 154166026744642705292573802496, coefficient := 154166026744642705292573802496 }, { argument := 154162003288399300354851733504, coefficient := 154162003288399300354851733504 }, { argument := 4294246182265648917912748032, coefficient := 4294246182265648917912748032 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 1820132268759481615424421888, coefficient := 1820132268759481615424421888 }] }

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

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-31050430637031483688892994945024)
def positiveArguments : Array ℕ := #[
    3855369, 84856431, 3855369, 192675, 300969, 1029763,
    16480859, 74099
  ]
def positiveCoefficients : Array ℕ := #[
    72825861378778644791527735296, 801446331220681462140949757952, 72825861378778644791527735296, 1819763924173817783097753600, 2842571835965588500641742848, 155613384847977422854119489536,
    155657312301001076293897289728, 2799381072113262725517279232
  ]
def positiveScales : Array ℕ := #[
    21, 26, 21, 17, 18, 19,
    23, 16
  ]
def negativeArguments : Array ℕ := #[
    3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    950737950171172051122527404032, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    21878437517217920, 26338520665408172, 21878437517217920, 17555809865396598, 18199255370559777, 19973880907651264,
    23974288102537513, 16177166452380480
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 0
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 75266511 / 200000000000
noncomputable def negativeCeiling : ℝ := 18138457 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 72825861378778644791527735296, coefficient := 72825861378778644791527735296 }, { argument := 801446331220681462140949757952, coefficient := 801446331220681462140949757952 }, { argument := 72825861378778644791527735296, coefficient := 72825861378778644791527735296 }, { argument := 1819763924173817783097753600, coefficient := 1819763924173817783097753600 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 2842571835965588500641742848, coefficient := 2842571835965588500641742848 }, { argument := 155613384847977422854119489536, coefficient := 155613384847977422854119489536 }, { argument := 155657312301001076293897289728, coefficient := 155657312301001076293897289728 }, { argument := 2799381072113262725517279232, coefficient := 2799381072113262725517279232 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk2
