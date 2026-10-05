import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 0, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk0

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
def constantNumerator : ℤ := 11863496172815470070159242166272
def positiveArguments : Array ℕ := #[
    1, 58071, 2039083, 8155897, 232703, 38367
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 2193860352213785337636323328, 77034377719914278170231046144, 77030269261074181578895130624, 2197817695326430100325400576, 724732139393038711655497728
  ]
def positiveScales : Array ℕ := #[
    0, 15, 20, 22, 17, 15
  ]
def negativeArguments : Array ℕ := #[
    8181797403, 478953057765, 479112056163, 8022799005, 1472026689, 24926694597,
    541041036543, 12463328115, 735840693, 287292521119, 16817775445345, 16823358454599,
    281709511865, 24926694597, 422098395481, 9161766415739, 211048872895, 12460423689,
    8181797403, 287292521119, 1149108796021, 32786223779, 1149108796021, 67267514025355,
    67289844871341, 1126777950035, 541041036543, 9161766415739, 198858760789441, 4580876157005,
    270457060491, 478953057765, 16817775445345, 67267514025355, 1919268023645, 32786223779,
    1919268023645, 1919905164459, 32149082965, 12463328115, 211048872895, 4580876157005,
    105524274025, 6230202255, 479112056163, 16823358454599, 67289844871341, 1919905164459,
    735840693, 12460423689, 270457060491, 6230202255, 367834041, 8022799005,
    281709511865, 1126777950035, 32149082965, 1
  ]
def negativeCoefficients : Array ℕ := #[
    9211884933842922972905472, 539253203119603411436175360, 539432219401099737890291712, 9032868652346596518789120, 828677356007478125395968, 28064963124656838990102528,
    304579026320900213667004416, 28064919927255113159147520, 828482967699711886098432, 323462622764464688129376256, 18935131807214104854428385280, 18941417716813084962142027776,
    317176713165484580415733760, 28064963124656838990102528, 950481088300957926359564288, 10315231953994421284829659136, 950479625326885173377105920, 28058379741329450569039872,
    9211884933842922972905472, 323462622764464688129376256, 323445371598020931041099776, 9228501574624380949889024, 323445371598020931041099776, 18934121943670524463682682880,
    18940407518024363059703709696, 317159797244182335020072960, 304579026320900213667004416, 10315231953994421284829659136, 111947530123835636071993966592, 10315216076859053864900362240,
    304507579211746823985168384, 539253203119603411436175360, 18935131807214104854428385280, 18934121943670524463682682880, 540225922256983144131461120, 9228501574624380949889024,
    540225922256983144131461120, 540405261452765202537775104, 9049162378842322543575040, 28064919927255113159147520, 950479625326885173377105920, 10315216076859053864900362240,
    950478162355064220208332800, 28058336554060823899668480, 539432219401099737890291712, 18941417716813084962142027776, 18940407518024363059703709696, 540405261452765202537775104,
    828482967699711886098432, 28058379741329450569039872, 304507579211746823985168384, 28058336554060823899668480, 828288624990891873927168, 9032868652346596518789120,
    317176713165484580415733760, 317159797244182335020072960, 9049162378842322543575040, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    32, 38, 38, 32, 30, 34,
    38, 33, 29, 38, 43, 43,
    38, 34, 38, 43, 37, 33,
    32, 38, 40, 34, 40, 45,
    45, 40, 38, 43, 47, 42,
    37, 38, 43, 45, 40, 34,
    40, 40, 34, 33, 37, 42,
    36, 32, 38, 43, 45, 40,
    29, 33, 37, 32, 28, 32,
    38, 40, 34, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 15825530257377616, 20959489069403038, 22959412124390183, 17828130284410333, 15227578341406248
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32929770675134959, 38801093308632881, 38801572161692394, 32901458512374146, 30455156682812555, 34536972535888522,
    38976947082911482, 33536970315300348, 29454818220631321, 38063729480470721, 43935052128766108, 43935530981885909,
    38035417320604075, 34536972535888522, 38618788388972194, 43058762919671610, 37618786168384020, 33536634073707279,
    32929770675134959, 38063729480470721, 40063652535456899, 34932370702509942, 40063652535456899, 45934975183741607,
    45935454036861326, 40035340375590253, 38976947082911482, 43058762919671610, 47498737450380718, 42058760699083437,
    37976608620640104, 38801093308632881, 43935052128766108, 45934975183741607, 40803693335704937, 34932370702509942,
    40803693335704937, 40804172188764777, 34904058539623548, 33536970315300348, 37618786168384020, 42058760699083437,
    36618783947795845, 32536631853119106, 38801572161692394, 43935530981885909, 45935454036861326, 40804172188764777,
    29454818220631321, 33536634073707279, 37976608620640104, 32536631853119106, 28454479758450087, 32901458512374146,
    38035417320604075, 40035340375590253, 34904058539623548, 0
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
noncomputable def positiveFloor : ℝ := 41745841 / 1000000000000
noncomputable def negativeCeiling : ℝ := 172769433 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9211884933842922972905472, coefficient := (-9211884933842922972905472) }, { argument := 539253203119603411436175360, coefficient := (-539253203119603411436175360) }, { argument := 539432219401099737890291712, coefficient := (-539432219401099737890291712) }, { argument := 9032868652346596518789120, coefficient := (-9032868652346596518789120) }, { argument := 828677356007478125395968, coefficient := (-828677356007478125395968) }, { argument := 28064963124656838990102528, coefficient := (-28064963124656838990102528) }, { argument := 304579026320900213667004416, coefficient := (-304579026320900213667004416) }, { argument := 28064919927255113159147520, coefficient := (-28064919927255113159147520) }, { argument := 828482967699711886098432, coefficient := (-828482967699711886098432) }, { argument := 323462622764464688129376256, coefficient := (-323462622764464688129376256) }, { argument := 18935131807214104854428385280, coefficient := (-18935131807214104854428385280) }, { argument := 18941417716813084962142027776, coefficient := (-18941417716813084962142027776) }, { argument := 317176713165484580415733760, coefficient := (-317176713165484580415733760) }, { argument := 28064963124656838990102528, coefficient := (-28064963124656838990102528) }, { argument := 950481088300957926359564288, coefficient := (-950481088300957926359564288) }, { argument := 10315231953994421284829659136, coefficient := (-10315231953994421284829659136) }, { argument := 950479625326885173377105920, coefficient := (-950479625326885173377105920) }, { argument := 28058379741329450569039872, coefficient := (-28058379741329450569039872) }, { argument := 9211884933842922972905472, coefficient := (-9211884933842922972905472) }, { argument := 323462622764464688129376256, coefficient := (-323462622764464688129376256) }, { argument := 323445371598020931041099776, coefficient := (-323445371598020931041099776) }, { argument := 9228501574624380949889024, coefficient := (-9228501574624380949889024) }, { argument := 323445371598020931041099776, coefficient := (-323445371598020931041099776) }, { argument := 18934121943670524463682682880, coefficient := (-18934121943670524463682682880) }, { argument := 18940407518024363059703709696, coefficient := (-18940407518024363059703709696) }, { argument := 317159797244182335020072960, coefficient := (-317159797244182335020072960) }, { argument := 304579026320900213667004416, coefficient := (-304579026320900213667004416) }, { argument := 10315231953994421284829659136, coefficient := (-10315231953994421284829659136) }, { argument := 111947530123835636071993966592, coefficient := (-111947530123835636071993966592) }, { argument := 10315216076859053864900362240, coefficient := (-10315216076859053864900362240) }, { argument := 304507579211746823985168384, coefficient := (-304507579211746823985168384) }, { argument := 539253203119603411436175360, coefficient := (-539253203119603411436175360) }, { argument := 18935131807214104854428385280, coefficient := (-18935131807214104854428385280) }, { argument := 18934121943670524463682682880, coefficient := (-18934121943670524463682682880) }, { argument := 540225922256983144131461120, coefficient := (-540225922256983144131461120) }, { argument := 9228501574624380949889024, coefficient := (-9228501574624380949889024) }, { argument := 540225922256983144131461120, coefficient := (-540225922256983144131461120) }, { argument := 540405261452765202537775104, coefficient := (-540405261452765202537775104) }, { argument := 9049162378842322543575040, coefficient := (-9049162378842322543575040) }, { argument := 28064919927255113159147520, coefficient := (-28064919927255113159147520) }, { argument := 950479625326885173377105920, coefficient := (-950479625326885173377105920) }, { argument := 10315216076859053864900362240, coefficient := (-10315216076859053864900362240) }, { argument := 950478162355064220208332800, coefficient := (-950478162355064220208332800) }, { argument := 28058336554060823899668480, coefficient := (-28058336554060823899668480) }, { argument := 539432219401099737890291712, coefficient := (-539432219401099737890291712) }, { argument := 18941417716813084962142027776, coefficient := (-18941417716813084962142027776) }, { argument := 18940407518024363059703709696, coefficient := (-18940407518024363059703709696) }, { argument := 540405261452765202537775104, coefficient := (-540405261452765202537775104) }, { argument := 828482967699711886098432, coefficient := (-828482967699711886098432) }, { argument := 28058379741329450569039872, coefficient := (-28058379741329450569039872) }, { argument := 304507579211746823985168384, coefficient := (-304507579211746823985168384) }, { argument := 28058336554060823899668480, coefficient := (-28058336554060823899668480) }, { argument := 828288624990891873927168, coefficient := (-828288624990891873927168) }, { argument := 9032868652346596518789120, coefficient := (-9032868652346596518789120) }, { argument := 317176713165484580415733760, coefficient := (-317176713165484580415733760) }, { argument := 317159797244182335020072960, coefficient := (-317159797244182335020072960) }, { argument := 9049162378842322543575040, coefficient := (-9049162378842322543575040) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 2193860352213785337636323328, coefficient := 2193860352213785337636323328 }, { argument := 77034377719914278170231046144, coefficient := 77034377719914278170231046144 }, { argument := 77030269261074181578895130624, coefficient := 77030269261074181578895130624 }, { argument := 2197817695326430100325400576, coefficient := 2197817695326430100325400576 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 724732139393038711655497728, coefficient := 724732139393038711655497728 }] }

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

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-11388127197729884044597978464256)
def positiveArguments : Array ℕ := #[
    649691, 14101729, 324845, 19179, 140893, 8247715,
    8250453, 138155
  ]
def positiveCoefficients : Array ℕ := #[
    24544632020976501348250943488, 266374129520443516518752321536, 24544594242044638391089233920, 724562134199655404427804672, 1330696761741905846186541056, 77897465752522431747357409280,
    77923325431382625924547608576, 1304837082881711668996341760
  ]
def positiveScales : Array ℕ := #[
    19, 23, 18, 14, 17, 22,
    22, 17
  ]
def negativeArguments : Array ℕ := #[
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    316912650057057350374175801344, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    19309394194481380, 23749368725176471, 18309391973893206, 14227239879225015, 17104240410313222, 22975563049544053,
    22976041902589359, 17075928250446576
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0
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
noncomputable def positiveFloor : ℝ := 131023591 / 1000000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 24544632020976501348250943488, coefficient := 24544632020976501348250943488 }, { argument := 266374129520443516518752321536, coefficient := 266374129520443516518752321536 }, { argument := 24544594242044638391089233920, coefficient := 24544594242044638391089233920 }, { argument := 724562134199655404427804672, coefficient := 724562134199655404427804672 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 1330696761741905846186541056, coefficient := 1330696761741905846186541056 }, { argument := 77897465752522431747357409280, coefficient := 77897465752522431747357409280 }, { argument := 77923325431382625924547608576, coefficient := 77923325431382625924547608576 }, { argument := 1304837082881711668996341760, coefficient := 1304837082881711668996341760 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk0
