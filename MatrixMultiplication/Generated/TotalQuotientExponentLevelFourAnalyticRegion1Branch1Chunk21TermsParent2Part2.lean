import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 21, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 17929060807527070680279327912755200
def positiveArguments : Array ℕ := #[
    2387, 3, 9, 19, 49, 41,
    1147, 35, 41, 37, 19, 19,
    37, 1147, 37, 3, 49, 87,
    1305, 2291, 87, 725, 87, 2291,
    4553, 725, 70267, 4495, 1305, 2291,
    87, 4495, 87, 2291, 2291, 87,
    3375, 15375
  ]
def positiveCoefficients : Array ℕ := #[
    189117623921548973835789409452032, 3713820117856140824697372672, 2785365088392105618523029504, 2940107593302778152885420032, 3791191370311477091878567936, 50755541610700591270864093184,
    88744826566270698456830967808, 2707993835936769351341834240, 50755541610700591270864093184, 2862736340847441885704224768, 2940107593302778152885420032, 2940107593302778152885420032,
    2862736340847441885704224768, 88744826566270698456830967808, 2862736340847441885704224768, 3713820117856140824697372672, 3791191370311477091878567936, 26925195854457020979055951872,
    403877937816855314685839278080, 709030157500701552448473399296, 26925195854457020979055951872, 448753264240950349650932531200, 26925195854457020979055951872, 709030157500701552448473399296,
    704542624858292048951964073984, 448753264240950349650932531200, 10873291592558226972042095230976, 695567559573473041958945423360, 403877937816855314685839278080, 709030157500701552448473399296,
    26925195854457020979055951872, 695567559573473041958945423360, 26925195854457020979055951872, 709030157500701552448473399296, 709030157500701552448473399296, 26925195854457020979055951872,
    522255954073519803473068032000, 594791503250397553955438592000
  ]
def positiveScales : Array ℕ := #[
    11, 1, 3, 4, 5, 5,
    10, 5, 5, 5, 4, 4,
    5, 10, 5, 1, 5, 6,
    10, 11, 6, 9, 6, 11,
    12, 9, 16, 12, 10, 11,
    6, 12, 6, 11, 11, 6,
    11, 13
  ]
def negativeArguments : Array ℕ := #[
    75399288237, 10480947561, 37706788465, 37706797455, 19, 729808809,
    729808983, 19, 23228038197, 83550562641, 11614022973, 19218298637,
    19218303219, 37, 19218298637, 19218303219, 1147, 37,
    851179161, 310545, 851179335, 310545, 482855, 49,
    1, 29
  ]
def negativeCoefficients : Array ℕ := #[
    173858921680974757014351642624, 48334839326934332308029702144, 173891869163839607658627727360, 173891910622896913320844984320, 1470053796651389076442710016, 6731298161180888038398492672,
    6731299766047622451129483264, 1470053796651389076442710016, 53560209494301106052523884544, 192654480781620676691578847232, 53560227362278584449438318592, 177257518244430051677826973696,
    177257560505920724546409725952, 1431368170423720942852112384, 177257518244430051677826973696, 177257560505920724546409725952, 44372413283135349228415483904, 1431368170423720942852112384,
    7850742071920909151096537088, 45828353106961061652725760, 7850743676787643563827527680, 45828353106961061652725760, 2280218268086022539659182080, 1895595685155738545939283968,
    316912650057057350374175801344, 18380933703309326321702196477952
  ]
def negativeScales : Array ℕ := #[
    36, 33, 35, 35, 4, 29,
    29, 4, 34, 36, 33, 34,
    34, 5, 34, 34, 10, 5,
    29, 18, 29, 18, 18, 5,
    0, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11220982851081776, 1584962500720924, 3169925001442312, 4247927513443585, 5614709844114682, 5357552004618083,
    10163649676015824, 5129283016944966, 5357552004618083, 5209453365628949, 4247927513443585, 4247927513443585,
    5209453365628949, 10163649676015824, 5209453365628949, 1584962500720924, 5614709844114682, 6442943495848725,
    10349834091457246, 11161761743304674, 6442943495848725, 9501837184902278, 6442943495848725, 11161761743304674,
    12152601744019198, 9501837184902278, 16100559684578918, 12134105400401809, 10349834091457246, 11161761743304674,
    6442943495848725, 12134105400401809, 6442943495848725, 11161761743304674, 11161761743304674, 6442943495848725,
    11720671786818303, 13908298789688351
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36133831853510838, 33287050102748803, 35134105228419149, 35134105572384451, 4247927513443586, 29442943323866103,
    29442943667831405, 4247927513443586, 34435148260447123, 36281930492499972, 33435148741737963, 34161761571322015,
    34161761915287316, 5209453365628950, 34161761571322015, 34161761915287316, 10163649676015826, 5209453365628950,
    29664887589609512, 18244442813970666, 29664887884528517, 18244442813970666, 18881230494374467, 5614709844123661,
    0, 4857980997143165
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 7213190807 / 250000000000
noncomputable def negativeCeiling : ℝ := 1753162883 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 173858921680974757014351642624, coefficient := (-173858921680974757014351642624) }, { argument := 48334839326934332308029702144, coefficient := (-48334839326934332308029702144) }, { argument := 173891869163839607658627727360, coefficient := (-173891869163839607658627727360) }, { argument := 173891910622896913320844984320, coefficient := (-173891910622896913320844984320) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 6731298161180888038398492672, coefficient := (-6731298161180888038398492672) }, { argument := 6731299766047622451129483264, coefficient := (-6731299766047622451129483264) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 53560209494301106052523884544, coefficient := (-53560209494301106052523884544) }, { argument := 192654480781620676691578847232, coefficient := (-192654480781620676691578847232) }, { argument := 53560227362278584449438318592, coefficient := (-53560227362278584449438318592) }, { argument := 177257518244430051677826973696, coefficient := (-177257518244430051677826973696) }, { argument := 177257560505920724546409725952, coefficient := (-177257560505920724546409725952) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 177257518244430051677826973696, coefficient := (-177257518244430051677826973696) }, { argument := 177257560505920724546409725952, coefficient := (-177257560505920724546409725952) }, { argument := 44372413283135349228415483904, coefficient := (-44372413283135349228415483904) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 7850742071920909151096537088, coefficient := (-7850742071920909151096537088) }, { argument := 45828353106961061652725760, coefficient := (-45828353106961061652725760) }, { argument := 7850743676787643563827527680, coefficient := (-7850743676787643563827527680) }, { argument := 45828353106961061652725760, coefficient := (-45828353106961061652725760) }, { argument := 2280218268086022539659182080, coefficient := (-2280218268086022539659182080) }, { argument := 1895595685155738545939283968, coefficient := (-1895595685155738545939283968) }, { argument := 189117623921548973835789409452032, coefficient := 189117623921548973835789409452032 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 2785365088392105618523029504, coefficient := 2785365088392105618523029504 }, { argument := 2940107593302778152885420032, coefficient := 2940107593302778152885420032 }, { argument := 3791191370311477091878567936, coefficient := 3791191370311477091878567936 }, { argument := 50755541610700591270864093184, coefficient := 50755541610700591270864093184 }, { argument := 88744826566270698456830967808, coefficient := 88744826566270698456830967808 }, { argument := 2707993835936769351341834240, coefficient := 2707993835936769351341834240 }, { argument := 50755541610700591270864093184, coefficient := 50755541610700591270864093184 }, { argument := 2862736340847441885704224768, coefficient := 2862736340847441885704224768 }, { argument := 2940107593302778152885420032, coefficient := 2940107593302778152885420032 }, { argument := 2940107593302778152885420032, coefficient := 2940107593302778152885420032 }, { argument := 2862736340847441885704224768, coefficient := 2862736340847441885704224768 }, { argument := 88744826566270698456830967808, coefficient := 88744826566270698456830967808 }, { argument := 2862736340847441885704224768, coefficient := 2862736340847441885704224768 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 3791191370311477091878567936, coefficient := 3791191370311477091878567936 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 26925195854457020979055951872, coefficient := 26925195854457020979055951872 }, { argument := 403877937816855314685839278080, coefficient := 403877937816855314685839278080 }, { argument := 709030157500701552448473399296, coefficient := 709030157500701552448473399296 }, { argument := 26925195854457020979055951872, coefficient := 26925195854457020979055951872 }, { argument := 448753264240950349650932531200, coefficient := 448753264240950349650932531200 }, { argument := 26925195854457020979055951872, coefficient := 26925195854457020979055951872 }, { argument := 709030157500701552448473399296, coefficient := 709030157500701552448473399296 }, { argument := 704542624858292048951964073984, coefficient := 704542624858292048951964073984 }, { argument := 448753264240950349650932531200, coefficient := 448753264240950349650932531200 }, { argument := 10873291592558226972042095230976, coefficient := 10873291592558226972042095230976 }, { argument := 695567559573473041958945423360, coefficient := 695567559573473041958945423360 }, { argument := 403877937816855314685839278080, coefficient := 403877937816855314685839278080 }, { argument := 709030157500701552448473399296, coefficient := 709030157500701552448473399296 }, { argument := 26925195854457020979055951872, coefficient := 26925195854457020979055951872 }, { argument := 695567559573473041958945423360, coefficient := 695567559573473041958945423360 }, { argument := 26925195854457020979055951872, coefficient := 26925195854457020979055951872 }, { argument := 709030157500701552448473399296, coefficient := 709030157500701552448473399296 }, { argument := 709030157500701552448473399296, coefficient := 709030157500701552448473399296 }, { argument := 26925195854457020979055951872, coefficient := 26925195854457020979055951872 }, { argument := 18380933703309326321702196477952, coefficient := (-18380933703309326321702196477952) }, { argument := 522255954073519803473068032000, coefficient := 522255954073519803473068032000 }, { argument := 594791503250397553955438592000, coefficient := 594791503250397553955438592000 }] }

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

end TermShard4


end Parent2

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-7852825099917894828294850052358144)
def positiveArguments : Array ℕ := #[
    375, 160875, 7125, 375, 7125, 13875,
    262125, 13875, 160875, 262125, 3375, 13875,
    13875, 15375, 1225, 6125, 5075, 91175,
    34125, 1225, 136675, 136675, 97825, 5075,
    549, 603, 549, 603, 1, 3,
    321912803, 321912861, 2799572567, 20326098975, 5599144755, 273313373,
    2666358147, 10665429201, 136657251, 15615, 33310305, 1291799781,
    133241367, 15615, 11205, 2085947, 16687577, 89639
  ]
def positiveCoefficients : Array ℕ := #[
    464227514732017603087171584000, 6223550119376110991387394048000, 551270173744270903666016256000, 464227514732017603087171584000, 551270173744270903666016256000, 536763063908895353569542144000,
    20280939549855019034870808576000, 536763063908895353569542144000, 6223550119376110991387394048000, 20280939549855019034870808576000, 522255954073519803473068032000, 536763063908895353569542144000,
    536763063908895353569542144000, 594791503250397553955438592000, 94779784257786927296964198400, 1895595685155738545939283968000, 98164776552707888986141491200, 1763580985653821040061369548800,
    2640293990038350117558288384000, 94779784257786927296964198400, 2643678982333271079247465676800, 2643678982333271079247465676800, 1892210692860817584250106675200, 98164776552707888986141491200,
    339814540783836885459809599488, 373238921844542152882085953536, 339814540783836885459809599488, 373238921844542152882085953536, 158456325028528675187087900672, 475368975085586025561263702016,
    12161521850350551794851306799104, 12161524041528599846366685954048, 26441215313524268354572348555264, 95987288527031050636719921561600, 26441213523747371346976812564480, 1290685911975249452668559556608,
    50366081378876857818151542325248, 50366065384221580338663203536896, 1290691243527008612498005819392, 4719344168320608640759234560, 629213871464660629240015749120, 6100351988372747938600191000576,
    629214565652533611077862162432, 4719344168320608640759234560, 846625863048869993911418880, 157609699165479805193176481792, 157609708610212770932466909184, 846616418315904254620991488
  ]
def positiveScales : Array ℕ := #[
    8, 17, 12, 8, 12, 13,
    17, 13, 17, 17, 11, 13,
    13, 13, 10, 12, 12, 16,
    15, 10, 17, 17, 16, 12,
    9, 9, 9, 9, 0, 1,
    28, 28, 31, 34, 32, 28,
    31, 33, 27, 13, 24, 30,
    26, 13, 13, 20, 23, 16
  ]
def negativeArguments : Array ℕ := #[
    375, 175, 9, 1, 3, 307,
    1879, 163, 93, 1
  ]
def negativeCoefficients : Array ℕ := #[
    59421121885698253195157962752000, 13864928439996259078870191308800, 1426106925256758076683791106048, 158456325028528675187087900672, 475368975085586025561263702016, 24323045891879151641217992753152,
    148869717364302690338269082681344, 103313523918600696221981311238144, 7368219113826583396199587381248, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    8, 7, 3, 0, 1, 8,
    10, 7, 6, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8550746785383158, 17295580622882788, 12798674298787868, 8550746785383158, 12798674298787868, 13760200150994793,
    17999895429301525, 13760200150994793, 17295580622882788, 17999895429301525, 11720671786818303, 13760200150994793,
    13760200150994793, 13908298789688351, 10258566033889932, 12580494128777091, 12309192106959900, 16476350674110829,
    15058541425581939, 10258566033889932, 17060389849974308, 17060389849974308, 16577915584675329, 12309192106959900,
    9100662339005198, 9236014191900084, 9100662339005198, 9236014191900084, 0, 1584962500720924,
    28262094715402827, 28262094975337518, 31382559430248694, 34242614305745656, 32382559332594243, 28025980810576465,
    31312223431186485, 33312222973032646, 27025986770033622, 13930644948445348, 24989465226836850, 30266735334743810,
    26989466818506829, 13930644948445348, 13451855028397752, 20992271070183114, 23992271156636352, 16451838933985791
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    8550746785384604, 7451211111832378, 3169925001442313, 0, 1584962500724866, 8262094845370180,
    10875749354229199, 7348728154231079, 6539158811108986, 0
  ]

abbrev PositiveTerm := Fin 48
abbrev NegativeTerm := Fin 10
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
noncomputable def positiveFloor : ℝ := 125843110069 / 1000000000000
noncomputable def negativeCeiling : ℝ := 39049596687 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 464227514732017603087171584000, coefficient := 464227514732017603087171584000 }, { argument := 6223550119376110991387394048000, coefficient := 6223550119376110991387394048000 }, { argument := 551270173744270903666016256000, coefficient := 551270173744270903666016256000 }, { argument := 464227514732017603087171584000, coefficient := 464227514732017603087171584000 }, { argument := 551270173744270903666016256000, coefficient := 551270173744270903666016256000 }, { argument := 536763063908895353569542144000, coefficient := 536763063908895353569542144000 }, { argument := 20280939549855019034870808576000, coefficient := 20280939549855019034870808576000 }, { argument := 536763063908895353569542144000, coefficient := 536763063908895353569542144000 }, { argument := 6223550119376110991387394048000, coefficient := 6223550119376110991387394048000 }, { argument := 20280939549855019034870808576000, coefficient := 20280939549855019034870808576000 }, { argument := 522255954073519803473068032000, coefficient := 522255954073519803473068032000 }, { argument := 536763063908895353569542144000, coefficient := 536763063908895353569542144000 }, { argument := 536763063908895353569542144000, coefficient := 536763063908895353569542144000 }, { argument := 594791503250397553955438592000, coefficient := 594791503250397553955438592000 }, { argument := 59421121885698253195157962752000, coefficient := (-59421121885698253195157962752000) }, { argument := 94779784257786927296964198400, coefficient := 94779784257786927296964198400 }, { argument := 1895595685155738545939283968000, coefficient := 1895595685155738545939283968000 }, { argument := 98164776552707888986141491200, coefficient := 98164776552707888986141491200 }, { argument := 1763580985653821040061369548800, coefficient := 1763580985653821040061369548800 }, { argument := 2640293990038350117558288384000, coefficient := 2640293990038350117558288384000 }, { argument := 94779784257786927296964198400, coefficient := 94779784257786927296964198400 }, { argument := 2643678982333271079247465676800, coefficient := 2643678982333271079247465676800 }, { argument := 2643678982333271079247465676800, coefficient := 2643678982333271079247465676800 }, { argument := 1892210692860817584250106675200, coefficient := 1892210692860817584250106675200 }, { argument := 98164776552707888986141491200, coefficient := 98164776552707888986141491200 }, { argument := 13864928439996259078870191308800, coefficient := (-13864928439996259078870191308800) }, { argument := 339814540783836885459809599488, coefficient := 339814540783836885459809599488 }, { argument := 373238921844542152882085953536, coefficient := 373238921844542152882085953536 }, { argument := 339814540783836885459809599488, coefficient := 339814540783836885459809599488 }, { argument := 373238921844542152882085953536, coefficient := 373238921844542152882085953536 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 12161521850350551794851306799104, coefficient := 12161521850350551794851306799104 }, { argument := 12161524041528599846366685954048, coefficient := 12161524041528599846366685954048 }, { argument := 24323045891879151641217992753152, coefficient := (-24323045891879151641217992753152) }, { argument := 26441215313524268354572348555264, coefficient := 26441215313524268354572348555264 }, { argument := 95987288527031050636719921561600, coefficient := 95987288527031050636719921561600 }, { argument := 26441213523747371346976812564480, coefficient := 26441213523747371346976812564480 }, { argument := 148869717364302690338269082681344, coefficient := (-148869717364302690338269082681344) }, { argument := 1290685911975249452668559556608, coefficient := 1290685911975249452668559556608 }, { argument := 50366081378876857818151542325248, coefficient := 50366081378876857818151542325248 }, { argument := 50366065384221580338663203536896, coefficient := 50366065384221580338663203536896 }, { argument := 1290691243527008612498005819392, coefficient := 1290691243527008612498005819392 }, { argument := 103313523918600696221981311238144, coefficient := (-103313523918600696221981311238144) }, { argument := 4719344168320608640759234560, coefficient := 4719344168320608640759234560 }, { argument := 629213871464660629240015749120, coefficient := 629213871464660629240015749120 }, { argument := 6100351988372747938600191000576, coefficient := 6100351988372747938600191000576 }, { argument := 629214565652533611077862162432, coefficient := 629214565652533611077862162432 }, { argument := 4719344168320608640759234560, coefficient := 4719344168320608640759234560 }, { argument := 7368219113826583396199587381248, coefficient := (-7368219113826583396199587381248) }, { argument := 846625863048869993911418880, coefficient := 846625863048869993911418880 }, { argument := 157609699165479805193176481792, coefficient := 157609699165479805193176481792 }, { argument := 157609708610212770932466909184, coefficient := 157609708610212770932466909184 }, { argument := 846616418315904254620991488, coefficient := 846616418315904254620991488 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end TermShard5


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21
