import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 6, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk6

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
def constantNumerator : ℤ := 29804073478445227378641958076416
def positiveArguments : Array ℕ := #[
    5, 224327, 4082139, 16330147, 447075, 190923
  ]
def positiveCoefficients : Array ℕ := #[
    792281625142643375935439503360, 4237417224010795607411130368, 154218851136120085143934205952, 154233877706268576355004186624, 4222503990657893267826278400, 1803216752017842546268962816
  ]
def positiveScales : Array ℕ := #[
    2, 17, 21, 23, 18, 17
  ]
def negativeArguments : Array ℕ := #[
    67909606781, 923915844201, 3696689771231, 130668579, 1465721505, 243630846711,
    2704168007331, 243632625591, 5862044715, 614200132049, 33629184339037, 33638681590069,
    604861683869, 243630846711, 305881158429, 27127512444333, 4894140511785, 243596379747,
    67909606781, 614200132049, 2457024688959, 33050341, 2457024688959, 134529859470713,
    134567852830999, 2419666540081, 2704168007331, 27127512444333, 150358299238197, 54255492804087,
    2703785639187, 923915844201, 33629184339037, 134529859470713, 3682640273263, 33050341,
    3682640273263, 1841831173019, 66684125531, 243632625591, 4894140511785, 54255492804087,
    2447091244413, 243598158357, 3696689771231, 33638681590069, 134567852830999, 1841831173019,
    5862044715, 243596379747, 2703785639187, 243598158357, 2930601765, 130668579,
    604861683869, 2419666540081, 66684125531, 1
  ]
def negativeCoefficients : Array ℕ := #[
    19114854987111781772558336, 1040236762916330209410023424, 1040525667263765981519937536, 18831326838189831003045888, 1650255705936730647429120, 68575986903976126936252416,
    761155626885194268473819136, 68576487614182697987997696, 1650018899631449088983040, 691527871456696459461656576, 37863095514515188255018713088, 37873788468567378069664301056,
    681013713520779787822432256, 68575986903976126936252416, 2755132542241000103312621568, 30542863733946647978591649792, 2755156173146721823406161920, 68566285316086939917484032,
    19114854987111781772558336, 691527871456696459461656576, 691590967102241327340847104, 19052224436744681745809408, 691590967102241327340847104, 37866789061406766189907017728,
    37877483241608427602490425344, 681075583016853057763803136, 761155626885194268473819136, 30542863733946647978591649792, 338576790210602770893537017856, 30543127146911105042186502144,
    761047999820766971714076672, 1040236762916330209410023424, 37863095514515188255018713088, 37866789061406766189907017728, 1036571085150426772723990528, 19052224436744681745809408,
    1036571085150426772723990528, 1036858773060966493273980928, 18769912680808686169358336, 68576487614182697987997696, 2755156173146721823406161920, 30543127146911105042186502144,
    2755179804119997537910259712, 68566785950295267257352192, 1040525667263765981519937536, 37873788468567378069664301056, 37877483241608427602490425344, 1036858773060966493273980928,
    1650018899631449088983040, 68566285316086939917484032, 761047999820766971714076672, 68566785950295267257352192, 1649782127103164735815680, 18831326838189831003045888,
    681013713520779787822432256, 681075583016853057763803136, 18769912680808686169358336, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    35, 39, 41, 26, 30, 37,
    41, 37, 32, 39, 44, 44,
    39, 37, 38, 44, 42, 37,
    35, 39, 41, 24, 41, 46,
    46, 41, 41, 44, 47, 45,
    41, 39, 44, 46, 41, 24,
    41, 40, 35, 37, 42, 45,
    41, 37, 41, 44, 46, 40,
    32, 37, 41, 37, 31, 26,
    39, 41, 35, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 17775243748077474, 21960893876644300, 23961034441184314, 18770157348445181, 17542631385388057
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    35982896645517735, 39748970492285461, 41749371115507011, 26961337039307550, 30448963863649369, 37825905852883953,
    41298321926294182, 37825916386739064, 32448756826766868, 39159917866244779, 44934779028938503, 44935186404399831,
    39137814317040372, 37825905852883953, 38154180286720453, 44624821994076152, 42154192660732871, 37825701737364617,
    35982896645517735, 39159917866244779, 41160049493076045, 24978161837805380, 41160049493076045, 46934919757068632,
    46935327139502229, 41137945378660862, 41298321926294182, 44624821994076152, 47095397830118449, 45624834436358651,
    41298117915438276, 39748970492285461, 44934779028938503, 46934919757068632, 41743877617992468, 24978161837805380,
    41743877617992468, 40744277965199474, 35956624322484151, 37825916386739064, 42154192660732871, 45624834436358651,
    41154205034674532, 37825712271111121, 41749371115507011, 44935186404399831, 46935327139502229, 40744277965199474,
    32448756826766868, 37825701737364617, 41298117915438276, 37825712271111121, 31448549789706031, 26961337039307550,
    39137814317040372, 41137945378660862, 35956624322484151, 0
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
noncomputable def positiveFloor : ℝ := 109636203 / 1000000000000
noncomputable def negativeCeiling : ℝ := 439812839 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 19114854987111781772558336, coefficient := (-19114854987111781772558336) }, { argument := 1040236762916330209410023424, coefficient := (-1040236762916330209410023424) }, { argument := 1040525667263765981519937536, coefficient := (-1040525667263765981519937536) }, { argument := 18831326838189831003045888, coefficient := (-18831326838189831003045888) }, { argument := 1650255705936730647429120, coefficient := (-1650255705936730647429120) }, { argument := 68575986903976126936252416, coefficient := (-68575986903976126936252416) }, { argument := 761155626885194268473819136, coefficient := (-761155626885194268473819136) }, { argument := 68576487614182697987997696, coefficient := (-68576487614182697987997696) }, { argument := 1650018899631449088983040, coefficient := (-1650018899631449088983040) }, { argument := 691527871456696459461656576, coefficient := (-691527871456696459461656576) }, { argument := 37863095514515188255018713088, coefficient := (-37863095514515188255018713088) }, { argument := 37873788468567378069664301056, coefficient := (-37873788468567378069664301056) }, { argument := 681013713520779787822432256, coefficient := (-681013713520779787822432256) }, { argument := 68575986903976126936252416, coefficient := (-68575986903976126936252416) }, { argument := 2755132542241000103312621568, coefficient := (-2755132542241000103312621568) }, { argument := 30542863733946647978591649792, coefficient := (-30542863733946647978591649792) }, { argument := 2755156173146721823406161920, coefficient := (-2755156173146721823406161920) }, { argument := 68566285316086939917484032, coefficient := (-68566285316086939917484032) }, { argument := 19114854987111781772558336, coefficient := (-19114854987111781772558336) }, { argument := 691527871456696459461656576, coefficient := (-691527871456696459461656576) }, { argument := 691590967102241327340847104, coefficient := (-691590967102241327340847104) }, { argument := 19052224436744681745809408, coefficient := (-19052224436744681745809408) }, { argument := 691590967102241327340847104, coefficient := (-691590967102241327340847104) }, { argument := 37866789061406766189907017728, coefficient := (-37866789061406766189907017728) }, { argument := 37877483241608427602490425344, coefficient := (-37877483241608427602490425344) }, { argument := 681075583016853057763803136, coefficient := (-681075583016853057763803136) }, { argument := 761155626885194268473819136, coefficient := (-761155626885194268473819136) }, { argument := 30542863733946647978591649792, coefficient := (-30542863733946647978591649792) }, { argument := 338576790210602770893537017856, coefficient := (-338576790210602770893537017856) }, { argument := 30543127146911105042186502144, coefficient := (-30543127146911105042186502144) }, { argument := 761047999820766971714076672, coefficient := (-761047999820766971714076672) }, { argument := 1040236762916330209410023424, coefficient := (-1040236762916330209410023424) }, { argument := 37863095514515188255018713088, coefficient := (-37863095514515188255018713088) }, { argument := 37866789061406766189907017728, coefficient := (-37866789061406766189907017728) }, { argument := 1036571085150426772723990528, coefficient := (-1036571085150426772723990528) }, { argument := 19052224436744681745809408, coefficient := (-19052224436744681745809408) }, { argument := 1036571085150426772723990528, coefficient := (-1036571085150426772723990528) }, { argument := 1036858773060966493273980928, coefficient := (-1036858773060966493273980928) }, { argument := 18769912680808686169358336, coefficient := (-18769912680808686169358336) }, { argument := 68576487614182697987997696, coefficient := (-68576487614182697987997696) }, { argument := 2755156173146721823406161920, coefficient := (-2755156173146721823406161920) }, { argument := 30543127146911105042186502144, coefficient := (-30543127146911105042186502144) }, { argument := 2755179804119997537910259712, coefficient := (-2755179804119997537910259712) }, { argument := 68566785950295267257352192, coefficient := (-68566785950295267257352192) }, { argument := 1040525667263765981519937536, coefficient := (-1040525667263765981519937536) }, { argument := 37873788468567378069664301056, coefficient := (-37873788468567378069664301056) }, { argument := 37877483241608427602490425344, coefficient := (-37877483241608427602490425344) }, { argument := 1036858773060966493273980928, coefficient := (-1036858773060966493273980928) }, { argument := 1650018899631449088983040, coefficient := (-1650018899631449088983040) }, { argument := 68566285316086939917484032, coefficient := (-68566285316086939917484032) }, { argument := 761047999820766971714076672, coefficient := (-761047999820766971714076672) }, { argument := 68566785950295267257352192, coefficient := (-68566785950295267257352192) }, { argument := 1649782127103164735815680, coefficient := (-1649782127103164735815680) }, { argument := 18831326838189831003045888, coefficient := (-18831326838189831003045888) }, { argument := 681013713520779787822432256, coefficient := (-681013713520779787822432256) }, { argument := 681075583016853057763803136, coefficient := (-681075583016853057763803136) }, { argument := 18769912680808686169358336, coefficient := (-18769912680808686169358336) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 4237417224010795607411130368, coefficient := 4237417224010795607411130368 }, { argument := 154218851136120085143934205952, coefficient := 154218851136120085143934205952 }, { argument := 154233877706268576355004186624, coefficient := 154233877706268576355004186624 }, { argument := 4222503990657893267826278400, coefficient := 4222503990657893267826278400 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 1803216752017842546268962816, coefficient := 1803216752017842546268962816 }] }

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

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-31187635680089990256085992210432)
def positiveArguments : Array ℕ := #[
    7663593, 84954225, 7663659, 11931, 300969, 1029763,
    16480859, 74099
  ]
def positiveCoefficients : Array ℕ := #[
    72380589443108865944328339456, 802369969436332970309006131200, 72381212795484604737496547328, 1802961744227767585427423232, 2842571835965588500641742848, 155613384847977422854119489536,
    155657312301001076293897289728, 2799381072113262725517279232
  ]
def positiveScales : Array ℕ := #[
    22, 26, 22, 13, 18, 19,
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
    22869589513271269, 26340182362474184, 22869601937921483, 13542427347526301, 18199255370559777, 19973880907651264,
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
noncomputable def positiveFloor : ℝ := 378043519 / 1000000000000
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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 72380589443108865944328339456, coefficient := 72380589443108865944328339456 }, { argument := 802369969436332970309006131200, coefficient := 802369969436332970309006131200 }, { argument := 72381212795484604737496547328, coefficient := 72381212795484604737496547328 }, { argument := 1802961744227767585427423232, coefficient := 1802961744227767585427423232 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 2842571835965588500641742848, coefficient := 2842571835965588500641742848 }, { argument := 155613384847977422854119489536, coefficient := 155613384847977422854119489536 }, { argument := 155657312301001076293897289728, coefficient := 155657312301001076293897289728 }, { argument := 2799381072113262725517279232, coefficient := 2799381072113262725517279232 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk6
