import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 15, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk15

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    259, 357, 771, 939, 945, 1177,
    2341, 5631, 8197, 13553, 23005, 32517,
    32893, 33057, 79095
  ]
def positiveCoefficients : Array ℕ := #[
    119555297234024885428657821057024, 93647688091860447035568949297152, 2085364465537951629799670316793856, 984647603727277187612564214775808, 986865992277676589065183445385216, 54588203972328128601951781781504,
    54033606834728278238796974129152, 91746212191518102933323894489088, 879274147583305618613150760828928, 8590234292446596539242409271230464, 1971830508655010834028121835962368, 878957234933248561262776585027584,
    1067757946204740477748191818678272, 1068391771504854592448940170280960, 2426520933324373867477470566940672
  ]
def positiveScales : Array ℕ := #[
    8, 8, 9, 9, 9, 10,
    11, 12, 13, 13, 14, 14,
    15, 15, 16
  ]
def negativeArguments : Array ℕ := #[
    3, 7, 11, 23, 29, 47,
    161, 193, 227, 273, 333, 379,
    401, 579, 591, 653, 1091, 1973,
    3111, 3513, 3515, 5157, 13477, 13485,
    9154799272753
  ]
def negativeCoefficients : Array ℕ := #[
    950737950171172051122527404032, 8873554201597605810476922437632, 1743019575313815427057966907392, 14577981902624638117212086861824, 9190466851654663160851098238976, 14894894552681695467586262663168,
    408183493273489867281938432131072, 61164141461012068622215929659392, 143878343125904037069875813810176, 346068613862306626608599975067648, 52765956234500048837300270923776, 30027473592906183947953157177344,
    31770493168219999375011124084736, 91746212191518102933323894489088, 93647688091860447035568949297152, 51735990121814612448584199569408, 345751701212249569258225799266304, 1250537317125148304576497712103424,
    1971830508655010834028121835962368, 556657069825221235932239795060736, 556973982475278293282613970862080, 408579634086061188969906151882752, 1067757946204740477748191818678272, 1068391771504854592448940170280960,
    4295117146223298269621204635615232
  ]
def negativeScales : Array ℕ := #[
    1, 2, 3, 4, 4, 5,
    7, 7, 7, 8, 8, 8,
    8, 9, 9, 9, 10, 10,
    11, 11, 11, 12, 13, 13,
    43
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8016808287686553, 8479780264029090, 9590587049914763, 9874981347482478, 9884170518905654, 10200898605038444,
    11192909219112012, 12459175435552025, 13000880282558819, 13726324611642090, 14489659835990594, 14988906539652774,
    15005492974458719, 15012668182173969, 16271298876988350
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2807354922807594, 3459431618637364, 4523561956057598, 4857980997143165, 5554588851679165,
    7330916878114618, 7592457037272664, 7826548488390402, 8092757140919853, 8379378367071265, 8566054038173239,
    8647458426474890, 9177419537989237, 9207014320177533, 9350939181546432, 10091435386323608, 10946175250494239,
    11603162679540553, 11778487861636337, 11779308974381058, 12332316330199218, 13718211765882499, 13719067901235608,
    43057665392625244
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 25
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
noncomputable def positiveFloor : ℝ := 861157372581 / 250000000000
noncomputable def negativeCeiling : ℝ := 3409225745031 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-950737950171172051122527404032) }, { argument := 7, coefficient := (-8873554201597605810476922437632) }, { argument := 11, coefficient := (-1743019575313815427057966907392) }, { argument := 23, coefficient := (-14577981902624638117212086861824) }, { argument := 29, coefficient := (-9190466851654663160851098238976) }, { argument := 47, coefficient := (-14894894552681695467586262663168) }, { argument := 161, coefficient := (-408183493273489867281938432131072) }, { argument := 193, coefficient := (-61164141461012068622215929659392) }, { argument := 227, coefficient := (-143878343125904037069875813810176) }, { argument := 259, coefficient := 119555297234024885428657821057024 }, { argument := 273, coefficient := (-346068613862306626608599975067648) }, { argument := 333, coefficient := (-52765956234500048837300270923776) }, { argument := 357, coefficient := 93647688091860447035568949297152 }, { argument := 379, coefficient := (-30027473592906183947953157177344) }, { argument := 401, coefficient := (-31770493168219999375011124084736) }, { argument := 579, coefficient := (-91746212191518102933323894489088) }, { argument := 591, coefficient := (-93647688091860447035568949297152) }, { argument := 653, coefficient := (-51735990121814612448584199569408) }, { argument := 771, coefficient := 2085364465537951629799670316793856 }, { argument := 939, coefficient := 984647603727277187612564214775808 }, { argument := 945, coefficient := 986865992277676589065183445385216 }, { argument := 1091, coefficient := (-345751701212249569258225799266304) }, { argument := 1177, coefficient := 54588203972328128601951781781504 }, { argument := 1973, coefficient := (-1250537317125148304576497712103424) }, { argument := 2341, coefficient := 54033606834728278238796974129152 }, { argument := 3111, coefficient := (-1971830508655010834028121835962368) }, { argument := 3513, coefficient := (-556657069825221235932239795060736) }, { argument := 3515, coefficient := (-556973982475278293282613970862080) }, { argument := 5157, coefficient := (-408579634086061188969906151882752) }, { argument := 5631, coefficient := 91746212191518102933323894489088 }, { argument := 8197, coefficient := 879274147583305618613150760828928 }, { argument := 13477, coefficient := (-1067757946204740477748191818678272) }, { argument := 13485, coefficient := (-1068391771504854592448940170280960) }, { argument := 13553, coefficient := 8590234292446596539242409271230464 }, { argument := 23005, coefficient := 1971830508655010834028121835962368 }, { argument := 32517, coefficient := 878957234933248561262776585027584 }, { argument := 32893, coefficient := 1067757946204740477748191818678272 }, { argument := 33057, coefficient := 1068391771504854592448940170280960 }, { argument := 79095, coefficient := 2426520933324373867477470566940672 }, { argument := 9154799272753, coefficient := (-4295117146223298269621204635615232) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk15
