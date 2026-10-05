import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 13, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk13

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    257, 1123, 1129, 1297, 1569, 2315,
    2613, 2883, 3123, 4695, 5715, 19089,
    34601, 37723, 70399
  ]
def positiveCoefficients : Array ℕ := #[
    15924860665367131856302334017536, 363657265940473309554366732042240, 364132634915558895579927995744256, 83348026965006083148408235753472, 613939031323034352012372071153664, 2371457360376960152849957521457152,
    84061080427634462186750131306496, 2105013049841489185522869216477184, 615285910085776845751462318309376, 2351888004235936861464352165724160, 2111272074680116068192759188553728, 1252438793025490648678742766911488,
    10965494604624241380296856902303744, 1255132550550975636156923261222912, 2805469234630100194187391281397760
  ]
def positiveScales : Array ℕ := #[
    8, 10, 10, 10, 10, 11,
    11, 11, 11, 12, 12, 14,
    15, 15, 16
  ]
def negativeArguments : Array ℕ := #[
    3, 9, 13, 15, 25, 31,
    49, 59, 63, 117, 121, 145,
    379, 383, 561, 569, 987, 1045,
    1241, 1969, 2083, 2145, 3331, 3883,
    4985, 7749, 8643, 15517, 15669, 26569,
    4096972642911
  ]
def negativeCoefficients : Array ℕ := #[
    713053462628379038341895553024, 1426106925256758076683791106048, 2059932225370872777432142708736, 4753689750855860255612637020160, 1980704062856608439838598758400, 9824292151768777861599449841664,
    7764359926397905084167307132928, 18697846353366383672076372279296, 4991374238398653268393268871168, 18539390028337854996889284378624, 9586607664225984848818817990656, 22976167129136657902127745597440,
    30027473592906183947953157177344, 30344386242963241298327332978688, 44446999170502293389978156138496, 45080824470616408090726507741184, 156396392803157802409655757963264, 165586859654812465570506856202240,
    393288598720808171814352169467904, 156000251990586480721688038211584, 165032262517212615207352048549888, 679777634372388016552607093882880, 2111272074680116068192759188553728, 615285910085776845751462318309376,
    394952390133607722903816592424960, 613939031323034352012372071153664, 684769008610786669821000362754048, 1229383397733839726439021477363712, 1241426078436007905753240157814784, 2105013049841489185522869216477184,
    5482747302312120690148428451151872
  ]
def negativeScales : Array ℕ := #[
    1, 3, 3, 3, 4, 4,
    5, 5, 5, 6, 6, 7,
    8, 8, 9, 9, 9, 10,
    10, 10, 11, 11, 11, 11,
    12, 12, 13, 13, 13, 14,
    41
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8005624549193878, 10133142212400601, 10140829770773000, 10340962764251699, 10615629636967558, 11176796478147598,
    11351491409320020, 11493355121494892, 11608716854020125, 12196909442541136, 12480537783101831, 14220453906972867,
    15078526113197376, 15203156793447350, 16103267315439189
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 3169925001442313, 3700439718214233, 3906890600547867, 4643856189792934, 4954196321574415,
    5614709844123661, 5882643052550791, 5977279939904027, 6870364722125690, 6918863243376152, 7179909090014935,
    8566054038173239, 8581200581928289, 9131856960608793, 9152284842306582, 9946906284348933, 10029287226968246,
    10277287400130357, 10943247405198059, 11024447124040647, 11066761932386908, 11701739638749759, 11922955998462517,
    12283377789285559, 12919794435041029, 13077316445881027, 13921562045050676, 13935625497254068, 14697456308530331,
    41897695402250170
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 31
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
noncomputable def positiveFloor : ℝ := 181099386689 / 40000000000
noncomputable def negativeCeiling : ℝ := 4443160384117 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-713053462628379038341895553024) }, { argument := 9, coefficient := (-1426106925256758076683791106048) }, { argument := 13, coefficient := (-2059932225370872777432142708736) }, { argument := 15, coefficient := (-4753689750855860255612637020160) }, { argument := 25, coefficient := (-1980704062856608439838598758400) }, { argument := 31, coefficient := (-9824292151768777861599449841664) }, { argument := 49, coefficient := (-7764359926397905084167307132928) }, { argument := 59, coefficient := (-18697846353366383672076372279296) }, { argument := 63, coefficient := (-4991374238398653268393268871168) }, { argument := 117, coefficient := (-18539390028337854996889284378624) }, { argument := 121, coefficient := (-9586607664225984848818817990656) }, { argument := 145, coefficient := (-22976167129136657902127745597440) }, { argument := 257, coefficient := 15924860665367131856302334017536 }, { argument := 379, coefficient := (-30027473592906183947953157177344) }, { argument := 383, coefficient := (-30344386242963241298327332978688) }, { argument := 561, coefficient := (-44446999170502293389978156138496) }, { argument := 569, coefficient := (-45080824470616408090726507741184) }, { argument := 987, coefficient := (-156396392803157802409655757963264) }, { argument := 1045, coefficient := (-165586859654812465570506856202240) }, { argument := 1123, coefficient := 363657265940473309554366732042240 }, { argument := 1129, coefficient := 364132634915558895579927995744256 }, { argument := 1241, coefficient := (-393288598720808171814352169467904) }, { argument := 1297, coefficient := 83348026965006083148408235753472 }, { argument := 1569, coefficient := 613939031323034352012372071153664 }, { argument := 1969, coefficient := (-156000251990586480721688038211584) }, { argument := 2083, coefficient := (-165032262517212615207352048549888) }, { argument := 2145, coefficient := (-679777634372388016552607093882880) }, { argument := 2315, coefficient := 2371457360376960152849957521457152 }, { argument := 2613, coefficient := 84061080427634462186750131306496 }, { argument := 2883, coefficient := 2105013049841489185522869216477184 }, { argument := 3123, coefficient := 615285910085776845751462318309376 }, { argument := 3331, coefficient := (-2111272074680116068192759188553728) }, { argument := 3883, coefficient := (-615285910085776845751462318309376) }, { argument := 4695, coefficient := 2351888004235936861464352165724160 }, { argument := 4985, coefficient := (-394952390133607722903816592424960) }, { argument := 5715, coefficient := 2111272074680116068192759188553728 }, { argument := 7749, coefficient := (-613939031323034352012372071153664) }, { argument := 8643, coefficient := (-684769008610786669821000362754048) }, { argument := 15517, coefficient := (-1229383397733839726439021477363712) }, { argument := 15669, coefficient := (-1241426078436007905753240157814784) }, { argument := 19089, coefficient := 1252438793025490648678742766911488 }, { argument := 26569, coefficient := (-2105013049841489185522869216477184) }, { argument := 34601, coefficient := 10965494604624241380296856902303744 }, { argument := 37723, coefficient := 1255132550550975636156923261222912 }, { argument := 70399, coefficient := 2805469234630100194187391281397760 }, { argument := 4096972642911, coefficient := (-5482747302312120690148428451151872) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk13
