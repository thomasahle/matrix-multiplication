import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 12, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk12

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    71, 165, 257, 351, 523, 569,
    1589, 2095, 2263, 2653, 6353, 14039,
    18103, 23815
  ]
def positiveCoefficients : Array ℕ := #[
    431635029377712111209627441430528, 109968689569798900579839003066368, 112900131582826681070800129228800, 792281625142643375935439503360, 10933486426968478587909065146368, 443994622729937347874220297682944,
    443043884779766175823097770278912, 11091942751997007263096153047040, 206389363349658599431181990625280, 110602514869913015280587354669056, 443281569267308968835878402129920, 2224568347075514070951527037534208,
    206230907024630070755994902724608, 676846192359360236061645967720448
  ]
def positiveScales : Array ℕ := #[
    6, 7, 8, 8, 9, 9,
    10, 11, 11, 11, 12, 13,
    14, 14
  ]
def negativeArguments : Array ℕ := #[
    7, 15, 25, 27, 31, 33,
    35, 111, 171, 307, 347, 349,
    359, 599, 603, 607, 699, 719,
    1365, 1777, 5595, 669807078211
  ]
def negativeCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 4753689750855860255612637020160, 1980704062856608439838598758400, 2139160387885137115025686659072, 4912146075884388930799724920832, 2614529362970723140586950361088,
    2772985687999251815774038261760, 281418433250666927132268111593472, 108384126319513613827968124059648, 48646091783758303282435985506304, 109968689569798900579839003066368, 110602514869913015280587354669056,
    56885820685241794392164556341248, 47457669346044338218532826251264, 47774581996101395568907002052608, 48091494646158452919281177853952, 443043884779766175823097770278912, 56965048847756058729758100291584,
    108146441831970820815187492208640, 281576889575695455807455199494144, 443281569267308968835878402129920, 1112284173537757035475763518767104
  ]
def negativeScales : Array ℕ := #[
    2, 3, 4, 4, 4, 5,
    5, 6, 7, 8, 8, 8,
    8, 9, 9, 9, 9, 9,
    10, 10, 12, 39
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6149747119504681, 7366322214245815, 8005624549193878, 8455327220304556, 9030667136246941, 9152284842306581,
    10633903409347643, 11032734528586713, 11144020869266892, 11373408960228695, 12633222303799928, 13777152555450350,
    14143941177768493, 14539582928251323
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2807354922807594, 3906890600547867, 4643856189792934, 4754887502413606, 4954196321574415, 5044394119358454,
    5129283016944967, 6794415866926375, 7417852514885912, 8262094845370180, 8438791852578292, 8447083226209694,
    8487840033823231, 9226412192788786, 9236014191900085, 9245552706255683, 9449148645375482, 9489847960439491,
    10414685235807227, 10795227966614636, 12449922415863803, 39284954665619219
  ]

abbrev PositiveTerm := Fin 14
abbrev NegativeTerm := Fin 22
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
noncomputable def positiveFloor : ℝ := 158733255419 / 200000000000
noncomputable def negativeCeiling : ℝ := 782258040219 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7, coefficient := (-1109194275199700726309615304704) }, { argument := 15, coefficient := (-4753689750855860255612637020160) }, { argument := 25, coefficient := (-1980704062856608439838598758400) }, { argument := 27, coefficient := (-2139160387885137115025686659072) }, { argument := 31, coefficient := (-4912146075884388930799724920832) }, { argument := 33, coefficient := (-2614529362970723140586950361088) }, { argument := 35, coefficient := (-2772985687999251815774038261760) }, { argument := 71, coefficient := 431635029377712111209627441430528 }, { argument := 111, coefficient := (-281418433250666927132268111593472) }, { argument := 165, coefficient := 109968689569798900579839003066368 }, { argument := 171, coefficient := (-108384126319513613827968124059648) }, { argument := 257, coefficient := 112900131582826681070800129228800 }, { argument := 307, coefficient := (-48646091783758303282435985506304) }, { argument := 347, coefficient := (-109968689569798900579839003066368) }, { argument := 349, coefficient := (-110602514869913015280587354669056) }, { argument := 351, coefficient := 792281625142643375935439503360 }, { argument := 359, coefficient := (-56885820685241794392164556341248) }, { argument := 523, coefficient := 10933486426968478587909065146368 }, { argument := 569, coefficient := 443994622729937347874220297682944 }, { argument := 599, coefficient := (-47457669346044338218532826251264) }, { argument := 603, coefficient := (-47774581996101395568907002052608) }, { argument := 607, coefficient := (-48091494646158452919281177853952) }, { argument := 699, coefficient := (-443043884779766175823097770278912) }, { argument := 719, coefficient := (-56965048847756058729758100291584) }, { argument := 1365, coefficient := (-108146441831970820815187492208640) }, { argument := 1589, coefficient := 443043884779766175823097770278912 }, { argument := 1777, coefficient := (-281576889575695455807455199494144) }, { argument := 2095, coefficient := 11091942751997007263096153047040 }, { argument := 2263, coefficient := 206389363349658599431181990625280 }, { argument := 2653, coefficient := 110602514869913015280587354669056 }, { argument := 5595, coefficient := (-443281569267308968835878402129920) }, { argument := 6353, coefficient := 443281569267308968835878402129920 }, { argument := 14039, coefficient := 2224568347075514070951527037534208 }, { argument := 18103, coefficient := 206230907024630070755994902724608 }, { argument := 23815, coefficient := 676846192359360236061645967720448 }, { argument := 669807078211, coefficient := (-1112284173537757035475763518767104) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk12
