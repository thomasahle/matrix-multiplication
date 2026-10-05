import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 24, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk24

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
def constantNumerator : ℤ := (-312425117414647846877666476032)
def positiveArguments : Array ℕ := #[
    15, 483, 541, 483, 541, 5,
    1, 1, 1, 8944409, 64885661, 17888817
  ]
def positiveCoefficients : Array ℕ := #[
    1188422437713965063903159255040, 37370314935927417048517312512, 41857847578336920545026637824, 37370314935927417048517312512, 41857847578336920545026637824, 792281625142643375935439503360,
    158456325028528675187087900672, 158456325028528675187087900672, 158456325028528675187087900672, 168955109082710401904757702656, 612827741450484213052302426112, 168955099637977436165467275264
  ]
def positiveScales : Array ℕ := #[
    3, 8, 9, 8, 9, 2,
    0, 0, 0, 23, 25, 24
  ]
def negativeArguments : Array ℕ := #[
    8944409, 64885661, 17888817, 995, 541, 995,
    541, 8944409, 541, 541, 995, 541,
    995, 541, 64885661, 17888817, 541, 541,
    1, 5, 1, 1, 3
  ]
def negativeCoefficients : Array ℕ := #[
    84477554541355200952378851328, 306413870725242106526151213056, 84477549818988718082733637632, 38492198096529792922644643840, 10464461894584230136256659456, 38492198096529792922644643840,
    10464461894584230136256659456, 84477554541355200952378851328, 10464461894584230136256659456, 10464461894584230136256659456, 38492198096529792922644643840, 10464461894584230136256659456,
    38492198096529792922644643840, 10464461894584230136256659456, 306413870725242106526151213056, 84477549818988718082733637632, 10464461894584230136256659456, 10464461894584230136256659456,
    158456325028528675187087900672, 792281625142643375935439503360, 158456325028528675187087900672, 316912650057057350374175801344, 950737950171172051122527404032
  ]
def negativeScales : Array ℕ := #[
    23, 25, 24, 9, 9, 9,
    9, 23, 9, 9, 9, 9,
    9, 9, 25, 24, 9, 9,
    0, 2, 0, 0, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3906890595303263, 8915879378478017, 9079484783826815, 8915879378478017, 9079484783826815, 2321928094887362,
    0, 0, 0, 23092554728970020, 25951396357650820, 24092554648322149
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    23092554728970021, 25951396368982182, 24092554648322150, 9958552727465983, 9079484783826816, 9958552727465983,
    9079484783826816, 23092554728970021, 9079484783826816, 9079484783826816, 9958552727465983, 9079484783826816,
    9958552727465983, 9079484783826816, 25951396368982182, 24092554648322150, 9079484783826816, 9079484783826816,
    0, 2321928094887363, 0, 0, 1584962500724866
  ]

abbrev PositiveTerm := Fin 12
abbrev NegativeTerm := Fin 23
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
noncomputable def positiveFloor : ℝ := 95649601 / 250000000000
noncomputable def negativeCeiling : ℝ := 44410451 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 84477554541355200952378851328, coefficient := (-84477554541355200952378851328) }, { argument := 306413870725242106526151213056, coefficient := (-306413870725242106526151213056) }, { argument := 84477549818988718082733637632, coefficient := (-84477549818988718082733637632) }, { argument := 38492198096529792922644643840, coefficient := (-38492198096529792922644643840) }, { argument := 10464461894584230136256659456, coefficient := (-10464461894584230136256659456) }, { argument := 38492198096529792922644643840, coefficient := (-38492198096529792922644643840) }, { argument := 10464461894584230136256659456, coefficient := (-10464461894584230136256659456) }, { argument := 84477554541355200952378851328, coefficient := (-84477554541355200952378851328) }, { argument := 10464461894584230136256659456, coefficient := (-10464461894584230136256659456) }, { argument := 10464461894584230136256659456, coefficient := (-10464461894584230136256659456) }, { argument := 38492198096529792922644643840, coefficient := (-38492198096529792922644643840) }, { argument := 10464461894584230136256659456, coefficient := (-10464461894584230136256659456) }, { argument := 38492198096529792922644643840, coefficient := (-38492198096529792922644643840) }, { argument := 10464461894584230136256659456, coefficient := (-10464461894584230136256659456) }, { argument := 306413870725242106526151213056, coefficient := (-306413870725242106526151213056) }, { argument := 84477549818988718082733637632, coefficient := (-84477549818988718082733637632) }, { argument := 10464461894584230136256659456, coefficient := (-10464461894584230136256659456) }, { argument := 10464461894584230136256659456, coefficient := (-10464461894584230136256659456) }, { argument := 1188422437713965063903159255040, coefficient := 1188422437713965063903159255040 }, { argument := 37370314935927417048517312512, coefficient := 37370314935927417048517312512 }, { argument := 41857847578336920545026637824, coefficient := 41857847578336920545026637824 }, { argument := 37370314935927417048517312512, coefficient := 37370314935927417048517312512 }, { argument := 41857847578336920545026637824, coefficient := 41857847578336920545026637824 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 168955109082710401904757702656, coefficient := 168955109082710401904757702656 }, { argument := 612827741450484213052302426112, coefficient := 612827741450484213052302426112 }, { argument := 168955099637977436165467275264, coefficient := 168955099637977436165467275264 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk24
