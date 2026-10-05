import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 0, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk0

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
def constantNumerator : ℤ := 1868539753318791425254389448704
def positiveArguments : Array ℕ := #[
    1, 6205911, 2642429, 6209089, 51013, 31971,
    8184503, 204085
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 58613172204144085595546714112, 199656290287404059718104121344, 58643187565509205060524965888, 3854433302250067380580384768, 154602269515597237378124611584,
    154600890584584239441722212352, 3855056654625806173748592640
  ]
def positiveScales : Array ℕ := #[
    0, 22, 21, 22, 15, 14,
    22, 17
  ]
def negativeArguments : Array ℕ := #[
    1266320963649, 50792757818851, 12698076193847, 4947366273, 1266320963649, 2156816378129,
    1266895238557, 2156816378129, 86508599197431, 86507827678603, 2157165136493, 50792757818851,
    86508599197431, 50818842627119, 1266895238557, 50818842627119, 25409194617351, 633550107923,
    12698076193847, 86507827678603, 25409194617351, 4947366273, 2157165136493, 633550107923,
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    356437663751317738166943744, 14296890324131075673089376256, 14296762803732878833146134528, 356495310456770553370902528, 356437663751317738166943744, 1214179679606043399839285248,
    356599307767672552283963392, 1214179679606043399839285248, 48700011888736730115811049472, 48699577562248443850586587136, 1214376013110812492815138816, 14296890324131075673089376256,
    48700011888736730115811049472, 14304232544930812900161880064, 356599307767672552283963392, 14304232544930812900161880064, 14304104926310797037128384512, 356657003745320040688254976,
    14296762803732878833146134528, 48699577562248443850586587136, 14304104926310797037128384512, 356495310456770553370902528, 1214376013110812492815138816, 356657003745320040688254976,
    316912650057057350374175801344, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    40, 45, 43, 32, 40, 40,
    40, 40, 46, 46, 40, 45,
    46, 45, 40, 45, 44, 39,
    43, 46, 44, 32, 40, 39,
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 22565211576409924, 21333433277365806, 22565950180508204, 15638577325565731, 14964476248668600,
    22964463380902912, 17638810624367123
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40203780257456263, 45529688041485334, 43529675173381683, 32204013565829617, 40203780257456263, 40972040510709782,
    40204434369470349, 40972040510709782, 46297908781347181, 46297895914749400, 40972273776469722, 45529688041485334,
    46297908781347181, 45530428752667780, 40204434369470349, 45530428752667780, 44530415881262693, 39204667771403622,
    43529675173381683, 46297895914749400, 44530415881262693, 32204013565829617, 40972273776469722, 39204667771403622,
    0, 0
  ]

abbrev PositiveTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 155247491 / 1000000000000
noncomputable def negativeCeiling : ℝ := 43481131 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 356437663751317738166943744, coefficient := (-356437663751317738166943744) }, { argument := 14296890324131075673089376256, coefficient := (-14296890324131075673089376256) }, { argument := 14296762803732878833146134528, coefficient := (-14296762803732878833146134528) }, { argument := 356495310456770553370902528, coefficient := (-356495310456770553370902528) }, { argument := 356437663751317738166943744, coefficient := (-356437663751317738166943744) }, { argument := 1214179679606043399839285248, coefficient := (-1214179679606043399839285248) }, { argument := 356599307767672552283963392, coefficient := (-356599307767672552283963392) }, { argument := 1214179679606043399839285248, coefficient := (-1214179679606043399839285248) }, { argument := 48700011888736730115811049472, coefficient := (-48700011888736730115811049472) }, { argument := 48699577562248443850586587136, coefficient := (-48699577562248443850586587136) }, { argument := 1214376013110812492815138816, coefficient := (-1214376013110812492815138816) }, { argument := 14296890324131075673089376256, coefficient := (-14296890324131075673089376256) }, { argument := 48700011888736730115811049472, coefficient := (-48700011888736730115811049472) }, { argument := 14304232544930812900161880064, coefficient := (-14304232544930812900161880064) }, { argument := 356599307767672552283963392, coefficient := (-356599307767672552283963392) }, { argument := 14304232544930812900161880064, coefficient := (-14304232544930812900161880064) }, { argument := 14304104926310797037128384512, coefficient := (-14304104926310797037128384512) }, { argument := 356657003745320040688254976, coefficient := (-356657003745320040688254976) }, { argument := 14296762803732878833146134528, coefficient := (-14296762803732878833146134528) }, { argument := 48699577562248443850586587136, coefficient := (-48699577562248443850586587136) }, { argument := 14304104926310797037128384512, coefficient := (-14304104926310797037128384512) }, { argument := 356495310456770553370902528, coefficient := (-356495310456770553370902528) }, { argument := 1214376013110812492815138816, coefficient := (-1214376013110812492815138816) }, { argument := 356657003745320040688254976, coefficient := (-356657003745320040688254976) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 58613172204144085595546714112, coefficient := 58613172204144085595546714112 }, { argument := 199656290287404059718104121344, coefficient := 199656290287404059718104121344 }, { argument := 58643187565509205060524965888, coefficient := 58643187565509205060524965888 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 3854433302250067380580384768, coefficient := 3854433302250067380580384768 }, { argument := 154602269515597237378124611584, coefficient := 154602269515597237378124611584 }, { argument := 154600890584584239441722212352, coefficient := 154600890584584239441722212352 }, { argument := 3855056654625806173748592640, coefficient := 3855056654625806173748592640 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk0
