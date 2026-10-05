import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 14, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk14

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
    95, 257, 307, 1951, 1953, 4861,
    4863, 6915, 8245, 16437, 17515, 27505,
    34813, 42757
  ]
def positiveCoefficients : Array ℕ := #[
    281101520600609869781893935792128, 133657910161563937520308644216832, 158456325028528675187087900672, 4040636288227481217270741467136, 4119864450741745554864285417472, 5545971375998503631548076523520,
    5545971375998503631548076523520, 1095725487572275788918712833146880, 98718290492773364641555762118656, 98401377842716307291181586317312, 131597977936193064742876501508096, 274287898624383136748849156063232,
    130884924473564685704534605955072, 342424118386650467079296953352192
  ]
def positiveScales : Array ℕ := #[
    6, 8, 8, 10, 10, 12,
    12, 12, 13, 14, 14, 14,
    15, 15
  ]
def negativeArguments : Array ℕ := #[
    9, 15, 21, 35, 43, 153,
    287, 289, 303, 413, 1003, 1007,
    1661, 1731, 20669369589
  ]
def negativeCoefficients : Array ℕ := #[
    47061528533473016530565106499584, 9507379501711720511225274040320, 3327582825599102178928845914112, 11091942751997007263096153047040, 3406810988113366516522389864448, 48487635458729774607248897605632,
    45476965283187729778694227492864, 183175511732979148516273613176832, 48012266483644188581687633903616, 130884924473564685704534605955072, 79465847001807130606324582187008, 79782759651864187956698757988352,
    131597977936193064742876501508096, 274287898624383136748849156063232, 547862743786137894459356416573440
  ]
def negativeScales : Array ℕ := #[
    3, 3, 4, 5, 5, 7,
    8, 8, 8, 8, 9, 9,
    10, 10, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6569855608330797, 8005624549193878, 8262094845370179, 10929998062151574, 10931476233417526, 12247037418788581,
    12247630876238697, 12755513536022131, 13009303778324829, 14004659389027135, 14096303367689425, 14747406282519510,
    15087338522787476, 15383873010976493
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3169925001442313, 3906890600547867, 4392317422778766, 5129283016944967, 5426264754702117, 7257387842692652,
    8164906926675688, 8174925682500679, 8243173983472952, 8689997971476554, 9970105905192551, 9975847984030745,
    10697836358031166, 10757390009630712, 34266775336442359
  ]

abbrev PositiveTerm := Fin 14
abbrev NegativeTerm := Fin 15
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
noncomputable def positiveFloor : ℝ := 396315906961 / 1000000000000
noncomputable def negativeCeiling : ℝ := 69213705417 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9, coefficient := (-47061528533473016530565106499584) }, { argument := 15, coefficient := (-9507379501711720511225274040320) }, { argument := 21, coefficient := (-3327582825599102178928845914112) }, { argument := 35, coefficient := (-11091942751997007263096153047040) }, { argument := 43, coefficient := (-3406810988113366516522389864448) }, { argument := 95, coefficient := 281101520600609869781893935792128 }, { argument := 153, coefficient := (-48487635458729774607248897605632) }, { argument := 257, coefficient := 133657910161563937520308644216832 }, { argument := 287, coefficient := (-45476965283187729778694227492864) }, { argument := 289, coefficient := (-183175511732979148516273613176832) }, { argument := 303, coefficient := (-48012266483644188581687633903616) }, { argument := 307, coefficient := 158456325028528675187087900672 }, { argument := 413, coefficient := (-130884924473564685704534605955072) }, { argument := 1003, coefficient := (-79465847001807130606324582187008) }, { argument := 1007, coefficient := (-79782759651864187956698757988352) }, { argument := 1661, coefficient := (-131597977936193064742876501508096) }, { argument := 1731, coefficient := (-274287898624383136748849156063232) }, { argument := 1951, coefficient := 4040636288227481217270741467136 }, { argument := 1953, coefficient := 4119864450741745554864285417472 }, { argument := 4861, coefficient := 5545971375998503631548076523520 }, { argument := 4863, coefficient := 5545971375998503631548076523520 }, { argument := 6915, coefficient := 1095725487572275788918712833146880 }, { argument := 8245, coefficient := 98718290492773364641555762118656 }, { argument := 16437, coefficient := 98401377842716307291181586317312 }, { argument := 17515, coefficient := 131597977936193064742876501508096 }, { argument := 27505, coefficient := 274287898624383136748849156063232 }, { argument := 34813, coefficient := 130884924473564685704534605955072 }, { argument := 42757, coefficient := 342424118386650467079296953352192 }, { argument := 20669369589, coefficient := (-547862743786137894459356416573440) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk14
