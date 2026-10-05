import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 6, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk6

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
def constantNumerator : ℤ := (-5482761074620376053938665816064)
def positiveArguments : Array ℕ := #[
    7, 25154589, 25177059, 49797261, 168818867, 778427,
    1385079, 24467583, 48946533, 698259
  ]
def positiveCoefficients : Array ℕ := #[
    2218388550399401452619230609408, 475156751935845863705360203776, 475581198235326187417167200256, 470321832570223503367640973312, 1594449118393656827336263204864, 470530249492578472289502232576,
    13081701291453210645881683968, 462179575504124489786638467072, 462286933783746048300926631936, 13189739591848302389080621056
  ]
def positiveScales : Array ℕ := #[
    2, 24, 24, 25, 27, 19,
    20, 24, 25, 19
  ]
def negativeArguments : Array ℕ := #[
    11613710391567, 205157326915389, 410409960793629, 5854810536237, 77479939609533, 131367539609073,
    77514683175009, 11613710391567, 11624059168497, 11624059168497, 205340598073539, 410776595798499,
    5860031530707, 131367539609073, 890569539166259, 262850679882731, 205157326915389, 205340598073539,
    77514683175009, 262850679882731, 19387362589421, 410409960793629, 410776595798499, 5854810536237,
    5860031530707, 3, 1, 3
  ]
def negativeCoefficients : Array ℕ := #[
    3268968861990624899421437952, 115493307631059116244093370368, 115520134156207964825661210624, 3295965318665225883504082944, 43617328394272669018720567296, 147906700608000009142693527552,
    43636887282839073522406391808, 3268968861990624899421437952, 3271881783735980423519404032, 3271881783735980423519404032, 115596480121003128649225863168, 115623332735665059324802105344,
    3298904477258925311036227584, 147906700608000009142693527552, 501346080592084796921041911808, 147971777996743607604396163072, 115493307631059116244093370368, 115596480121003128649225863168,
    43636887282839073522406391808, 147971777996743607604396163072, 43656459466706555017948561408, 115520134156207964825661210624, 115623332735665059324802105344, 3295965318665225883504082944,
    3298904477258925311036227584, 950737950171172051122527404032, 2535301200456458802993406410752, 950737950171172051122527404032
  ]
def negativeScales : Array ℕ := #[
    43, 47, 48, 42, 46, 46,
    46, 43, 43, 43, 47, 48,
    42, 46, 49, 47, 47, 47,
    46, 47, 44, 48, 48, 42,
    42, 1, 0, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 24584318281880606, 24585606432021139, 25569563056095338, 27330900906072193, 19570202225781984,
    20401536834160270, 24544368257817679, 25544703338119125, 19413402738246997
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    43400894196982092, 47543724007469335, 48544059074508485, 42412759624002702, 46138888062992350, 46900602168389136,
    46139534851500933, 43400894196982092, 43402179185208231, 43402179185208231, 47545012220600180, 48545347314152109,
    42414045565936198, 46900602168389136, 49661721595470196, 47901236799440617, 47543724007469335, 47545012220600180,
    46139534851500933, 47901236799440617, 44140181789535263, 48544059074508485, 48545347314152109, 42412759624002702,
    42414045565936198, 1584962500724866, 0, 1584962500724866
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 28
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
noncomputable def positiveFloor : ℝ := 710725449 / 500000000000
noncomputable def negativeCeiling : ℝ := 658851021 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3268968861990624899421437952, coefficient := (-3268968861990624899421437952) }, { argument := 115493307631059116244093370368, coefficient := (-115493307631059116244093370368) }, { argument := 115520134156207964825661210624, coefficient := (-115520134156207964825661210624) }, { argument := 3295965318665225883504082944, coefficient := (-3295965318665225883504082944) }, { argument := 43617328394272669018720567296, coefficient := (-43617328394272669018720567296) }, { argument := 147906700608000009142693527552, coefficient := (-147906700608000009142693527552) }, { argument := 43636887282839073522406391808, coefficient := (-43636887282839073522406391808) }, { argument := 3268968861990624899421437952, coefficient := (-3268968861990624899421437952) }, { argument := 3271881783735980423519404032, coefficient := (-3271881783735980423519404032) }, { argument := 3271881783735980423519404032, coefficient := (-3271881783735980423519404032) }, { argument := 115596480121003128649225863168, coefficient := (-115596480121003128649225863168) }, { argument := 115623332735665059324802105344, coefficient := (-115623332735665059324802105344) }, { argument := 3298904477258925311036227584, coefficient := (-3298904477258925311036227584) }, { argument := 147906700608000009142693527552, coefficient := (-147906700608000009142693527552) }, { argument := 501346080592084796921041911808, coefficient := (-501346080592084796921041911808) }, { argument := 147971777996743607604396163072, coefficient := (-147971777996743607604396163072) }, { argument := 115493307631059116244093370368, coefficient := (-115493307631059116244093370368) }, { argument := 115596480121003128649225863168, coefficient := (-115596480121003128649225863168) }, { argument := 43636887282839073522406391808, coefficient := (-43636887282839073522406391808) }, { argument := 147971777996743607604396163072, coefficient := (-147971777996743607604396163072) }, { argument := 43656459466706555017948561408, coefficient := (-43656459466706555017948561408) }, { argument := 115520134156207964825661210624, coefficient := (-115520134156207964825661210624) }, { argument := 115623332735665059324802105344, coefficient := (-115623332735665059324802105344) }, { argument := 3295965318665225883504082944, coefficient := (-3295965318665225883504082944) }, { argument := 3298904477258925311036227584, coefficient := (-3298904477258925311036227584) }, { argument := 2218388550399401452619230609408, coefficient := 2218388550399401452619230609408 }, { argument := 475156751935845863705360203776, coefficient := 475156751935845863705360203776 }, { argument := 475581198235326187417167200256, coefficient := 475581198235326187417167200256 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 470321832570223503367640973312, coefficient := 470321832570223503367640973312 }, { argument := 1594449118393656827336263204864, coefficient := 1594449118393656827336263204864 }, { argument := 470530249492578472289502232576, coefficient := 470530249492578472289502232576 }, { argument := 2535301200456458802993406410752, coefficient := (-2535301200456458802993406410752) }, { argument := 13081701291453210645881683968, coefficient := 13081701291453210645881683968 }, { argument := 462179575504124489786638467072, coefficient := 462179575504124489786638467072 }, { argument := 462286933783746048300926631936, coefficient := 462286933783746048300926631936 }, { argument := 13189739591848302389080621056, coefficient := 13189739591848302389080621056 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk6
