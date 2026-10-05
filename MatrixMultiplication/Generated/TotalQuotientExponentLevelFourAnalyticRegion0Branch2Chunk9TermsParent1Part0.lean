import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 9, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk9

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-391634344370176499026076106752)
def positiveArguments : Array ℕ := #[
    9, 16777185, 16777247, 15128459, 53635251, 7561185,
    49311, 16379087, 4095943, 397085
  ]
def positiveCoefficients : Array ℕ := #[
    713053462628379038341895553024, 158456032241806737269084651520, 158456617815250613105091149824, 142884255438135259919892348928, 506570623245401242635067195392, 142826746459106873380479959040,
    3725833818188561202121015296, 154696102937611857228520751104, 154740351511556345804173082624, 3750361789700586139360952320
  ]
def positiveScales : Array ℕ := #[
    3, 23, 24, 23, 25, 22,
    15, 23, 21, 18
  ]
def negativeArguments : Array ℕ := #[
    3309196971573, 137397488289891, 137436789034929, 3330982320567, 5721835634643, 162282610479055,
    45756128833945, 3309196971573, 3309213413835, 3309213413835, 137397992191901, 137437292703823,
    3330998494793, 162282610479055, 575350043630509, 40554384282913, 137397488289891, 137397992191901,
    45756128833945, 40554384282913, 45737601956323, 137436789034929, 137437292703823, 3330982320567,
    3330998494793, 1, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    931456140504483540278181888, 38673954816499699705756778496, 38685016992793982185110503424, 937588171105203203396861952, 12884428416026720146726846464, 45678494005136465460283310080,
    12879205297904444352936017920, 931456140504483540278181888, 931460768589797060782325760, 931460768589797060782325760, 38674096652306228908503597056, 38685158762984190716976037888,
    937592723745089866283614208, 45678494005136465460283310080, 161946640131372434249067003904, 45660177486191721608183283712, 38673954816499699705756778496, 38674096652306228908503597056,
    12879205297904444352936017920, 45660177486191721608183283712, 12873990445457270729120677888, 38685016992793982185110503424, 38685158762984190716976037888, 937588171105203203396861952,
    937592723745089866283614208, 316912650057057350374175801344, 792281625142643375935439503360, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    41, 46, 46, 41, 42, 47,
    45, 41, 41, 41, 46, 46,
    41, 47, 49, 45, 46, 46,
    45, 45, 45, 46, 46, 41,
    41, 0, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 23999997332806929, 24000002665728625, 23850761704778210, 25676678167259357, 22850180922664469,
    15589621889748028, 23965351604163281, 21965764207118307, 18599088338108356
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    41589618305629157, 46965348972949616, 46965761577982896, 41599084835476693, 42379615194070495, 47205501743467720,
    45379030232585644, 41589618305629157, 41589625473866987, 41589625473866987, 46965354263990736, 46965766865063981,
    41599091840743231, 47205501743467720, 49031433288924409, 45204923124335852, 46965348972949616, 46965354263990736,
    45379030232585644, 45204923124335852, 45378445960098275, 46965761577982896, 46965766865063981, 41599084835476693,
    41599091840743231, 0, 2321928094887363, 0
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
noncomputable def positiveFloor : ℝ := 442710747 / 1000000000000
noncomputable def negativeCeiling : ℝ := 8513509 / 20000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 931456140504483540278181888, coefficient := (-931456140504483540278181888) }, { argument := 38673954816499699705756778496, coefficient := (-38673954816499699705756778496) }, { argument := 38685016992793982185110503424, coefficient := (-38685016992793982185110503424) }, { argument := 937588171105203203396861952, coefficient := (-937588171105203203396861952) }, { argument := 12884428416026720146726846464, coefficient := (-12884428416026720146726846464) }, { argument := 45678494005136465460283310080, coefficient := (-45678494005136465460283310080) }, { argument := 12879205297904444352936017920, coefficient := (-12879205297904444352936017920) }, { argument := 931456140504483540278181888, coefficient := (-931456140504483540278181888) }, { argument := 931460768589797060782325760, coefficient := (-931460768589797060782325760) }, { argument := 931460768589797060782325760, coefficient := (-931460768589797060782325760) }, { argument := 38674096652306228908503597056, coefficient := (-38674096652306228908503597056) }, { argument := 38685158762984190716976037888, coefficient := (-38685158762984190716976037888) }, { argument := 937592723745089866283614208, coefficient := (-937592723745089866283614208) }, { argument := 45678494005136465460283310080, coefficient := (-45678494005136465460283310080) }, { argument := 161946640131372434249067003904, coefficient := (-161946640131372434249067003904) }, { argument := 45660177486191721608183283712, coefficient := (-45660177486191721608183283712) }, { argument := 38673954816499699705756778496, coefficient := (-38673954816499699705756778496) }, { argument := 38674096652306228908503597056, coefficient := (-38674096652306228908503597056) }, { argument := 12879205297904444352936017920, coefficient := (-12879205297904444352936017920) }, { argument := 45660177486191721608183283712, coefficient := (-45660177486191721608183283712) }, { argument := 12873990445457270729120677888, coefficient := (-12873990445457270729120677888) }, { argument := 38685016992793982185110503424, coefficient := (-38685016992793982185110503424) }, { argument := 38685158762984190716976037888, coefficient := (-38685158762984190716976037888) }, { argument := 937588171105203203396861952, coefficient := (-937588171105203203396861952) }, { argument := 937592723745089866283614208, coefficient := (-937592723745089866283614208) }, { argument := 713053462628379038341895553024, coefficient := 713053462628379038341895553024 }, { argument := 158456032241806737269084651520, coefficient := 158456032241806737269084651520 }, { argument := 158456617815250613105091149824, coefficient := 158456617815250613105091149824 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 142884255438135259919892348928, coefficient := 142884255438135259919892348928 }, { argument := 506570623245401242635067195392, coefficient := 506570623245401242635067195392 }, { argument := 142826746459106873380479959040, coefficient := 142826746459106873380479959040 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 3725833818188561202121015296, coefficient := 3725833818188561202121015296 }, { argument := 154696102937611857228520751104, coefficient := 154696102937611857228520751104 }, { argument := 154740351511556345804173082624, coefficient := 154740351511556345804173082624 }, { argument := 3750361789700586139360952320, coefficient := 3750361789700586139360952320 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk9
