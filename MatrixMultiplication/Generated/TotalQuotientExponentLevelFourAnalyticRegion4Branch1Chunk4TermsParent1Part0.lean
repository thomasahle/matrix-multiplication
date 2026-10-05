import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 4, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk4

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
def constantNumerator : ℤ := 629559926245339463000640192512
def positiveArguments : Array ℕ := #[
    1, 63641, 2554531, 28318075, 2554553, 3977,
    300969, 1029763, 16480859, 74099
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 601072250672614182089654272, 24126863147702955314776113152, 267456656478777656769668710400, 24127070931828201579165515776, 600987248075922528475807744,
    2842571835965588500641742848, 155613384847977422854119489536, 155657312301001076293897289728, 2799381072113262725517279232
  ]
def positiveScales : Array ℕ := #[
    0, 15, 21, 24, 21, 11,
    18, 19, 23, 16
  ]
def negativeArguments : Array ℕ := #[
    4731427403, 524395537953, 131137110859, 9311967261, 384294520295, 21044615098857,
    21050560941935, 378447804609, 4731427403, 384294520295, 4261905378859, 384297658307,
    9461510037, 4261905378859, 233286771944569, 233352605241819, 4197178413953, 524395537953,
    21044615098857, 233286771944569, 21044796510143, 262160692703, 384297658307, 21044796510143,
    21050742411807, 378450884191, 131137110859, 21050560941935, 233352605241819, 21050742411807,
    524474269547, 9461510037, 262160692703, 524474269547, 4655321761, 9311967261,
    378447804609, 4197178413953, 378450884191, 4655321761, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    2663556836135169201012736, 147604221832492599547527168, 147647260899758956154454016, 2621085767920366141833216, 108169291150067844534763520, 5923532544835493690125320192,
    5925206150877398955311759360, 106523586988517167416213504, 2663556836135169201012736, 108169291150067844534763520, 1199619717257356561302421504, 108170174421922462293819392,
    2663178317312212988854272, 1199619717257356561302421504, 65664388700001676808383627264, 65682919125811906252074123264, 1181400696317888763074183168, 147604221832492599547527168,
    5923532544835493690125320192, 65664388700001676808383627264, 5923583607572995590280183808, 147583349746052738723086336, 108170174421922462293819392, 5923583607572995590280183808,
    5925257230105393841037115392, 106524453813788895971639296, 147647260899758956154454016, 5925206150877398955311759360, 65682919125811906252074123264, 5925257230105393841037115392,
    147626382806080142371192832, 2663178317312212988854272, 147583349746052738723086336, 147626382806080142371192832, 2620713168516170154770432, 2621085767920366141833216,
    106523586988517167416213504, 1181400696317888763074183168, 106524453813788895971639296, 2620713168516170154770432, 316912650057057350374175801344, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    32, 38, 36, 33, 38, 44,
    44, 38, 32, 38, 41, 38,
    33, 41, 47, 47, 41, 38,
    44, 47, 44, 37, 38, 44,
    44, 38, 36, 44, 47, 44,
    38, 33, 37, 38, 32, 33,
    38, 41, 38, 32, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 15957668883935083, 21284627012705120, 24755219861737403, 21284639437355370, 11957464846075818,
    18199255370559777, 19973880907651264, 23974288102537513, 16177166452380480
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32139628343378977, 38931864461225139, 36932285067123516, 33116438840016396, 38483421448734347, 44258516356897344,
    44258923911357802, 38461303381688499, 32139628343378977, 38483421448734347, 41954635713249094, 38483433229219438,
    33139423307005307, 41954635713249094, 47729097833096124, 47729504902782247, 41932556937098111, 38931864461225139,
    44258516356897344, 47729097833096124, 44258528793334570, 37931660441391540, 38483433229219438, 44258528793334570,
    44258936348297447, 38461315121430541, 36932285067123516, 44258923911357802, 47729504902782247, 44258936348297447,
    38932081048059160, 33139423307005307, 37931660441391540, 38932081048059160, 32116233739698702, 33116438840016396,
    38461303381688499, 41932556937098111, 38461315121430541, 32116233739698702, 0, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 175762639 / 1000000000000
noncomputable def negativeCeiling : ℝ := 35905199 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2663556836135169201012736, coefficient := (-2663556836135169201012736) }, { argument := 147604221832492599547527168, coefficient := (-147604221832492599547527168) }, { argument := 147647260899758956154454016, coefficient := (-147647260899758956154454016) }, { argument := 2621085767920366141833216, coefficient := (-2621085767920366141833216) }, { argument := 108169291150067844534763520, coefficient := (-108169291150067844534763520) }, { argument := 5923532544835493690125320192, coefficient := (-5923532544835493690125320192) }, { argument := 5925206150877398955311759360, coefficient := (-5925206150877398955311759360) }, { argument := 106523586988517167416213504, coefficient := (-106523586988517167416213504) }, { argument := 2663556836135169201012736, coefficient := (-2663556836135169201012736) }, { argument := 108169291150067844534763520, coefficient := (-108169291150067844534763520) }, { argument := 1199619717257356561302421504, coefficient := (-1199619717257356561302421504) }, { argument := 108170174421922462293819392, coefficient := (-108170174421922462293819392) }, { argument := 2663178317312212988854272, coefficient := (-2663178317312212988854272) }, { argument := 1199619717257356561302421504, coefficient := (-1199619717257356561302421504) }, { argument := 65664388700001676808383627264, coefficient := (-65664388700001676808383627264) }, { argument := 65682919125811906252074123264, coefficient := (-65682919125811906252074123264) }, { argument := 1181400696317888763074183168, coefficient := (-1181400696317888763074183168) }, { argument := 147604221832492599547527168, coefficient := (-147604221832492599547527168) }, { argument := 5923532544835493690125320192, coefficient := (-5923532544835493690125320192) }, { argument := 65664388700001676808383627264, coefficient := (-65664388700001676808383627264) }, { argument := 5923583607572995590280183808, coefficient := (-5923583607572995590280183808) }, { argument := 147583349746052738723086336, coefficient := (-147583349746052738723086336) }, { argument := 108170174421922462293819392, coefficient := (-108170174421922462293819392) }, { argument := 5923583607572995590280183808, coefficient := (-5923583607572995590280183808) }, { argument := 5925257230105393841037115392, coefficient := (-5925257230105393841037115392) }, { argument := 106524453813788895971639296, coefficient := (-106524453813788895971639296) }, { argument := 147647260899758956154454016, coefficient := (-147647260899758956154454016) }, { argument := 5925206150877398955311759360, coefficient := (-5925206150877398955311759360) }, { argument := 65682919125811906252074123264, coefficient := (-65682919125811906252074123264) }, { argument := 5925257230105393841037115392, coefficient := (-5925257230105393841037115392) }, { argument := 147626382806080142371192832, coefficient := (-147626382806080142371192832) }, { argument := 2663178317312212988854272, coefficient := (-2663178317312212988854272) }, { argument := 147583349746052738723086336, coefficient := (-147583349746052738723086336) }, { argument := 147626382806080142371192832, coefficient := (-147626382806080142371192832) }, { argument := 2620713168516170154770432, coefficient := (-2620713168516170154770432) }, { argument := 2621085767920366141833216, coefficient := (-2621085767920366141833216) }, { argument := 106523586988517167416213504, coefficient := (-106523586988517167416213504) }, { argument := 1181400696317888763074183168, coefficient := (-1181400696317888763074183168) }, { argument := 106524453813788895971639296, coefficient := (-106524453813788895971639296) }, { argument := 2620713168516170154770432, coefficient := (-2620713168516170154770432) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 601072250672614182089654272, coefficient := 601072250672614182089654272 }, { argument := 24126863147702955314776113152, coefficient := 24126863147702955314776113152 }, { argument := 267456656478777656769668710400, coefficient := 267456656478777656769668710400 }, { argument := 24127070931828201579165515776, coefficient := 24127070931828201579165515776 }, { argument := 600987248075922528475807744, coefficient := 600987248075922528475807744 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 2842571835965588500641742848, coefficient := 2842571835965588500641742848 }, { argument := 155613384847977422854119489536, coefficient := 155613384847977422854119489536 }, { argument := 155657312301001076293897289728, coefficient := 155657312301001076293897289728 }, { argument := 2799381072113262725517279232, coefficient := 2799381072113262725517279232 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk4
