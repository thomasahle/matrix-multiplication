import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 1, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk1

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
def constantNumerator : ℤ := 14237992508359541876062158848
def positiveArguments : Array ℕ := #[
    1, 37183, 2387961, 28626583, 2387971, 77551,
    355035, 16422859, 8209639, 89315
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 702367011730168071923433472, 22553653977599761708285427712, 270370432156571953780842561536, 22553748424929419101189701632, 732448486226047711934676992,
    3353210768491248976889118720, 155109517788988197449108553728, 155075696200237885050088062976, 3374225299340018898090065920
  ]
def positiveScales : Array ℕ := #[
    0, 15, 21, 24, 21, 16,
    18, 23, 22, 16
  ]
def negativeArguments : Array ℕ := #[
    13218240135, 610635640675, 305252058793, 3324111665, 424084680705, 9804204464091,
    19604150543559, 213346672065, 13218240135, 424084680705, 5081339086775, 106021622315,
    13770385685, 5081339086775, 117532758019361, 235014223632681, 2556643787375, 610635640675,
    9804204464091, 117532758019361, 19608491011945, 159200290255, 106021622315, 19608491011945,
    19604232612621, 213347577455, 305252058793, 19604150543559, 235014223632681, 19604232612621,
    636662663601, 13770385685, 159200290255, 636662663601, 6927833855, 3324111665,
    213346672065, 2556643787375, 213347577455, 6927833855, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    3720603834154983421378560, 171878652737692130659532800, 171841632279278942123196416, 3742617013957979757608960, 119369225624785860931092480, 5519276446393047628898107392,
    5518077817680463688267464704, 120103499101583676046049280, 3720603834154983421378560, 119369225624785860931092480, 1430269801108939152451174400, 119369734687762365871554560,
    3876018989982125769359360, 1430269801108939152451174400, 66165060652477609386686021632, 66150623123681785400562548736, 1439262501017642950721536000, 171878652737692130659532800,
    5519276446393047628898107392, 66165060652477609386686021632, 5519299550918326376904785920, 179243591967423201405829120, 119369734687762365871554560, 5519299550918326376904785920,
    5518100918067778803650789376, 120104008790842004167720960, 171841632279278942123196416, 5518077817680463688267464704, 66150623123681785400562548736, 5518100918067778803650789376,
    179204608409635690440032256, 3876018989982125769359360, 179243591967423201405829120, 179204608409635690440032256, 3900023745982838352117760, 3742617013957979757608960,
    120103499101583676046049280, 1439262501017642950721536000, 120104008790842004167720960, 3900023745982838352117760, 316912650057057350374175801344, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    33, 39, 38, 31, 38, 43,
    44, 37, 33, 38, 42, 36,
    33, 42, 46, 47, 41, 39,
    43, 46, 44, 37, 36, 44,
    44, 37, 38, 44, 47, 44,
    39, 33, 37, 39, 32, 31,
    37, 41, 37, 32, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 15182355554070389, 21187347844132063, 24770852138119059, 21187353885654601, 16242857764108549,
    18437601729582122, 23969201966206902, 22968887352642833, 16446614868538854
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    33621811059351441, 39151520840846597, 38151210069360020, 31630321700558551, 38625561412888894, 43156537710190336,
    44156224364135668, 37634408650293798, 33621811059351441, 38625561412888894, 42208345879596769, 36625567565404855,
    33680849916383941, 42208345879596769, 46740056240674723, 47739741403449568, 41217388305099344, 39151520840846597,
    43156537710190336, 46740056240674723, 44156543749517156, 37212052009975886, 36625567565404855, 44156543749517156,
    44156230403692478, 37634414772718298, 38151210069360020, 44156224364135668, 47739741403449568, 44156230403692478,
    39211738205160245, 33680849916383941, 37212052009975886, 39211738205160245, 32689757185458463, 31630321700558551,
    37634408650293798, 41217388305099344, 37634414772718298, 32689757185458463, 0, 0
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
noncomputable def positiveFloor : ℝ := 45357637 / 250000000000
noncomputable def negativeCeiling : ℝ := 44446809 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3720603834154983421378560, coefficient := (-3720603834154983421378560) }, { argument := 171878652737692130659532800, coefficient := (-171878652737692130659532800) }, { argument := 171841632279278942123196416, coefficient := (-171841632279278942123196416) }, { argument := 3742617013957979757608960, coefficient := (-3742617013957979757608960) }, { argument := 119369225624785860931092480, coefficient := (-119369225624785860931092480) }, { argument := 5519276446393047628898107392, coefficient := (-5519276446393047628898107392) }, { argument := 5518077817680463688267464704, coefficient := (-5518077817680463688267464704) }, { argument := 120103499101583676046049280, coefficient := (-120103499101583676046049280) }, { argument := 3720603834154983421378560, coefficient := (-3720603834154983421378560) }, { argument := 119369225624785860931092480, coefficient := (-119369225624785860931092480) }, { argument := 1430269801108939152451174400, coefficient := (-1430269801108939152451174400) }, { argument := 119369734687762365871554560, coefficient := (-119369734687762365871554560) }, { argument := 3876018989982125769359360, coefficient := (-3876018989982125769359360) }, { argument := 1430269801108939152451174400, coefficient := (-1430269801108939152451174400) }, { argument := 66165060652477609386686021632, coefficient := (-66165060652477609386686021632) }, { argument := 66150623123681785400562548736, coefficient := (-66150623123681785400562548736) }, { argument := 1439262501017642950721536000, coefficient := (-1439262501017642950721536000) }, { argument := 171878652737692130659532800, coefficient := (-171878652737692130659532800) }, { argument := 5519276446393047628898107392, coefficient := (-5519276446393047628898107392) }, { argument := 66165060652477609386686021632, coefficient := (-66165060652477609386686021632) }, { argument := 5519299550918326376904785920, coefficient := (-5519299550918326376904785920) }, { argument := 179243591967423201405829120, coefficient := (-179243591967423201405829120) }, { argument := 119369734687762365871554560, coefficient := (-119369734687762365871554560) }, { argument := 5519299550918326376904785920, coefficient := (-5519299550918326376904785920) }, { argument := 5518100918067778803650789376, coefficient := (-5518100918067778803650789376) }, { argument := 120104008790842004167720960, coefficient := (-120104008790842004167720960) }, { argument := 171841632279278942123196416, coefficient := (-171841632279278942123196416) }, { argument := 5518077817680463688267464704, coefficient := (-5518077817680463688267464704) }, { argument := 66150623123681785400562548736, coefficient := (-66150623123681785400562548736) }, { argument := 5518100918067778803650789376, coefficient := (-5518100918067778803650789376) }, { argument := 179204608409635690440032256, coefficient := (-179204608409635690440032256) }, { argument := 3876018989982125769359360, coefficient := (-3876018989982125769359360) }, { argument := 179243591967423201405829120, coefficient := (-179243591967423201405829120) }, { argument := 179204608409635690440032256, coefficient := (-179204608409635690440032256) }, { argument := 3900023745982838352117760, coefficient := (-3900023745982838352117760) }, { argument := 3742617013957979757608960, coefficient := (-3742617013957979757608960) }, { argument := 120103499101583676046049280, coefficient := (-120103499101583676046049280) }, { argument := 1439262501017642950721536000, coefficient := (-1439262501017642950721536000) }, { argument := 120104008790842004167720960, coefficient := (-120104008790842004167720960) }, { argument := 3900023745982838352117760, coefficient := (-3900023745982838352117760) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 702367011730168071923433472, coefficient := 702367011730168071923433472 }, { argument := 22553653977599761708285427712, coefficient := 22553653977599761708285427712 }, { argument := 270370432156571953780842561536, coefficient := 270370432156571953780842561536 }, { argument := 22553748424929419101189701632, coefficient := 22553748424929419101189701632 }, { argument := 732448486226047711934676992, coefficient := 732448486226047711934676992 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 3353210768491248976889118720, coefficient := 3353210768491248976889118720 }, { argument := 155109517788988197449108553728, coefficient := 155109517788988197449108553728 }, { argument := 155075696200237885050088062976, coefficient := 155075696200237885050088062976 }, { argument := 3374225299340018898090065920, coefficient := 3374225299340018898090065920 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk1
