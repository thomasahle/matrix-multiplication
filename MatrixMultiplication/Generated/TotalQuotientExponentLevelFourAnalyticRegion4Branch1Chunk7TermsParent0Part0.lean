import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 7, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7

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
def constantNumerator : ℤ := 2879902974149174031113567338496
def positiveArguments : Array ℕ := #[
    49, 12582915, 12582909, 38963055, 131803175, 19474485,
    2770315, 97892987, 24473547, 1384551
  ]
def positiveCoefficients : Array ℕ := #[
    3882179963198952542083653566464, 950738176844763228865497661440, 950737723497580873379557146624, 735991300008826177166896005120, 2489691583823209401154745139200, 735725241881181301355556372480,
    26164885405982042360360468480, 924573121433587803197909499904, 924584464557879656085712797696, 26153428944894600601072041984
  ]
def positiveScales : Array ℕ := #[
    5, 23, 23, 25, 26, 24,
    21, 26, 24, 20
  ]
def negativeArguments : Array ℕ := #[
    23239095879627, 821186085911143, 410598080280247, 725903767683, 242858030855435, 821753078541895,
    121386035056215, 23239095879627, 23239077263413, 23239077263413, 821185701873049, 410597888330057,
    725903181693, 821753078541895, 2779375163448675, 410726215465515, 821186085911143, 821185701873049,
    121386035056215, 410726215465515, 60671516072895, 410598080280247, 410597888330057, 725903767683,
    725903181693, 3, 25, 3
  ]
def negativeCoefficients : Array ℕ := #[
    6541223971494711635384205312, 231143334406953733126837239808, 231146170168645173877422424064, 6538359875287995793104961536, 68358458579029342870160015360, 231302928644489765903788933120,
    68334262780893979809499054080, 6541223971494711635384205312, 6541218731496309544796028928, 6541218731496309544796028928, 231143226309840168472117510144, 231146062110294654165433974784,
    6538354597159304507431059456, 231302928644489765903788933120, 782324559401891509012581580800, 231218303865223425661002055680, 231143334406953733126837239808, 231143226309840168472117510144,
    68334262780893979809499054080, 231218303865223425661002055680, 68310054294473245207277076480, 231146170168645173877422424064, 231146062110294654165433974784, 6538359875287995793104961536,
    6538354597159304507431059456, 1901475900342344102245054808064, 3961408125713216879677197516800, 1901475900342344102245054808064
  ]
def negativeScales : Array ℕ := #[
    44, 49, 48, 39, 47, 49,
    46, 44, 44, 44, 49, 48,
    39, 49, 51, 48, 49, 49,
    46, 48, 45, 48, 48, 39,
    39, 1, 4, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5614709844114682, 23584962844686185, 23584962156755582, 25215603464336032, 26973809881915106, 24215081841136730,
    21401618597259370, 26544702173859399, 24544719873453298, 20400986765746210
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    44401619175111571, 49544702511207964, 48544720210676756, 39400987348058279, 47787106523263555, 49545698284523018,
    46786595784164140, 44401619175111571, 44401618019406956, 44401618019406956, 49544701836513162, 48544719536232170,
    39400986183433923, 49545698284523018, 51303682007728806, 48545170361728693, 49544702511207964, 49544701836513162,
    46786595784164140, 48545170361728693, 45786084596216140, 48544720210676756, 48544719536232170, 39400987348058279,
    39400986183433923, 1584962500724866, 4643856189792934, 1584962500724866
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
noncomputable def positiveFloor : ℝ := 657536083 / 250000000000
noncomputable def negativeCeiling : ℝ := 64880143 / 25000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6541223971494711635384205312, coefficient := (-6541223971494711635384205312) }, { argument := 231143334406953733126837239808, coefficient := (-231143334406953733126837239808) }, { argument := 231146170168645173877422424064, coefficient := (-231146170168645173877422424064) }, { argument := 6538359875287995793104961536, coefficient := (-6538359875287995793104961536) }, { argument := 68358458579029342870160015360, coefficient := (-68358458579029342870160015360) }, { argument := 231302928644489765903788933120, coefficient := (-231302928644489765903788933120) }, { argument := 68334262780893979809499054080, coefficient := (-68334262780893979809499054080) }, { argument := 6541223971494711635384205312, coefficient := (-6541223971494711635384205312) }, { argument := 6541218731496309544796028928, coefficient := (-6541218731496309544796028928) }, { argument := 6541218731496309544796028928, coefficient := (-6541218731496309544796028928) }, { argument := 231143226309840168472117510144, coefficient := (-231143226309840168472117510144) }, { argument := 231146062110294654165433974784, coefficient := (-231146062110294654165433974784) }, { argument := 6538354597159304507431059456, coefficient := (-6538354597159304507431059456) }, { argument := 231302928644489765903788933120, coefficient := (-231302928644489765903788933120) }, { argument := 782324559401891509012581580800, coefficient := (-782324559401891509012581580800) }, { argument := 231218303865223425661002055680, coefficient := (-231218303865223425661002055680) }, { argument := 231143334406953733126837239808, coefficient := (-231143334406953733126837239808) }, { argument := 231143226309840168472117510144, coefficient := (-231143226309840168472117510144) }, { argument := 68334262780893979809499054080, coefficient := (-68334262780893979809499054080) }, { argument := 231218303865223425661002055680, coefficient := (-231218303865223425661002055680) }, { argument := 68310054294473245207277076480, coefficient := (-68310054294473245207277076480) }, { argument := 231146170168645173877422424064, coefficient := (-231146170168645173877422424064) }, { argument := 231146062110294654165433974784, coefficient := (-231146062110294654165433974784) }, { argument := 6538359875287995793104961536, coefficient := (-6538359875287995793104961536) }, { argument := 6538354597159304507431059456, coefficient := (-6538354597159304507431059456) }, { argument := 3882179963198952542083653566464, coefficient := 3882179963198952542083653566464 }, { argument := 950738176844763228865497661440, coefficient := 950738176844763228865497661440 }, { argument := 950737723497580873379557146624, coefficient := 950737723497580873379557146624 }, { argument := 1901475900342344102245054808064, coefficient := (-1901475900342344102245054808064) }, { argument := 735991300008826177166896005120, coefficient := 735991300008826177166896005120 }, { argument := 2489691583823209401154745139200, coefficient := 2489691583823209401154745139200 }, { argument := 735725241881181301355556372480, coefficient := 735725241881181301355556372480 }, { argument := 3961408125713216879677197516800, coefficient := (-3961408125713216879677197516800) }, { argument := 26164885405982042360360468480, coefficient := 26164885405982042360360468480 }, { argument := 924573121433587803197909499904, coefficient := 924573121433587803197909499904 }, { argument := 924584464557879656085712797696, coefficient := 924584464557879656085712797696 }, { argument := 26153428944894600601072041984, coefficient := 26153428944894600601072041984 }, { argument := 1901475900342344102245054808064, coefficient := (-1901475900342344102245054808064) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7
