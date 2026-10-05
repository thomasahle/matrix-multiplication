import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 8, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk8

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
def constantNumerator : ℤ := 500971964242108980064866533376
def positiveArguments : Array ℕ := #[
    1, 16777241, 16777191, 3033261, 10709691, 379283,
    201239, 16374759, 16374727, 100617
  ]
def positiveCoefficients : Array ℕ := #[
    633825300114114700748351602688, 158456561146852818669348585472, 158456088910204531704827215872, 114593360641565303284325941248, 404600686562325548146505023488, 114631252910223849317520637952,
    3801297234584818132635877376, 154655226133336137579550998528, 154654923901881233922257321984, 3801202787255160739731603456
  ]
def positiveScales : Array ℕ := #[
    0, 24, 23, 21, 23, 18,
    17, 23, 23, 16
  ]
def negativeArguments : Array ℕ := #[
    1688117449863, 137361639331981, 137361370895773, 422018876697, 71886734615, 8120886056313,
    2301157181351, 1688117449863, 1688112720761, 1688112720761, 137361229358963, 137360960924259,
    422017694439, 8120886056313, 57350572268669, 16247055218833, 137361639331981, 137361229358963,
    2301157181351, 16247055218833, 4603881682977, 137361370895773, 137360960924259, 422018876697,
    422017694439, 1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    950325639770079845475680256, 38663864231906881168564289536, 38663788673831486071754457088, 950302027917962248879865856, 10359970279199863559453409280, 36573219417129483595570741248,
    10363490624453304487138820096, 950325639770079845475680256, 950322977522329220842258432, 950322977522329220842258432, 38663748834761187621211209728, 38663673277109130889374203904,
    950299365709618120985935872, 36573219417129483595570741248, 129142007949331204904857894912, 36585115914702085572823875584, 38663864231906881168564289536, 38663748834761187621211209728,
    10363490624453304487138820096, 36585115914702085572823875584, 10367019915956534598797623296, 38663788673831486071754457088, 38663673277109130889374203904, 950302027917962248879865856,
    950299365709618120985935872, 316912650057057350374175801344, 633825300114114700748351602688, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    40, 46, 46, 38, 36, 42,
    41, 40, 40, 40, 46, 46,
    38, 42, 45, 43, 46, 46,
    41, 43, 42, 46, 46, 38,
    38, 0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 24000002149781534, 23999997848755731, 21532438210776212, 23352413519724666, 18532915183887716,
    17618550400127233, 23964970336932094, 23964967517575438, 16618514554367619
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40618552420925726, 46964972504105310, 46964969684744297, 38618516575186400, 36065006521056668, 42884774288008650,
    41065496669368460, 40618552420925726, 40618548379345822, 40618548379345822, 46964968198193871, 46964965378840240,
    38618512533565900, 42884774288008650, 45704873115761212, 43885243490025593, 46964972504105310, 46964968198193871,
    41065496669368460, 43885243490025593, 42065987896189799, 46964969684744297, 46964965378840240, 38618516575186400,
    38618512533565900, 0, 0, 0
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
noncomputable def positiveFloor : ℝ := 351349611 / 1000000000000
noncomputable def negativeCeiling : ℝ := 345935751 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 950325639770079845475680256, coefficient := (-950325639770079845475680256) }, { argument := 38663864231906881168564289536, coefficient := (-38663864231906881168564289536) }, { argument := 38663788673831486071754457088, coefficient := (-38663788673831486071754457088) }, { argument := 950302027917962248879865856, coefficient := (-950302027917962248879865856) }, { argument := 10359970279199863559453409280, coefficient := (-10359970279199863559453409280) }, { argument := 36573219417129483595570741248, coefficient := (-36573219417129483595570741248) }, { argument := 10363490624453304487138820096, coefficient := (-10363490624453304487138820096) }, { argument := 950325639770079845475680256, coefficient := (-950325639770079845475680256) }, { argument := 950322977522329220842258432, coefficient := (-950322977522329220842258432) }, { argument := 950322977522329220842258432, coefficient := (-950322977522329220842258432) }, { argument := 38663748834761187621211209728, coefficient := (-38663748834761187621211209728) }, { argument := 38663673277109130889374203904, coefficient := (-38663673277109130889374203904) }, { argument := 950299365709618120985935872, coefficient := (-950299365709618120985935872) }, { argument := 36573219417129483595570741248, coefficient := (-36573219417129483595570741248) }, { argument := 129142007949331204904857894912, coefficient := (-129142007949331204904857894912) }, { argument := 36585115914702085572823875584, coefficient := (-36585115914702085572823875584) }, { argument := 38663864231906881168564289536, coefficient := (-38663864231906881168564289536) }, { argument := 38663748834761187621211209728, coefficient := (-38663748834761187621211209728) }, { argument := 10363490624453304487138820096, coefficient := (-10363490624453304487138820096) }, { argument := 36585115914702085572823875584, coefficient := (-36585115914702085572823875584) }, { argument := 10367019915956534598797623296, coefficient := (-10367019915956534598797623296) }, { argument := 38663788673831486071754457088, coefficient := (-38663788673831486071754457088) }, { argument := 38663673277109130889374203904, coefficient := (-38663673277109130889374203904) }, { argument := 950302027917962248879865856, coefficient := (-950302027917962248879865856) }, { argument := 950299365709618120985935872, coefficient := (-950299365709618120985935872) }, { argument := 633825300114114700748351602688, coefficient := 633825300114114700748351602688 }, { argument := 158456561146852818669348585472, coefficient := 158456561146852818669348585472 }, { argument := 158456088910204531704827215872, coefficient := 158456088910204531704827215872 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 114593360641565303284325941248, coefficient := 114593360641565303284325941248 }, { argument := 404600686562325548146505023488, coefficient := 404600686562325548146505023488 }, { argument := 114631252910223849317520637952, coefficient := 114631252910223849317520637952 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 3801297234584818132635877376, coefficient := 3801297234584818132635877376 }, { argument := 154655226133336137579550998528, coefficient := 154655226133336137579550998528 }, { argument := 154654923901881233922257321984, coefficient := 154654923901881233922257321984 }, { argument := 3801202787255160739731603456, coefficient := 3801202787255160739731603456 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk8
