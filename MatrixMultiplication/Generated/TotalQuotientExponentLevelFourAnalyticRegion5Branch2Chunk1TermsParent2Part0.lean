import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 1, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk1

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
def constantNumerator : ℤ := 463813174296810620416121896960
def positiveArguments : Array ℕ := #[
    1, 3026819, 21443291, 6057503, 407831, 4092347,
    8184677, 407859
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 57174994381252066624296452096, 202526157401640634768081027072, 57211498274164648981798322176, 3851854890150420554293706752, 154604498472577151850665476096,
    154604177351656316714790944768, 3852119342673461254425673728
  ]
def positiveScales : Array ℕ := #[
    0, 21, 24, 22, 18, 21,
    22, 18
  ]
def negativeArguments : Array ℕ := #[
    617207191241, 24773595430139, 24773543964499, 617249570025, 617207191241, 4372799692607,
    1235054703407, 4372799692607, 175506594830207, 175506230510043, 4373099824999, 24773595430139,
    175506594830207, 49578972573323, 1235054703407, 49578972573323, 49578869399423, 1235139575495,
    24773543964499, 175506230510043, 49578869399423, 617249570025, 4373099824999, 1235139575495,
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    347456759560419757829128192, 13946294393475177871329722368, 13946265420895537073318002688, 347480616694898609671372800, 347456759560419757829128192, 1230833691636919040781320192,
    347636993877871478536404992, 1230833691636919040781320192, 49400714692399054055687585792, 49400612145389376933313118208, 1230918171394967354258489344, 13946294393475177871329722368,
    49400714692399054055687585792, 13955240150414343998315429888, 347636993877871478536404992, 13955240150414343998315429888, 13955211109543244350764351488, 347660883246864663282974720,
    13946265420895537073318002688, 49400612145389376933313118208, 13955211109543244350764351488, 347480616694898609671372800, 1230918171394967354258489344, 347660883246864663282974720,
    316912650057057350374175801344, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    39, 44, 44, 39, 39, 41,
    40, 41, 47, 47, 41, 44,
    47, 45, 40, 45, 45, 40,
    44, 47, 45, 39, 41, 40,
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 21529370975705346, 24354023004009984, 22530291783500799, 18637611915917047, 21964497048375919,
    22964494051826405, 18637710962028093
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    39166963914981508, 44493868497873401, 44493865500758956, 39167062970150483, 39166963914981508, 41991694422932431,
    40167712082147526, 41991694422932431, 47318518570634265, 47318515575855408, 41991793440685240, 44493868497873401,
    47318518570634265, 45494793608253632, 40167712082147526, 45494793608253632, 45494790606000438, 40167811219726753,
    44493865500758956, 47318515575855408, 45494790606000438, 39167062970150483, 41991793440685240, 40167811219726753,
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
noncomputable def positiveFloor : ℝ := 175043691 / 1000000000000
noncomputable def negativeCeiling : ℝ := 176811943 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 347456759560419757829128192, coefficient := (-347456759560419757829128192) }, { argument := 13946294393475177871329722368, coefficient := (-13946294393475177871329722368) }, { argument := 13946265420895537073318002688, coefficient := (-13946265420895537073318002688) }, { argument := 347480616694898609671372800, coefficient := (-347480616694898609671372800) }, { argument := 347456759560419757829128192, coefficient := (-347456759560419757829128192) }, { argument := 1230833691636919040781320192, coefficient := (-1230833691636919040781320192) }, { argument := 347636993877871478536404992, coefficient := (-347636993877871478536404992) }, { argument := 1230833691636919040781320192, coefficient := (-1230833691636919040781320192) }, { argument := 49400714692399054055687585792, coefficient := (-49400714692399054055687585792) }, { argument := 49400612145389376933313118208, coefficient := (-49400612145389376933313118208) }, { argument := 1230918171394967354258489344, coefficient := (-1230918171394967354258489344) }, { argument := 13946294393475177871329722368, coefficient := (-13946294393475177871329722368) }, { argument := 49400714692399054055687585792, coefficient := (-49400714692399054055687585792) }, { argument := 13955240150414343998315429888, coefficient := (-13955240150414343998315429888) }, { argument := 347636993877871478536404992, coefficient := (-347636993877871478536404992) }, { argument := 13955240150414343998315429888, coefficient := (-13955240150414343998315429888) }, { argument := 13955211109543244350764351488, coefficient := (-13955211109543244350764351488) }, { argument := 347660883246864663282974720, coefficient := (-347660883246864663282974720) }, { argument := 13946265420895537073318002688, coefficient := (-13946265420895537073318002688) }, { argument := 49400612145389376933313118208, coefficient := (-49400612145389376933313118208) }, { argument := 13955211109543244350764351488, coefficient := (-13955211109543244350764351488) }, { argument := 347480616694898609671372800, coefficient := (-347480616694898609671372800) }, { argument := 1230918171394967354258489344, coefficient := (-1230918171394967354258489344) }, { argument := 347660883246864663282974720, coefficient := (-347660883246864663282974720) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 57174994381252066624296452096, coefficient := 57174994381252066624296452096 }, { argument := 202526157401640634768081027072, coefficient := 202526157401640634768081027072 }, { argument := 57211498274164648981798322176, coefficient := 57211498274164648981798322176 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 3851854890150420554293706752, coefficient := 3851854890150420554293706752 }, { argument := 154604498472577151850665476096, coefficient := 154604498472577151850665476096 }, { argument := 154604177351656316714790944768, coefficient := 154604177351656316714790944768 }, { argument := 3852119342673461254425673728, coefficient := 3852119342673461254425673728 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk1
