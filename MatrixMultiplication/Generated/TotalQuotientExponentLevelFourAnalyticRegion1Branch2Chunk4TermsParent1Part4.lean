import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 4, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-6439041225859836161708284411117568)
def positiveArguments : Array ℕ := #[
    3465, 3069, 143649, 39105, 4597337067, 143649,
    3465, 3465, 1485, 3465, 39105, 1485,
    167031829, 3069, 33417403, 5511, 269768517, 8877,
    275, 8877, 5929, 33777851, 5511, 33,
    535, 489, 535, 489
  ]
def positiveCoefficients : Array ℕ := #[
    1072365559030960663131366359040, 949809495141708015916353060864, 44457212175826397777246073913344, 12102411309063698912482563194880, 43420620951310080940127513739264, 44457212175826397777246073913344,
    1072365559030960663131366359040, 1072365559030960663131366359040, 919170479169394854112599736320, 1072365559030960663131366359040, 12102411309063698912482563194880, 919170479169394854112599736320,
    1577571021684028017249477459968, 949809495141708015916353060864, 157809223871747530573100351488, 852785944562716336871134199808, 2547891605628500187229836017664, 1373649216092040087534940717056,
    42554188850434946949657395200, 1373649216092040087534940717056, 917468311615377456234613440512, 159511391425764928451086647296, 852785944562716336871134199808, 40852021296417549071671099392,
    41393620063604902941939466240, 37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096
  ]
def positiveScales : Array ℕ := #[
    11, 11, 17, 15, 32, 17,
    11, 11, 10, 11, 15, 10,
    27, 11, 24, 12, 28, 13,
    8, 13, 12, 25, 12, 5,
    9, 8, 9, 8
  ]
def negativeArguments : Array ℕ := #[
    2665, 105, 1
  ]
def negativeCoefficients : Array ℕ := #[
    211143053100514459686794627645440, 8318957063997755447322114785280, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    11, 6, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11758639637007751, 11583552930466262, 17132188424146353, 15255065463144074, 32098151299358342, 17132188424146353,
    11758639637007751, 11758639637007751, 10536247215688073, 11758639637007751, 15255065463144074, 10536247215688073,
    27315547802906280, 11583552930466262, 24994096283038743, 12428098411832503, 28007146749274504, 13115856481915077,
    8103287808412021, 13115856481915077, 12533573081389752, 25009574208743215, 12428098411832503, 5044394119358453,
    9063395081288509, 8933690654464738, 9063395081288509, 8933690654464738
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    11379919817646542, 6714245517766967, 0
  ]

abbrev PositiveTerm := Fin 28
abbrev NegativeTerm := Fin 3
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
noncomputable def positiveFloor : ℝ := 42986393607 / 1000000000000
noncomputable def negativeCeiling : ℝ := 29594881147 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1072365559030960663131366359040, coefficient := 1072365559030960663131366359040 }, { argument := 949809495141708015916353060864, coefficient := 949809495141708015916353060864 }, { argument := 44457212175826397777246073913344, coefficient := 44457212175826397777246073913344 }, { argument := 12102411309063698912482563194880, coefficient := 12102411309063698912482563194880 }, { argument := 43420620951310080940127513739264, coefficient := 43420620951310080940127513739264 }, { argument := 44457212175826397777246073913344, coefficient := 44457212175826397777246073913344 }, { argument := 1072365559030960663131366359040, coefficient := 1072365559030960663131366359040 }, { argument := 1072365559030960663131366359040, coefficient := 1072365559030960663131366359040 }, { argument := 919170479169394854112599736320, coefficient := 919170479169394854112599736320 }, { argument := 1072365559030960663131366359040, coefficient := 1072365559030960663131366359040 }, { argument := 12102411309063698912482563194880, coefficient := 12102411309063698912482563194880 }, { argument := 919170479169394854112599736320, coefficient := 919170479169394854112599736320 }, { argument := 1577571021684028017249477459968, coefficient := 1577571021684028017249477459968 }, { argument := 949809495141708015916353060864, coefficient := 949809495141708015916353060864 }, { argument := 211143053100514459686794627645440, coefficient := (-211143053100514459686794627645440) }, { argument := 157809223871747530573100351488, coefficient := 157809223871747530573100351488 }, { argument := 852785944562716336871134199808, coefficient := 852785944562716336871134199808 }, { argument := 2547891605628500187229836017664, coefficient := 2547891605628500187229836017664 }, { argument := 1373649216092040087534940717056, coefficient := 1373649216092040087534940717056 }, { argument := 42554188850434946949657395200, coefficient := 42554188850434946949657395200 }, { argument := 1373649216092040087534940717056, coefficient := 1373649216092040087534940717056 }, { argument := 917468311615377456234613440512, coefficient := 917468311615377456234613440512 }, { argument := 159511391425764928451086647296, coefficient := 159511391425764928451086647296 }, { argument := 852785944562716336871134199808, coefficient := 852785944562716336871134199808 }, { argument := 40852021296417549071671099392, coefficient := 40852021296417549071671099392 }, { argument := 8318957063997755447322114785280, coefficient := (-8318957063997755447322114785280) }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end TermShard8


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
