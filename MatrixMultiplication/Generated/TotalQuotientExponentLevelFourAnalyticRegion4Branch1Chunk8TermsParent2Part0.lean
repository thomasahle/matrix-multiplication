import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 8, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk8

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
def constantNumerator : ℤ := 1743019575313815427057966907392
def positiveArguments : Array ℕ := #[
    5, 1, 75497479, 75497465, 13963713, 47572149,
    6980805, 244873, 1017967, 1017967, 244871
  ]
def positiveCoefficients : Array ℕ := #[
    1584563250285286751870879006720, 158456325028528675187087900672, 713053528741509798516928544768, 713053396515248278166862561280, 263767080990444568703498452992, 898612487822722838732331810816,
    263727356443590669247960842240, 2312760095519477264826761216, 76915411863477826068007616512, 76915411863477826068007616512, 2312741206053545786245906432
  ]
def positiveScales : Array ℕ := #[
    2, 0, 26, 26, 23, 25,
    22, 17, 19, 19, 17
  ]
def negativeArguments : Array ℕ := #[
    244873, 1017967, 1017967, 244871, 58568062635031, 199532073530007,
    29279620997289, 58568062635031, 58568051946473, 244873, 58568051946473, 199532036148585,
    29279615672151, 199532073530007, 199532036148585, 1017967, 29279620997289, 29279615672151,
    1017967, 244871, 1, 9, 9, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1156380047759738632413380608, 38457705931738913034003808256, 38457705931738913034003808256, 1156370603026772893122953216, 65941776264734370416866361344, 224653142999550483405490618368,
    65931845106470045436107292672, 65941776264734370416866361344, 65941764230487913934882865152, 1156380047759738632413380608, 65941764230487913934882865152, 224653100911810935960675287040,
    65931833115325289187873128448, 224653142999550483405490618368, 224653100911810935960675287040, 38457705931738913034003808256, 65931845106470045436107292672, 65931833115325289187873128448,
    38457705931738913034003808256, 1156370603026772893122953216, 158456325028528675187087900672, 1426106925256758076683791106048, 1426106925256758076683791106048, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    17, 19, 19, 17, 45, 47,
    44, 45, 45, 17, 45, 47,
    44, 47, 47, 19, 44, 44,
    19, 17, 0, 3, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 0, 26169925135206589, 26169924867678021, 23735179274405027, 25503613862554032,
    22734961981471581, 17901674183489213, 19957259362124816, 19957259362124816, 17901662400230746
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    17901674188267944, 19957259374629056, 19957259374629056, 17901662405008469, 45735179406221715, 47503613997695525,
    44734962112835698, 45735179406221715, 45735179142932639, 17901674188267944, 45735179142932639, 47503613727413178,
    44734961850450098, 47503613997695525, 47503613727413178, 19957259374629056, 44734962112835698, 44734961850450098,
    19957259374629056, 17901662405008469, 0, 3169925001442313, 3169925001442313, 0
  ]

abbrev PositiveTerm := Fin 11
abbrev NegativeTerm := Fin 24
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
noncomputable def positiveFloor : ℝ := 95486951 / 100000000000
noncomputable def negativeCeiling : ℝ := 473915739 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1156380047759738632413380608, coefficient := (-1156380047759738632413380608) }, { argument := 38457705931738913034003808256, coefficient := (-38457705931738913034003808256) }, { argument := 38457705931738913034003808256, coefficient := (-38457705931738913034003808256) }, { argument := 1156370603026772893122953216, coefficient := (-1156370603026772893122953216) }, { argument := 65941776264734370416866361344, coefficient := (-65941776264734370416866361344) }, { argument := 224653142999550483405490618368, coefficient := (-224653142999550483405490618368) }, { argument := 65931845106470045436107292672, coefficient := (-65931845106470045436107292672) }, { argument := 65941776264734370416866361344, coefficient := (-65941776264734370416866361344) }, { argument := 65941764230487913934882865152, coefficient := (-65941764230487913934882865152) }, { argument := 1156380047759738632413380608, coefficient := (-1156380047759738632413380608) }, { argument := 65941764230487913934882865152, coefficient := (-65941764230487913934882865152) }, { argument := 224653100911810935960675287040, coefficient := (-224653100911810935960675287040) }, { argument := 65931833115325289187873128448, coefficient := (-65931833115325289187873128448) }, { argument := 224653142999550483405490618368, coefficient := (-224653142999550483405490618368) }, { argument := 224653100911810935960675287040, coefficient := (-224653100911810935960675287040) }, { argument := 38457705931738913034003808256, coefficient := (-38457705931738913034003808256) }, { argument := 65931845106470045436107292672, coefficient := (-65931845106470045436107292672) }, { argument := 65931833115325289187873128448, coefficient := (-65931833115325289187873128448) }, { argument := 38457705931738913034003808256, coefficient := (-38457705931738913034003808256) }, { argument := 1156370603026772893122953216, coefficient := (-1156370603026772893122953216) }, { argument := 1584563250285286751870879006720, coefficient := 1584563250285286751870879006720 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 713053528741509798516928544768, coefficient := 713053528741509798516928544768 }, { argument := 713053396515248278166862561280, coefficient := 713053396515248278166862561280 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 263767080990444568703498452992, coefficient := 263767080990444568703498452992 }, { argument := 898612487822722838732331810816, coefficient := 898612487822722838732331810816 }, { argument := 263727356443590669247960842240, coefficient := 263727356443590669247960842240 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 2312760095519477264826761216, coefficient := 2312760095519477264826761216 }, { argument := 76915411863477826068007616512, coefficient := 76915411863477826068007616512 }, { argument := 76915411863477826068007616512, coefficient := 76915411863477826068007616512 }, { argument := 2312741206053545786245906432, coefficient := 2312741206053545786245906432 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk8
