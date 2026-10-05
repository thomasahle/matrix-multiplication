import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 4, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk4

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
def constantNumerator : ℤ := 93763395875604899917870399488
def positiveArguments : Array ℕ := #[
    3, 78895, 12267341, 12267333, 157785, 79175,
    485791, 42248369, 3886593, 19001
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 5961137658656010546152734720, 231723519889330385541706809344, 231723368773602933713059971072, 5960948763996695760344186880, 1495573465124816639177523200,
    36705330177275645088105496576, 399024563443017899774624923648, 36707833031511566000068755456, 1435674968656098059287003136
  ]
def positiveScales : Array ℕ := #[
    1, 16, 23, 23, 17, 16,
    18, 25, 21, 14
  ]
def negativeArguments : Array ℕ := #[
    8306773505, 6405232589, 2221033958437, 102506479355, 1988944785, 8306773505,
    647554987995, 647554514635, 2076628395, 647554987995, 1986314662311, 86380281495123,
    15891537727051, 155414174719, 6405232589, 1986314662311, 1986313529983, 25620107961,
    647554514635, 1986313529983, 86380223893639, 15891528741363, 155414050447, 2221033958437,
    86380281495123, 86380223893639, 2220963742977, 2076628395, 25620107961, 2220963742977,
    205006373355, 248610405, 102506479355, 15891537727051, 15891528741363, 205006373355,
    1988944785, 155414174719, 155414050447, 248610405, 3, 3
  ]
def negativeCoefficients : Array ℕ := #[
    9352595515442277247877120, 230772824808334058850353152, 2500661926898522725116018688, 230824071113119720580055040, 8957410992586491282063360, 9352595515442277247877120,
    364541050329523501337149440, 364540783851533549824901120, 9352302865908991178833920, 364541050329523501337149440, 8945565973024372195124576256, 97255550888398623472984522752,
    8946140423236382821462310912, 349961609676290779944845312, 230772824808334058850353152, 8945565973024372195124576256, 8945560873472413333945581568, 230765417332702956132237312,
    364540783851533549824901120, 8945560873472413333945581568, 97255486034893153876087668736, 8946135364743741763020128256, 349961329840624333651705856, 2500661926898522725116018688,
    97255550888398623472984522752, 97255486034893153876087668736, 2500582871318649813124251648, 9352302865908991178833920, 230765417332702956132237312, 2500582871318649813124251648,
    230816656662538694971883520, 8957133818547424764887040, 230824071113119720580055040, 8946140423236382821462310912, 8946135364743741763020128256, 230816656662538694971883520,
    8957410992586491282063360, 349961609676290779944845312, 349961329840624333651705856, 8957133818547424764887040, 475368975085586025561263702016, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    32, 32, 41, 36, 30, 32,
    39, 39, 30, 39, 40, 46,
    43, 37, 32, 40, 40, 34,
    39, 40, 46, 43, 37, 41,
    46, 46, 41, 30, 34, 41,
    37, 27, 36, 43, 43, 37,
    30, 37, 37, 27, 1, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 16267646251349932, 23548319236616327, 23548318295779671, 17267600534957917, 16272757341802914,
    18889976236363806, 25332392311380781, 21890074607152450, 14213787727425491
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32951641082705664, 32576603813143831, 41014368589747617, 36576924148010644, 30889356083730901, 32951641082705664,
    39236211750134471, 39236210695530018, 30951595939011424, 39236211750134471, 40853231326194855, 46295767251527234,
    43853323967610165, 37177327136079363, 32576603813143831, 40853231326194855, 40853230503764983, 34576557503965589,
    39236210695530018, 40853230503764983, 46295766289485880, 43853323151854519, 37177325982473715, 41014368589747617,
    46295767251527234, 46295766289485880, 41014322979865418, 30951595939011424, 34576557503965589, 41014322979865418,
    37576877805517695, 27889311440940136, 36576924148010644, 43853323967610165, 43853323151854519, 37576877805517695,
    30889356083730901, 37177327136079363, 37177325982473715, 27889311440940136, 1584962500724866, 1584962500724866
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
noncomputable def positiveFloor : ℝ := 70767791 / 250000000000
noncomputable def negativeCeiling : ℝ := 55695551 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9352595515442277247877120, coefficient := (-9352595515442277247877120) }, { argument := 230772824808334058850353152, coefficient := (-230772824808334058850353152) }, { argument := 2500661926898522725116018688, coefficient := (-2500661926898522725116018688) }, { argument := 230824071113119720580055040, coefficient := (-230824071113119720580055040) }, { argument := 8957410992586491282063360, coefficient := (-8957410992586491282063360) }, { argument := 9352595515442277247877120, coefficient := (-9352595515442277247877120) }, { argument := 364541050329523501337149440, coefficient := (-364541050329523501337149440) }, { argument := 364540783851533549824901120, coefficient := (-364540783851533549824901120) }, { argument := 9352302865908991178833920, coefficient := (-9352302865908991178833920) }, { argument := 364541050329523501337149440, coefficient := (-364541050329523501337149440) }, { argument := 8945565973024372195124576256, coefficient := (-8945565973024372195124576256) }, { argument := 97255550888398623472984522752, coefficient := (-97255550888398623472984522752) }, { argument := 8946140423236382821462310912, coefficient := (-8946140423236382821462310912) }, { argument := 349961609676290779944845312, coefficient := (-349961609676290779944845312) }, { argument := 230772824808334058850353152, coefficient := (-230772824808334058850353152) }, { argument := 8945565973024372195124576256, coefficient := (-8945565973024372195124576256) }, { argument := 8945560873472413333945581568, coefficient := (-8945560873472413333945581568) }, { argument := 230765417332702956132237312, coefficient := (-230765417332702956132237312) }, { argument := 364540783851533549824901120, coefficient := (-364540783851533549824901120) }, { argument := 8945560873472413333945581568, coefficient := (-8945560873472413333945581568) }, { argument := 97255486034893153876087668736, coefficient := (-97255486034893153876087668736) }, { argument := 8946135364743741763020128256, coefficient := (-8946135364743741763020128256) }, { argument := 349961329840624333651705856, coefficient := (-349961329840624333651705856) }, { argument := 2500661926898522725116018688, coefficient := (-2500661926898522725116018688) }, { argument := 97255550888398623472984522752, coefficient := (-97255550888398623472984522752) }, { argument := 97255486034893153876087668736, coefficient := (-97255486034893153876087668736) }, { argument := 2500582871318649813124251648, coefficient := (-2500582871318649813124251648) }, { argument := 9352302865908991178833920, coefficient := (-9352302865908991178833920) }, { argument := 230765417332702956132237312, coefficient := (-230765417332702956132237312) }, { argument := 2500582871318649813124251648, coefficient := (-2500582871318649813124251648) }, { argument := 230816656662538694971883520, coefficient := (-230816656662538694971883520) }, { argument := 8957133818547424764887040, coefficient := (-8957133818547424764887040) }, { argument := 230824071113119720580055040, coefficient := (-230824071113119720580055040) }, { argument := 8946140423236382821462310912, coefficient := (-8946140423236382821462310912) }, { argument := 8946135364743741763020128256, coefficient := (-8946135364743741763020128256) }, { argument := 230816656662538694971883520, coefficient := (-230816656662538694971883520) }, { argument := 8957410992586491282063360, coefficient := (-8957410992586491282063360) }, { argument := 349961609676290779944845312, coefficient := (-349961609676290779944845312) }, { argument := 349961329840624333651705856, coefficient := (-349961329840624333651705856) }, { argument := 8957133818547424764887040, coefficient := (-8957133818547424764887040) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 5961137658656010546152734720, coefficient := 5961137658656010546152734720 }, { argument := 231723519889330385541706809344, coefficient := 231723519889330385541706809344 }, { argument := 231723368773602933713059971072, coefficient := 231723368773602933713059971072 }, { argument := 5960948763996695760344186880, coefficient := 5960948763996695760344186880 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 1495573465124816639177523200, coefficient := 1495573465124816639177523200 }, { argument := 36705330177275645088105496576, coefficient := 36705330177275645088105496576 }, { argument := 399024563443017899774624923648, coefficient := 399024563443017899774624923648 }, { argument := 36707833031511566000068755456, coefficient := 36707833031511566000068755456 }, { argument := 1435674968656098059287003136, coefficient := 1435674968656098059287003136 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk4
