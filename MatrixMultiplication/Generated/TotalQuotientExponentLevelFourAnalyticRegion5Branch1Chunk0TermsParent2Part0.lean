import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 0, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk0

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    1, 38201, 1276761, 7073665, 638373, 19089
  ]
def positiveCoefficients : Array ℕ := #[
    79228162514264337593543950336, 360798244024206633616801792, 12058666706070262185367437312, 133617754028192435642155663360, 12058525035075776096011026432, 360581015165994629936971776
  ]
def positiveScales : Array ℕ := #[
    0, 15, 20, 22, 19, 14
  ]
def negativeArguments : Array ℕ := #[
    1459316401, 48773546961, 270221076665, 24386486973, 729218889, 48773546961,
    1630118651121, 9031379599065, 815049749853, 24372090729, 270221076665, 9031379599065,
    50036736532225, 4515636747045, 135029191185, 24386486973, 815049749853, 4515636747045,
    407520087129, 12185902197, 729218889, 24372090729, 135029191185, 12185902197,
    364389921, 1
  ]
def negativeCoefficients : Array ℕ := #[
    410761049984953332269056, 13728532994943561725116416, 152120942522018528996884480, 13728371705559781868568576, 410513739596490885562368, 13728532994943561725116416,
    458837609359889448227045376, 5084214724623829195586273280, 458832218715798347119067136, 13720267340670540026216448, 152120942522018528996884480, 5084214724623829195586273280,
    56336357000341048554579558400, 5084154992833095176112046080, 152029353776226365803069440, 13728371705559781868568576, 458832218715798347119067136, 5084154992833095176112046080,
    458826828135039115770986496, 13720106148395627134844928, 410513739596490885562368, 13720267340670540026216448, 152029353776226365803069440, 13720106148395627134844928,
    410266578108291118792704, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    30, 35, 37, 34, 29, 35,
    40, 43, 39, 34, 37, 43,
    45, 42, 36, 34, 39, 42,
    38, 33, 29, 34, 36, 33,
    28, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 15221322784202037, 20284057058041302, 22754026465718032, 19284040108469115, 14220453906972867
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    30442645568404112, 35505379842243666, 37975349265828795, 34505362892671478, 29441776691174940, 35505379842243666,
    40568114116084887, 43038083523774562, 39568097166512699, 34504510965014486, 37975349265828795, 43038083523774562,
    45508052931466873, 42038066574202375, 36974480388374686, 34505362892671478, 39568097166512699, 42038066574202375,
    38568080216940510, 33504494015442298, 29441776691174940, 34504510965014486, 36974480388374686, 33504494015442298,
    28440907813945768, 0
  ]

abbrev PositiveTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 10616981 / 250000000000
noncomputable def negativeCeiling : ℝ := 1698717 / 40000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 410761049984953332269056, coefficient := (-410761049984953332269056) }, { argument := 13728532994943561725116416, coefficient := (-13728532994943561725116416) }, { argument := 152120942522018528996884480, coefficient := (-152120942522018528996884480) }, { argument := 13728371705559781868568576, coefficient := (-13728371705559781868568576) }, { argument := 410513739596490885562368, coefficient := (-410513739596490885562368) }, { argument := 13728532994943561725116416, coefficient := (-13728532994943561725116416) }, { argument := 458837609359889448227045376, coefficient := (-458837609359889448227045376) }, { argument := 5084214724623829195586273280, coefficient := (-5084214724623829195586273280) }, { argument := 458832218715798347119067136, coefficient := (-458832218715798347119067136) }, { argument := 13720267340670540026216448, coefficient := (-13720267340670540026216448) }, { argument := 152120942522018528996884480, coefficient := (-152120942522018528996884480) }, { argument := 5084214724623829195586273280, coefficient := (-5084214724623829195586273280) }, { argument := 56336357000341048554579558400, coefficient := (-56336357000341048554579558400) }, { argument := 5084154992833095176112046080, coefficient := (-5084154992833095176112046080) }, { argument := 152029353776226365803069440, coefficient := (-152029353776226365803069440) }, { argument := 13728371705559781868568576, coefficient := (-13728371705559781868568576) }, { argument := 458832218715798347119067136, coefficient := (-458832218715798347119067136) }, { argument := 5084154992833095176112046080, coefficient := (-5084154992833095176112046080) }, { argument := 458826828135039115770986496, coefficient := (-458826828135039115770986496) }, { argument := 13720106148395627134844928, coefficient := (-13720106148395627134844928) }, { argument := 410513739596490885562368, coefficient := (-410513739596490885562368) }, { argument := 13720267340670540026216448, coefficient := (-13720267340670540026216448) }, { argument := 152029353776226365803069440, coefficient := (-152029353776226365803069440) }, { argument := 13720106148395627134844928, coefficient := (-13720106148395627134844928) }, { argument := 410266578108291118792704, coefficient := (-410266578108291118792704) }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 360798244024206633616801792, coefficient := 360798244024206633616801792 }, { argument := 12058666706070262185367437312, coefficient := 12058666706070262185367437312 }, { argument := 133617754028192435642155663360, coefficient := 133617754028192435642155663360 }, { argument := 12058525035075776096011026432, coefficient := 12058525035075776096011026432 }, { argument := 360581015165994629936971776, coefficient := 360581015165994629936971776 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk0
