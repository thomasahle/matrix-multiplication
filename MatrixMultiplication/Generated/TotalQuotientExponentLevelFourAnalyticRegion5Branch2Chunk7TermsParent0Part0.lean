import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 7, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk7

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
def constantNumerator : ℤ := (-2311142460434802399673904529408)
def positiveArguments : Array ℕ := #[
    7, 33550923, 33557941, 1136997, 32139789, 9095883,
    869331, 32685107, 32685115, 869311
  ]
def positiveCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 316879508489080571204066082816, 316945791625034129544285519872, 171818128765546815969174749184, 607103449360410046692197400576, 171816372045215188461155254272,
    8210599153839103086535114752, 308702107571616041723383250944, 308702183129479767637706670080, 8210410259179788300726566912
  ]
def positiveScales : Array ℕ := #[
    2, 24, 25, 20, 24, 23,
    19, 24, 24, 19
  ]
def negativeArguments : Array ℕ := #[
    7291869557605, 274153721773787, 274153789053891, 7291701785085, 6894050753373, 48726697919709,
    13787777614953, 7291869557605, 7293084404891, 7293084404891, 274211378348325, 274211445285949,
    7292916633091, 48726697919709, 43038700768845, 48726590128623, 274153721773787, 274211378348325,
    13787777614953, 48726590128623, 1723428644661, 274153789053891, 274211445285949, 7291701785085,
    7292916633091, 1, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    2052478813904008844809338880, 77167412451416360554984374272, 77167431389082067045497962496, 2052431590137849156741365760, 15524022201981965009896341504, 54861384648549043755250876416,
    15523657532242399219440156672, 2052478813904008844809338880, 2052820763015542698458218496, 2052820763015542698458218496, 77183641334391660306707251200, 77183660175657816773355372544,
    2052773539452044993621917696, 54861384648549043755250876416, 193829076745080621700868997120, 54861263286575357889978826752, 77167412451416360554984374272, 77183641334391660306707251200,
    15523657532242399219440156672, 54861263286575357889978826752, 15523265203789837121158643712, 77167431389082067045497962496, 77183660175657816773355372544, 2052431590137849156741365760,
    2052773539452044993621917696, 633825300114114700748351602688, 950737950171172051122527404032, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    42, 47, 47, 42, 42, 45,
    43, 42, 42, 42, 47, 47,
    42, 45, 45, 45, 47, 47,
    43, 45, 40, 47, 47, 42,
    42, 0, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 24999849118874090, 25000150863892209, 20116797016966091, 24937857121336517, 23116782266341781,
    19729546065893649, 24962130083502125, 24962130436615815, 19729512874585935
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    42729425892395028, 47961978400239816, 47961978754291844, 42729392698251056, 42648489058402464, 45469777691726304,
    43648455168125984, 42729425892395028, 42729666229686342, 42729666229686342, 47962281777942520, 47962282130118230,
    42729633041214187, 45469777691726304, 45290699760718453, 45469774500255429, 47961978400239816, 47962281777942520,
    43648455168125984, 45469774500255429, 40648418706521203, 47961978754291844, 47962282130118230, 42729392698251056,
    42729633041214187, 0, 1584962500724866, 0
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
noncomputable def positiveFloor : ℝ := 689282753 / 1000000000000
noncomputable def negativeCeiling : ℝ := 640679779 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2052478813904008844809338880, coefficient := (-2052478813904008844809338880) }, { argument := 77167412451416360554984374272, coefficient := (-77167412451416360554984374272) }, { argument := 77167431389082067045497962496, coefficient := (-77167431389082067045497962496) }, { argument := 2052431590137849156741365760, coefficient := (-2052431590137849156741365760) }, { argument := 15524022201981965009896341504, coefficient := (-15524022201981965009896341504) }, { argument := 54861384648549043755250876416, coefficient := (-54861384648549043755250876416) }, { argument := 15523657532242399219440156672, coefficient := (-15523657532242399219440156672) }, { argument := 2052478813904008844809338880, coefficient := (-2052478813904008844809338880) }, { argument := 2052820763015542698458218496, coefficient := (-2052820763015542698458218496) }, { argument := 2052820763015542698458218496, coefficient := (-2052820763015542698458218496) }, { argument := 77183641334391660306707251200, coefficient := (-77183641334391660306707251200) }, { argument := 77183660175657816773355372544, coefficient := (-77183660175657816773355372544) }, { argument := 2052773539452044993621917696, coefficient := (-2052773539452044993621917696) }, { argument := 54861384648549043755250876416, coefficient := (-54861384648549043755250876416) }, { argument := 193829076745080621700868997120, coefficient := (-193829076745080621700868997120) }, { argument := 54861263286575357889978826752, coefficient := (-54861263286575357889978826752) }, { argument := 77167412451416360554984374272, coefficient := (-77167412451416360554984374272) }, { argument := 77183641334391660306707251200, coefficient := (-77183641334391660306707251200) }, { argument := 15523657532242399219440156672, coefficient := (-15523657532242399219440156672) }, { argument := 54861263286575357889978826752, coefficient := (-54861263286575357889978826752) }, { argument := 15523265203789837121158643712, coefficient := (-15523265203789837121158643712) }, { argument := 77167431389082067045497962496, coefficient := (-77167431389082067045497962496) }, { argument := 77183660175657816773355372544, coefficient := (-77183660175657816773355372544) }, { argument := 2052431590137849156741365760, coefficient := (-2052431590137849156741365760) }, { argument := 2052773539452044993621917696, coefficient := (-2052773539452044993621917696) }, { argument := 1109194275199700726309615304704, coefficient := 1109194275199700726309615304704 }, { argument := 316879508489080571204066082816, coefficient := 316879508489080571204066082816 }, { argument := 316945791625034129544285519872, coefficient := 316945791625034129544285519872 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 171818128765546815969174749184, coefficient := 171818128765546815969174749184 }, { argument := 607103449360410046692197400576, coefficient := 607103449360410046692197400576 }, { argument := 171816372045215188461155254272, coefficient := 171816372045215188461155254272 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 8210599153839103086535114752, coefficient := 8210599153839103086535114752 }, { argument := 308702107571616041723383250944, coefficient := 308702107571616041723383250944 }, { argument := 308702183129479767637706670080, coefficient := 308702183129479767637706670080 }, { argument := 8210410259179788300726566912, coefficient := 8210410259179788300726566912 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk7
