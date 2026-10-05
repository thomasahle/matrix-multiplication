import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 5, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk5

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
def constantNumerator : ℤ := 614604588508061711499698110464
def positiveArguments : Array ℕ := #[
    17, 8386841, 8390375, 13593833, 48311895, 212371,
    466853, 4077587, 4077597, 466843
  ]
def positiveCoefficients : Array ℕ := #[
    1346878762742493739090247155712, 316845894684455505069434994688, 316979405429659195678916608000, 256780245331709271216930947072, 912585894687670393005334855680, 256740785237378412461525303296,
    8818603838508569907798474752, 308093762876559808287664504832, 308094518455197067430898696192, 8818414943849255121989926912
  ]
def positiveScales : Array ℕ := #[
    4, 22, 23, 23, 25, 17,
    18, 21, 21, 18
  ]
def negativeArguments : Array ℕ := #[
    1957719409619, 68396139188369, 68396306932329, 1957677484339, 20533184106637, 72969929664797,
    10265111241515, 1957719409619, 1958527401005, 1958527401005, 68424976527215, 68425144327575,
    1958485440205, 72969929664797, 259341327330509, 36479145948427, 68396139188369, 68424976527215,
    10265111241515, 36479145948427, 5131824518117, 68396306932329, 68425144327575, 1957677484339,
    1958485440205, 1, 9, 1
  ]
def negativeCoefficients : Array ℕ := #[
    2204196100914028955624800256, 77007206740579801780774240256, 77007395603488739193620791296, 2204148897245182604697665536, 23118310072845046000792895488, 82156837011907767822951907328,
    23114975581101821784720670720, 2204196100914028955624800256, 2205105818340255998274437120, 2205105818340255998274437120, 77039674697700102363058012160, 77039863624109794521828556800,
    2205058574679444956297297920, 82156837011907767822951907328, 291992376281862540632696815616, 82143734050064888047018704896, 77007206740579801780774240256, 77039674697700102363058012160,
    23114975581101821784720670720, 82143734050064888047018704896, 23111682987522496399023276032, 77007395603488739193620791296, 77039863624109794521828556800, 2204148897245182604697665536,
    2205058574679444956297297920, 633825300114114700748351602688, 1426106925256758076683791106048, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    40, 45, 45, 40, 44, 46,
    43, 40, 40, 40, 45, 45,
    40, 46, 47, 45, 45, 45,
    43, 45, 42, 45, 45, 40,
    40, 0, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4087462841250339, 22999696073192418, 23000303861342093, 23696448968760339, 25525875106786578, 17696227248989884,
    18832608828243331, 21959284227392843, 21959287765498231, 18832577925357621
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40832311145189042, 45958980136104435, 45958983674361628, 40832280249013437, 44223022598861497, 46052367296692680,
    43222814495342912, 40832311145189042, 40832906452516056, 40832906452516056, 45959588280463009, 45959591818418185,
    40832875542921424, 46052367296692680, 47881845456707735, 45052137186985944, 45958980136104435, 45959588280463009,
    43222814495342912, 45052137186985944, 42222608977203220, 45958983674361628, 45959591818418185, 40832280249013437,
    40832875542921424, 0, 3169925001442313, 0
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
noncomputable def positiveFloor : ℝ := 816945551 / 1000000000000
noncomputable def negativeCeiling : ℝ := 400271109 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2204196100914028955624800256, coefficient := (-2204196100914028955624800256) }, { argument := 77007206740579801780774240256, coefficient := (-77007206740579801780774240256) }, { argument := 77007395603488739193620791296, coefficient := (-77007395603488739193620791296) }, { argument := 2204148897245182604697665536, coefficient := (-2204148897245182604697665536) }, { argument := 23118310072845046000792895488, coefficient := (-23118310072845046000792895488) }, { argument := 82156837011907767822951907328, coefficient := (-82156837011907767822951907328) }, { argument := 23114975581101821784720670720, coefficient := (-23114975581101821784720670720) }, { argument := 2204196100914028955624800256, coefficient := (-2204196100914028955624800256) }, { argument := 2205105818340255998274437120, coefficient := (-2205105818340255998274437120) }, { argument := 2205105818340255998274437120, coefficient := (-2205105818340255998274437120) }, { argument := 77039674697700102363058012160, coefficient := (-77039674697700102363058012160) }, { argument := 77039863624109794521828556800, coefficient := (-77039863624109794521828556800) }, { argument := 2205058574679444956297297920, coefficient := (-2205058574679444956297297920) }, { argument := 82156837011907767822951907328, coefficient := (-82156837011907767822951907328) }, { argument := 291992376281862540632696815616, coefficient := (-291992376281862540632696815616) }, { argument := 82143734050064888047018704896, coefficient := (-82143734050064888047018704896) }, { argument := 77007206740579801780774240256, coefficient := (-77007206740579801780774240256) }, { argument := 77039674697700102363058012160, coefficient := (-77039674697700102363058012160) }, { argument := 23114975581101821784720670720, coefficient := (-23114975581101821784720670720) }, { argument := 82143734050064888047018704896, coefficient := (-82143734050064888047018704896) }, { argument := 23111682987522496399023276032, coefficient := (-23111682987522496399023276032) }, { argument := 77007395603488739193620791296, coefficient := (-77007395603488739193620791296) }, { argument := 77039863624109794521828556800, coefficient := (-77039863624109794521828556800) }, { argument := 2204148897245182604697665536, coefficient := (-2204148897245182604697665536) }, { argument := 2205058574679444956297297920, coefficient := (-2205058574679444956297297920) }, { argument := 1346878762742493739090247155712, coefficient := 1346878762742493739090247155712 }, { argument := 316845894684455505069434994688, coefficient := 316845894684455505069434994688 }, { argument := 316979405429659195678916608000, coefficient := 316979405429659195678916608000 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 256780245331709271216930947072, coefficient := 256780245331709271216930947072 }, { argument := 912585894687670393005334855680, coefficient := 912585894687670393005334855680 }, { argument := 256740785237378412461525303296, coefficient := 256740785237378412461525303296 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 8818603838508569907798474752, coefficient := 8818603838508569907798474752 }, { argument := 308093762876559808287664504832, coefficient := 308093762876559808287664504832 }, { argument := 308094518455197067430898696192, coefficient := 308094518455197067430898696192 }, { argument := 8818414943849255121989926912, coefficient := 8818414943849255121989926912 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk5
