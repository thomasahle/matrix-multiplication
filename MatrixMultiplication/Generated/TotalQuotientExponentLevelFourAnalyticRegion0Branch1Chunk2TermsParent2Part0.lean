import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 2, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk2

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
def constantNumerator : ℤ := 475313118934826643397676105728
def positiveArguments : Array ℕ := #[
    9, 8386525, 8390691, 3952907, 26128455, 7908771,
    228457, 16316487, 16320261, 230385
  ]
def positiveCoefficients : Array ℕ := #[
    713053462628379038341895553024, 158416978270993405303167385600, 158495671786063945071008415744, 149336604213606405221883314176, 493552560564671183328085278720, 149392460364365787385470910464,
    4315430718307802146341388288, 154104862653956577647766011904, 154140507076169277729838989312, 4351849608623692850229411840
  ]
def positiveScales : Array ℕ := #[
    3, 22, 23, 21, 24, 22,
    17, 23, 23, 17
  ]
def negativeArguments : Array ℕ := #[
    1915954959313, 136838631847959, 136870287692205, 1932126685005, 50015160460383, 165225861397603,
    25017038204831, 1915954959313, 1916917476399, 1916917476399, 136906594912233, 136938256281171,
    1933092223155, 165225861397603, 546212365451815, 82643619856571, 136838631847959, 136906594912233,
    25017038204831, 82643619856571, 12513250650067, 136870287692205, 136938256281171, 1932126685005,
    1933092223155, 1, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1078586755102585078107078656, 38516650712522289928527151104, 38525561040544188932271636480, 1087690627327638712677826560, 14078016125766027747941941248, 46506945488888380639902957568,
    14083340492148794223096758272, 1078586755102585078107078656, 1079128604051315995063615488, 1079128604051315995063615488, 38535780614455998895355854848, 38544692497540449932647858176,
    1088234176984207712436879360, 46506945488888380639902957568, 153745112844621951063965040640, 46524221948825259960174641152, 38516650712522289928527151104, 38535780614455998895355854848,
    14083340492148794223096758272, 46524221948825259960174641152, 14088667741208839509464055808, 38525561040544188932271636480, 38544692497540449932647858176, 1087690627327638712677826560,
    1088234176984207712436879360, 316912650057057350374175801344, 792281625142643375935439503360, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    40, 46, 46, 40, 45, 47,
    44, 40, 40, 40, 46, 46,
    40, 47, 48, 46, 46, 46,
    44, 46, 43, 46, 46, 40,
    40, 0, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 22999641714201809, 23000358195391310, 21914482582261356, 24639118483482427, 22915022090475996,
    17801563122284677, 23959827136617658, 23960160793086100, 17813687262648284
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40801200785593477, 46959468925453853, 46959802635726314, 40813326830891572, 45507430700539387, 47231432845628392,
    44507976230868208, 40801200785593477, 40801925369413087, 40801925369413087, 46960185284961482, 46960518887798345,
    40814047606188711, 47231432845628392, 48956455315028661, 46231968680317949, 46959468925453853, 46960185284961482,
    44507976230868208, 46231968680317949, 43508521850181431, 46959802635726314, 46960518887798345, 40813326830891572,
    40814047606188711, 0, 2321928094887363, 0
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
noncomputable def positiveFloor : ℝ := 10817071 / 25000000000
noncomputable def negativeCeiling : ℝ := 426083043 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1078586755102585078107078656, coefficient := (-1078586755102585078107078656) }, { argument := 38516650712522289928527151104, coefficient := (-38516650712522289928527151104) }, { argument := 38525561040544188932271636480, coefficient := (-38525561040544188932271636480) }, { argument := 1087690627327638712677826560, coefficient := (-1087690627327638712677826560) }, { argument := 14078016125766027747941941248, coefficient := (-14078016125766027747941941248) }, { argument := 46506945488888380639902957568, coefficient := (-46506945488888380639902957568) }, { argument := 14083340492148794223096758272, coefficient := (-14083340492148794223096758272) }, { argument := 1078586755102585078107078656, coefficient := (-1078586755102585078107078656) }, { argument := 1079128604051315995063615488, coefficient := (-1079128604051315995063615488) }, { argument := 1079128604051315995063615488, coefficient := (-1079128604051315995063615488) }, { argument := 38535780614455998895355854848, coefficient := (-38535780614455998895355854848) }, { argument := 38544692497540449932647858176, coefficient := (-38544692497540449932647858176) }, { argument := 1088234176984207712436879360, coefficient := (-1088234176984207712436879360) }, { argument := 46506945488888380639902957568, coefficient := (-46506945488888380639902957568) }, { argument := 153745112844621951063965040640, coefficient := (-153745112844621951063965040640) }, { argument := 46524221948825259960174641152, coefficient := (-46524221948825259960174641152) }, { argument := 38516650712522289928527151104, coefficient := (-38516650712522289928527151104) }, { argument := 38535780614455998895355854848, coefficient := (-38535780614455998895355854848) }, { argument := 14083340492148794223096758272, coefficient := (-14083340492148794223096758272) }, { argument := 46524221948825259960174641152, coefficient := (-46524221948825259960174641152) }, { argument := 14088667741208839509464055808, coefficient := (-14088667741208839509464055808) }, { argument := 38525561040544188932271636480, coefficient := (-38525561040544188932271636480) }, { argument := 38544692497540449932647858176, coefficient := (-38544692497540449932647858176) }, { argument := 1087690627327638712677826560, coefficient := (-1087690627327638712677826560) }, { argument := 1088234176984207712436879360, coefficient := (-1088234176984207712436879360) }, { argument := 713053462628379038341895553024, coefficient := 713053462628379038341895553024 }, { argument := 158416978270993405303167385600, coefficient := 158416978270993405303167385600 }, { argument := 158495671786063945071008415744, coefficient := 158495671786063945071008415744 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 149336604213606405221883314176, coefficient := 149336604213606405221883314176 }, { argument := 493552560564671183328085278720, coefficient := 493552560564671183328085278720 }, { argument := 149392460364365787385470910464, coefficient := 149392460364365787385470910464 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 4315430718307802146341388288, coefficient := 4315430718307802146341388288 }, { argument := 154104862653956577647766011904, coefficient := 154104862653956577647766011904 }, { argument := 154140507076169277729838989312, coefficient := 154140507076169277729838989312 }, { argument := 4351849608623692850229411840, coefficient := 4351849608623692850229411840 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk2
