import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 15, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk15

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    155, 257, 619, 2297, 2299, 5235,
    5269, 8945, 17273, 25163, 26775, 30617,
    30895, 35731, 138583
  ]
def positiveCoefficients : Array ℕ := #[
    860893213879996292291448564350976, 200684935648631567124446826201088, 859942475929825120240326036946944, 2931442013027780490961126162432, 3010670175542044828554670112768, 40564819207303340847894502572032,
    41357100832445984223829942075392, 519895202418602583288835402104832, 932436244630376989138418751504384, 999146357467387561392182757687296, 4242668102638855278134278540492800, 124071302497337952671489826226176,
    124705127797452067372238177828864, 519736746093574054613648314204160, 934100036043176540227883174461440
  ]
def positiveScales : Array ℕ := #[
    7, 8, 9, 11, 11, 12,
    12, 13, 14, 14, 14, 14,
    14, 15, 17
  ]
def negativeArguments : Array ℕ := #[
    3, 7, 9, 27, 57, 63,
    193, 197, 205, 261, 265, 377,
    533, 907, 1011, 1591, 3281, 4037,
    5769, 5779, 12611, 10044891037643
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 2218388550399401452619230609408, 1426106925256758076683791106048, 2139160387885137115025686659072, 72256084213009075885312082706432, 19965496953594613073573075484672,
    30582070730506034311107964829696, 124863584122480596047425265729536, 519736746093574054613648314204160, 41357100832445984223829942075392, 41990926132560098924578293678080, 29869017267877655272766069276672,
    42228610620102891937358925529088, 71859943400437754197344362954752, 320398689207684981228291735158784, 126052006560194561111328424984576, 519895202418602583288835402104832, 319844092070085130865136927506432,
    457067269544790963577155049488384, 457859551169933606953090488991744, 999146357467387561392182757687296, 2121334051319427639067139270246400
  ]
def negativeScales : Array ℕ := #[
    1, 2, 3, 4, 5, 5,
    7, 7, 7, 8, 8, 8,
    9, 9, 9, 10, 11, 11,
    12, 12, 13, 43
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7276124405274237, 8005624549193878, 9273795599214264, 11165535141377923, 11166790750718179, 12353973821818170,
    12363313464373477, 13126865766939270, 14076231053571284, 14619016313972320, 14708598954519486, 14902045306876591,
    14915085752637562, 15124888670602562, 17080390767121703
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2807354922807594, 3169925001442313, 4754887502413606, 5832890015409720, 5977279939904027,
    7592457037272664, 7622051819466668, 7679480099549776, 8027905996569885, 8049848549450562, 8558420713270378,
    9057991722759176, 9824958741594111, 9981567299496062, 10635718120345800, 11679919878563226, 11979067888371053,
    12494105548061276, 12496604154575845, 13622395059495557, 43191527147999679
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 22
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
noncomputable def positiveFloor : ℝ := 340429746477 / 200000000000
noncomputable def negativeCeiling : ℝ := 1671480243049 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-475368975085586025561263702016) }, { argument := 7, coefficient := (-2218388550399401452619230609408) }, { argument := 9, coefficient := (-1426106925256758076683791106048) }, { argument := 27, coefficient := (-2139160387885137115025686659072) }, { argument := 57, coefficient := (-72256084213009075885312082706432) }, { argument := 63, coefficient := (-19965496953594613073573075484672) }, { argument := 155, coefficient := 860893213879996292291448564350976 }, { argument := 193, coefficient := (-30582070730506034311107964829696) }, { argument := 197, coefficient := (-124863584122480596047425265729536) }, { argument := 205, coefficient := (-519736746093574054613648314204160) }, { argument := 257, coefficient := 200684935648631567124446826201088 }, { argument := 261, coefficient := (-41357100832445984223829942075392) }, { argument := 265, coefficient := (-41990926132560098924578293678080) }, { argument := 377, coefficient := (-29869017267877655272766069276672) }, { argument := 533, coefficient := (-42228610620102891937358925529088) }, { argument := 619, coefficient := 859942475929825120240326036946944 }, { argument := 907, coefficient := (-71859943400437754197344362954752) }, { argument := 1011, coefficient := (-320398689207684981228291735158784) }, { argument := 1591, coefficient := (-126052006560194561111328424984576) }, { argument := 2297, coefficient := 2931442013027780490961126162432 }, { argument := 2299, coefficient := 3010670175542044828554670112768 }, { argument := 3281, coefficient := (-519895202418602583288835402104832) }, { argument := 4037, coefficient := (-319844092070085130865136927506432) }, { argument := 5235, coefficient := 40564819207303340847894502572032 }, { argument := 5269, coefficient := 41357100832445984223829942075392 }, { argument := 5769, coefficient := (-457067269544790963577155049488384) }, { argument := 5779, coefficient := (-457859551169933606953090488991744) }, { argument := 8945, coefficient := 519895202418602583288835402104832 }, { argument := 12611, coefficient := (-999146357467387561392182757687296) }, { argument := 17273, coefficient := 932436244630376989138418751504384 }, { argument := 25163, coefficient := 999146357467387561392182757687296 }, { argument := 26775, coefficient := 4242668102638855278134278540492800 }, { argument := 30617, coefficient := 124071302497337952671489826226176 }, { argument := 30895, coefficient := 124705127797452067372238177828864 }, { argument := 35731, coefficient := 519736746093574054613648314204160 }, { argument := 138583, coefficient := 934100036043176540227883174461440 }, { argument := 10044891037643, coefficient := (-2121334051319427639067139270246400) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  rfl

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk15
