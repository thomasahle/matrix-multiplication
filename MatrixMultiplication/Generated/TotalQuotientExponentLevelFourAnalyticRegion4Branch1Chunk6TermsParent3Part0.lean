import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 6, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk6

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
def constantNumerator : ℤ := 849437824505293621371785445376
def positiveArguments : Array ℕ := #[
    5, 1, 75497513, 75497431, 7052497, 23648327,
    880989, 221977, 8166631, 510415, 13873
  ]
def positiveCoefficients : Array ℕ := #[
    1584563250285286751870879006720, 158456325028528675187087900672, 713053849862430633652803076096, 713053075394327443030988029952, 266435803626709794085243191296, 893408534405930147099743092736,
    266262587224118135498804822016, 2096513489535910471201193984, 77131649024728427122342756352, 77131734027325118775956602880, 2096428486939218817587347456
  ]
def positiveScales : Array ℕ := #[
    2, 0, 26, 26, 22, 24,
    19, 17, 22, 18, 13
  ]
def negativeArguments : Array ℕ := #[
    221977, 8166631, 510415, 13873, 14790165823617, 49594163965121,
    7390275201375, 14790165823617, 14790150553471, 221977, 14790150553471, 49594108564287,
    7390267545249, 49594163965121, 49594108564287, 8166631, 7390275201375, 7390267545249,
    510415, 13873, 1, 9, 9, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1048256744767955235600596992, 38565824512364213561171378176, 38565867013662559387978301440, 1048214243469609408793673728, 66608985291989366267845804032, 223352258353070215982288470016,
    66565681286155734576267264000, 66608985291989366267845804032, 66608916521365530774775791616, 1048256744767955235600596992, 66608916521365530774775791616, 223352008849894857567583076352,
    66565612325903333173135147008, 223352258353070215982288470016, 223352008849894857567583076352, 38565824512364213561171378176, 66565681286155734576267264000, 66565612325903333173135147008,
    38565867013662559387978301440, 1048214243469609408793673728, 158456325028528675187087900672, 1426106925256758076683791106048, 1426106925256758076683791106048, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    17, 22, 18, 13, 43, 45,
    42, 43, 43, 17, 43, 45,
    42, 45, 45, 22, 42, 42,
    18, 13, 0, 3, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 0, 26169925784918620, 26169924217965578, 22749702716425871, 24495234787980106,
    19748764480238023, 17760050674846444, 22961309611177009, 18961311201091877, 13759992179963677
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    17760050675143472, 22961309624556415, 18961311214471637, 13759992180260331, 43749703461420513, 45495235593786161,
    42748765227767279, 43749703461420513, 43749701971905409, 17760050675143472, 43749701971905409, 45495233982174094,
    42748763733173304, 45495235593786161, 45495233982174094, 22961309624556415, 42748765227767279, 42748763733173304,
    18961311214471637, 13759992180260331, 0, 3169925001442313, 3169925001442313, 0
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
noncomputable def positiveFloor : ℝ := 466459877 / 500000000000
noncomputable def negativeCeiling : ℝ := 114390703 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1048256744767955235600596992, coefficient := (-1048256744767955235600596992) }, { argument := 38565824512364213561171378176, coefficient := (-38565824512364213561171378176) }, { argument := 38565867013662559387978301440, coefficient := (-38565867013662559387978301440) }, { argument := 1048214243469609408793673728, coefficient := (-1048214243469609408793673728) }, { argument := 66608985291989366267845804032, coefficient := (-66608985291989366267845804032) }, { argument := 223352258353070215982288470016, coefficient := (-223352258353070215982288470016) }, { argument := 66565681286155734576267264000, coefficient := (-66565681286155734576267264000) }, { argument := 66608985291989366267845804032, coefficient := (-66608985291989366267845804032) }, { argument := 66608916521365530774775791616, coefficient := (-66608916521365530774775791616) }, { argument := 1048256744767955235600596992, coefficient := (-1048256744767955235600596992) }, { argument := 66608916521365530774775791616, coefficient := (-66608916521365530774775791616) }, { argument := 223352008849894857567583076352, coefficient := (-223352008849894857567583076352) }, { argument := 66565612325903333173135147008, coefficient := (-66565612325903333173135147008) }, { argument := 223352258353070215982288470016, coefficient := (-223352258353070215982288470016) }, { argument := 223352008849894857567583076352, coefficient := (-223352008849894857567583076352) }, { argument := 38565824512364213561171378176, coefficient := (-38565824512364213561171378176) }, { argument := 66565681286155734576267264000, coefficient := (-66565681286155734576267264000) }, { argument := 66565612325903333173135147008, coefficient := (-66565612325903333173135147008) }, { argument := 38565867013662559387978301440, coefficient := (-38565867013662559387978301440) }, { argument := 1048214243469609408793673728, coefficient := (-1048214243469609408793673728) }, { argument := 1584563250285286751870879006720, coefficient := 1584563250285286751870879006720 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 713053849862430633652803076096, coefficient := 713053849862430633652803076096 }, { argument := 713053075394327443030988029952, coefficient := 713053075394327443030988029952 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 266435803626709794085243191296, coefficient := 266435803626709794085243191296 }, { argument := 893408534405930147099743092736, coefficient := 893408534405930147099743092736 }, { argument := 266262587224118135498804822016, coefficient := 266262587224118135498804822016 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 2096513489535910471201193984, coefficient := 2096513489535910471201193984 }, { argument := 77131649024728427122342756352, coefficient := 77131649024728427122342756352 }, { argument := 77131734027325118775956602880, coefficient := 77131734027325118775956602880 }, { argument := 2096428486939218817587347456, coefficient := 2096428486939218817587347456 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk6
