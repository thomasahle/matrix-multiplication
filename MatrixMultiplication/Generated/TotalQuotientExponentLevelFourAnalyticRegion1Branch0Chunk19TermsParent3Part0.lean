import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 19, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk19

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    395, 567, 569, 617, 2001, 2003,
    2459, 3823, 4457, 13947, 17763, 36925
  ]
def positiveCoefficients : Array ℕ := #[
    950737950171172051122527404032, 440350127254281188344917275967488, 440587811741823981357697907818496, 80812725764549624345414829342720, 12597277839768029677373488103424, 12755734164796558352560576004096,
    80495813114492566995040653541376, 467446158834159591801909306982400, 232693113304394359512238582136832, 2209990365172889432834314950672384, 232930797791937152525019213987840, 613067521535377444298843087699968
  ]
def positiveScales : Array ℕ := #[
    8, 9, 9, 9, 10, 10,
    11, 11, 12, 13, 14, 15
  ]
def negativeArguments : Array ℕ := #[
    3, 5, 7, 11, 23, 31,
    45, 63, 103, 159, 161, 211,
    243, 457, 467, 491, 735, 1585,
    1603, 2937, 3401, 3413, 3869, 330829521043
  ]
def negativeCoefficients : Array ℕ := #[
    1426106925256758076683791106048, 792281625142643375935439503360, 554597137599850363154807652352, 3486039150627630854115933814784, 7288990951312319058606043430912, 4912146075884388930799724920832,
    7130534626283790383418955530240, 4991374238398653268393268871168, 65284005911753814177080215076864, 12597277839768029677373488103424, 12755734164796558352560576004096, 66868569162039100928951094083584,
    38504886981932468070462359863296, 36207270269018802280249585303552, 36999551894161445656185024806912, 38901027794503789758430079614976, 232930797791937152525019213987840, 125576637585108975085767161282560,
    127002744510365733162450952388608, 232693113304394359512238582136832, 269454980711013012155642975092736, 270405718661184184206765502496768, 141501498250476106942069495300096, 1104995182586444716417157475336192
  ]
def negativeScales : Array ℕ := #[
    1, 2, 2, 3, 4, 4,
    5, 5, 6, 7, 7, 7,
    7, 8, 8, 8, 9, 10,
    10, 11, 11, 11, 11, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8625708843063759, 9147204924942228, 9152284842306581, 9269126679149417, 10966505451058055, 10967946704944591,
    11263856019596082, 11900489484562305, 12121857245612654, 13767667211219704, 14116587639143779, 15172310300539513
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2321928094887363, 2807354922807594, 3459431618637364, 4523561956057598, 4954196321574415,
    5491853096329881, 5977279939904027, 6686500527235738, 7312882955284356, 7330916878114618, 7721099188825173,
    7924812510375204, 8836050356382083, 8867278742109862, 8939579223047345, 9521600439724276, 10630267125039561,
    10646558710174063, 11520127550325376, 11731743290857941, 11736824699267021, 11917745019426307, 38267297020598053
  ]

abbrev PositiveTerm := Fin 12
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
noncomputable def positiveFloor : ℝ := 739101244779 / 1000000000000
noncomputable def negativeCeiling : ℝ := 181986576959 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-1426106925256758076683791106048) }, { argument := 5, coefficient := (-792281625142643375935439503360) }, { argument := 7, coefficient := (-554597137599850363154807652352) }, { argument := 11, coefficient := (-3486039150627630854115933814784) }, { argument := 23, coefficient := (-7288990951312319058606043430912) }, { argument := 31, coefficient := (-4912146075884388930799724920832) }, { argument := 45, coefficient := (-7130534626283790383418955530240) }, { argument := 63, coefficient := (-4991374238398653268393268871168) }, { argument := 103, coefficient := (-65284005911753814177080215076864) }, { argument := 159, coefficient := (-12597277839768029677373488103424) }, { argument := 161, coefficient := (-12755734164796558352560576004096) }, { argument := 211, coefficient := (-66868569162039100928951094083584) }, { argument := 243, coefficient := (-38504886981932468070462359863296) }, { argument := 395, coefficient := 950737950171172051122527404032 }, { argument := 457, coefficient := (-36207270269018802280249585303552) }, { argument := 467, coefficient := (-36999551894161445656185024806912) }, { argument := 491, coefficient := (-38901027794503789758430079614976) }, { argument := 567, coefficient := 440350127254281188344917275967488 }, { argument := 569, coefficient := 440587811741823981357697907818496 }, { argument := 617, coefficient := 80812725764549624345414829342720 }, { argument := 735, coefficient := (-232930797791937152525019213987840) }, { argument := 1585, coefficient := (-125576637585108975085767161282560) }, { argument := 1603, coefficient := (-127002744510365733162450952388608) }, { argument := 2001, coefficient := 12597277839768029677373488103424 }, { argument := 2003, coefficient := 12755734164796558352560576004096 }, { argument := 2459, coefficient := 80495813114492566995040653541376 }, { argument := 2937, coefficient := (-232693113304394359512238582136832) }, { argument := 3401, coefficient := (-269454980711013012155642975092736) }, { argument := 3413, coefficient := (-270405718661184184206765502496768) }, { argument := 3823, coefficient := 467446158834159591801909306982400 }, { argument := 3869, coefficient := (-141501498250476106942069495300096) }, { argument := 4457, coefficient := 232693113304394359512238582136832 }, { argument := 13947, coefficient := 2209990365172889432834314950672384 }, { argument := 17763, coefficient := 232930797791937152525019213987840 }, { argument := 36925, coefficient := 613067521535377444298843087699968 }, { argument := 330829521043, coefficient := (-1104995182586444716417157475336192) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk19
