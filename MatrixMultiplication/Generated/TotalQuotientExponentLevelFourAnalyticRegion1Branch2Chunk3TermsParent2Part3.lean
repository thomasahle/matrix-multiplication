import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 3, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-254528712247686939352064803733504)
def positiveArguments : Array ℕ := #[
    1113, 93, 253413, 9183771, 73470195, 2027277,
    30771, 4009005, 42252095, 2004503, 30771, 2011227,
    133078949, 105, 93, 4353, 1185, 66539481,
    4353, 105, 105, 45, 105, 1185,
    45, 1005607, 93, 13637731, 3507, 74633117,
    5649, 175, 5649, 3773, 13666403, 3507,
    21, 535, 489, 535, 489
  ]
def positiveCoefficients : Array ℕ := #[
    86114203982789265372670328832, 3597763239173136423925579776, 19147344920375126440613511168, 693906117708003911901282041856, 693906372715793986862123581440, 19147089912585051479771971584,
    1162495512355054822965116928, 151455926733254576079466659840, 1596239018072192977483029544960, 151455964512186439036628369408, 1162495512355054822965116928, 18995501948484935868412329984,
    1256895136666237778083088171008, 4061990753905154027012751360, 3597763239173136423925579776, 168398530969039385519871492096, 45842467079786738304858193920, 1256895259447766332693863727104,
    168398530969039385519871492096, 4061990753905154027012751360, 4061990753905154027012751360, 3481706360490132023153786880, 4061990753905154027012751360, 45842467079786738304858193920,
    3481706360490132023153786880, 18995379166956381257636773888, 3597763239173136423925579776, 128804727553584658979647127552, 135670491180432144502225895424, 1409779720931554907929054281728,
    218535102560097286653286023168, 6769984589841923378354585600, 218535102560097286653286023168, 145960867756991868037324865536, 129075526937178335914781310976, 135670491180432144502225895424,
    6499185206248246443220402176, 331148960508839223535515729920, 302676339605275477212835872768, 331148960508839223535515729920, 302676339605275477212835872768
  ]
def positiveScales : Array ℕ := #[
    10, 6, 17, 23, 26, 20,
    14, 21, 25, 20, 14, 20,
    26, 6, 6, 12, 10, 25,
    12, 6, 6, 5, 6, 10,
    5, 19, 6, 23, 11, 26,
    12, 7, 12, 11, 23, 11,
    4, 9, 8, 9, 8
  ]
def negativeArguments : Array ℕ := #[
    3, 9, 3, 19, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 1426106925256758076683791106048, 1901475900342344102245054808064, 3010670175542044828554670112768, 2535301200456458802993406410752, 1267650600228229401496703205376
  ]
def negativeScales : Array ℕ := #[
    1, 3, 1, 4, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10120237877341959, 6539158811107971, 17951131009918936, 23130655237765980, 26130655767950680, 20951111795718665,
    14909283708557224, 21934812785635083, 25332519541018853, 20934813145498653, 14909283708557224, 20939644491448084,
    26987707135497080, 6714245517659862, 6539158811107971, 12087794304787900, 10210671343785621, 25987707276428718,
    12087794304787900, 6714245517659862, 6714245517659862, 5491853096329661, 6714245517659862, 10210671343785621,
    5491853096329661, 19939635166247113, 6539158811107971, 23701100297766400, 11776021715228447, 26153312604744052,
    12463779785335379, 7451211111832325, 12463779785335379, 11881496384617007, 23704130239489671, 11776021715228447,
    4392317422778759, 9063395081288509, 8933690654464738, 9063395081288509, 8933690654464738
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 3169925001442313, 1584962500724866, 4247927513443586, 0, 0
  ]

abbrev PositiveTerm := Fin 41
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 2650552537 / 1000000000000
noncomputable def negativeCeiling : ℝ := 126852403 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 86114203982789265372670328832, coefficient := 86114203982789265372670328832 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 19147344920375126440613511168, coefficient := 19147344920375126440613511168 }, { argument := 693906117708003911901282041856, coefficient := 693906117708003911901282041856 }, { argument := 693906372715793986862123581440, coefficient := 693906372715793986862123581440 }, { argument := 19147089912585051479771971584, coefficient := 19147089912585051479771971584 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 1162495512355054822965116928, coefficient := 1162495512355054822965116928 }, { argument := 151455926733254576079466659840, coefficient := 151455926733254576079466659840 }, { argument := 1596239018072192977483029544960, coefficient := 1596239018072192977483029544960 }, { argument := 151455964512186439036628369408, coefficient := 151455964512186439036628369408 }, { argument := 1162495512355054822965116928, coefficient := 1162495512355054822965116928 }, { argument := 1901475900342344102245054808064, coefficient := (-1901475900342344102245054808064) }, { argument := 18995501948484935868412329984, coefficient := 18995501948484935868412329984 }, { argument := 1256895136666237778083088171008, coefficient := 1256895136666237778083088171008 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 1256895259447766332693863727104, coefficient := 1256895259447766332693863727104 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 18995379166956381257636773888, coefficient := 18995379166956381257636773888 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 3010670175542044828554670112768, coefficient := (-3010670175542044828554670112768) }, { argument := 128804727553584658979647127552, coefficient := 128804727553584658979647127552 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 1409779720931554907929054281728, coefficient := 1409779720931554907929054281728 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 6769984589841923378354585600, coefficient := 6769984589841923378354585600 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 145960867756991868037324865536, coefficient := 145960867756991868037324865536 }, { argument := 129075526937178335914781310976, coefficient := 129075526937178335914781310976 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 6499185206248246443220402176, coefficient := 6499185206248246443220402176 }, { argument := 2535301200456458802993406410752, coefficient := (-2535301200456458802993406410752) }, { argument := 331148960508839223535515729920, coefficient := 331148960508839223535515729920 }, { argument := 302676339605275477212835872768, coefficient := 302676339605275477212835872768 }, { argument := 331148960508839223535515729920, coefficient := 331148960508839223535515729920 }, { argument := 302676339605275477212835872768, coefficient := 302676339605275477212835872768 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }] }

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

end TermShard6


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3
