import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 18, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3050855376061500997810827472928768)
def positiveArguments : Array ℕ := #[
    195, 6175, 10543, 195, 10543, 10543,
    3471, 195, 1, 1, 159426809, 570338883,
    39856689, 7478243, 276161565, 2209291979, 59826485, 1123983,
    179440731, 7162194609, 179440731, 4495419, 640809, 53885143,
    26942565, 320411
  ]
def positiveCoefficients : Array ℕ := #[
    7543697114395286050166538240, 119441870977925362460970188800, 203931278659152566222835417088, 7543697114395286050166538240, 203931278659152566222835417088, 203931278659152566222835417088,
    134277808636236091692964380672, 7543697114395286050166538240, 39614081257132168796771975168, 39614081257132168796771975168, 1505743638584921398763352752128, 5386698449913024171571345883136,
    1505743138014074214580960100352, 1130080131006545415417779716096, 41732355789210461222689497415680, 41732345570009392292777254977536, 1130090350207614345330022154240, 21231438586061089744902684672,
    3389539574944112459425045807104, 33822507765331263799276144164864, 3389539574944112459425045807104, 21229016012055377616908058624, 6052269887042428959486640128, 508930786455675765398549037056,
    508930663674147210787773480960, 6052392668570983570262196224
  ]
def positiveScales : Array ℕ := #[
    7, 12, 13, 7, 13, 13,
    11, 7, 0, 0, 27, 29,
    25, 22, 28, 31, 25, 20,
    27, 32, 27, 22, 19, 25,
    24, 18
  ]
def negativeArguments : Array ℕ := #[
    13, 1, 53, 541, 513, 13
  ]
def negativeCoefficients : Array ℕ := #[
    1029966112685436388716071354368, 79228162514264337593543950336, 8398185226512019784915658735616, 85724871840434013276214554263552, 40644047369817605185488046522368, 1029966112685436388716071354368
  ]
def negativeScales : Array ℕ := #[
    3, 0, 5, 9, 9, 3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7607330313749179, 12592223421359118, 13363997822358364, 7607330313749179, 13363997822358364, 13363997822358364,
    11761135649810892, 7607330313749179, 0, 0, 27248319010505167, 29087244151264772,
    25248318530894176, 22834267920515838, 28040937304464722, 31040936951185060, 25834280966603117, 20100188784597276,
    27418932161853323, 32737754573642815, 27418932161853323, 22100024159157388, 19289534884611941, 25683384217801936,
    24683383869746113, 18289564152061827
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3700439718214233, 0, 5727920454700926, 9079484783826816, 9002815015607055, 3700439718214233
  ]

abbrev PositiveTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 24601900601 / 500000000000
noncomputable def negativeCeiling : ℝ := 2888835457 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7543697114395286050166538240, coefficient := 7543697114395286050166538240 }, { argument := 119441870977925362460970188800, coefficient := 119441870977925362460970188800 }, { argument := 203931278659152566222835417088, coefficient := 203931278659152566222835417088 }, { argument := 7543697114395286050166538240, coefficient := 7543697114395286050166538240 }, { argument := 203931278659152566222835417088, coefficient := 203931278659152566222835417088 }, { argument := 203931278659152566222835417088, coefficient := 203931278659152566222835417088 }, { argument := 134277808636236091692964380672, coefficient := 134277808636236091692964380672 }, { argument := 7543697114395286050166538240, coefficient := 7543697114395286050166538240 }, { argument := 1029966112685436388716071354368, coefficient := (-1029966112685436388716071354368) }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 1505743638584921398763352752128, coefficient := 1505743638584921398763352752128 }, { argument := 5386698449913024171571345883136, coefficient := 5386698449913024171571345883136 }, { argument := 1505743138014074214580960100352, coefficient := 1505743138014074214580960100352 }, { argument := 8398185226512019784915658735616, coefficient := (-8398185226512019784915658735616) }, { argument := 1130080131006545415417779716096, coefficient := 1130080131006545415417779716096 }, { argument := 41732355789210461222689497415680, coefficient := 41732355789210461222689497415680 }, { argument := 41732345570009392292777254977536, coefficient := 41732345570009392292777254977536 }, { argument := 1130090350207614345330022154240, coefficient := 1130090350207614345330022154240 }, { argument := 85724871840434013276214554263552, coefficient := (-85724871840434013276214554263552) }, { argument := 21231438586061089744902684672, coefficient := 21231438586061089744902684672 }, { argument := 3389539574944112459425045807104, coefficient := 3389539574944112459425045807104 }, { argument := 33822507765331263799276144164864, coefficient := 33822507765331263799276144164864 }, { argument := 3389539574944112459425045807104, coefficient := 3389539574944112459425045807104 }, { argument := 21229016012055377616908058624, coefficient := 21229016012055377616908058624 }, { argument := 40644047369817605185488046522368, coefficient := (-40644047369817605185488046522368) }, { argument := 6052269887042428959486640128, coefficient := 6052269887042428959486640128 }, { argument := 508930786455675765398549037056, coefficient := 508930786455675765398549037056 }, { argument := 508930663674147210787773480960, coefficient := 508930663674147210787773480960 }, { argument := 6052392668570983570262196224, coefficient := 6052392668570983570262196224 }, { argument := 1029966112685436388716071354368, coefficient := (-1029966112685436388716071354368) }] }

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

end TermShard8


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18
