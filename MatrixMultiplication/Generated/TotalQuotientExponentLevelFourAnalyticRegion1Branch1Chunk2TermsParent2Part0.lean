import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 2, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2

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
def constantNumerator : ℤ := (-29603991407996949582848599261184)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    12477, 511185, 60098403, 240267363, 119986391, 240267363,
    10525695, 2181757085, 8701988765, 4321781545, 8701988765, 37,
    37, 37, 37, 3, 3, 3,
    3, 643, 643, 643, 643, 1163,
    1163, 1163, 1163, 511185, 2181757085, 8701988765,
    4321781545, 8701988765, 643, 643, 643, 643,
    19, 19, 19, 19, 60098403, 2181757085,
    37, 3, 643, 1163, 2181757085, 643,
    19, 19, 37, 37, 1163, 37,
    60098403, 3, 19, 19, 19, 19,
    37, 37, 37, 37
  ]
def negativeCoefficients : Array ℕ := #[
    117841933213529126662569984, 19312023284365756708505518080, 277154964844914584491917312, 277009409657879474668044288, 276669780888130885079007232, 277009409657879474668044288,
    198824757107634441110295674880, 10061578644499394117595299840, 10032709980015678127226224640, 9965349762887007483031715840, 10032709980015678127226224640, 178921021302965117856514048,
    178921021302965117856514048, 178921021302965117856514048, 178921021302965117856514048, 232113757366008801543585792, 232113757366008801543585792, 232113757366008801543585792,
    232113757366008801543585792, 3109357208048826237344284672, 3109357208048826237344284672, 3109357208048826237344284672, 3109357208048826237344284672, 5623922912847254920733130752,
    5623922912847254920733130752, 5623922912847254920733130752, 5623922912847254920733130752, 19312023284365756708505518080, 10061578644499394117595299840, 10032709980015678127226224640,
    9965349762887007483031715840, 10032709980015678127226224640, 3109357208048826237344284672, 3109357208048826237344284672, 3109357208048826237344284672, 3109357208048826237344284672,
    183756724581423634555338752, 183756724581423634555338752, 183756724581423634555338752, 183756724581423634555338752, 277154964844914584491917312, 10061578644499394117595299840,
    178921021302965117856514048, 232113757366008801543585792, 3109357208048826237344284672, 5623922912847254920733130752, 10061578644499394117595299840, 3109357208048826237344284672,
    183756724581423634555338752, 183756724581423634555338752, 178921021302965117856514048, 178921021302965117856514048, 5623922912847254920733130752, 178921021302965117856514048,
    277154964844914584491917312, 232113757366008801543585792, 183756724581423634555338752, 183756724581423634555338752, 183756724581423634555338752, 183756724581423634555338752,
    178921021302965117856514048, 178921021302965117856514048, 178921021302965117856514048, 178921021302965117856514048
  ]
def negativeScales : Array ℕ := #[
    13, 18, 25, 27, 26, 27,
    23, 31, 33, 32, 33, 5,
    5, 5, 5, 1, 1, 1,
    1, 9, 9, 9, 9, 10,
    10, 10, 10, 18, 31, 33,
    32, 33, 9, 9, 9, 9,
    4, 4, 4, 4, 25, 31,
    5, 1, 9, 10, 31, 9,
    4, 4, 5, 5, 10, 5,
    25, 1, 4, 4, 4, 4,
    5, 5, 5, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13606983470374365, 18963485990566218, 25840823320251007, 27840065452127928, 26838295543397300, 27840065452127928,
    23327412160206296, 31022843336136020, 33018698008225167, 32008979003483453, 33018698008225167, 5209453365628950,
    5209453365628950, 5209453365628950, 5209453365628950, 1584962500724866, 1584962500724866, 1584962500724866,
    1584962500724866, 9328674927327948, 9328674927327948, 9328674927327948, 9328674927327948, 10183635381473219,
    10183635381473219, 10183635381473219, 10183635381473219, 18963485990566218, 31022843336136020, 33018698008225167,
    32008979003483453, 33018698008225167, 9328674927327948, 9328674927327948, 9328674927327948, 9328674927327948,
    4247927513443586, 4247927513443586, 4247927513443586, 4247927513443586, 25840823320251007, 31022843336136020,
    5209453365628950, 1584962500724866, 9328674927327948, 10183635381473219, 31022843336136020, 9328674927327948,
    4247927513443586, 4247927513443586, 5209453365628950, 5209453365628950, 10183635381473219, 5209453365628950,
    25840823320251007, 1584962500724866, 4247927513443586, 4247927513443586, 4247927513443586, 4247927513443586,
    5209453365628950, 5209453365628950, 5209453365628950, 5209453365628950
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 27934797 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 117841933213529126662569984, coefficient := (-117841933213529126662569984) }, { argument := 19312023284365756708505518080, coefficient := (-19312023284365756708505518080) }, { argument := 277154964844914584491917312, coefficient := (-277154964844914584491917312) }, { argument := 277009409657879474668044288, coefficient := (-277009409657879474668044288) }, { argument := 276669780888130885079007232, coefficient := (-276669780888130885079007232) }, { argument := 277009409657879474668044288, coefficient := (-277009409657879474668044288) }, { argument := 198824757107634441110295674880, coefficient := (-198824757107634441110295674880) }, { argument := 10061578644499394117595299840, coefficient := (-10061578644499394117595299840) }, { argument := 10032709980015678127226224640, coefficient := (-10032709980015678127226224640) }, { argument := 9965349762887007483031715840, coefficient := (-9965349762887007483031715840) }, { argument := 10032709980015678127226224640, coefficient := (-10032709980015678127226224640) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 232113757366008801543585792, coefficient := (-232113757366008801543585792) }, { argument := 232113757366008801543585792, coefficient := (-232113757366008801543585792) }, { argument := 232113757366008801543585792, coefficient := (-232113757366008801543585792) }, { argument := 232113757366008801543585792, coefficient := (-232113757366008801543585792) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 19312023284365756708505518080, coefficient := (-19312023284365756708505518080) }, { argument := 10061578644499394117595299840, coefficient := (-10061578644499394117595299840) }, { argument := 10032709980015678127226224640, coefficient := (-10032709980015678127226224640) }, { argument := 9965349762887007483031715840, coefficient := (-9965349762887007483031715840) }, { argument := 10032709980015678127226224640, coefficient := (-10032709980015678127226224640) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 277154964844914584491917312, coefficient := (-277154964844914584491917312) }, { argument := 10061578644499394117595299840, coefficient := (-10061578644499394117595299840) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 232113757366008801543585792, coefficient := (-232113757366008801543585792) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 10061578644499394117595299840, coefficient := (-10061578644499394117595299840) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 277154964844914584491917312, coefficient := (-277154964844914584491917312) }, { argument := 232113757366008801543585792, coefficient := (-232113757366008801543585792) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }] }

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

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-9998655708548154724952848728064)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    37, 37, 37, 37, 1163, 1163,
    1163, 1163, 37, 37, 37, 37,
    240267363, 8701988765, 37, 3, 643, 1163,
    8701988765, 643, 19, 19, 37, 37,
    1163, 37, 240267363, 3, 12477, 60098403,
    240267363, 119986391, 240267363, 3, 3, 3,
    3, 119986391, 4321781545, 37, 3, 643,
    1163, 4321781545, 643, 19, 19, 37,
    37, 1163, 37, 119986391, 3, 240267363,
    8701988765, 37, 3, 643, 1163, 8701988765,
    643, 19, 19, 37
  ]
def negativeCoefficients : Array ℕ := #[
    178921021302965117856514048, 178921021302965117856514048, 178921021302965117856514048, 178921021302965117856514048, 5623922912847254920733130752, 5623922912847254920733130752,
    5623922912847254920733130752, 5623922912847254920733130752, 178921021302965117856514048, 178921021302965117856514048, 178921021302965117856514048, 178921021302965117856514048,
    277009409657879474668044288, 10032709980015678127226224640, 178921021302965117856514048, 232113757366008801543585792, 3109357208048826237344284672, 5623922912847254920733130752,
    10032709980015678127226224640, 3109357208048826237344284672, 183756724581423634555338752, 183756724581423634555338752, 178921021302965117856514048, 178921021302965117856514048,
    5623922912847254920733130752, 178921021302965117856514048, 277009409657879474668044288, 232113757366008801543585792, 117841933213529126662569984, 277154964844914584491917312,
    277009409657879474668044288, 276669780888130885079007232, 277009409657879474668044288, 232113757366008801543585792, 232113757366008801543585792, 232113757366008801543585792,
    232113757366008801543585792, 276669780888130885079007232, 9965349762887007483031715840, 178921021302965117856514048, 232113757366008801543585792, 3109357208048826237344284672,
    5623922912847254920733130752, 9965349762887007483031715840, 3109357208048826237344284672, 183756724581423634555338752, 183756724581423634555338752, 178921021302965117856514048,
    178921021302965117856514048, 5623922912847254920733130752, 178921021302965117856514048, 276669780888130885079007232, 232113757366008801543585792, 277009409657879474668044288,
    10032709980015678127226224640, 178921021302965117856514048, 232113757366008801543585792, 3109357208048826237344284672, 5623922912847254920733130752, 10032709980015678127226224640,
    3109357208048826237344284672, 183756724581423634555338752, 183756724581423634555338752, 178921021302965117856514048
  ]
def negativeScales : Array ℕ := #[
    5, 5, 5, 5, 10, 10,
    10, 10, 5, 5, 5, 5,
    27, 33, 5, 1, 9, 10,
    33, 9, 4, 4, 5, 5,
    10, 5, 27, 1, 13, 25,
    27, 26, 27, 1, 1, 1,
    1, 26, 32, 5, 1, 9,
    10, 32, 9, 4, 4, 5,
    5, 10, 5, 26, 1, 27,
    33, 5, 1, 9, 10, 33,
    9, 4, 4, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    5209453365628950, 5209453365628950, 5209453365628950, 5209453365628950, 10183635381473219, 10183635381473219,
    10183635381473219, 10183635381473219, 5209453365628950, 5209453365628950, 5209453365628950, 5209453365628950,
    27840065452127928, 33018698008225167, 5209453365628950, 1584962500724866, 9328674927327948, 10183635381473219,
    33018698008225167, 9328674927327948, 4247927513443586, 4247927513443586, 5209453365628950, 5209453365628950,
    10183635381473219, 5209453365628950, 27840065452127928, 1584962500724866, 13606983470374365, 25840823320251007,
    27840065452127928, 26838295543397300, 27840065452127928, 1584962500724866, 1584962500724866, 1584962500724866,
    1584962500724866, 26838295543397300, 32008979003483453, 5209453365628950, 1584962500724866, 9328674927327948,
    10183635381473219, 32008979003483453, 9328674927327948, 4247927513443586, 4247927513443586, 5209453365628950,
    5209453365628950, 10183635381473219, 5209453365628950, 26838295543397300, 1584962500724866, 27840065452127928,
    33018698008225167, 5209453365628950, 1584962500724866, 9328674927327948, 10183635381473219, 33018698008225167,
    9328674927327948, 4247927513443586, 4247927513443586, 5209453365628950
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 33064457 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 277009409657879474668044288, coefficient := (-277009409657879474668044288) }, { argument := 10032709980015678127226224640, coefficient := (-10032709980015678127226224640) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 232113757366008801543585792, coefficient := (-232113757366008801543585792) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 10032709980015678127226224640, coefficient := (-10032709980015678127226224640) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 277009409657879474668044288, coefficient := (-277009409657879474668044288) }, { argument := 232113757366008801543585792, coefficient := (-232113757366008801543585792) }, { argument := 117841933213529126662569984, coefficient := (-117841933213529126662569984) }, { argument := 277154964844914584491917312, coefficient := (-277154964844914584491917312) }, { argument := 277009409657879474668044288, coefficient := (-277009409657879474668044288) }, { argument := 276669780888130885079007232, coefficient := (-276669780888130885079007232) }, { argument := 277009409657879474668044288, coefficient := (-277009409657879474668044288) }, { argument := 232113757366008801543585792, coefficient := (-232113757366008801543585792) }, { argument := 232113757366008801543585792, coefficient := (-232113757366008801543585792) }, { argument := 232113757366008801543585792, coefficient := (-232113757366008801543585792) }, { argument := 232113757366008801543585792, coefficient := (-232113757366008801543585792) }, { argument := 276669780888130885079007232, coefficient := (-276669780888130885079007232) }, { argument := 9965349762887007483031715840, coefficient := (-9965349762887007483031715840) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 232113757366008801543585792, coefficient := (-232113757366008801543585792) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 9965349762887007483031715840, coefficient := (-9965349762887007483031715840) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 276669780888130885079007232, coefficient := (-276669780888130885079007232) }, { argument := 232113757366008801543585792, coefficient := (-232113757366008801543585792) }, { argument := 277009409657879474668044288, coefficient := (-277009409657879474668044288) }, { argument := 10032709980015678127226224640, coefficient := (-10032709980015678127226224640) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 232113757366008801543585792, coefficient := (-232113757366008801543585792) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 10032709980015678127226224640, coefficient := (-10032709980015678127226224640) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }] }

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

end TermShard1


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2
