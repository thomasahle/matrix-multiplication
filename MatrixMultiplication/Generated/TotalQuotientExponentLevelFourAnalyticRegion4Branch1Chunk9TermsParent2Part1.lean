import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 4, branch 1,
parent chunk 9, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk9

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 26130802143034765719077688180736
def positiveArguments : Array ℕ := #[
    3, 9, 67, 17, 5, 15,
    5, 133, 17, 15, 2423, 15,
    133, 133, 5, 15, 5, 17,
    17, 9, 652435, 766043, 12258279, 649279,
    18885, 1283667, 14134327, 1283687, 37765
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 696341272098026404630757376, 5183873914507529901140082688, 5261245166962866168321277952, 773712524553362671811952640, 4642275147320176030871715840,
    773712524553362671811952640, 5145188288279861767549485056, 5261245166962866168321277952, 4642275147320176030871715840, 93735272349639887690018062336, 4642275147320176030871715840,
    5145188288279861767549485056, 5145188288279861767549485056, 773712524553362671811952640, 4642275147320176030871715840, 773712524553362671811952640, 5261245166962866168321277952,
    5261245166962866168321277952, 696341272098026404630757376, 6162074352502113949995499520, 231522290408762344219860795392, 231552343549059326642000756736, 6132266775262240749406650368,
    713455128231945998885191680, 24247784063863315450118012928, 266989888330877855297456570368, 24248161853181945021735108608, 713360680902288605980917760
  ]
def positiveScales : Array ℕ := #[
    1, 3, 6, 4, 2, 3,
    2, 7, 4, 3, 11, 3,
    7, 7, 2, 3, 2, 4,
    4, 3, 19, 19, 23, 19,
    14, 20, 23, 20, 15
  ]
def negativeArguments : Array ℕ := #[
    1224365, 5089835, 5089835, 1224355, 3673095, 15269505,
    15269505, 3673065, 1224365, 5089835, 5089835, 1224355,
    4162841, 17305439, 17305439, 4162807, 4162841, 17305439,
    17305439, 4162807, 16722787737, 152327602801, 609370495319, 4165789651,
    1, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    5646386951951848791080960, 187781767244818911298846720, 187781767244818911298846720, 5646340835091664517201920, 33878321711711092746485760, 1126690603468913467793080320,
    1126690603468913467793080320, 33878045010549987103211520, 5646386951951848791080960, 187781767244818911298846720, 187781767244818911298846720, 5646340835091664517201920,
    38395431273272571779350528, 1276916017264768596832157696, 1276916017264768596832157696, 38395117678623318716973056, 38395431273272571779350528, 1276916017264768596832157696,
    1276916017264768596832157696, 38395117678623318716973056, 9414092577618637508050944, 343011267606412261377179648, 343045091956152872130838528, 9380524359973734289768448,
    158456325028528675187087900672, 475368975085586025561263702016, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    20, 22, 22, 20, 21, 23,
    23, 21, 20, 22, 22, 20,
    21, 24, 24, 21, 21, 24,
    24, 21, 33, 37, 39, 31,
    0, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 3169925001442312, 6066089190457772, 4087462841250339, 2321928094887362, 3906890595303263,
    2321928094887362, 7055282435501189, 4087462841250339, 3906890595303263, 11242578689451346, 3906890595303263,
    7055282435501189, 7055282435501189, 2321928094887362, 3906890595303263, 2321928094887362, 4087462841250339,
    4087462841250339, 3169925001442312, 19315474652213184, 19547065851111259, 23547253110413976, 19308479022650194,
    14204953163327534, 20291839566366545, 23752699855687199, 20291862043906315, 15204762166432983
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    20223602278654750, 22279187457739071, 22279187457739071, 20223590495396224, 21808564780144423, 23864149960723957,
    23864149960723957, 21808552996885714, 20223602278654750, 22279187457739071, 22279187457739071, 20223590495396224,
    21989137044907655, 24044722204102048, 24044722204102048, 21989125261645347, 21989137044907655, 24044722204102048,
    24044722204102048, 21989125261645347, 33961096330326644, 37148386435460465, 39148528692640918, 31955942858720835,
    0, 1584962500724866, 0
  ]

abbrev PositiveTerm := Fin 29
abbrev NegativeTerm := Fin 27
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
noncomputable def positiveFloor : ℝ := 236889389 / 1000000000000
noncomputable def negativeCeiling : ℝ := 11782683 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5646386951951848791080960, coefficient := (-5646386951951848791080960) }, { argument := 187781767244818911298846720, coefficient := (-187781767244818911298846720) }, { argument := 187781767244818911298846720, coefficient := (-187781767244818911298846720) }, { argument := 5646340835091664517201920, coefficient := (-5646340835091664517201920) }, { argument := 33878321711711092746485760, coefficient := (-33878321711711092746485760) }, { argument := 1126690603468913467793080320, coefficient := (-1126690603468913467793080320) }, { argument := 1126690603468913467793080320, coefficient := (-1126690603468913467793080320) }, { argument := 33878045010549987103211520, coefficient := (-33878045010549987103211520) }, { argument := 5646386951951848791080960, coefficient := (-5646386951951848791080960) }, { argument := 187781767244818911298846720, coefficient := (-187781767244818911298846720) }, { argument := 187781767244818911298846720, coefficient := (-187781767244818911298846720) }, { argument := 5646340835091664517201920, coefficient := (-5646340835091664517201920) }, { argument := 38395431273272571779350528, coefficient := (-38395431273272571779350528) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 38395117678623318716973056, coefficient := (-38395117678623318716973056) }, { argument := 38395431273272571779350528, coefficient := (-38395431273272571779350528) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 38395117678623318716973056, coefficient := (-38395117678623318716973056) }, { argument := 9414092577618637508050944, coefficient := (-9414092577618637508050944) }, { argument := 343011267606412261377179648, coefficient := (-343011267606412261377179648) }, { argument := 343045091956152872130838528, coefficient := (-343045091956152872130838528) }, { argument := 9380524359973734289768448, coefficient := (-9380524359973734289768448) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 5183873914507529901140082688, coefficient := 5183873914507529901140082688 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 773712524553362671811952640, coefficient := 773712524553362671811952640 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 773712524553362671811952640, coefficient := 773712524553362671811952640 }, { argument := 5145188288279861767549485056, coefficient := 5145188288279861767549485056 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 93735272349639887690018062336, coefficient := 93735272349639887690018062336 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 5145188288279861767549485056, coefficient := 5145188288279861767549485056 }, { argument := 5145188288279861767549485056, coefficient := 5145188288279861767549485056 }, { argument := 773712524553362671811952640, coefficient := 773712524553362671811952640 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 773712524553362671811952640, coefficient := 773712524553362671811952640 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 6162074352502113949995499520, coefficient := 6162074352502113949995499520 }, { argument := 231522290408762344219860795392, coefficient := 231522290408762344219860795392 }, { argument := 231552343549059326642000756736, coefficient := 231552343549059326642000756736 }, { argument := 6132266775262240749406650368, coefficient := 6132266775262240749406650368 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 713455128231945998885191680, coefficient := 713455128231945998885191680 }, { argument := 24247784063863315450118012928, coefficient := 24247784063863315450118012928 }, { argument := 266989888330877855297456570368, coefficient := 266989888330877855297456570368 }, { argument := 24248161853181945021735108608, coefficient := 24248161853181945021735108608 }, { argument := 713360680902288605980917760, coefficient := 713360680902288605980917760 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end TermShard2


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk9
