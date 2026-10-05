import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 7, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk7

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
def constantNumerator : ℤ := (-5252570128913663255893552136192)
def positiveArguments : Array ℕ := #[
    49, 100663351, 100663241, 75480045, 268453995, 9437045,
    1330563, 12250271, 98002203, 2661095
  ]
def positiveCoefficients : Array ℕ := #[
    3882179963198952542083653566464, 950738469631485166783500910592, 950737430710858935461553897472, 712888869266985099727617392640, 2535476296360910643698639831040, 713042960085321136250940293120,
    25133624458185934977883963392, 925604306823520184666062585856, 925604637389173985541227544576, 25133331671463997059880714240
  ]
def positiveScales : Array ℕ := #[
    5, 26, 26, 26, 28, 23,
    20, 23, 26, 21
  ]
def negativeArguments : Array ℕ := #[
    22323152803313, 822102221924429, 411051257763097, 1395180797305, 227898657104285, 810498218202425,
    113974071674005, 22323152803313, 22323132901903, 22323132901903, 822101319079859, 411050806340327,
    1395179553415, 810498218202425, 2882739448159775, 101334124226965, 822102221924429, 822101319079859,
    113974071674005, 101334124226965, 113998800885015, 411051257763097, 411050806340327, 1395180797305,
    1395179553415, 3, 25, 3
  ]
def negativeCoefficients : Array ℕ := #[
    6283408915420941874079203328, 231401203769957203212631015424, 231401286411507168795126923264, 6283335718857269509913313280, 64147769200818397935262760960, 228134967092555761771662540800,
    64161698340118390156883394560, 6283408915420941874079203328, 6283403313672025614862778368, 6283403313672025614862778368, 231400949641802889120400277504, 231401032283079823975486849024,
    6283330116874729020027043840, 228134967092555761771662540800, 811419019033661997561833062400, 228184162054237562515824312320, 231401203769957203212631015424, 231400949641802889120400277504,
    64161698340118390156883394560, 228184162054237562515824312320, 64175619648304615452762439680, 231401286411507168795126923264, 231401032283079823975486849024, 6283335718857269509913313280,
    6283330116874729020027043840, 1901475900342344102245054808064, 3961408125713216879677197516800, 1901475900342344102245054808064
  ]
def negativeScales : Array ℕ := #[
    44, 49, 48, 40, 47, 49,
    46, 44, 44, 44, 49, 48,
    40, 49, 51, 46, 49, 49,
    46, 46, 46, 48, 48, 40,
    40, 1, 4, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5614709844114682, 26584963288974525, 26584961712466893, 26169591947261943, 28000099633633418, 23169903751873846,
    20343605390571792, 23546310329033718, 26546310844270457, 21343588584224867
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    44343606033663569, 49546311121229497, 48546311636466804, 40343589227350957, 47695385752017499, 49525802342552267,
    46695698986896998, 44343606033663569, 44343604747479733, 44343604747479733, 49546309536840033, 48546310052076203,
    40343587941098495, 49525802342552267, 51356361870328932, 46526113411376684, 49546311121229497, 49546309536840033,
    46695698986896998, 46526113411376684, 46696011977735637, 48546311636466804, 48546310052076203, 40343589227350957,
    40343587941098495, 1584962500724866, 4643856189792934, 1584962500724866
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
noncomputable def positiveFloor : ℝ := 1359781259 / 500000000000
noncomputable def negativeCeiling : ℝ := 2586732821 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6283408915420941874079203328, coefficient := (-6283408915420941874079203328) }, { argument := 231401203769957203212631015424, coefficient := (-231401203769957203212631015424) }, { argument := 231401286411507168795126923264, coefficient := (-231401286411507168795126923264) }, { argument := 6283335718857269509913313280, coefficient := (-6283335718857269509913313280) }, { argument := 64147769200818397935262760960, coefficient := (-64147769200818397935262760960) }, { argument := 228134967092555761771662540800, coefficient := (-228134967092555761771662540800) }, { argument := 64161698340118390156883394560, coefficient := (-64161698340118390156883394560) }, { argument := 6283408915420941874079203328, coefficient := (-6283408915420941874079203328) }, { argument := 6283403313672025614862778368, coefficient := (-6283403313672025614862778368) }, { argument := 6283403313672025614862778368, coefficient := (-6283403313672025614862778368) }, { argument := 231400949641802889120400277504, coefficient := (-231400949641802889120400277504) }, { argument := 231401032283079823975486849024, coefficient := (-231401032283079823975486849024) }, { argument := 6283330116874729020027043840, coefficient := (-6283330116874729020027043840) }, { argument := 228134967092555761771662540800, coefficient := (-228134967092555761771662540800) }, { argument := 811419019033661997561833062400, coefficient := (-811419019033661997561833062400) }, { argument := 228184162054237562515824312320, coefficient := (-228184162054237562515824312320) }, { argument := 231401203769957203212631015424, coefficient := (-231401203769957203212631015424) }, { argument := 231400949641802889120400277504, coefficient := (-231400949641802889120400277504) }, { argument := 64161698340118390156883394560, coefficient := (-64161698340118390156883394560) }, { argument := 228184162054237562515824312320, coefficient := (-228184162054237562515824312320) }, { argument := 64175619648304615452762439680, coefficient := (-64175619648304615452762439680) }, { argument := 231401286411507168795126923264, coefficient := (-231401286411507168795126923264) }, { argument := 231401032283079823975486849024, coefficient := (-231401032283079823975486849024) }, { argument := 6283335718857269509913313280, coefficient := (-6283335718857269509913313280) }, { argument := 6283330116874729020027043840, coefficient := (-6283330116874729020027043840) }, { argument := 3882179963198952542083653566464, coefficient := 3882179963198952542083653566464 }, { argument := 950738469631485166783500910592, coefficient := 950738469631485166783500910592 }, { argument := 950737430710858935461553897472, coefficient := 950737430710858935461553897472 }, { argument := 1901475900342344102245054808064, coefficient := (-1901475900342344102245054808064) }, { argument := 712888869266985099727617392640, coefficient := 712888869266985099727617392640 }, { argument := 2535476296360910643698639831040, coefficient := 2535476296360910643698639831040 }, { argument := 713042960085321136250940293120, coefficient := 713042960085321136250940293120 }, { argument := 3961408125713216879677197516800, coefficient := (-3961408125713216879677197516800) }, { argument := 25133624458185934977883963392, coefficient := 25133624458185934977883963392 }, { argument := 925604306823520184666062585856, coefficient := 925604306823520184666062585856 }, { argument := 925604637389173985541227544576, coefficient := 925604637389173985541227544576 }, { argument := 25133331671463997059880714240, coefficient := 25133331671463997059880714240 }, { argument := 1901475900342344102245054808064, coefficient := (-1901475900342344102245054808064) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk7
