import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 1, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk1

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
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    1, 755715, 10728723, 3025633, 84047, 8220507,
    4110255, 168105
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 28550105492814671461346181120, 101329923798385337212040380416, 28576295737328666513701339136, 1587602943142980285102030848, 77640493457990597133408927744,
    77640521792189494351280209920, 1587706835205603417296732160
  ]
def positiveScales : Array ℕ := #[
    0, 19, 23, 21, 16, 22,
    21, 17
  ]
def negativeArguments : Array ℕ := #[
    63515578605, 6212360447505, 3106181357325, 127039470075, 63515578605, 901716981981,
    254295376751, 901716981981, 88195542522561, 44097787354365, 1803551979915, 6212360447505,
    88195542522561, 24872237255931, 254295376751, 24872237255931, 12436123166415, 508624035465,
    3106181357325, 44097787354365, 12436123166415, 127039470075, 1803551979915, 508624035465,
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    143024368068849724072919040, 6994496049118681444248453120, 6994498601697025742969241600, 143033727522778819382476800, 143024368068849724072919040, 507621533005409982005379072,
    143155570497230436472717312, 507621533005409982005379072, 24824838277521528400449110016, 24824847337122698080687226880, 507654751543032142878474240, 6994496049118681444248453120,
    24824838277521528400449110016, 7000912402355088722006900736, 143155570497230436472717312, 7000912402355088722006900736, 7000914957275023351983636480, 143164938536990746387415040,
    6994498601697025742969241600, 24824847337122698080687226880, 7000914957275023351983636480, 143033727522778819382476800, 507654751543032142878474240, 143164938536990746387415040,
    158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    35, 42, 41, 36, 35, 39,
    37, 39, 46, 45, 40, 42,
    46, 44, 37, 44, 43, 38,
    41, 45, 43, 36, 40, 38,
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 19527482733211083, 23354975031899148, 21528805573008920, 16358908703920281, 22970795943322402,
    21970796469820861, 17359003110182379
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    35886391440546446, 42498278677443643, 41498279203942110, 36886485846814425, 35886391440546446, 39713883735919438,
    37887714280427577, 39713883735919438, 46325770976131411, 45325771502629877, 40713978142181753, 42498278677443643,
    46325770976131411, 44499601517241493, 37887714280427577, 44499601517241493, 43499602043739960, 38887808686695691,
    41498279203942110, 45325771502629877, 43499602043739960, 36886485846814425, 40713978142181753, 38887808686695691,
    0, 0
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 2131193 / 25000000000
noncomputable def negativeCeiling : ℝ := 85247721 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 143024368068849724072919040, coefficient := (-143024368068849724072919040) }, { argument := 6994496049118681444248453120, coefficient := (-6994496049118681444248453120) }, { argument := 6994498601697025742969241600, coefficient := (-6994498601697025742969241600) }, { argument := 143033727522778819382476800, coefficient := (-143033727522778819382476800) }, { argument := 143024368068849724072919040, coefficient := (-143024368068849724072919040) }, { argument := 507621533005409982005379072, coefficient := (-507621533005409982005379072) }, { argument := 143155570497230436472717312, coefficient := (-143155570497230436472717312) }, { argument := 507621533005409982005379072, coefficient := (-507621533005409982005379072) }, { argument := 24824838277521528400449110016, coefficient := (-24824838277521528400449110016) }, { argument := 24824847337122698080687226880, coefficient := (-24824847337122698080687226880) }, { argument := 507654751543032142878474240, coefficient := (-507654751543032142878474240) }, { argument := 6994496049118681444248453120, coefficient := (-6994496049118681444248453120) }, { argument := 24824838277521528400449110016, coefficient := (-24824838277521528400449110016) }, { argument := 7000912402355088722006900736, coefficient := (-7000912402355088722006900736) }, { argument := 143155570497230436472717312, coefficient := (-143155570497230436472717312) }, { argument := 7000912402355088722006900736, coefficient := (-7000912402355088722006900736) }, { argument := 7000914957275023351983636480, coefficient := (-7000914957275023351983636480) }, { argument := 143164938536990746387415040, coefficient := (-143164938536990746387415040) }, { argument := 6994498601697025742969241600, coefficient := (-6994498601697025742969241600) }, { argument := 24824847337122698080687226880, coefficient := (-24824847337122698080687226880) }, { argument := 7000914957275023351983636480, coefficient := (-7000914957275023351983636480) }, { argument := 143033727522778819382476800, coefficient := (-143033727522778819382476800) }, { argument := 507654751543032142878474240, coefficient := (-507654751543032142878474240) }, { argument := 143164938536990746387415040, coefficient := (-143164938536990746387415040) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 28550105492814671461346181120, coefficient := 28550105492814671461346181120 }, { argument := 101329923798385337212040380416, coefficient := 101329923798385337212040380416 }, { argument := 28576295737328666513701339136, coefficient := 28576295737328666513701339136 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1587602943142980285102030848, coefficient := 1587602943142980285102030848 }, { argument := 77640493457990597133408927744, coefficient := 77640493457990597133408927744 }, { argument := 77640521792189494351280209920, coefficient := 77640521792189494351280209920 }, { argument := 1587706835205603417296732160, coefficient := 1587706835205603417296732160 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk1
