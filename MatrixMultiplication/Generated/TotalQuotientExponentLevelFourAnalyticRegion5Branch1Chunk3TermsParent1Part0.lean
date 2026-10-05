import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 3, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk3

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3217275349088652365376910262272)
def positiveArguments : Array ℕ := #[
    7, 33554427, 33554437, 18599169, 63455787, 4652085,
    884505, 32669967, 4083725, 55287
  ]
def positiveCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 316912602833392521677723664384, 316912697280722179070627938304, 175664184589656272599146037248, 599322963345830710891725717504, 175750802235685067631655649280,
    8353913531861231079480360960, 308559114314514748866312536064, 308557537044109470404811161600, 8354735223629250397747544064
  ]
def positiveScales : Array ℕ := #[
    2, 24, 25, 24, 25, 22,
    19, 24, 21, 15
  ]
def negativeArguments : Array ℕ := #[
    3709883207623, 137027751947535, 68513525750381, 231890506981, 14413696198335, 49176076736595,
    7210397999223, 3709883207623, 3709882511417, 3709882511417, 137027794588401, 68513547068819,
    231890463515, 49176076736595, 167776441429755, 24600171535449, 137027751947535, 137027794588401,
    7210397999223, 24600171535449, 450871744563, 68513525750381, 68513547068819, 231890506981,
    231890463515, 1, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    2088478578929875405689061376, 77139766576291922944374865920, 77139372259813688486075039744, 2088684001660774002722865152, 16228379206963260201935831040, 55367340216618039744166625280,
    16236372871246836353470562304, 2088478578929875405689061376, 2088478187000740134051119104, 2088478187000740134051119104, 77139790580965451488781402112, 77139396262241046716330541056,
    2088683610153851196150906880, 55367340216618039744166625280, 188899479776148116286335877120, 55394661680149199415360356352, 77139766576291922944374865920, 77139790580965451488781402112,
    16236372871246836353470562304, 55394661680149199415360356352, 16244366566446498046996905984, 77139372259813688486075039744, 77139396262241046716330541056, 2088684001660774002722865152,
    2088683610153851196150906880, 633825300114114700748351602688, 950737950171172051122527404032, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    41, 46, 45, 37, 43, 45,
    42, 41, 41, 41, 46, 45,
    37, 45, 47, 44, 46, 46,
    42, 44, 38, 45, 45, 37,
    37, 0, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 24999999783562094, 25000000214978297, 24148734828213595, 25919248403871491, 22149446026401463,
    19754510772741133, 24961461660939401, 21961454286255353, 15754652669390798
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    41754510908374516, 46961461449880792, 45961454075214953, 37754652804865865, 43712505576308841, 45483021874967773,
    42713216034226506, 41754510908374516, 41754510637634714, 41754510637634714, 46961461898824663, 45961454524119109,
    37754652534444321, 45483021874967773, 47253533480323716, 44483733608957244, 46961461449880792, 46961461898824663,
    42713216034226506, 44483733608957244, 38713926145195764, 45961454075214953, 45961454524119109, 37754652804865865,
    37754652534444321, 0, 1584962500724866, 0
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
noncomputable def positiveFloor : ℝ := 27638779 / 40000000000
noncomputable def negativeCeiling : ℝ := 631459323 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2088478578929875405689061376, coefficient := (-2088478578929875405689061376) }, { argument := 77139766576291922944374865920, coefficient := (-77139766576291922944374865920) }, { argument := 77139372259813688486075039744, coefficient := (-77139372259813688486075039744) }, { argument := 2088684001660774002722865152, coefficient := (-2088684001660774002722865152) }, { argument := 16228379206963260201935831040, coefficient := (-16228379206963260201935831040) }, { argument := 55367340216618039744166625280, coefficient := (-55367340216618039744166625280) }, { argument := 16236372871246836353470562304, coefficient := (-16236372871246836353470562304) }, { argument := 2088478578929875405689061376, coefficient := (-2088478578929875405689061376) }, { argument := 2088478187000740134051119104, coefficient := (-2088478187000740134051119104) }, { argument := 2088478187000740134051119104, coefficient := (-2088478187000740134051119104) }, { argument := 77139790580965451488781402112, coefficient := (-77139790580965451488781402112) }, { argument := 77139396262241046716330541056, coefficient := (-77139396262241046716330541056) }, { argument := 2088683610153851196150906880, coefficient := (-2088683610153851196150906880) }, { argument := 55367340216618039744166625280, coefficient := (-55367340216618039744166625280) }, { argument := 188899479776148116286335877120, coefficient := (-188899479776148116286335877120) }, { argument := 55394661680149199415360356352, coefficient := (-55394661680149199415360356352) }, { argument := 77139766576291922944374865920, coefficient := (-77139766576291922944374865920) }, { argument := 77139790580965451488781402112, coefficient := (-77139790580965451488781402112) }, { argument := 16236372871246836353470562304, coefficient := (-16236372871246836353470562304) }, { argument := 55394661680149199415360356352, coefficient := (-55394661680149199415360356352) }, { argument := 16244366566446498046996905984, coefficient := (-16244366566446498046996905984) }, { argument := 77139372259813688486075039744, coefficient := (-77139372259813688486075039744) }, { argument := 77139396262241046716330541056, coefficient := (-77139396262241046716330541056) }, { argument := 2088684001660774002722865152, coefficient := (-2088684001660774002722865152) }, { argument := 2088683610153851196150906880, coefficient := (-2088683610153851196150906880) }, { argument := 1109194275199700726309615304704, coefficient := 1109194275199700726309615304704 }, { argument := 316912602833392521677723664384, coefficient := 316912602833392521677723664384 }, { argument := 316912697280722179070627938304, coefficient := 316912697280722179070627938304 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 175664184589656272599146037248, coefficient := 175664184589656272599146037248 }, { argument := 599322963345830710891725717504, coefficient := 599322963345830710891725717504 }, { argument := 175750802235685067631655649280, coefficient := 175750802235685067631655649280 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 8353913531861231079480360960, coefficient := 8353913531861231079480360960 }, { argument := 308559114314514748866312536064, coefficient := 308559114314514748866312536064 }, { argument := 308557537044109470404811161600, coefficient := 308557537044109470404811161600 }, { argument := 8354735223629250397747544064, coefficient := 8354735223629250397747544064 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk3
