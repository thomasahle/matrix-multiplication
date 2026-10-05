import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 17, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk17

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
    155, 257, 405, 1695, 1987, 2049,
    6845, 7461, 30349, 30483, 61007, 119099,
    122687
  ]
def positiveCoefficients : Array ℕ := #[
    1571886744283004457855911974666240, 184443162333207377917770316382208, 417136275637601737430008898519040, 37395692706732767344152744558592, 1267650600228229401496703205376, 1267650600228229401496703205376,
    38029518006846882044901096161280, 339334220048594157913148739289088, 53162097047071370525267990675456, 53241325209585634862861534625792, 354070658276247324705547914051584, 338938079236022836225181019537408,
    355179852551447025431857529356288
  ]
def positiveScales : Array ℕ := #[
    7, 8, 8, 10, 10, 11,
    12, 12, 14, 14, 15, 16,
    16
  ]
def negativeArguments : Array ℕ := #[
    7, 21, 31, 87, 125, 135,
    179, 341, 671, 713, 2139, 2503,
    2511, 4283, 23611715854665
  ]
def negativeCoefficients : Array ℕ := #[
    2218388550399401452619230609408, 53241325209585634862861534625792, 9824292151768777861599449841664, 27571400554963989482553294716928, 9903520314283042199192993792000, 85566415515405484601027466362880,
    113454728720426531433954936881152, 27016803417364139119398487064576, 53162097047071370525267990675456, 112979359745340945408393673179136, 338938079236022836225181019537408, 198308090773203636996640507691008,
    198941916073317751697388859293696, 339334220048594157913148739289088, 785943372141502228927955987333120
  ]
def negativeScales : Array ℕ := #[
    2, 4, 4, 6, 6, 7,
    7, 8, 9, 9, 11, 11,
    11, 12, 44
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7276124405274237, 8005624549193878, 8661778097770205, 10727069558015321, 10956376156533436, 11000704269011246,
    12740834826133858, 12865153292795361, 14889361359767700, 14895717272686477, 15896687167640868, 16861801774145481,
    16904622862271210
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2807354922807594, 4392317422778766, 4954196321574415, 6442943495848765, 6965784298236803, 7076815597050831,
    7483815777264413, 8413627929024184, 9390168956200188, 9477758266444015, 11062720767165045, 11289442575688333,
    11294046313271501, 12064405961891043, 44424568119027261
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 15
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
noncomputable def positiveFloor : ℝ := 9807441653 / 20000000000
noncomputable def negativeCeiling : ℝ := 153567567053 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7, coefficient := (-2218388550399401452619230609408) }, { argument := 21, coefficient := (-53241325209585634862861534625792) }, { argument := 31, coefficient := (-9824292151768777861599449841664) }, { argument := 87, coefficient := (-27571400554963989482553294716928) }, { argument := 125, coefficient := (-9903520314283042199192993792000) }, { argument := 135, coefficient := (-85566415515405484601027466362880) }, { argument := 155, coefficient := 1571886744283004457855911974666240 }, { argument := 179, coefficient := (-113454728720426531433954936881152) }, { argument := 257, coefficient := 184443162333207377917770316382208 }, { argument := 341, coefficient := (-27016803417364139119398487064576) }, { argument := 405, coefficient := 417136275637601737430008898519040 }, { argument := 671, coefficient := (-53162097047071370525267990675456) }, { argument := 713, coefficient := (-112979359745340945408393673179136) }, { argument := 1695, coefficient := 37395692706732767344152744558592 }, { argument := 1987, coefficient := 1267650600228229401496703205376 }, { argument := 2049, coefficient := 1267650600228229401496703205376 }, { argument := 2139, coefficient := (-338938079236022836225181019537408) }, { argument := 2503, coefficient := (-198308090773203636996640507691008) }, { argument := 2511, coefficient := (-198941916073317751697388859293696) }, { argument := 4283, coefficient := (-339334220048594157913148739289088) }, { argument := 6845, coefficient := 38029518006846882044901096161280 }, { argument := 7461, coefficient := 339334220048594157913148739289088 }, { argument := 30349, coefficient := 53162097047071370525267990675456 }, { argument := 30483, coefficient := 53241325209585634862861534625792 }, { argument := 61007, coefficient := 354070658276247324705547914051584 }, { argument := 119099, coefficient := 338938079236022836225181019537408 }, { argument := 122687, coefficient := 355179852551447025431857529356288 }, { argument := 23611715854665, coefficient := (-785943372141502228927955987333120) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk17
