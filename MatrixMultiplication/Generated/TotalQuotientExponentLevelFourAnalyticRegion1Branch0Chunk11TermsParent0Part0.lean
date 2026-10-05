import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 11, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk11

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
    47, 65, 117, 259, 495, 935,
    989, 1333, 1557, 1595, 1937, 15541,
    16907
  ]
def positiveCoefficients : Array ℕ := #[
    1584563250285286751870879006720, 319368723094999544839575663804416, 13389559464910673053308927606784, 318417985144828372788453136400384, 329113787084254058363581569695744, 13310331302396408715715383656448,
    328717646271682736675613849944064, 602530175920980287398901742305280, 873807404369821379319196228255744, 631289998913658241945358196277248, 218273587726798250070213583175680, 218986641189426629108555478728704,
    2679021087257334311388095136661504
  ]
def positiveScales : Array ℕ := #[
    5, 6, 6, 8, 8, 9,
    9, 10, 10, 10, 10, 13,
    14
  ]
def negativeArguments : Array ℕ := #[
    5, 7, 19, 21, 41, 43,
    71, 83, 125, 129, 139, 173,
    231, 499, 655, 1039, 1215, 2077,
    2619, 4149, 5451, 7605, 329922106235
  ]
def negativeCoefficients : Array ℕ := #[
    1584563250285286751870879006720, 17747108403195211620953844875264, 96341445617345434513749443608576, 16637914127995510894644229570560, 3248354663084837841335301963776, 6813621976226733033044779728896,
    22500798154051071876566481895424, 13151874977367880040528295755776, 39614081257132168796771975168000, 81763463714720796396537356746752, 22025429178965485851005218193408, 13706472114967730403683103408128,
    18301705540795061984108652527616, 39534853094617904459178431217664, 207577785787372564495085149880320, 82318060852320646759692164399104, 96262217454831170176155899658240, 329113787084254058363581569695744,
    207498557624858300157491605929984, 328717646271682736675613849944064, 431872713865254904222408073281536, 602530175920980287398901742305280, 1339510543628667155694047568330752
  ]
def negativeScales : Array ℕ := #[
    2, 2, 4, 4, 5, 5,
    6, 6, 6, 7, 7, 7,
    7, 8, 9, 10, 10, 11,
    11, 12, 12, 12, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5554588851677541, 6022367813028454, 6870364719426147, 8016808287686553, 8951284714309401, 9868822554622187,
    9949826710117496, 10380461065088972, 10604553229078637, 10639340708651223, 10919608238221345, 13923791717416060,
    14045333068328068
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2321928094887363, 2807354922807594, 4247927513443586, 4392317422778766, 5357552004618085, 5426264754702117,
    6149747119504683, 6375039431346928, 6965784298236803, 7011227255423255, 7118941072723508, 7434628227636751,
    7851749043206919, 8962896018276254, 9355351096424814, 10020979938904212, 10246740598493144, 11020285500844648,
    11354800344350598, 12018547941871651, 12412305204955283, 12892732536443689, 38263334491827857
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 23
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
noncomputable def positiveFloor : ℝ := 458748051927 / 500000000000
noncomputable def negativeCeiling : ℝ := 968842681917 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5, coefficient := (-1584563250285286751870879006720) }, { argument := 7, coefficient := (-17747108403195211620953844875264) }, { argument := 19, coefficient := (-96341445617345434513749443608576) }, { argument := 21, coefficient := (-16637914127995510894644229570560) }, { argument := 41, coefficient := (-3248354663084837841335301963776) }, { argument := 43, coefficient := (-6813621976226733033044779728896) }, { argument := 47, coefficient := 1584563250285286751870879006720 }, { argument := 65, coefficient := 319368723094999544839575663804416 }, { argument := 71, coefficient := (-22500798154051071876566481895424) }, { argument := 83, coefficient := (-13151874977367880040528295755776) }, { argument := 117, coefficient := 13389559464910673053308927606784 }, { argument := 125, coefficient := (-39614081257132168796771975168000) }, { argument := 129, coefficient := (-81763463714720796396537356746752) }, { argument := 139, coefficient := (-22025429178965485851005218193408) }, { argument := 173, coefficient := (-13706472114967730403683103408128) }, { argument := 231, coefficient := (-18301705540795061984108652527616) }, { argument := 259, coefficient := 318417985144828372788453136400384 }, { argument := 495, coefficient := 329113787084254058363581569695744 }, { argument := 499, coefficient := (-39534853094617904459178431217664) }, { argument := 655, coefficient := (-207577785787372564495085149880320) }, { argument := 935, coefficient := 13310331302396408715715383656448 }, { argument := 989, coefficient := 328717646271682736675613849944064 }, { argument := 1039, coefficient := (-82318060852320646759692164399104) }, { argument := 1215, coefficient := (-96262217454831170176155899658240) }, { argument := 1333, coefficient := 602530175920980287398901742305280 }, { argument := 1557, coefficient := 873807404369821379319196228255744 }, { argument := 1595, coefficient := 631289998913658241945358196277248 }, { argument := 1937, coefficient := 218273587726798250070213583175680 }, { argument := 2077, coefficient := (-329113787084254058363581569695744) }, { argument := 2619, coefficient := (-207498557624858300157491605929984) }, { argument := 4149, coefficient := (-328717646271682736675613849944064) }, { argument := 5451, coefficient := (-431872713865254904222408073281536) }, { argument := 7605, coefficient := (-602530175920980287398901742305280) }, { argument := 15541, coefficient := 218986641189426629108555478728704 }, { argument := 16907, coefficient := 2679021087257334311388095136661504 }, { argument := 329922106235, coefficient := (-1339510543628667155694047568330752) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk11
