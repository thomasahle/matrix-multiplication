import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 7, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk7

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
def constantNumerator : ℤ := (-894563431332608825520639967232)
def positiveArguments : Array ℕ := #[
    7, 4194295, 4194313, 9173973, 63977663, 18337687,
    1410519, 48921087, 24460567, 352639, 6015, 1318507,
    14043967, 1322055, 44567
  ]
def positiveCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 79227992509070954286316257280, 79228332519457720900771643392, 173291450439804350840105336832, 604251942807058868822811344896, 173194556924308831459610722304,
    13321975298101618194354536448, 462046603108699846316711215104, 462047047011149236063361302528, 13322324753221350548100349952, 454480550311374655366103040, 12452946528458014603549343744,
    132641518094654725365709144064, 12486456441020457605985730560, 420923414084102956477579264
  ]
def positiveScales : Array ℕ := #[
    2, 21, 22, 23, 25, 24,
    20, 25, 24, 18, 12, 20,
    23, 20, 15
  ]
def negativeArguments : Array ℕ := #[
    25228684425, 5530207317565, 58904540568265, 5545088676225, 186927145265, 4310749108551,
    149602850009541, 74801496576219, 2155430463903, 4310749108551, 15045648900281, 8414421731,
    25228684425, 25228792695, 25228792695, 5530231050691, 58904793359671, 5545112473215,
    186927947471, 15045648900281, 521637436916111, 260818969681211, 7523023073697, 149602850009541,
    521637436916111, 37379839157035, 5530207317565, 5530231050691, 8414421731, 37379839157035,
    37379874892021, 33658559507, 74801496576219, 260818969681211, 37379874892021, 58904540568265,
    58904793359671, 2155430463903, 7523023073697, 33658559507, 5545088676225, 5545112473215,
    186927145265, 186927947471, 1, 3, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    113619893775477836139724800, 3113229951833415529822945280, 33160308369208564837441863680, 3121607411997908367782707200, 105230627720110571970887680, 1213368004934873838262419456,
    42109458722283315722396368896, 42109499013426915093226979328, 1213399479257070766166900736, 1213368004934873838262419456, 4234973673803301533134094336, 1212645970312633725780754432,
    113619893775477836139724800, 113620381380209491543326720, 113620381380209491543326720, 3113243312395591771951726592, 33160450678118797845412708352, 3121620808512320435210158080,
    105231079321940906267901952, 4234973673803301533134094336, 146827885407368632107391778816, 146828026833432319187413368832, 4235085488925181583466430464, 42109458722283315722396368896,
    146827885407368632107391778816, 42085957424697975328567459840, 3113229951833415529822945280, 3113243312395591771951726592, 1212645970312633725780754432, 42085957424697975328567459840,
    42085997658715383751040303104, 1212677408428422924416843776, 42109499013426915093226979328, 146828026833432319187413368832, 42085997658715383751040303104, 33160308369208564837441863680,
    33160450678118797845412708352, 1213399479257070766166900736, 4235085488925181583466430464, 1212677408428422924416843776, 3121607411997908367782707200, 3121620808512320435210158080,
    105230627720110571970887680, 105231079321940906267901952, 158456325028528675187087900672, 950737950171172051122527404032, 950737950171172051122527404032, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    34, 42, 45, 42, 37, 41,
    47, 46, 40, 41, 43, 32,
    34, 34, 34, 42, 45, 42,
    37, 43, 48, 47, 42, 47,
    48, 45, 42, 42, 32, 45,
    45, 34, 46, 47, 45, 45,
    45, 40, 42, 34, 42, 42,
    37, 37, 0, 1, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 21999996902849453, 22000003095684394, 23129115230741930, 25931064957857676, 24128308342180934,
    20427794668796865, 25543953124333654, 24543954510374695, 18427832512325673, 12554349022063343, 20330473799865652,
    23743447175542703, 20334350766273187, 15443688229645390
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    34554345926373919, 42330470704174617, 45743444080058479, 42334347670582152, 37443685133954393, 41971075751614011,
    47088130987976605, 46088132368374431, 40971113174119410, 41971075751614011, 43774411563586500, 32970216996418972,
    34554345926373919, 34554352117749350, 34554352117749350, 42330476895550048, 45743450271433936, 42334353861957584,
    37443691325329824, 43774411563586500, 48890040744806893, 47890042134424372, 42774449654258605, 47088130987976605,
    48890040744806893, 45087325594811206, 42330470704174617, 42330476895550048, 32970216996418972, 45087325594811206,
    45087326974021593, 34970254398132141, 46088132368374431, 47890042134424372, 45087326974021593, 45743444080058479,
    45743450271433936, 40971113174119410, 42774449654258605, 34970254398132141, 42334347670582152, 42334353861957584,
    37443685133954393, 37443691325329824, 0, 1584962500724866, 1584962500724866, 0
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 27822493 / 40000000000
noncomputable def negativeCeiling : ℝ := 331771643 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 113619893775477836139724800, coefficient := (-113619893775477836139724800) }, { argument := 3113229951833415529822945280, coefficient := (-3113229951833415529822945280) }, { argument := 33160308369208564837441863680, coefficient := (-33160308369208564837441863680) }, { argument := 3121607411997908367782707200, coefficient := (-3121607411997908367782707200) }, { argument := 105230627720110571970887680, coefficient := (-105230627720110571970887680) }, { argument := 1213368004934873838262419456, coefficient := (-1213368004934873838262419456) }, { argument := 42109458722283315722396368896, coefficient := (-42109458722283315722396368896) }, { argument := 42109499013426915093226979328, coefficient := (-42109499013426915093226979328) }, { argument := 1213399479257070766166900736, coefficient := (-1213399479257070766166900736) }, { argument := 1213368004934873838262419456, coefficient := (-1213368004934873838262419456) }, { argument := 4234973673803301533134094336, coefficient := (-4234973673803301533134094336) }, { argument := 1212645970312633725780754432, coefficient := (-1212645970312633725780754432) }, { argument := 113619893775477836139724800, coefficient := (-113619893775477836139724800) }, { argument := 113620381380209491543326720, coefficient := (-113620381380209491543326720) }, { argument := 113620381380209491543326720, coefficient := (-113620381380209491543326720) }, { argument := 3113243312395591771951726592, coefficient := (-3113243312395591771951726592) }, { argument := 33160450678118797845412708352, coefficient := (-33160450678118797845412708352) }, { argument := 3121620808512320435210158080, coefficient := (-3121620808512320435210158080) }, { argument := 105231079321940906267901952, coefficient := (-105231079321940906267901952) }, { argument := 4234973673803301533134094336, coefficient := (-4234973673803301533134094336) }, { argument := 146827885407368632107391778816, coefficient := (-146827885407368632107391778816) }, { argument := 146828026833432319187413368832, coefficient := (-146828026833432319187413368832) }, { argument := 4235085488925181583466430464, coefficient := (-4235085488925181583466430464) }, { argument := 42109458722283315722396368896, coefficient := (-42109458722283315722396368896) }, { argument := 146827885407368632107391778816, coefficient := (-146827885407368632107391778816) }, { argument := 42085957424697975328567459840, coefficient := (-42085957424697975328567459840) }, { argument := 3113229951833415529822945280, coefficient := (-3113229951833415529822945280) }, { argument := 3113243312395591771951726592, coefficient := (-3113243312395591771951726592) }, { argument := 1212645970312633725780754432, coefficient := (-1212645970312633725780754432) }, { argument := 42085957424697975328567459840, coefficient := (-42085957424697975328567459840) }, { argument := 42085997658715383751040303104, coefficient := (-42085997658715383751040303104) }, { argument := 1212677408428422924416843776, coefficient := (-1212677408428422924416843776) }, { argument := 42109499013426915093226979328, coefficient := (-42109499013426915093226979328) }, { argument := 146828026833432319187413368832, coefficient := (-146828026833432319187413368832) }, { argument := 42085997658715383751040303104, coefficient := (-42085997658715383751040303104) }, { argument := 33160308369208564837441863680, coefficient := (-33160308369208564837441863680) }, { argument := 33160450678118797845412708352, coefficient := (-33160450678118797845412708352) }, { argument := 1213399479257070766166900736, coefficient := (-1213399479257070766166900736) }, { argument := 4235085488925181583466430464, coefficient := (-4235085488925181583466430464) }, { argument := 1212677408428422924416843776, coefficient := (-1212677408428422924416843776) }, { argument := 3121607411997908367782707200, coefficient := (-3121607411997908367782707200) }, { argument := 3121620808512320435210158080, coefficient := (-3121620808512320435210158080) }, { argument := 105230627720110571970887680, coefficient := (-105230627720110571970887680) }, { argument := 105231079321940906267901952, coefficient := (-105231079321940906267901952) }, { argument := 1109194275199700726309615304704, coefficient := 1109194275199700726309615304704 }, { argument := 79227992509070954286316257280, coefficient := 79227992509070954286316257280 }, { argument := 79228332519457720900771643392, coefficient := 79228332519457720900771643392 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 173291450439804350840105336832, coefficient := 173291450439804350840105336832 }, { argument := 604251942807058868822811344896, coefficient := 604251942807058868822811344896 }, { argument := 173194556924308831459610722304, coefficient := 173194556924308831459610722304 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 13321975298101618194354536448, coefficient := 13321975298101618194354536448 }, { argument := 462046603108699846316711215104, coefficient := 462046603108699846316711215104 }, { argument := 462047047011149236063361302528, coefficient := 462047047011149236063361302528 }, { argument := 13322324753221350548100349952, coefficient := 13322324753221350548100349952 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 454480550311374655366103040, coefficient := 454480550311374655366103040 }, { argument := 12452946528458014603549343744, coefficient := 12452946528458014603549343744 }, { argument := 132641518094654725365709144064, coefficient := 132641518094654725365709144064 }, { argument := 12486456441020457605985730560, coefficient := 12486456441020457605985730560 }, { argument := 420923414084102956477579264, coefficient := 420923414084102956477579264 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk7
