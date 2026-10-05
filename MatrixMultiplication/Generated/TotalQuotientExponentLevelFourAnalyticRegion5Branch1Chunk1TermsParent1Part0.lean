import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 1, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk1

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
def constantNumerator : ℤ := 641772728480711620807427620864
def positiveArguments : Array ℕ := #[
    3, 637533, 24528343, 6132041, 79701, 55311,
    119753, 21225187, 956995, 6911
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 6021328941846667044046503936, 231663649727060564179687571456, 231661959119859696846701068288, 6022037296819097490828558336, 1044795250136011785658957824,
    36193123419077671889647173632, 400932446725762065137410244608, 36154248898190688970248028160, 1044360792419587778299297792
  ]
def positiveScales : Array ℕ := #[
    1, 19, 24, 22, 16, 15,
    16, 24, 19, 12
  ]
def negativeArguments : Array ℕ := #[
    11821546479, 203575302097, 4510443874045, 203391064867, 2954067403, 11821546479,
    452161688101, 226079247019, 5911432779, 452161688101, 7832929099079, 173539697543607,
    7824481429985, 112993506677, 203575302097, 7832929099079, 7832871912807, 203599267201,
    226079247019, 7832871912807, 43384607720969, 3912212179695, 112992708351, 4510443874045,
    173539697543607, 43384607720969, 563871829733, 5911432779, 203599267201, 563871829733,
    101707485839, 2954397121, 203391064867, 7824481429985, 3912212179695, 101707485839,
    2954067403, 112993506677, 112992708351, 2954397121, 3, 3
  ]
def negativeCoefficients : Array ℕ := #[
    6654939039720924877160448, 229205413666471338236182528, 2539154168803074799346647040, 228997980986377395144491008, 6651968427689064418770944, 6654939039720924877160448,
    254544401255359754390208512, 254542603157742679654137856, 6655681615182533907972096, 254544401255359754390208512, 8819094142957924835756343296, 97694164648922133151963152384,
    8809582913111952921869680640, 254438757282911425864400896, 229205413666471338236182528, 8819094142957924835756343296, 8819029756939607358799085568, 229232395974832412031975424,
    254542603157742679654137856, 8819029756939607358799085568, 97693451582885566050375565312, 8809518657334358968746639360, 254436959612573365775106048, 2539154168803074799346647040,
    97694164648922133151963152384, 97693451582885566050375565312, 2539452962270258567019757568, 6655681615182533907972096, 229232395974832412031975424, 2539452962270258567019757568,
    229024897662655199363203072, 6652710886620033091371008, 228997980986377395144491008, 8809582913111952921869680640, 8809518657334358968746639360, 229024897662655199363203072,
    6651968427689064418770944, 254438757282911425864400896, 254436959612573365775106048, 6652710886620033091371008, 475368975085586025561263702016, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    33, 37, 42, 37, 31, 33,
    38, 37, 32, 38, 42, 47,
    42, 36, 37, 42, 42, 37,
    37, 42, 45, 41, 36, 42,
    47, 45, 39, 32, 37, 39,
    36, 31, 37, 42, 41, 36,
    31, 36, 36, 31, 1, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 19282140495159931, 24547946440853528, 22547935912488256, 16282310205220530, 15755278805152985,
    16869702272463473, 24339273928603946, 19868151861385861, 12754678763807085
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    33460699728182976, 37566771586986644, 42036406555138480, 37565465345597578, 31460055598458851, 33460699728182976,
    38718047800825006, 37718037609614077, 32460860698879210, 38718047800825006, 42832689039551049, 47302259048277446,
    42831132279988565, 36717448912491809, 37566771586986644, 42832689039551049, 42832678506753785, 37566941412606141,
    37718037609614077, 42832678506753785, 45302248518062127, 41831121757148511, 36717438719472169, 42036406555138480,
    47302259048277446, 45302248518062127, 39036576313437450, 32460860698879210, 37566941412606141, 39036576313437450,
    36565634911605044, 31460216615766158, 37565465345597578, 42831132279988565, 41831121757148511, 36565634911605044,
    31460055598458851, 36717448912491809, 36717438719472169, 31460216615766158, 1584962500724866, 1584962500724866
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 276792679 / 1000000000000
noncomputable def negativeCeiling : ℝ := 69698923 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6654939039720924877160448, coefficient := (-6654939039720924877160448) }, { argument := 229205413666471338236182528, coefficient := (-229205413666471338236182528) }, { argument := 2539154168803074799346647040, coefficient := (-2539154168803074799346647040) }, { argument := 228997980986377395144491008, coefficient := (-228997980986377395144491008) }, { argument := 6651968427689064418770944, coefficient := (-6651968427689064418770944) }, { argument := 6654939039720924877160448, coefficient := (-6654939039720924877160448) }, { argument := 254544401255359754390208512, coefficient := (-254544401255359754390208512) }, { argument := 254542603157742679654137856, coefficient := (-254542603157742679654137856) }, { argument := 6655681615182533907972096, coefficient := (-6655681615182533907972096) }, { argument := 254544401255359754390208512, coefficient := (-254544401255359754390208512) }, { argument := 8819094142957924835756343296, coefficient := (-8819094142957924835756343296) }, { argument := 97694164648922133151963152384, coefficient := (-97694164648922133151963152384) }, { argument := 8809582913111952921869680640, coefficient := (-8809582913111952921869680640) }, { argument := 254438757282911425864400896, coefficient := (-254438757282911425864400896) }, { argument := 229205413666471338236182528, coefficient := (-229205413666471338236182528) }, { argument := 8819094142957924835756343296, coefficient := (-8819094142957924835756343296) }, { argument := 8819029756939607358799085568, coefficient := (-8819029756939607358799085568) }, { argument := 229232395974832412031975424, coefficient := (-229232395974832412031975424) }, { argument := 254542603157742679654137856, coefficient := (-254542603157742679654137856) }, { argument := 8819029756939607358799085568, coefficient := (-8819029756939607358799085568) }, { argument := 97693451582885566050375565312, coefficient := (-97693451582885566050375565312) }, { argument := 8809518657334358968746639360, coefficient := (-8809518657334358968746639360) }, { argument := 254436959612573365775106048, coefficient := (-254436959612573365775106048) }, { argument := 2539154168803074799346647040, coefficient := (-2539154168803074799346647040) }, { argument := 97694164648922133151963152384, coefficient := (-97694164648922133151963152384) }, { argument := 97693451582885566050375565312, coefficient := (-97693451582885566050375565312) }, { argument := 2539452962270258567019757568, coefficient := (-2539452962270258567019757568) }, { argument := 6655681615182533907972096, coefficient := (-6655681615182533907972096) }, { argument := 229232395974832412031975424, coefficient := (-229232395974832412031975424) }, { argument := 2539452962270258567019757568, coefficient := (-2539452962270258567019757568) }, { argument := 229024897662655199363203072, coefficient := (-229024897662655199363203072) }, { argument := 6652710886620033091371008, coefficient := (-6652710886620033091371008) }, { argument := 228997980986377395144491008, coefficient := (-228997980986377395144491008) }, { argument := 8809582913111952921869680640, coefficient := (-8809582913111952921869680640) }, { argument := 8809518657334358968746639360, coefficient := (-8809518657334358968746639360) }, { argument := 229024897662655199363203072, coefficient := (-229024897662655199363203072) }, { argument := 6651968427689064418770944, coefficient := (-6651968427689064418770944) }, { argument := 254438757282911425864400896, coefficient := (-254438757282911425864400896) }, { argument := 254436959612573365775106048, coefficient := (-254436959612573365775106048) }, { argument := 6652710886620033091371008, coefficient := (-6652710886620033091371008) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 6021328941846667044046503936, coefficient := 6021328941846667044046503936 }, { argument := 231663649727060564179687571456, coefficient := 231663649727060564179687571456 }, { argument := 231661959119859696846701068288, coefficient := 231661959119859696846701068288 }, { argument := 6022037296819097490828558336, coefficient := 6022037296819097490828558336 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 1044795250136011785658957824, coefficient := 1044795250136011785658957824 }, { argument := 36193123419077671889647173632, coefficient := 36193123419077671889647173632 }, { argument := 400932446725762065137410244608, coefficient := 400932446725762065137410244608 }, { argument := 36154248898190688970248028160, coefficient := 36154248898190688970248028160 }, { argument := 1044360792419587778299297792, coefficient := 1044360792419587778299297792 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk1
