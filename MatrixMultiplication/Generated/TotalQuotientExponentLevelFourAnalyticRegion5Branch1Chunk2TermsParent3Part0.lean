import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 2, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk2

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 23732363658236991997691662696448
def positiveArguments : Array ℕ := #[
    1, 476401, 16300815, 8150397, 238211, 154761
  ]
def positiveCoefficients : Array ℕ := #[
    633825300114114700748351602688, 4499480229611163698899976192, 153956844798917511488187924480, 153956646459525230963088949248, 4499678569003444223998951424, 1461676318510778325833613312
  ]
def positiveScales : Array ℕ := #[
    0, 18, 23, 22, 17, 17
  ]
def negativeArguments : Array ℕ := #[
    84870213299, 1955988993237, 3910976724335, 21214388877, 376155065, 199311629787,
    2186080169127, 199166799295, 5881646127, 2910584519981, 66924326604209, 133812945865717,
    727527659231, 199311629787, 3318169789303, 72782398730869, 6630401242301, 194744972293,
    84870213299, 2910584519981, 1455290144359, 42436965289, 1455290144359, 16731060150179,
    66906387005057, 363763301155, 2186080169127, 72782398730869, 199534437253953, 18179175575849,
    533872923599, 1955988993237, 66924326604209, 16731060150179, 978037612407, 42436965289,
    978037612407, 1955574574285, 10607659047, 199166799295, 6630401242301, 18179175575849,
    1656124047587, 48650028373, 3910976724335, 133812945865717, 66906387005057, 1955574574285,
    5881646127, 194744972293, 533872923599, 48650028373, 1436243663, 21214388877,
    727527659231, 363763301155, 10607659047, 1
  ]
def negativeCoefficients : Array ℕ := #[
    23888841311764432126214144, 1101123912635368102579666944, 1100842082398111815969013760, 23885278460337498775093248, 1694051810567524701962240, 56101236352458715689910272,
    615326864692649254623117312, 56060470193096022839787520, 1655536206617645062029312, 819256709976047848087617536, 37675046544592128042449502208, 37664995821136964654938980352,
    819123323753615198617862144, 56101236352458715689910272, 1867963528332128503029825536, 20486423987717030586628440064, 1866292035258978585024659456, 54815836540689522997854208,
    23888841311764432126214144, 819256709976047848087617536, 819255518981393466427179008, 23889887632784384136839168, 819255518981393466427179008, 37674998128929749622316859392,
    37664947448085112634195574784, 819122133766359758604861440, 615326864692649254623117312, 20486423987717030586628440064, 224655804316121086485092892672, 20467932087324094610618187776,
    601087474945913420068683776, 1101123912635368102579666944, 37675046544592128042449502208, 37674998128929749622316859392, 1101172456697623698858835968, 23889887632784384136839168,
    1101172456697623698858835968, 1100890615505642793646161920, 23886324665671235357638656, 56060470193096022839787520, 1866292035258978585024659456, 20467932087324094610618187776,
    1864629910898032696295948288, 54775062413051714445770752, 1100842082398111815969013760, 37664995821136964654938980352, 37664947448085112634195574784, 1100890615505642793646161920,
    1655536206617645062029312, 54815836540689522997854208, 601087474945913420068683776, 54775062413051714445770752, 1617066606375009058291712, 23885278460337498775093248,
    819123323753615198617862144, 819122133766359758604861440, 23886324665671235357638656, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    36, 40, 41, 34, 28, 37,
    40, 37, 32, 41, 45, 46,
    39, 37, 41, 46, 42, 37,
    36, 41, 40, 35, 40, 43,
    45, 38, 40, 46, 47, 44,
    38, 40, 45, 43, 39, 35,
    39, 40, 33, 37, 42, 44,
    40, 35, 41, 46, 45, 40,
    32, 37, 38, 35, 30, 34,
    39, 38, 33, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 18861816915828728, 23958440760875245, 22958438902280138, 17861880509163036, 17239682430444689
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36304539252168734, 40831035391812440, 41830666089926473, 34304324068378050, 28486752275760252, 37536234937313234,
    40991483468586146, 37535186216847910, 32453572840152791, 41404446051024421, 45927595958112676, 46927211033169775,
    39404211141372094, 37536234937313234, 41593524848912558, 46048654833219020, 42592233317099691, 37502795126648558,
    36304539252168734, 41404446051024421, 40404443953704607, 35304602440209951, 40404443953704607, 43927594104124535,
    45927209180319035, 38404209045485053, 40991483468586146, 46048654833219020, 47503631088244207, 44047352008447090,
    38957705437406682, 40831035391812440, 45927595958112676, 43927594104124535, 39831098992952154, 35304602440209951,
    39831098992952154, 40830729692992609, 33304387258857255, 37535186216847910, 42592233317099691, 44047352008447090,
    40590947876789535, 35501721595269290, 41830666089926473, 46927211033169775, 45927209180319035, 40830729692992609,
    32453572840152791, 37502795126648558, 38957705437406682, 35501721595269290, 30419653381406912, 34304324068378050,
    39404211141372094, 38404209045485053, 33304387258857255, 0
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 58
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
noncomputable def positiveFloor : ℝ := 17847617 / 200000000000
noncomputable def negativeCeiling : ℝ := 175628027 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 23888841311764432126214144, coefficient := (-23888841311764432126214144) }, { argument := 1101123912635368102579666944, coefficient := (-1101123912635368102579666944) }, { argument := 1100842082398111815969013760, coefficient := (-1100842082398111815969013760) }, { argument := 23885278460337498775093248, coefficient := (-23885278460337498775093248) }, { argument := 1694051810567524701962240, coefficient := (-1694051810567524701962240) }, { argument := 56101236352458715689910272, coefficient := (-56101236352458715689910272) }, { argument := 615326864692649254623117312, coefficient := (-615326864692649254623117312) }, { argument := 56060470193096022839787520, coefficient := (-56060470193096022839787520) }, { argument := 1655536206617645062029312, coefficient := (-1655536206617645062029312) }, { argument := 819256709976047848087617536, coefficient := (-819256709976047848087617536) }, { argument := 37675046544592128042449502208, coefficient := (-37675046544592128042449502208) }, { argument := 37664995821136964654938980352, coefficient := (-37664995821136964654938980352) }, { argument := 819123323753615198617862144, coefficient := (-819123323753615198617862144) }, { argument := 56101236352458715689910272, coefficient := (-56101236352458715689910272) }, { argument := 1867963528332128503029825536, coefficient := (-1867963528332128503029825536) }, { argument := 20486423987717030586628440064, coefficient := (-20486423987717030586628440064) }, { argument := 1866292035258978585024659456, coefficient := (-1866292035258978585024659456) }, { argument := 54815836540689522997854208, coefficient := (-54815836540689522997854208) }, { argument := 23888841311764432126214144, coefficient := (-23888841311764432126214144) }, { argument := 819256709976047848087617536, coefficient := (-819256709976047848087617536) }, { argument := 819255518981393466427179008, coefficient := (-819255518981393466427179008) }, { argument := 23889887632784384136839168, coefficient := (-23889887632784384136839168) }, { argument := 819255518981393466427179008, coefficient := (-819255518981393466427179008) }, { argument := 37674998128929749622316859392, coefficient := (-37674998128929749622316859392) }, { argument := 37664947448085112634195574784, coefficient := (-37664947448085112634195574784) }, { argument := 819122133766359758604861440, coefficient := (-819122133766359758604861440) }, { argument := 615326864692649254623117312, coefficient := (-615326864692649254623117312) }, { argument := 20486423987717030586628440064, coefficient := (-20486423987717030586628440064) }, { argument := 224655804316121086485092892672, coefficient := (-224655804316121086485092892672) }, { argument := 20467932087324094610618187776, coefficient := (-20467932087324094610618187776) }, { argument := 601087474945913420068683776, coefficient := (-601087474945913420068683776) }, { argument := 1101123912635368102579666944, coefficient := (-1101123912635368102579666944) }, { argument := 37675046544592128042449502208, coefficient := (-37675046544592128042449502208) }, { argument := 37674998128929749622316859392, coefficient := (-37674998128929749622316859392) }, { argument := 1101172456697623698858835968, coefficient := (-1101172456697623698858835968) }, { argument := 23889887632784384136839168, coefficient := (-23889887632784384136839168) }, { argument := 1101172456697623698858835968, coefficient := (-1101172456697623698858835968) }, { argument := 1100890615505642793646161920, coefficient := (-1100890615505642793646161920) }, { argument := 23886324665671235357638656, coefficient := (-23886324665671235357638656) }, { argument := 56060470193096022839787520, coefficient := (-56060470193096022839787520) }, { argument := 1866292035258978585024659456, coefficient := (-1866292035258978585024659456) }, { argument := 20467932087324094610618187776, coefficient := (-20467932087324094610618187776) }, { argument := 1864629910898032696295948288, coefficient := (-1864629910898032696295948288) }, { argument := 54775062413051714445770752, coefficient := (-54775062413051714445770752) }, { argument := 1100842082398111815969013760, coefficient := (-1100842082398111815969013760) }, { argument := 37664995821136964654938980352, coefficient := (-37664995821136964654938980352) }, { argument := 37664947448085112634195574784, coefficient := (-37664947448085112634195574784) }, { argument := 1100890615505642793646161920, coefficient := (-1100890615505642793646161920) }, { argument := 1655536206617645062029312, coefficient := (-1655536206617645062029312) }, { argument := 54815836540689522997854208, coefficient := (-54815836540689522997854208) }, { argument := 601087474945913420068683776, coefficient := (-601087474945913420068683776) }, { argument := 54775062413051714445770752, coefficient := (-54775062413051714445770752) }, { argument := 1617066606375009058291712, coefficient := (-1617066606375009058291712) }, { argument := 23885278460337498775093248, coefficient := (-23885278460337498775093248) }, { argument := 819123323753615198617862144, coefficient := (-819123323753615198617862144) }, { argument := 819122133766359758604861440, coefficient := (-819122133766359758604861440) }, { argument := 23886324665671235357638656, coefficient := (-23886324665671235357638656) }, { argument := 633825300114114700748351602688, coefficient := 633825300114114700748351602688 }, { argument := 4499480229611163698899976192, coefficient := 4499480229611163698899976192 }, { argument := 153956844798917511488187924480, coefficient := 153956844798917511488187924480 }, { argument := 153956646459525230963088949248, coefficient := 153956646459525230963088949248 }, { argument := 4499678569003444223998951424, coefficient := 4499678569003444223998951424 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 1461676318510778325833613312, coefficient := 1461676318510778325833613312 }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-24255543809244302022436706058240)
def positiveArguments : Array ℕ := #[
    161013, 56502725, 5147777, 151185, 178543, 16422347,
    16417971, 89257
  ]
def positiveCoefficients : Array ℕ := #[
    48663193248402571826741379072, 533653149461601548714062643200, 48619379132174507258448707584, 1427901953425294623265259520, 3372581915803980261555699712, 155104682085709738932409729024,
    155063351934251663797499461632, 3372034121291967382710910976
  ]
def positiveScales : Array ℕ := #[
    17, 25, 22, 17, 17, 23,
    23, 16
  ]
def negativeArguments : Array ℕ := #[
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    633825300114114700748351602688, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    17296817648977830, 25751817111356441, 22295518127163588, 17205955482387872, 17445912046819186, 23969156987962576,
    23968772507310203, 16445677696806287
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 27975961 / 100000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 48663193248402571826741379072, coefficient := 48663193248402571826741379072 }, { argument := 533653149461601548714062643200, coefficient := 533653149461601548714062643200 }, { argument := 48619379132174507258448707584, coefficient := 48619379132174507258448707584 }, { argument := 1427901953425294623265259520, coefficient := 1427901953425294623265259520 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 3372581915803980261555699712, coefficient := 3372581915803980261555699712 }, { argument := 155104682085709738932409729024, coefficient := 155104682085709738932409729024 }, { argument := 155063351934251663797499461632, coefficient := 155063351934251663797499461632 }, { argument := 3372034121291967382710910976, coefficient := 3372034121291967382710910976 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk2
