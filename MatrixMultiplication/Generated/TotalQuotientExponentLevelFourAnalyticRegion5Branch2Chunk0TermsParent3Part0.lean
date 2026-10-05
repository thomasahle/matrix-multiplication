import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 0, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk0

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
def constantNumerator : ℤ := 11757274452890371334273381695488
def positiveArguments : Array ℕ := #[
    1, 238171, 8150425, 8150449, 238171, 101353
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 2249461495183092540382380032, 76978587682285656181676441600, 76978814355876833924646699008, 2249461495183092540382380032, 957252020276574302687461376
  ]
def positiveScales : Array ℕ := #[
    0, 17, 22, 22, 17, 16
  ]
def negativeArguments : Array ℕ := #[
    21045027731, 977926077093, 488949581885, 10526443687, 638597935, 33073338473,
    1425762833305, 132185976703, 1267556467, 720179703425, 33465506492775, 16732292747375,
    360224333725, 33073338473, 211565991837, 36651528133405, 3381991512903, 16397487557,
    21045027731, 720179703425, 720181824089, 21045027731, 720181824089, 33465605036367,
    16732342017815, 360225394453, 1425762833305, 36651528133405, 198062901556975, 36619686369395,
    1414242454265, 977926077093, 33465506492775, 33465605036367, 977926077093, 21045027731,
    977926077093, 488949581885, 10526443687, 132185976703, 3381991512903, 36619686369395,
    844731858813, 131072532179, 488949581885, 16732292747375, 16732342017815, 488949581885,
    1267556467, 16397487557, 1414242454265, 131072532179, 78619289, 10526443687,
    360224333725, 360225394453, 10526443687, 1
  ]
def negativeCoefficients : Array ℕ := #[
    11847297380916669366403072, 550523439548990718021206016, 550508288695061455296266240, 11851721966577427507314688, 1437994711052784112762880, 37237268705725272295473152,
    401316560299443787745198080, 37207044713952241587847168, 1427141708113065602449408, 405425130498078040234393600, 18839405321328300561059020800, 18838886845533025690714112000,
    405576543783423798830694400, 37237268705725272295473152, 952808522001382598510641152, 10316488027760125550453063680, 951945982330008175921594368, 36923859425758772394459136,
    11847297380916669366403072, 405425130498078040234393600, 405426324325778062487584768, 11847297380916669366403072, 405426324325778062487584768, 18839460796438826929832853504,
    18838942319116831785809346560, 405577738056980184193564672, 401316560299443787745198080, 10316488027760125550453063680, 111499501205988980252947251200, 10307525367976984596048773120,
    398073861877461858218147840, 550523439548990718021206016, 18839405321328300561059020800, 18839460796438826929832853504, 550523439548990718021206016, 11847297380916669366403072,
    550523439548990718021206016, 550508288695061455296266240, 11851721966577427507314688, 37207044713952241587847168, 951945982330008175921594368, 10307525367976984596048773120,
    951083521144553309378445312, 36893637942490734132199424, 550508288695061455296266240, 18838886845533025690714112000, 18838942319116831785809346560, 550508288695061455296266240,
    1427141708113065602449408, 36923859425758772394459136, 398073861877461858218147840, 36893637942490734132199424, 1416279202578133340389376, 11851721966577427507314688,
    405576543783423798830694400, 405577738056980184193564672, 11851721966577427507314688, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    34, 39, 38, 33, 29, 34,
    40, 36, 30, 39, 44, 43,
    38, 34, 37, 45, 41, 33,
    34, 39, 39, 34, 39, 44,
    43, 38, 40, 45, 47, 45,
    40, 39, 44, 44, 39, 34,
    39, 38, 33, 36, 41, 45,
    39, 36, 38, 43, 43, 38,
    30, 33, 40, 36, 26, 33,
    38, 38, 33, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 17861638233839341, 22958443858528436, 22958448106727710, 17861638233839341, 16629029266951434
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    34292760359590835, 39830934458764522, 38830894754073400, 33293299059337971, 29250332646848628, 34944949639150447,
    40374871157126378, 36943778186007494, 30239402871705060, 39389565984887747, 44927740089985630, 43927700385290537,
    38390104684634883, 34944949639150447, 37622316783930067, 45058938584269289, 41621010177972157, 33932755736927689,
    34292760359590835, 39389565984887747, 39389570233087075, 34292760359590835, 39389570233087075, 44927744338185482,
    43927704633490389, 38390108932834211, 40374871157126378, 45058938584269289, 47492952007984632, 45057684668710936,
    40363166612105904, 39830934458764522, 44927740089985630, 44927744338185482, 39830934458764522, 34292760359590835,
    39830934458764522, 38830894754073400, 33293299059337971, 36943778186007494, 41621010177972157, 45057684668710936,
    39619702506642355, 36931574434558713, 38830894754073400, 43927700385290537, 43927704633490389, 38830894754073400,
    30239402871705060, 33932755736927689, 40363166612105904, 36931574434558713, 26228379980901396, 33293299059337971,
    38390104684634883, 38390108932834211, 33293299059337971, 0
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
noncomputable def positiveFloor : ℝ := 10926339 / 250000000000
noncomputable def negativeCeiling : ℝ := 34619797 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 11847297380916669366403072, coefficient := (-11847297380916669366403072) }, { argument := 550523439548990718021206016, coefficient := (-550523439548990718021206016) }, { argument := 550508288695061455296266240, coefficient := (-550508288695061455296266240) }, { argument := 11851721966577427507314688, coefficient := (-11851721966577427507314688) }, { argument := 1437994711052784112762880, coefficient := (-1437994711052784112762880) }, { argument := 37237268705725272295473152, coefficient := (-37237268705725272295473152) }, { argument := 401316560299443787745198080, coefficient := (-401316560299443787745198080) }, { argument := 37207044713952241587847168, coefficient := (-37207044713952241587847168) }, { argument := 1427141708113065602449408, coefficient := (-1427141708113065602449408) }, { argument := 405425130498078040234393600, coefficient := (-405425130498078040234393600) }, { argument := 18839405321328300561059020800, coefficient := (-18839405321328300561059020800) }, { argument := 18838886845533025690714112000, coefficient := (-18838886845533025690714112000) }, { argument := 405576543783423798830694400, coefficient := (-405576543783423798830694400) }, { argument := 37237268705725272295473152, coefficient := (-37237268705725272295473152) }, { argument := 952808522001382598510641152, coefficient := (-952808522001382598510641152) }, { argument := 10316488027760125550453063680, coefficient := (-10316488027760125550453063680) }, { argument := 951945982330008175921594368, coefficient := (-951945982330008175921594368) }, { argument := 36923859425758772394459136, coefficient := (-36923859425758772394459136) }, { argument := 11847297380916669366403072, coefficient := (-11847297380916669366403072) }, { argument := 405425130498078040234393600, coefficient := (-405425130498078040234393600) }, { argument := 405426324325778062487584768, coefficient := (-405426324325778062487584768) }, { argument := 11847297380916669366403072, coefficient := (-11847297380916669366403072) }, { argument := 405426324325778062487584768, coefficient := (-405426324325778062487584768) }, { argument := 18839460796438826929832853504, coefficient := (-18839460796438826929832853504) }, { argument := 18838942319116831785809346560, coefficient := (-18838942319116831785809346560) }, { argument := 405577738056980184193564672, coefficient := (-405577738056980184193564672) }, { argument := 401316560299443787745198080, coefficient := (-401316560299443787745198080) }, { argument := 10316488027760125550453063680, coefficient := (-10316488027760125550453063680) }, { argument := 111499501205988980252947251200, coefficient := (-111499501205988980252947251200) }, { argument := 10307525367976984596048773120, coefficient := (-10307525367976984596048773120) }, { argument := 398073861877461858218147840, coefficient := (-398073861877461858218147840) }, { argument := 550523439548990718021206016, coefficient := (-550523439548990718021206016) }, { argument := 18839405321328300561059020800, coefficient := (-18839405321328300561059020800) }, { argument := 18839460796438826929832853504, coefficient := (-18839460796438826929832853504) }, { argument := 550523439548990718021206016, coefficient := (-550523439548990718021206016) }, { argument := 11847297380916669366403072, coefficient := (-11847297380916669366403072) }, { argument := 550523439548990718021206016, coefficient := (-550523439548990718021206016) }, { argument := 550508288695061455296266240, coefficient := (-550508288695061455296266240) }, { argument := 11851721966577427507314688, coefficient := (-11851721966577427507314688) }, { argument := 37207044713952241587847168, coefficient := (-37207044713952241587847168) }, { argument := 951945982330008175921594368, coefficient := (-951945982330008175921594368) }, { argument := 10307525367976984596048773120, coefficient := (-10307525367976984596048773120) }, { argument := 951083521144553309378445312, coefficient := (-951083521144553309378445312) }, { argument := 36893637942490734132199424, coefficient := (-36893637942490734132199424) }, { argument := 550508288695061455296266240, coefficient := (-550508288695061455296266240) }, { argument := 18838886845533025690714112000, coefficient := (-18838886845533025690714112000) }, { argument := 18838942319116831785809346560, coefficient := (-18838942319116831785809346560) }, { argument := 550508288695061455296266240, coefficient := (-550508288695061455296266240) }, { argument := 1427141708113065602449408, coefficient := (-1427141708113065602449408) }, { argument := 36923859425758772394459136, coefficient := (-36923859425758772394459136) }, { argument := 398073861877461858218147840, coefficient := (-398073861877461858218147840) }, { argument := 36893637942490734132199424, coefficient := (-36893637942490734132199424) }, { argument := 1416279202578133340389376, coefficient := (-1416279202578133340389376) }, { argument := 11851721966577427507314688, coefficient := (-11851721966577427507314688) }, { argument := 405576543783423798830694400, coefficient := (-405576543783423798830694400) }, { argument := 405577738056980184193564672, coefficient := (-405577738056980184193564672) }, { argument := 11851721966577427507314688, coefficient := (-11851721966577427507314688) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 2249461495183092540382380032, coefficient := 2249461495183092540382380032 }, { argument := 76978587682285656181676441600, coefficient := 76978587682285656181676441600 }, { argument := 76978814355876833924646699008, coefficient := 76978814355876833924646699008 }, { argument := 2249461495183092540382380032, coefficient := 2249461495183092540382380032 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 957252020276574302687461376, coefficient := 957252020276574302687461376 }] }

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
def constantNumerator : ℤ := (-9962888857340320181758342463488)
def positiveArguments : Array ℕ := #[
    2603653, 439805, 2601377, 100529, 88361, 4105983,
    2052935, 44197
  ]
def positiveCoefficients : Array ℕ := #[
    24590807320446000739150462976, 265845810047805992090824867840, 24569311108215978114137718784, 949469560312805127375290368, 1669092099171378882909569024, 77559825993730217853868572672,
    77557691484079960774231982080, 1669715451547117676077776896
  ]
def positiveScales : Array ℕ := #[
    21, 18, 21, 16, 16, 21,
    20, 15
  ]
def negativeArguments : Array ℕ := #[
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    316912650057057350374175801344, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    21312105756484683, 18746504480240692, 21310844063805739, 16617252215850361, 16431122125617886, 21969296222705614,
    20969256518016003, 15431660825365022
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
noncomputable def positiveFloor : ℝ := 113516541 / 1000000000000
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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 24590807320446000739150462976, coefficient := 24590807320446000739150462976 }, { argument := 265845810047805992090824867840, coefficient := 265845810047805992090824867840 }, { argument := 24569311108215978114137718784, coefficient := 24569311108215978114137718784 }, { argument := 949469560312805127375290368, coefficient := 949469560312805127375290368 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 1669092099171378882909569024, coefficient := 1669092099171378882909569024 }, { argument := 77559825993730217853868572672, coefficient := 77559825993730217853868572672 }, { argument := 77557691484079960774231982080, coefficient := 77557691484079960774231982080 }, { argument := 1669715451547117676077776896, coefficient := 1669715451547117676077776896 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk0
