import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 15, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-9733791824392627817731939528343552)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    16485, 1582958153, 891289, 932036511, 891289, 891289,
    293433, 16485, 17427838971, 304965456369, 304965605943, 17427689397,
    348826631391, 4580919, 257355, 592033856673, 13914327, 348826631391,
    13914327, 13914327, 4580919, 257355, 58957, 58957,
    13975215345, 5607, 315, 23702158095, 17031, 13975215345,
    17031, 17031, 5607, 315, 63419, 63419,
    1113, 21151713007583, 827959143, 778838035635361, 13029462303, 392191173,
    12460871552992439, 392191173, 392191173, 33597710487, 392191173, 13029462303,
    33597710487, 338964450722633, 392191173, 392191173, 827959143, 24095484334739207,
    9345, 525, 85490651394335319, 28385, 12047741950084945, 28385,
    28385, 9345, 525, 2645011469835703
  ]
def negativeCoefficients : Array ℕ := #[
    155696422940212202695557120, 934413565689054965904688807936, 4208993300150403212869894144, 275088623772322837048816828416, 4208993300150403212869894144, 4208993300150403212869894144,
    2771396328335777207980916736, 155696422940212202695557120, 160743442627929310094130413568, 5625619724960979583327801442304, 5625622484114277664360274853888, 160742063051280269577893707776,
    6434715595363995495550320377856, 43265556692681464565358133248, 2430649252397835087941468160, 21842194074036145657716079067136, 65708551456488141877351022592, 6434715595363995495550320377856,
    65708551456488141877351022592, 65708551456488141877351022592, 43265556692681464565358133248, 2430649252397835087941468160, 1140394232752315076050432294912, 1140394232752315076050432294912,
    515594441688387073633985495040, 1694611767644806445644382208, 95202908294652047508111360, 1748910577492272502055978926080, 2573651954232093684302610432, 515594441688387073633985495040,
    2573651954232093684302610432, 2573651954232093684302610432, 1694611767644806445644382208, 95202908294652047508111360, 2453403729732485364182111223808, 2453403729732485364182111223808,
    86114203982789265372670328832, 381035387276793888135993884672, 3818287603602222296724406272, 14030298748277523537844422836224, 30043894565185907018963091456, 3617325098149473754791542784,
    14029694120692090520279434919936, 3617325098149473754791542784, 3617325098149473754791542784, 154942091704069125830237749248, 3617325098149473754791542784, 30043894565185907018963091456,
    154942091704069125830237749248, 381640043491573708098205908992, 3617325098149473754791542784, 3617325098149473754791542784, 3818287603602222296724406272, 13564551783905389543944915779584,
    2824352946074677409407303680, 158671513824420079180185600, 48126958220398689617540208918528, 4289419923720156140504350720, 13564551539264612780463546695680, 4289419923720156140504350720,
    4289419923720156140504350720, 2824352946074677409407303680, 158671513824420079180185600, 11912072669942759951611029618688
  ]
def negativeScales : Array ℕ := #[
    14, 30, 19, 29, 19, 19,
    18, 14, 34, 38, 38, 34,
    38, 22, 17, 39, 23, 38,
    23, 23, 22, 17, 15, 15,
    33, 12, 8, 34, 14, 33,
    14, 14, 12, 8, 15, 15,
    10, 44, 29, 49, 33, 28,
    53, 28, 28, 34, 28, 33,
    34, 48, 28, 28, 29, 54,
    13, 9, 56, 14, 53, 14,
    14, 13, 9, 51
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14008866266557750, 30559975970955651, 19765533775481114, 29795811230887892, 19765533775481114, 19765533775481114,
    18162671602636786, 14008866266557750, 34020674637149085, 38149854880706986, 38149855588294061, 34020662255201190,
    38343719231550865, 22127205622611998, 17973400301926033, 39106888725455693, 23730067795286271, 38343719231550865,
    23730067795286271, 23730067795286271, 22127205622611998, 17973400301926033, 15847375496619654, 15847375496619654,
    33702151462770997, 12453013354466367, 8299208018387279, 34464299372183238, 14055875526996034, 33702151462770997,
    14055875526996034, 14055875526996034, 12453013354466367, 8299208018387279, 15952627519441893, 15952627519441893,
    10120237877341960, 44265839740732905, 29624984336441376, 49468316670214514, 33601058497190593, 28546981824430190,
    53468254496768975, 28546981824430190, 28546981824430190, 34967643886900966, 28546981824430190, 33601058497190593,
    34967643886900966, 48268127305455934, 28546981824430190, 28546981824430190, 29624984336441376, 54419612318665783,
    13189978948632521, 9036173612553486, 56246616184694196, 14792841121720145, 53419612292646343, 14792841121720145,
    14792841121720145, 13189978948632521, 9036173612553486, 51232195401770421
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 20018904709 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 155696422940212202695557120, coefficient := (-155696422940212202695557120) }, { argument := 934413565689054965904688807936, coefficient := (-934413565689054965904688807936) }, { argument := 4208993300150403212869894144, coefficient := (-4208993300150403212869894144) }, { argument := 275088623772322837048816828416, coefficient := (-275088623772322837048816828416) }, { argument := 4208993300150403212869894144, coefficient := (-4208993300150403212869894144) }, { argument := 4208993300150403212869894144, coefficient := (-4208993300150403212869894144) }, { argument := 2771396328335777207980916736, coefficient := (-2771396328335777207980916736) }, { argument := 155696422940212202695557120, coefficient := (-155696422940212202695557120) }, { argument := 160743442627929310094130413568, coefficient := (-160743442627929310094130413568) }, { argument := 5625619724960979583327801442304, coefficient := (-5625619724960979583327801442304) }, { argument := 5625622484114277664360274853888, coefficient := (-5625622484114277664360274853888) }, { argument := 160742063051280269577893707776, coefficient := (-160742063051280269577893707776) }, { argument := 6434715595363995495550320377856, coefficient := (-6434715595363995495550320377856) }, { argument := 43265556692681464565358133248, coefficient := (-43265556692681464565358133248) }, { argument := 2430649252397835087941468160, coefficient := (-2430649252397835087941468160) }, { argument := 21842194074036145657716079067136, coefficient := (-21842194074036145657716079067136) }, { argument := 65708551456488141877351022592, coefficient := (-65708551456488141877351022592) }, { argument := 6434715595363995495550320377856, coefficient := (-6434715595363995495550320377856) }, { argument := 65708551456488141877351022592, coefficient := (-65708551456488141877351022592) }, { argument := 65708551456488141877351022592, coefficient := (-65708551456488141877351022592) }, { argument := 43265556692681464565358133248, coefficient := (-43265556692681464565358133248) }, { argument := 2430649252397835087941468160, coefficient := (-2430649252397835087941468160) }, { argument := 1140394232752315076050432294912, coefficient := (-1140394232752315076050432294912) }, { argument := 1140394232752315076050432294912, coefficient := (-1140394232752315076050432294912) }, { argument := 515594441688387073633985495040, coefficient := (-515594441688387073633985495040) }, { argument := 1694611767644806445644382208, coefficient := (-1694611767644806445644382208) }, { argument := 95202908294652047508111360, coefficient := (-95202908294652047508111360) }, { argument := 1748910577492272502055978926080, coefficient := (-1748910577492272502055978926080) }, { argument := 2573651954232093684302610432, coefficient := (-2573651954232093684302610432) }, { argument := 515594441688387073633985495040, coefficient := (-515594441688387073633985495040) }, { argument := 2573651954232093684302610432, coefficient := (-2573651954232093684302610432) }, { argument := 2573651954232093684302610432, coefficient := (-2573651954232093684302610432) }, { argument := 1694611767644806445644382208, coefficient := (-1694611767644806445644382208) }, { argument := 95202908294652047508111360, coefficient := (-95202908294652047508111360) }, { argument := 2453403729732485364182111223808, coefficient := (-2453403729732485364182111223808) }, { argument := 2453403729732485364182111223808, coefficient := (-2453403729732485364182111223808) }, { argument := 86114203982789265372670328832, coefficient := (-86114203982789265372670328832) }, { argument := 381035387276793888135993884672, coefficient := (-381035387276793888135993884672) }, { argument := 3818287603602222296724406272, coefficient := (-3818287603602222296724406272) }, { argument := 14030298748277523537844422836224, coefficient := (-14030298748277523537844422836224) }, { argument := 30043894565185907018963091456, coefficient := (-30043894565185907018963091456) }, { argument := 3617325098149473754791542784, coefficient := (-3617325098149473754791542784) }, { argument := 14029694120692090520279434919936, coefficient := (-14029694120692090520279434919936) }, { argument := 3617325098149473754791542784, coefficient := (-3617325098149473754791542784) }, { argument := 3617325098149473754791542784, coefficient := (-3617325098149473754791542784) }, { argument := 154942091704069125830237749248, coefficient := (-154942091704069125830237749248) }, { argument := 3617325098149473754791542784, coefficient := (-3617325098149473754791542784) }, { argument := 30043894565185907018963091456, coefficient := (-30043894565185907018963091456) }, { argument := 154942091704069125830237749248, coefficient := (-154942091704069125830237749248) }, { argument := 381640043491573708098205908992, coefficient := (-381640043491573708098205908992) }, { argument := 3617325098149473754791542784, coefficient := (-3617325098149473754791542784) }, { argument := 3617325098149473754791542784, coefficient := (-3617325098149473754791542784) }, { argument := 3818287603602222296724406272, coefficient := (-3818287603602222296724406272) }, { argument := 13564551783905389543944915779584, coefficient := (-13564551783905389543944915779584) }, { argument := 2824352946074677409407303680, coefficient := (-2824352946074677409407303680) }, { argument := 158671513824420079180185600, coefficient := (-158671513824420079180185600) }, { argument := 48126958220398689617540208918528, coefficient := (-48126958220398689617540208918528) }, { argument := 4289419923720156140504350720, coefficient := (-4289419923720156140504350720) }, { argument := 13564551539264612780463546695680, coefficient := (-13564551539264612780463546695680) }, { argument := 4289419923720156140504350720, coefficient := (-4289419923720156140504350720) }, { argument := 4289419923720156140504350720, coefficient := (-4289419923720156140504350720) }, { argument := 2824352946074677409407303680, coefficient := (-2824352946074677409407303680) }, { argument := 158671513824420079180185600, coefficient := (-158671513824420079180185600) }, { argument := 11912072669942759951611029618688, coefficient := (-11912072669942759951611029618688) }] }

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

end TermShard6


end Parent1

namespace Parent1

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1258812861570774744101904432758784)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2645010479178313, 28263998007, 285957, 16065, 47954836041, 868581,
    28263998007, 868581, 868581, 285957, 16065, 58957,
    58957, 27678687, 2055, 2055, 483, 315,
    525, 16065, 525, 16485, 525, 16065,
    9135, 16485, 257355, 315, 525, 16065,
    525, 315, 525, 8085, 9135, 315,
    203437809, 3559908051, 3559909797, 203436063, 2174058579, 9345,
    525, 3688080557, 28385, 2174058579, 28385, 28385,
    9345, 525, 203437809, 3559908051, 3559909797, 203436063,
    13975215345, 5607, 315, 23702158095, 17031, 13975215345,
    17031, 17031, 5607, 315
  ]
def negativeCoefficients : Array ℕ := #[
    11912068208418507495782899253248, 521378737734965827971487629312, 2700787504683910272745734144, 151729635094601700716052480, 1769221175090059932801813184512, 4101757802057399309357285376,
    521378737734965827971487629312, 4101757802057399309357285376, 4101757802057399309357285376, 2700787504683910272745734144, 151729635094601700716052480, 1140394232752315076050432294912,
    1140394232752315076050432294912, 261417807557279543341879394304, 79498961897858014528678133760, 79498961897858014528678133760, 74740629871854834097034625024, 5950181768415752969256960,
    158671513824420079180185600, 151729635094601700716052480, 4958484807013127474380800, 155696422940212202695557120, 4958484807013127474380800, 151729635094601700716052480,
    86277635642028418054225920, 155696422940212202695557120, 2430649252397835087941468160, 95202908294652047508111360, 158671513824420079180185600, 151729635094601700716052480,
    4958484807013127474380800, 95202908294652047508111360, 4958484807013127474380800, 152721332056004326210928640, 86277635642028418054225920, 5950181768415752969256960,
    3752765197539205683131449344, 131337425485470340466796920832, 131337489901500645860551163904, 3752732989524052986254327808, 20052151104032829522504056832, 88261029564833669043978240,
    4958484807013127474380800, 68033078158203172180157530112, 134044372616254879390760960, 20052151104032829522504056832, 134044372616254879390760960, 134044372616254879390760960,
    88261029564833669043978240, 4958484807013127474380800, 3752765197539205683131449344, 131337425485470340466796920832, 131337489901500645860551163904, 3752732989524052986254327808,
    515594441688387073633985495040, 1694611767644806445644382208, 95202908294652047508111360, 1748910577492272502055978926080, 2573651954232093684302610432, 515594441688387073633985495040,
    2573651954232093684302610432, 2573651954232093684302610432, 1694611767644806445644382208, 95202908294652047508111360
  ]
def negativeScales : Array ℕ := #[
    51, 34, 18, 13, 35, 19,
    34, 19, 19, 18, 13, 15,
    15, 24, 11, 11, 8, 8,
    9, 13, 9, 14, 9, 13,
    13, 14, 17, 8, 9, 13,
    9, 8, 9, 12, 13, 8,
    27, 31, 31, 27, 31, 13,
    9, 31, 14, 31, 14, 14,
    13, 9, 27, 31, 31, 27,
    33, 12, 8, 34, 14, 33,
    14, 14, 12, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    51232194861426159, 34718246501595563, 18125438696437810, 13971633375310864, 35480957261104856, 19728300869106443,
    34718246501595563, 19728300869106443, 19728300869106443, 18125438696437810, 13971633375310864, 15847375496619654,
    15847375496619654, 24722272171486650, 11004922678569046, 11004922678569046, 8915879384625971, 8299208018387279,
    9036173612553486, 13971633375310864, 9036173612553486, 14008866266557750, 9036173612553486, 13971633375310864,
    13157189013514852, 14008866266557750, 17973400301926033, 8299208018387279, 9036173612553486, 13971633375310864,
    9036173612553486, 8299208018387279, 9036173612553486, 12981032075801390, 13157189013514852, 8299208018387279,
    27600012588682020, 31729192832375999, 31729193539963075, 27600000206734123, 31017743667623897, 13189978948632521,
    9036173612553486, 31780223022632694, 14792841121720145, 31017743667623897, 14792841121720145, 14792841121720145,
    13189978948632521, 9036173612553486, 27600012588682020, 31729192832375999, 31729193539963075, 27600000206734123,
    33702151462770997, 12453013354466367, 8299208018387279, 34464299372183238, 14055875526996034, 33702151462770997,
    14055875526996034, 14055875526996034, 12453013354466367, 8299208018387279
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 10476671057 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 11912068208418507495782899253248, coefficient := (-11912068208418507495782899253248) }, { argument := 521378737734965827971487629312, coefficient := (-521378737734965827971487629312) }, { argument := 2700787504683910272745734144, coefficient := (-2700787504683910272745734144) }, { argument := 151729635094601700716052480, coefficient := (-151729635094601700716052480) }, { argument := 1769221175090059932801813184512, coefficient := (-1769221175090059932801813184512) }, { argument := 4101757802057399309357285376, coefficient := (-4101757802057399309357285376) }, { argument := 521378737734965827971487629312, coefficient := (-521378737734965827971487629312) }, { argument := 4101757802057399309357285376, coefficient := (-4101757802057399309357285376) }, { argument := 4101757802057399309357285376, coefficient := (-4101757802057399309357285376) }, { argument := 2700787504683910272745734144, coefficient := (-2700787504683910272745734144) }, { argument := 151729635094601700716052480, coefficient := (-151729635094601700716052480) }, { argument := 1140394232752315076050432294912, coefficient := (-1140394232752315076050432294912) }, { argument := 1140394232752315076050432294912, coefficient := (-1140394232752315076050432294912) }, { argument := 261417807557279543341879394304, coefficient := (-261417807557279543341879394304) }, { argument := 79498961897858014528678133760, coefficient := (-79498961897858014528678133760) }, { argument := 79498961897858014528678133760, coefficient := (-79498961897858014528678133760) }, { argument := 74740629871854834097034625024, coefficient := (-74740629871854834097034625024) }, { argument := 5950181768415752969256960, coefficient := (-5950181768415752969256960) }, { argument := 158671513824420079180185600, coefficient := (-158671513824420079180185600) }, { argument := 151729635094601700716052480, coefficient := (-151729635094601700716052480) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 155696422940212202695557120, coefficient := (-155696422940212202695557120) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 151729635094601700716052480, coefficient := (-151729635094601700716052480) }, { argument := 86277635642028418054225920, coefficient := (-86277635642028418054225920) }, { argument := 155696422940212202695557120, coefficient := (-155696422940212202695557120) }, { argument := 2430649252397835087941468160, coefficient := (-2430649252397835087941468160) }, { argument := 95202908294652047508111360, coefficient := (-95202908294652047508111360) }, { argument := 158671513824420079180185600, coefficient := (-158671513824420079180185600) }, { argument := 151729635094601700716052480, coefficient := (-151729635094601700716052480) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 95202908294652047508111360, coefficient := (-95202908294652047508111360) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 152721332056004326210928640, coefficient := (-152721332056004326210928640) }, { argument := 86277635642028418054225920, coefficient := (-86277635642028418054225920) }, { argument := 5950181768415752969256960, coefficient := (-5950181768415752969256960) }, { argument := 3752765197539205683131449344, coefficient := (-3752765197539205683131449344) }, { argument := 131337425485470340466796920832, coefficient := (-131337425485470340466796920832) }, { argument := 131337489901500645860551163904, coefficient := (-131337489901500645860551163904) }, { argument := 3752732989524052986254327808, coefficient := (-3752732989524052986254327808) }, { argument := 20052151104032829522504056832, coefficient := (-20052151104032829522504056832) }, { argument := 88261029564833669043978240, coefficient := (-88261029564833669043978240) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 68033078158203172180157530112, coefficient := (-68033078158203172180157530112) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 20052151104032829522504056832, coefficient := (-20052151104032829522504056832) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 88261029564833669043978240, coefficient := (-88261029564833669043978240) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 3752765197539205683131449344, coefficient := (-3752765197539205683131449344) }, { argument := 131337425485470340466796920832, coefficient := (-131337425485470340466796920832) }, { argument := 131337489901500645860551163904, coefficient := (-131337489901500645860551163904) }, { argument := 3752732989524052986254327808, coefficient := (-3752732989524052986254327808) }, { argument := 515594441688387073633985495040, coefficient := (-515594441688387073633985495040) }, { argument := 1694611767644806445644382208, coefficient := (-1694611767644806445644382208) }, { argument := 95202908294652047508111360, coefficient := (-95202908294652047508111360) }, { argument := 1748910577492272502055978926080, coefficient := (-1748910577492272502055978926080) }, { argument := 2573651954232093684302610432, coefficient := (-2573651954232093684302610432) }, { argument := 515594441688387073633985495040, coefficient := (-515594441688387073633985495040) }, { argument := 2573651954232093684302610432, coefficient := (-2573651954232093684302610432) }, { argument := 2573651954232093684302610432, coefficient := (-2573651954232093684302610432) }, { argument := 1694611767644806445644382208, coefficient := (-1694611767644806445644382208) }, { argument := 95202908294652047508111360, coefficient := (-95202908294652047508111360) }] }

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

end TermShard7


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15
