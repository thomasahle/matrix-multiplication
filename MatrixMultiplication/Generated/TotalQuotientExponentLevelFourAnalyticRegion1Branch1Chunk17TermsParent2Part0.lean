import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 17, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17

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
def constantNumerator : ℤ := (-36948787910282596541193893370134528)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2372079, 363655497, 4343, 3620193017, 687, 329,
    8685, 4319, 687, 133293, 8527, 11364255,
    8685, 329, 8527, 329, 8685, 2173,
    2372079, 14862042547239623, 9356145415, 578684732928512161, 97954756675, 4338334205,
    578684725378765783, 4338334205, 8450176075, 159768306389, 8452174923, 97954756675,
    159768306389, 14862098432139457, 8450176075, 8452174923, 9356145415, 93298476839211279,
    182110215, 150891321, 681486914188061417, 1014614055, 186582172211442425, 4063659369,
    4063659369, 2908560291, 150891321, 2077, 2345, 1005,
    26465, 2345, 1005, 2345, 2345, 97217,
    603, 26465, 97217, 2077, 2345, 603,
    2345, 182110215, 1326767855, 364220675
  ]
def negativeCoefficients : Array ℕ := #[
    44807305457275780595435175936, 6869258121376411265601160347648, 168011674706762704183965515776, 68383512659998158895558927843328, 106308100873632031106962292736, 6363785514451407975653310464,
    167992331893648870117170216960, 167083219677298668977791172608, 106308100873632031106962292736, 2578261588382284265345765081088, 164936167421663087563513004032, 6869270645092323835900267069440,
    167992331893648870117170216960, 6363785514451407975653310464, 164936167421663087563513004032, 6363785514451407975653310464, 167992331893648870117170216960, 168127731585445708584737308672,
    44807305457275780595435175936, 4183293079857051458625169522688, 21573802498364505424218030080, 162885271723865147797227874287616, 225868290898277174146079129600, 20007035196463797252726456320,
    162885269598800461878318384283648, 20007035196463797252726456320, 19484779429163561195562598400, 736801264761974410595224518656, 19489388458850841969291165696, 225868290898277174146079129600,
    736801264761974410595224518656, 4183308810057930711118529953792, 19484779429163561195562598400, 19489388458850841969291165696, 21573802498364505424218030080, 52522373190913345944201669378048,
    13437362117252889169373429760, 695863395357738903413981184, 191821513299701411325831966359552, 18716325806173667057341562880, 52518212577839363677351627980800, 18740321095668761502286872576,
    18740321095668761502286872576, 13413366827757794724428120064, 695863395357738903413981184, 156933682958724049741545472, 177183190437269088417873920, 151871306089087790072463360,
    1999638863506322569287434240, 177183190437269088417873920, 151871306089087790072463360, 177183190437269088417873920, 177183190437269088417873920, 7345508837842212779838144512,
    182245567306905348086956032, 1999638863506322569287434240, 7345508837842212779838144512, 156933682958724049741545472, 177183190437269088417873920, 182245567306905348086956032,
    177183190437269088417873920, 13437362117252889169373429760, 48949094132819167381144207360, 13437371156157485287053721600
  ]
def negativeScales : Array ℕ := #[
    21, 28, 12, 31, 9, 8,
    13, 12, 9, 17, 13, 23,
    13, 8, 13, 8, 13, 11,
    21, 53, 33, 59, 36, 32,
    59, 32, 32, 37, 32, 36,
    37, 53, 32, 32, 33, 56,
    27, 27, 59, 29, 57, 31,
    31, 31, 27, 11, 11, 9,
    14, 11, 9, 11, 11, 16,
    9, 14, 16, 11, 11, 9,
    11, 27, 30, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    21177720627694738, 28437997143276290, 12084476237453893, 31753419473427955, 9424166288818118, 8361943773735243,
    13084310133597756, 12076481601207023, 9424166288818118, 17024241492444666, 13057822541282478, 23437999773529230,
    13084310133597756, 8361943773735243, 13057822541282478, 8361943773735243, 13084310133597756, 11085472459181283,
    21177720627694738, 53722481922908787, 33123267138492877, 59005555195989139, 36511396500221515, 32014494049763656,
    59005555177167177, 32014494049763656, 32976334273057804, 37217190289634340, 32976675495278989, 36511396500221515,
    37217190289634340, 53722487347783345, 32976334273057804, 32976675495278989, 33123267138492877, 56372703046493979,
    27440236607918430, 27168934586101003, 59241463567962684, 29918283910762953, 57372588757415942, 31920132335354063,
    31920132335354063, 31437658063816650, 27168934586101003, 11020285500844648, 11195372207402739, 9972979801353332,
    14691798033581851, 11195372207402739, 9972979801353332, 11195372207402739, 11195372207402739, 16568920994526853,
    9236014191900085, 14691798033581851, 16568920994526853, 11020285500844648, 11195372207402739, 9236014191900085,
    11195372207402739, 27440236607918430, 30305268817958421, 28440237578375156
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
noncomputable def negativeCeiling : ℝ := 9553516681 / 20000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 44807305457275780595435175936, coefficient := (-44807305457275780595435175936) }, { argument := 6869258121376411265601160347648, coefficient := (-6869258121376411265601160347648) }, { argument := 168011674706762704183965515776, coefficient := (-168011674706762704183965515776) }, { argument := 68383512659998158895558927843328, coefficient := (-68383512659998158895558927843328) }, { argument := 106308100873632031106962292736, coefficient := (-106308100873632031106962292736) }, { argument := 6363785514451407975653310464, coefficient := (-6363785514451407975653310464) }, { argument := 167992331893648870117170216960, coefficient := (-167992331893648870117170216960) }, { argument := 167083219677298668977791172608, coefficient := (-167083219677298668977791172608) }, { argument := 106308100873632031106962292736, coefficient := (-106308100873632031106962292736) }, { argument := 2578261588382284265345765081088, coefficient := (-2578261588382284265345765081088) }, { argument := 164936167421663087563513004032, coefficient := (-164936167421663087563513004032) }, { argument := 6869270645092323835900267069440, coefficient := (-6869270645092323835900267069440) }, { argument := 167992331893648870117170216960, coefficient := (-167992331893648870117170216960) }, { argument := 6363785514451407975653310464, coefficient := (-6363785514451407975653310464) }, { argument := 164936167421663087563513004032, coefficient := (-164936167421663087563513004032) }, { argument := 6363785514451407975653310464, coefficient := (-6363785514451407975653310464) }, { argument := 167992331893648870117170216960, coefficient := (-167992331893648870117170216960) }, { argument := 168127731585445708584737308672, coefficient := (-168127731585445708584737308672) }, { argument := 44807305457275780595435175936, coefficient := (-44807305457275780595435175936) }, { argument := 4183293079857051458625169522688, coefficient := (-4183293079857051458625169522688) }, { argument := 21573802498364505424218030080, coefficient := (-21573802498364505424218030080) }, { argument := 162885271723865147797227874287616, coefficient := (-162885271723865147797227874287616) }, { argument := 225868290898277174146079129600, coefficient := (-225868290898277174146079129600) }, { argument := 20007035196463797252726456320, coefficient := (-20007035196463797252726456320) }, { argument := 162885269598800461878318384283648, coefficient := (-162885269598800461878318384283648) }, { argument := 20007035196463797252726456320, coefficient := (-20007035196463797252726456320) }, { argument := 19484779429163561195562598400, coefficient := (-19484779429163561195562598400) }, { argument := 736801264761974410595224518656, coefficient := (-736801264761974410595224518656) }, { argument := 19489388458850841969291165696, coefficient := (-19489388458850841969291165696) }, { argument := 225868290898277174146079129600, coefficient := (-225868290898277174146079129600) }, { argument := 736801264761974410595224518656, coefficient := (-736801264761974410595224518656) }, { argument := 4183308810057930711118529953792, coefficient := (-4183308810057930711118529953792) }, { argument := 19484779429163561195562598400, coefficient := (-19484779429163561195562598400) }, { argument := 19489388458850841969291165696, coefficient := (-19489388458850841969291165696) }, { argument := 21573802498364505424218030080, coefficient := (-21573802498364505424218030080) }, { argument := 52522373190913345944201669378048, coefficient := (-52522373190913345944201669378048) }, { argument := 13437362117252889169373429760, coefficient := (-13437362117252889169373429760) }, { argument := 695863395357738903413981184, coefficient := (-695863395357738903413981184) }, { argument := 191821513299701411325831966359552, coefficient := (-191821513299701411325831966359552) }, { argument := 18716325806173667057341562880, coefficient := (-18716325806173667057341562880) }, { argument := 52518212577839363677351627980800, coefficient := (-52518212577839363677351627980800) }, { argument := 18740321095668761502286872576, coefficient := (-18740321095668761502286872576) }, { argument := 18740321095668761502286872576, coefficient := (-18740321095668761502286872576) }, { argument := 13413366827757794724428120064, coefficient := (-13413366827757794724428120064) }, { argument := 695863395357738903413981184, coefficient := (-695863395357738903413981184) }, { argument := 156933682958724049741545472, coefficient := (-156933682958724049741545472) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 151871306089087790072463360, coefficient := (-151871306089087790072463360) }, { argument := 1999638863506322569287434240, coefficient := (-1999638863506322569287434240) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 151871306089087790072463360, coefficient := (-151871306089087790072463360) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 7345508837842212779838144512, coefficient := (-7345508837842212779838144512) }, { argument := 182245567306905348086956032, coefficient := (-182245567306905348086956032) }, { argument := 1999638863506322569287434240, coefficient := (-1999638863506322569287434240) }, { argument := 7345508837842212779838144512, coefficient := (-7345508837842212779838144512) }, { argument := 156933682958724049741545472, coefficient := (-156933682958724049741545472) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 182245567306905348086956032, coefficient := (-182245567306905348086956032) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 13437362117252889169373429760, coefficient := (-13437362117252889169373429760) }, { argument := 48949094132819167381144207360, coefficient := (-48949094132819167381144207360) }, { argument := 13437371156157485287053721600, coefficient := (-13437371156157485287053721600) }] }

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

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-101307676151422284420278054650118144)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    7424016401331013, 2077, 7424016127593659, 2077, 150891321, 1099321937,
    301782845, 9356145415, 2345, 9356152057, 2345, 4696997,
    14862041988056377, 9356152057, 578684709116751711, 97954826173, 4338337283, 578684701567003689,
    4338337283, 8450182069, 159768419627, 8452180917, 97954826173, 159768419627,
    14862097872969535, 8450182069, 8452180917, 9356152057, 85185810636814477, 1326767855,
    1099321937, 2488336808504902397, 7391992335, 681433475684767899, 29605876993, 29605876993,
    21190378027, 1099321937, 36133487020862031, 1005, 36133485561255345, 1005,
    1014614055, 7391992335, 2029229475, 97954756675, 26465, 97954826173,
    26465, 90347825, 4338334205, 2345, 4338337283, 2345,
    4185, 93291085736357053, 364220675, 301782845, 340716950988790029, 2029229475,
    46641847498024219, 8127324205, 8127324205, 5817124495
  ]
def negativeCoefficients : Array ℕ := #[
    4179349687328350103869960749056, 156933682958724049741545472, 4179349533227919419896766660608, 156933682958724049741545472, 695863395357738903413981184, 2534863803306706882237825024,
    695863863443869773793853440, 21573802498364505424218030080, 177183190437269088417873920, 21573817813773772621573259264, 177183190437269088417873920, 44361882405878549919588941824,
    4183292922460960313786144653312, 21573817813773772621573259264, 162885265021450429693758239932416, 225868451149754628479381405696, 20007049391233361972226424832, 162885262896385281029987037609984,
    20007049391233361972226424832, 19484793250386558422444146688, 736801786980075765275775991808, 19489402280073839196172713984, 225868451149754628479381405696, 736801786980075765275775991808,
    4183308652665589938869197864960, 19484793250386558422444146688, 19489402280073839196172713984, 21573817813773772621573259264, 191821392520605656591548647735296, 48949094132819167381144207360,
    2534863803306706882237825024, 700404545222185481062777389842432, 68179095399283840280879431680, 191806471698231416032829840031744, 68266504495949588794060046336, 68266504495949588794060046336,
    48861685036153418867963592704, 2534863803306706882237825024, 162730758682750896437343736037376, 151871306089087790072463360, 162730752109266769260259175301120, 151871306089087790072463360,
    18716325806173667057341562880, 68179095399283840280879431680, 18716338396076497364110540800, 225868290898277174146079129600, 1999638863506322569287434240, 225868451149754628479381405696,
    1999638863506322569287434240, 6826488649282755257265500979200, 20007035196463797252726456320, 177183190437269088417873920, 20007049391233361972226424832, 177183190437269088417873920,
    161899345762791139076651089920, 52518212369905827291324571713536, 13437371156157485287053721600, 695863863443869773793853440, 191806591688990790407407741698048, 18716338396076497364110540800,
    52514051752993343463998573510656, 18740333701712492873551708160, 18740333701712492873551708160, 13413375850521489777612554240
  ]
def negativeScales : Array ℕ := #[
    52, 11, 52, 11, 27, 30,
    28, 33, 11, 33, 11, 22,
    53, 33, 59, 36, 32, 59,
    32, 32, 37, 32, 36, 37,
    53, 32, 32, 33, 56, 30,
    30, 61, 32, 59, 34, 34,
    34, 30, 55, 9, 55, 9,
    29, 32, 30, 36, 14, 36,
    14, 26, 32, 11, 32, 11,
    12, 56, 28, 28, 58, 30,
    55, 32, 32, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    52721121321137069, 11020285500844648, 52721121267942206, 11020285500844648, 27168934586101003, 30033966796141026,
    28168935556557729, 33123267138492877, 11195372207402739, 33123268162672882, 11195372207402739, 22163307241462242,
    53722481868627492, 33123268162672882, 59005555136625020, 36511397523800030, 32014495073339423, 59005555117803053,
    32014495073339423, 32976335296410834, 37217191312164070, 32976676518390009, 36511397523800030, 37217191312164070,
    53722487293503547, 32976335296410834, 32976676518390009, 33123268162672882, 56241462659579394, 30305268817958421,
    30033966796141026, 61109887482457515, 32783316115221042, 59241350435215817, 34785164539631388, 34785164539631388,
    34302690273856644, 30033966796141026, 55004186005322319, 9972979801353332, 55004185947044872, 9972979801353332,
    29918283910762953, 32783316115221042, 30918284881219782, 36511396500221515, 14691798033581851, 36511397523800030,
    14691798033581851, 26428986534814621, 32014494049763656, 11195372207402739, 32014495073339423, 11195372207402739,
    12031011907437707, 56372588751703929, 28440237578375156, 28168935556557729, 58241351337740210, 30918284881219782,
    55372474453465384, 32920133305810895, 32920133305810895, 32437659034273377
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
noncomputable def negativeCeiling : ℝ := 724042387487 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4179349687328350103869960749056, coefficient := (-4179349687328350103869960749056) }, { argument := 156933682958724049741545472, coefficient := (-156933682958724049741545472) }, { argument := 4179349533227919419896766660608, coefficient := (-4179349533227919419896766660608) }, { argument := 156933682958724049741545472, coefficient := (-156933682958724049741545472) }, { argument := 695863395357738903413981184, coefficient := (-695863395357738903413981184) }, { argument := 2534863803306706882237825024, coefficient := (-2534863803306706882237825024) }, { argument := 695863863443869773793853440, coefficient := (-695863863443869773793853440) }, { argument := 21573802498364505424218030080, coefficient := (-21573802498364505424218030080) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 21573817813773772621573259264, coefficient := (-21573817813773772621573259264) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 44361882405878549919588941824, coefficient := (-44361882405878549919588941824) }, { argument := 4183292922460960313786144653312, coefficient := (-4183292922460960313786144653312) }, { argument := 21573817813773772621573259264, coefficient := (-21573817813773772621573259264) }, { argument := 162885265021450429693758239932416, coefficient := (-162885265021450429693758239932416) }, { argument := 225868451149754628479381405696, coefficient := (-225868451149754628479381405696) }, { argument := 20007049391233361972226424832, coefficient := (-20007049391233361972226424832) }, { argument := 162885262896385281029987037609984, coefficient := (-162885262896385281029987037609984) }, { argument := 20007049391233361972226424832, coefficient := (-20007049391233361972226424832) }, { argument := 19484793250386558422444146688, coefficient := (-19484793250386558422444146688) }, { argument := 736801786980075765275775991808, coefficient := (-736801786980075765275775991808) }, { argument := 19489402280073839196172713984, coefficient := (-19489402280073839196172713984) }, { argument := 225868451149754628479381405696, coefficient := (-225868451149754628479381405696) }, { argument := 736801786980075765275775991808, coefficient := (-736801786980075765275775991808) }, { argument := 4183308652665589938869197864960, coefficient := (-4183308652665589938869197864960) }, { argument := 19484793250386558422444146688, coefficient := (-19484793250386558422444146688) }, { argument := 19489402280073839196172713984, coefficient := (-19489402280073839196172713984) }, { argument := 21573817813773772621573259264, coefficient := (-21573817813773772621573259264) }, { argument := 191821392520605656591548647735296, coefficient := (-191821392520605656591548647735296) }, { argument := 48949094132819167381144207360, coefficient := (-48949094132819167381144207360) }, { argument := 2534863803306706882237825024, coefficient := (-2534863803306706882237825024) }, { argument := 700404545222185481062777389842432, coefficient := (-700404545222185481062777389842432) }, { argument := 68179095399283840280879431680, coefficient := (-68179095399283840280879431680) }, { argument := 191806471698231416032829840031744, coefficient := (-191806471698231416032829840031744) }, { argument := 68266504495949588794060046336, coefficient := (-68266504495949588794060046336) }, { argument := 68266504495949588794060046336, coefficient := (-68266504495949588794060046336) }, { argument := 48861685036153418867963592704, coefficient := (-48861685036153418867963592704) }, { argument := 2534863803306706882237825024, coefficient := (-2534863803306706882237825024) }, { argument := 162730758682750896437343736037376, coefficient := (-162730758682750896437343736037376) }, { argument := 151871306089087790072463360, coefficient := (-151871306089087790072463360) }, { argument := 162730752109266769260259175301120, coefficient := (-162730752109266769260259175301120) }, { argument := 151871306089087790072463360, coefficient := (-151871306089087790072463360) }, { argument := 18716325806173667057341562880, coefficient := (-18716325806173667057341562880) }, { argument := 68179095399283840280879431680, coefficient := (-68179095399283840280879431680) }, { argument := 18716338396076497364110540800, coefficient := (-18716338396076497364110540800) }, { argument := 225868290898277174146079129600, coefficient := (-225868290898277174146079129600) }, { argument := 1999638863506322569287434240, coefficient := (-1999638863506322569287434240) }, { argument := 225868451149754628479381405696, coefficient := (-225868451149754628479381405696) }, { argument := 1999638863506322569287434240, coefficient := (-1999638863506322569287434240) }, { argument := 6826488649282755257265500979200, coefficient := (-6826488649282755257265500979200) }, { argument := 20007035196463797252726456320, coefficient := (-20007035196463797252726456320) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 20007049391233361972226424832, coefficient := (-20007049391233361972226424832) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 161899345762791139076651089920, coefficient := (-161899345762791139076651089920) }, { argument := 52518212369905827291324571713536, coefficient := (-52518212369905827291324571713536) }, { argument := 13437371156157485287053721600, coefficient := (-13437371156157485287053721600) }, { argument := 695863863443869773793853440, coefficient := (-695863863443869773793853440) }, { argument := 191806591688990790407407741698048, coefficient := (-191806591688990790407407741698048) }, { argument := 18716338396076497364110540800, coefficient := (-18716338396076497364110540800) }, { argument := 52514051752993343463998573510656, coefficient := (-52514051752993343463998573510656) }, { argument := 18740333701712492873551708160, coefficient := (-18740333701712492873551708160) }, { argument := 18740333701712492873551708160, coefficient := (-18740333701712492873551708160) }, { argument := 13413375850521489777612554240, coefficient := (-13413375850521489777612554240) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17
