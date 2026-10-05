import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 20, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20

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
def constantNumerator : ℤ := (-116037889827581520447130103185408)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    31, 751, 569, 317, 31, 317,
    633, 31, 751, 31, 1747570741, 1717641835,
    86353043, 222699953, 186340777, 5212996859, 420320677, 186340777,
    168161189, 86353043, 86353043, 168161189, 5212996859, 168161189,
    436892673, 222699953, 11651465, 2043557495, 510889435, 2912805,
    408637719, 12270498489, 9193726515, 67096264959, 2909407125, 349128855,
    9193726515, 18271076745, 2909407125, 281979738555, 18038324175, 12270503313,
    9193726515, 349128855, 18038324175, 349128855, 9193726515, 9193726515,
    408637719, 9654071, 1693233353, 423308389, 2413467, 2117937,
    1001306223, 38008785837, 4005227639, 2117937, 201969039, 8250471,
    3386684109, 86328099, 3823389, 6773365743
  ]
def negativeCoefficients : Array ℕ := #[
    299813603264428035327131648, 7263226324244692081634705408, 5503030330885792003262513152, 6131671757085399174109724672, 299813603264428035327131648, 6131671757085399174109724672,
    6122000350528482140712075264, 299813603264428035327131648, 7263226324244692081634705408, 299813603264428035327131648, 8059247552482489934087716864, 7921224835135462373683363840,
    6371729936828144320828669952, 8216178076436291361068548096, 109996179962085859854305460224, 192325637830049514105012748288, 7753547957507336636603564032, 109996179962085859854305460224,
    6204052833227403680806862848, 6371729936828144320828669952, 6371729936828144320828669952, 6204052833227403680806862848, 192325637830049514105012748288, 6204052833227403680806862848,
    8059247326509875031145709568, 8216178076436291361068548096, 214931592938784260819517440, 37696982110175986657966161920, 37696986629628284716806307840, 214927073486486201979371520,
    942254427657179880109375488, 28293843160427844716124438528, 21199290013235327387597537280, 154713453500059887654527827968, 13417272160275523663036416000, 805036329616531419782184960,
    21199290013235327387597537280, 21065117291632572150967173120, 13417272160275523663036416000, 325100504443475938355372359680, 20796771848427061677706444800, 28293854283814521162984062976,
    21199290013235327387597537280, 805036329616531419782184960, 20796771848427061677706444800, 805036329616531419782184960, 21199290013235327387597537280, 21199290013235327387597537280,
    942254427657179880109375488, 11130386062901327792439296, 1952165144991256451930390528, 1952165379034321887120326656, 11130152019835892602503168, 156276167212960746483744768,
    18470839635093744727640506368, 175284586221893822378460315648, 18470852303395237347675078656, 156276167212960746483744768, 931417793311515826251104256, 152194327024562518030811136,
    31236647508611031569711235072, 1592472348622861469151657984, 141058156754472577687093248, 31236636094688135961926172672
  ]
def negativeScales : Array ℕ := #[
    4, 9, 9, 8, 4, 8,
    9, 4, 9, 4, 30, 30,
    26, 27, 27, 32, 28, 27,
    27, 26, 26, 27, 32, 27,
    28, 27, 23, 30, 28, 21,
    28, 33, 33, 35, 31, 28,
    33, 34, 31, 38, 34, 33,
    33, 28, 34, 28, 33, 33,
    28, 23, 30, 28, 21, 21,
    29, 35, 31, 21, 27, 22,
    31, 26, 21, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    4954196321574415, 9552669097515714, 9152284842306582, 8308339030139408, 4954196321574415, 8308339030139408,
    9306061689428342, 4954196321574415, 9552669097515714, 4954196321574415, 30702703710593564, 30677782089143445,
    26363743682077569, 27730526012895241, 27473368173252175, 32279465844649808, 28646915188417460, 27473368173252175,
    27325269534262933, 26363743682077569, 26363743682077569, 27325269534262933, 32279465844649808, 27325269534262933,
    28702703670141950, 27730526012895241, 23474008028134599, 30928435695003678, 28928435867966910, 21473977691691822,
    28606247136213243, 33514474808551321, 33098002605052703, 35965513420689170, 31438078046650355, 28379184357596759,
    33098002605052703, 34088842605767227, 31438078046650355, 38036800546326947, 34070346262149838, 33514475375729542,
    33098002605052703, 28379184357596759, 34070346262149838, 28379184357596759, 33098002605052703, 33098002605052703,
    28606247136213243, 23202706006317094, 30657133666002926, 28657133838966136, 21202675669874317, 21014228244990891,
    29899236110033063, 35145613888966518, 31899237099511140, 21014228244990891, 27589558909978022, 22976045067178793,
    31657226280574445, 26363326883984466, 21866420562290529, 32657225753411184
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
noncomputable def negativeCeiling : ℝ := 715441931 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 7263226324244692081634705408, coefficient := (-7263226324244692081634705408) }, { argument := 5503030330885792003262513152, coefficient := (-5503030330885792003262513152) }, { argument := 6131671757085399174109724672, coefficient := (-6131671757085399174109724672) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 6131671757085399174109724672, coefficient := (-6131671757085399174109724672) }, { argument := 6122000350528482140712075264, coefficient := (-6122000350528482140712075264) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 7263226324244692081634705408, coefficient := (-7263226324244692081634705408) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 8059247552482489934087716864, coefficient := (-8059247552482489934087716864) }, { argument := 7921224835135462373683363840, coefficient := (-7921224835135462373683363840) }, { argument := 6371729936828144320828669952, coefficient := (-6371729936828144320828669952) }, { argument := 8216178076436291361068548096, coefficient := (-8216178076436291361068548096) }, { argument := 109996179962085859854305460224, coefficient := (-109996179962085859854305460224) }, { argument := 192325637830049514105012748288, coefficient := (-192325637830049514105012748288) }, { argument := 7753547957507336636603564032, coefficient := (-7753547957507336636603564032) }, { argument := 109996179962085859854305460224, coefficient := (-109996179962085859854305460224) }, { argument := 6204052833227403680806862848, coefficient := (-6204052833227403680806862848) }, { argument := 6371729936828144320828669952, coefficient := (-6371729936828144320828669952) }, { argument := 6371729936828144320828669952, coefficient := (-6371729936828144320828669952) }, { argument := 6204052833227403680806862848, coefficient := (-6204052833227403680806862848) }, { argument := 192325637830049514105012748288, coefficient := (-192325637830049514105012748288) }, { argument := 6204052833227403680806862848, coefficient := (-6204052833227403680806862848) }, { argument := 8059247326509875031145709568, coefficient := (-8059247326509875031145709568) }, { argument := 8216178076436291361068548096, coefficient := (-8216178076436291361068548096) }, { argument := 214931592938784260819517440, coefficient := (-214931592938784260819517440) }, { argument := 37696982110175986657966161920, coefficient := (-37696982110175986657966161920) }, { argument := 37696986629628284716806307840, coefficient := (-37696986629628284716806307840) }, { argument := 214927073486486201979371520, coefficient := (-214927073486486201979371520) }, { argument := 942254427657179880109375488, coefficient := (-942254427657179880109375488) }, { argument := 28293843160427844716124438528, coefficient := (-28293843160427844716124438528) }, { argument := 21199290013235327387597537280, coefficient := (-21199290013235327387597537280) }, { argument := 154713453500059887654527827968, coefficient := (-154713453500059887654527827968) }, { argument := 13417272160275523663036416000, coefficient := (-13417272160275523663036416000) }, { argument := 805036329616531419782184960, coefficient := (-805036329616531419782184960) }, { argument := 21199290013235327387597537280, coefficient := (-21199290013235327387597537280) }, { argument := 21065117291632572150967173120, coefficient := (-21065117291632572150967173120) }, { argument := 13417272160275523663036416000, coefficient := (-13417272160275523663036416000) }, { argument := 325100504443475938355372359680, coefficient := (-325100504443475938355372359680) }, { argument := 20796771848427061677706444800, coefficient := (-20796771848427061677706444800) }, { argument := 28293854283814521162984062976, coefficient := (-28293854283814521162984062976) }, { argument := 21199290013235327387597537280, coefficient := (-21199290013235327387597537280) }, { argument := 805036329616531419782184960, coefficient := (-805036329616531419782184960) }, { argument := 20796771848427061677706444800, coefficient := (-20796771848427061677706444800) }, { argument := 805036329616531419782184960, coefficient := (-805036329616531419782184960) }, { argument := 21199290013235327387597537280, coefficient := (-21199290013235327387597537280) }, { argument := 21199290013235327387597537280, coefficient := (-21199290013235327387597537280) }, { argument := 942254427657179880109375488, coefficient := (-942254427657179880109375488) }, { argument := 11130386062901327792439296, coefficient := (-11130386062901327792439296) }, { argument := 1952165144991256451930390528, coefficient := (-1952165144991256451930390528) }, { argument := 1952165379034321887120326656, coefficient := (-1952165379034321887120326656) }, { argument := 11130152019835892602503168, coefficient := (-11130152019835892602503168) }, { argument := 156276167212960746483744768, coefficient := (-156276167212960746483744768) }, { argument := 18470839635093744727640506368, coefficient := (-18470839635093744727640506368) }, { argument := 175284586221893822378460315648, coefficient := (-175284586221893822378460315648) }, { argument := 18470852303395237347675078656, coefficient := (-18470852303395237347675078656) }, { argument := 156276167212960746483744768, coefficient := (-156276167212960746483744768) }, { argument := 931417793311515826251104256, coefficient := (-931417793311515826251104256) }, { argument := 152194327024562518030811136, coefficient := (-152194327024562518030811136) }, { argument := 31236647508611031569711235072, coefficient := (-31236647508611031569711235072) }, { argument := 1592472348622861469151657984, coefficient := (-1592472348622861469151657984) }, { argument := 141058156754472577687093248, coefficient := (-141058156754472577687093248) }, { argument := 31236636094688135961926172672, coefficient := (-31236636094688135961926172672) }] }

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

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1632469172087552761857977194905600)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3823389, 7445547, 140660469, 7445547, 86328099, 140660469,
    25246233, 7445547, 7445547, 8250471, 31, 751,
    569, 317, 31, 317, 633, 31,
    751, 31, 25671531179, 49543381097, 10092994275, 26029301025,
    21779619225, 609298128075, 49012174519, 21779619225, 19654778325, 10092994275,
    10092994275, 19654778325, 609298128075, 19654778325, 6417881883, 26029301025,
    6835400949, 105260317659, 179302417545, 36474346389, 56741271375, 6808952565,
    179302417545, 356335184235, 56741271375, 5499364021665, 351795882525, 105260319803,
    179302417545, 6808952565, 351795882525, 6808952565, 179302417545, 179302417545,
    6835400949, 64915305, 11385534615, 2846383995, 16228485, 22160853,
    10477082187, 397701685953, 41908357491, 22160853
  ]
def negativeCoefficients : Array ℕ := #[
    141058156754472577687093248, 137346099997775930905853952, 5189455345861912200172535808, 137346099997775930905853952, 1592472348622861469151657984, 5189455345861912200172535808,
    931421597952481028846125056, 137346099997775930905853952, 137346099997775930905853952, 152194327024562518030811136, 299813603264428035327131648, 7263226324244692081634705408,
    5503030330885792003262513152, 6131671757085399174109724672, 299813603264428035327131648, 6131671757085399174109724672, 6122000350528482140712075264, 299813603264428035327131648,
    7263226324244692081634705408, 299813603264428035327131648, 29597260352454264281265864704, 57119629477663660887530012672, 23272860291042585309138124800, 30009740901607544214414950400,
    401763061866419367441963417600, 702472914574364351304774451200, 56507189990498846470039404544, 401763061866419367441963417600, 22660416599173043590476595200, 23272860291042585309138124800,
    23272860291042585309138124800, 22660416599173043590476595200, 702472914574364351304774451200, 22660416599173043590476595200, 29597256147749536980094943232, 30009740901607544214414950400,
    31522722986848598766592720896, 485427535243235778400654196736, 826886452062506070226690375680, 168208233273428783454964678656, 523345855735763335586512896000, 31400751344145800135190773760,
    826886452062506070226690375680, 821652993505148436870825246720, 523345855735763335586512896000, 12680670084477545621261207470080, 811186076390433170159094988800, 485427545130690601908973862912,
    826886452062506070226690375680, 31400751344145800135190773760, 811186076390433170159094988800, 31400751344145800135190773760, 826886452062506070226690375680, 826886452062506070226690375680,
    31522722986848598766592720896, 299369004450449506141470720, 52506510796316552845024296960, 52506517091267967998408785920, 299362709499034352756981760, 1635182334984394152232353792,
    193268053742810158247750664192, 1834075304614449995130718912512, 193268186296501385906161188864, 1635182334984394152232353792
  ]
def negativeScales : Array ℕ := #[
    21, 22, 27, 22, 26, 27,
    24, 22, 22, 22, 4, 9,
    9, 8, 4, 8, 9, 4,
    9, 4, 34, 35, 33, 34,
    34, 39, 35, 34, 34, 33,
    33, 34, 39, 34, 32, 34,
    32, 36, 37, 35, 35, 32,
    37, 38, 35, 42, 38, 36,
    37, 32, 38, 32, 37, 37,
    32, 25, 33, 31, 23, 24,
    33, 38, 35, 24
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    21866420562290529, 22827946413243993, 27067641691860356, 22827946413243993, 26363326883984466, 27067641691860356,
    24589564803064328, 22827946413243993, 22827946413243993, 22976045067178793, 4954196321574415, 9552669097515714,
    9152284842306582, 8308339030139408, 4954196321574415, 8308339030139408, 9306061689428342, 4954196321574415,
    9552669097515714, 4954196321574415, 34579450296931536, 35527973277802226, 33232635189210040, 34599417519887227,
    34342259680384539, 39148357351782280, 35512421104970475, 34342259680384539, 34194161041395404, 33232635189210040,
    33232635189210040, 34194161041395404, 39148357351782280, 34194161041395404, 32579450091976516, 34599417519887227,
    32670378819529515, 36615170697545022, 37383603984040170, 35086163074520639, 35723679425762908, 32664785736615119,
    37383603984040170, 38374443984754693, 35723679425762908, 42322401925314410, 38355947641137302, 36615170726930627,
    37383603984040170, 32664785736615119, 38355947641137302, 32664785736615119, 37383603984040170, 37383603984040170,
    32670378819529515, 25952055335730863, 33406482984599453, 31406483157562663, 23952024999282572, 24401510077872360,
    33286517938606346, 38532895721848765, 35286518928084347, 24401510077872360
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
noncomputable def negativeCeiling : ℝ := 6334240209 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 141058156754472577687093248, coefficient := (-141058156754472577687093248) }, { argument := 137346099997775930905853952, coefficient := (-137346099997775930905853952) }, { argument := 5189455345861912200172535808, coefficient := (-5189455345861912200172535808) }, { argument := 137346099997775930905853952, coefficient := (-137346099997775930905853952) }, { argument := 1592472348622861469151657984, coefficient := (-1592472348622861469151657984) }, { argument := 5189455345861912200172535808, coefficient := (-5189455345861912200172535808) }, { argument := 931421597952481028846125056, coefficient := (-931421597952481028846125056) }, { argument := 137346099997775930905853952, coefficient := (-137346099997775930905853952) }, { argument := 137346099997775930905853952, coefficient := (-137346099997775930905853952) }, { argument := 152194327024562518030811136, coefficient := (-152194327024562518030811136) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 7263226324244692081634705408, coefficient := (-7263226324244692081634705408) }, { argument := 5503030330885792003262513152, coefficient := (-5503030330885792003262513152) }, { argument := 6131671757085399174109724672, coefficient := (-6131671757085399174109724672) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 6131671757085399174109724672, coefficient := (-6131671757085399174109724672) }, { argument := 6122000350528482140712075264, coefficient := (-6122000350528482140712075264) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 7263226324244692081634705408, coefficient := (-7263226324244692081634705408) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 29597260352454264281265864704, coefficient := (-29597260352454264281265864704) }, { argument := 57119629477663660887530012672, coefficient := (-57119629477663660887530012672) }, { argument := 23272860291042585309138124800, coefficient := (-23272860291042585309138124800) }, { argument := 30009740901607544214414950400, coefficient := (-30009740901607544214414950400) }, { argument := 401763061866419367441963417600, coefficient := (-401763061866419367441963417600) }, { argument := 702472914574364351304774451200, coefficient := (-702472914574364351304774451200) }, { argument := 56507189990498846470039404544, coefficient := (-56507189990498846470039404544) }, { argument := 401763061866419367441963417600, coefficient := (-401763061866419367441963417600) }, { argument := 22660416599173043590476595200, coefficient := (-22660416599173043590476595200) }, { argument := 23272860291042585309138124800, coefficient := (-23272860291042585309138124800) }, { argument := 23272860291042585309138124800, coefficient := (-23272860291042585309138124800) }, { argument := 22660416599173043590476595200, coefficient := (-22660416599173043590476595200) }, { argument := 702472914574364351304774451200, coefficient := (-702472914574364351304774451200) }, { argument := 22660416599173043590476595200, coefficient := (-22660416599173043590476595200) }, { argument := 29597256147749536980094943232, coefficient := (-29597256147749536980094943232) }, { argument := 30009740901607544214414950400, coefficient := (-30009740901607544214414950400) }, { argument := 31522722986848598766592720896, coefficient := (-31522722986848598766592720896) }, { argument := 485427535243235778400654196736, coefficient := (-485427535243235778400654196736) }, { argument := 826886452062506070226690375680, coefficient := (-826886452062506070226690375680) }, { argument := 168208233273428783454964678656, coefficient := (-168208233273428783454964678656) }, { argument := 523345855735763335586512896000, coefficient := (-523345855735763335586512896000) }, { argument := 31400751344145800135190773760, coefficient := (-31400751344145800135190773760) }, { argument := 826886452062506070226690375680, coefficient := (-826886452062506070226690375680) }, { argument := 821652993505148436870825246720, coefficient := (-821652993505148436870825246720) }, { argument := 523345855735763335586512896000, coefficient := (-523345855735763335586512896000) }, { argument := 12680670084477545621261207470080, coefficient := (-12680670084477545621261207470080) }, { argument := 811186076390433170159094988800, coefficient := (-811186076390433170159094988800) }, { argument := 485427545130690601908973862912, coefficient := (-485427545130690601908973862912) }, { argument := 826886452062506070226690375680, coefficient := (-826886452062506070226690375680) }, { argument := 31400751344145800135190773760, coefficient := (-31400751344145800135190773760) }, { argument := 811186076390433170159094988800, coefficient := (-811186076390433170159094988800) }, { argument := 31400751344145800135190773760, coefficient := (-31400751344145800135190773760) }, { argument := 826886452062506070226690375680, coefficient := (-826886452062506070226690375680) }, { argument := 826886452062506070226690375680, coefficient := (-826886452062506070226690375680) }, { argument := 31522722986848598766592720896, coefficient := (-31522722986848598766592720896) }, { argument := 299369004450449506141470720, coefficient := (-299369004450449506141470720) }, { argument := 52506510796316552845024296960, coefficient := (-52506510796316552845024296960) }, { argument := 52506517091267967998408785920, coefficient := (-52506517091267967998408785920) }, { argument := 299362709499034352756981760, coefficient := (-299362709499034352756981760) }, { argument := 1635182334984394152232353792, coefficient := (-1635182334984394152232353792) }, { argument := 193268053742810158247750664192, coefficient := (-193268053742810158247750664192) }, { argument := 1834075304614449995130718912512, coefficient := (-1834075304614449995130718912512) }, { argument := 193268186296501385906161188864, coefficient := (-193268186296501385906161188864) }, { argument := 1635182334984394152232353792, coefficient := (-1635182334984394152232353792) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20
