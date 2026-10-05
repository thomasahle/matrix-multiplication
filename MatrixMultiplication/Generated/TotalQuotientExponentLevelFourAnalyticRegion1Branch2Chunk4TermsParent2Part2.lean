import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 4, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-8576437920792365188131245436960768)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    70479117475, 734592054625, 70479117475, 954388825, 3821214627, 138482082909,
    1107857070405, 30569309883, 51949625, 3836343875, 39985570625, 3836343875,
    51949625, 2172847533, 78744713811, 629957941995, 17382548757, 11121299073,
    18849100159, 11121299073, 14048505, 1181328135, 590663925, 7024395,
    1726211825, 127476226475, 1328663389625, 127476226475, 1726211825, 3921115663,
    142102529521, 1136820653945, 31368507527, 954388825, 70479117475, 734592054625,
    70479117475, 954388825, 61214359809, 2218428661503, 17747435814135, 489708356361,
    520548546933, 882259494539, 520548546933, 74925777, 2715334959, 21722687655,
    599398233, 141706875285, 240174018155, 141706875285, 3507, 3507,
    17050655057421, 1045818138458855, 15267423087, 8430712992435805, 15666571403, 498935395,
    15267423087, 8681475873, 15666571403, 244578130629
  ]
def negativeCoefficients : Array ℕ := #[
    325027560650558886843410022400, 3387707907561960491771232256000, 325027560650558886843410022400, 2200670800197921544758886400, 70488968274984504784670687232, 2554543542216550534072126930944,
    2554544481001332404270986690560, 70488029490202634585810927616, 119787679637522945671168000, 17692013410217046717759488000, 184400896990153370469662720000, 17692013410217046717759488000,
    119787679637522945671168000, 40081962352442169387361763328, 1452583582829018931139052568576, 1452584116647816465173698314240, 40081428533644635352716017664, 51287939441703570014566612992,
    173852263326395508542482153472, 51287939441703570014566612992, 518298352706458008850268160, 43583315546835214284431032320, 43583305032191092269986611200, 518308867350580023294689280,
    3980373469098262451873382400, 587880331316640723792979558400, 6127378377129953424463364096000, 587880331316640723792979558400, 3980373469098262451873382400, 72331817118774949354204561408,
    2621328994300643358492313255936, 2621329957628818218761731440640, 72330853790600089084786376704, 2200670800197921544758886400, 325027560650558886843410022400, 3387707907561960491771232256000,
    325027560650558886843410022400, 2200670800197921544758886400, 1129205629032594909981881401344, 40922785764527878163469170638848, 40922800803491932829203845611520, 1129190590068540244247206428672,
    2400606455803609035197940498432, 8137407551180641383714245312512, 2400606455803609035197940498432, 44228372250970669668812980224, 1602850850018227786084471799808, 1602851439059659547777874001920,
    44227783209538907975410778112, 653507615466868069540445552640, 2215214323029878254009046794240, 653507615466868069540445552640, 33917622795108036125556473856, 33917622795108036125556473856,
    4799332735189004917382578176, 294371636166287823117096058880, 70408561587733409518634139648, 2373034743200093166268139438080, 72249308295909446368794509312, 2300933385220046062700462080,
    70408561587733409518634139648, 40036240902828801490988040192, 72249308295909446368794509312, 1127917545434866579935766511616
  ]
def negativeScales : Array ℕ := #[
    36, 39, 36, 29, 31, 37,
    40, 34, 25, 31, 35, 31,
    25, 31, 36, 39, 34, 33,
    34, 33, 23, 30, 29, 22,
    30, 36, 40, 36, 30, 31,
    37, 40, 34, 29, 36, 39,
    36, 29, 35, 41, 44, 38,
    38, 39, 38, 26, 31, 34,
    29, 37, 37, 37, 11, 11,
    43, 49, 33, 52, 33, 28,
    33, 33, 33, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36036476808114749, 39418152335671707, 36036476808114749, 29830001910798741, 31831384147335099, 37010908373317385,
    40010908903502084, 34831364933134162, 25630609999252044, 31837084899082653, 35218760425288713, 31837084899082653,
    25630609999252044, 31016939799282288, 36196464026473461, 39196464556658161, 34016920585081805, 33372606267214760,
    34133776600901504, 33372606267214760, 23743913275719710, 30137762608715976, 29137762260660153, 22743942543169723,
    30684962363818002, 36891437266003043, 40273112789816965, 36891437266003043, 30684962363818002, 31868617054786071,
    37048141279516360, 40048141809701060, 34868597840584706, 29830001910798741, 36036476808114749, 39418152335671707,
    36036476808114749, 29830001910798741, 35833151073551735, 41012675299491573, 44012675829676272, 38833131859350783,
    38921241767255472, 39682412094628966, 38921241767255472, 26158958804154716, 31338483031345890, 34338483561530589,
    29158939589954233, 37044118799892348, 37805289134298409, 37044118799892348, 11776021715645854, 11776021715645854,
    43954892411080161, 49893553424525742, 33829737527350226, 52904576074301263, 33866970434765077, 28894277782314735,
    33829737527350226, 33015293179335759, 33866970434765077, 37831504453565606
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
noncomputable def negativeCeiling : ℝ := 34022810267 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 325027560650558886843410022400, coefficient := (-325027560650558886843410022400) }, { argument := 3387707907561960491771232256000, coefficient := (-3387707907561960491771232256000) }, { argument := 325027560650558886843410022400, coefficient := (-325027560650558886843410022400) }, { argument := 2200670800197921544758886400, coefficient := (-2200670800197921544758886400) }, { argument := 70488968274984504784670687232, coefficient := (-70488968274984504784670687232) }, { argument := 2554543542216550534072126930944, coefficient := (-2554543542216550534072126930944) }, { argument := 2554544481001332404270986690560, coefficient := (-2554544481001332404270986690560) }, { argument := 70488029490202634585810927616, coefficient := (-70488029490202634585810927616) }, { argument := 119787679637522945671168000, coefficient := (-119787679637522945671168000) }, { argument := 17692013410217046717759488000, coefficient := (-17692013410217046717759488000) }, { argument := 184400896990153370469662720000, coefficient := (-184400896990153370469662720000) }, { argument := 17692013410217046717759488000, coefficient := (-17692013410217046717759488000) }, { argument := 119787679637522945671168000, coefficient := (-119787679637522945671168000) }, { argument := 40081962352442169387361763328, coefficient := (-40081962352442169387361763328) }, { argument := 1452583582829018931139052568576, coefficient := (-1452583582829018931139052568576) }, { argument := 1452584116647816465173698314240, coefficient := (-1452584116647816465173698314240) }, { argument := 40081428533644635352716017664, coefficient := (-40081428533644635352716017664) }, { argument := 51287939441703570014566612992, coefficient := (-51287939441703570014566612992) }, { argument := 173852263326395508542482153472, coefficient := (-173852263326395508542482153472) }, { argument := 51287939441703570014566612992, coefficient := (-51287939441703570014566612992) }, { argument := 518298352706458008850268160, coefficient := (-518298352706458008850268160) }, { argument := 43583315546835214284431032320, coefficient := (-43583315546835214284431032320) }, { argument := 43583305032191092269986611200, coefficient := (-43583305032191092269986611200) }, { argument := 518308867350580023294689280, coefficient := (-518308867350580023294689280) }, { argument := 3980373469098262451873382400, coefficient := (-3980373469098262451873382400) }, { argument := 587880331316640723792979558400, coefficient := (-587880331316640723792979558400) }, { argument := 6127378377129953424463364096000, coefficient := (-6127378377129953424463364096000) }, { argument := 587880331316640723792979558400, coefficient := (-587880331316640723792979558400) }, { argument := 3980373469098262451873382400, coefficient := (-3980373469098262451873382400) }, { argument := 72331817118774949354204561408, coefficient := (-72331817118774949354204561408) }, { argument := 2621328994300643358492313255936, coefficient := (-2621328994300643358492313255936) }, { argument := 2621329957628818218761731440640, coefficient := (-2621329957628818218761731440640) }, { argument := 72330853790600089084786376704, coefficient := (-72330853790600089084786376704) }, { argument := 2200670800197921544758886400, coefficient := (-2200670800197921544758886400) }, { argument := 325027560650558886843410022400, coefficient := (-325027560650558886843410022400) }, { argument := 3387707907561960491771232256000, coefficient := (-3387707907561960491771232256000) }, { argument := 325027560650558886843410022400, coefficient := (-325027560650558886843410022400) }, { argument := 2200670800197921544758886400, coefficient := (-2200670800197921544758886400) }, { argument := 1129205629032594909981881401344, coefficient := (-1129205629032594909981881401344) }, { argument := 40922785764527878163469170638848, coefficient := (-40922785764527878163469170638848) }, { argument := 40922800803491932829203845611520, coefficient := (-40922800803491932829203845611520) }, { argument := 1129190590068540244247206428672, coefficient := (-1129190590068540244247206428672) }, { argument := 2400606455803609035197940498432, coefficient := (-2400606455803609035197940498432) }, { argument := 8137407551180641383714245312512, coefficient := (-8137407551180641383714245312512) }, { argument := 2400606455803609035197940498432, coefficient := (-2400606455803609035197940498432) }, { argument := 44228372250970669668812980224, coefficient := (-44228372250970669668812980224) }, { argument := 1602850850018227786084471799808, coefficient := (-1602850850018227786084471799808) }, { argument := 1602851439059659547777874001920, coefficient := (-1602851439059659547777874001920) }, { argument := 44227783209538907975410778112, coefficient := (-44227783209538907975410778112) }, { argument := 653507615466868069540445552640, coefficient := (-653507615466868069540445552640) }, { argument := 2215214323029878254009046794240, coefficient := (-2215214323029878254009046794240) }, { argument := 653507615466868069540445552640, coefficient := (-653507615466868069540445552640) }, { argument := 33917622795108036125556473856, coefficient := (-33917622795108036125556473856) }, { argument := 33917622795108036125556473856, coefficient := (-33917622795108036125556473856) }, { argument := 4799332735189004917382578176, coefficient := (-4799332735189004917382578176) }, { argument := 294371636166287823117096058880, coefficient := (-294371636166287823117096058880) }, { argument := 70408561587733409518634139648, coefficient := (-70408561587733409518634139648) }, { argument := 2373034743200093166268139438080, coefficient := (-2373034743200093166268139438080) }, { argument := 72249308295909446368794509312, coefficient := (-72249308295909446368794509312) }, { argument := 2300933385220046062700462080, coefficient := (-2300933385220046062700462080) }, { argument := 70408561587733409518634139648, coefficient := (-70408561587733409518634139648) }, { argument := 40036240902828801490988040192, coefficient := (-40036240902828801490988040192) }, { argument := 72249308295909446368794509312, coefficient := (-72249308295909446368794509312) }, { argument := 1127917545434866579935766511616, coefficient := (-1127917545434866579935766511616) }] }

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

end TermShard4


end Parent2

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2588211785839356637865941368045568)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    299361237, 522909335467345, 15267423087, 498935395, 299361237, 498935395,
    7683605083, 8681475873, 17050655057421, 525252214512365, 2615459055, 8523689967023815,
    64718699595, 2058978405, 8523693847537105, 1057313235, 1057313235, 35781705795,
    1947682275, 64718699595, 35781705795, 525247462042595, 2058978405, 1947682275,
    2615459055, 185249685905427, 590663925, 192742965, 5118038562532593, 1946082195,
    1481997043749495, 3898381905, 1747121715, 590663925, 192742965, 3821214627,
    138482082909, 1107857070405, 30569309883, 520548546933, 882259494539, 520548546933,
    159476643235453, 159450263746947, 12556305405, 21281242115, 12556305405, 5649,
    5649, 4584249, 385486023, 192742965, 2292171, 54918175,
    4055563525, 42270460375, 4055563525, 54918175, 124876295, 4525558265,
    36204479425, 998997055, 51949625, 3836343875
  ]
def negativeCoefficients : Array ℕ := #[
    44177920996224884403848871936, 294371786044911078729203056640, 70408561587733409518634139648, 2300933385220046062700462080, 44177920996224884403848871936, 2300933385220046062700462080,
    70868748264777418731174232064, 40036240902828801490988040192, 4799332735189004917382578176, 295690709694176855669478522880, 24123351911425617107028541440, 9596821739827522143034865090560,
    596924644106127504159025397760, 18990723845164847509788426240, 9596826108897073855599235563520, 19503986651790924469512437760, 19503986651790924469512437760, 330027984660567485102539407360,
    17964198231912693590340403200, 596924644106127504159025397760, 330027984660567485102539407360, 295688034291541197976124784640, 18990723845164847509788426240, 17964198231912693590340403200,
    24123351911425617107028541440, 834290416414182462104946081792, 43583305032191092269986611200, 1777740073681478763644190720, 2881199570386201853175860822016, 35898880197567926001331077120,
    834290166749300292519922237440, 35956226651557651122738954240, 32228707142225518231226941440, 43583305032191092269986611200, 1777740073681478763644190720, 70488968274984504784670687232,
    2554543542216550534072126930944, 2554544481001332404270986690560, 70488029490202634585810927616, 2400606455803609035197940498432, 8137407551180641383714245312512, 2400606455803609035197940498432,
    89777368881185457798524174336, 89762518549359727063244734464, 57905738079342740339026821120, 196284813433027187064092753920, 57905738079342740339026821120, 54633775640024321663321505792,
    54633775640024321663321505792, 21141117018289734571524096, 1777740502568278477391265792, 1777740073681478763644190720, 21141545905089448318599168, 126632689902524256852377600,
    18702985605086592244488601600, 194938091103876420210786304000, 18702985605086592244488601600, 126632689902524256852377600, 2303561054738055711917342720, 83481815105116030525232906240,
    83481845784357268113430937600, 2303530375496818123719311360, 119787679637522945671168000, 17692013410217046717759488000
  ]
def negativeScales : Array ℕ := #[
    28, 48, 33, 28, 28, 28,
    32, 33, 43, 48, 31, 52,
    35, 30, 52, 29, 29, 35,
    30, 35, 35, 48, 30, 30,
    31, 47, 29, 27, 52, 30,
    50, 31, 30, 29, 27, 31,
    37, 40, 34, 38, 39, 38,
    47, 47, 33, 34, 33, 12,
    12, 22, 28, 27, 21, 25,
    31, 35, 31, 25, 26, 32,
    35, 29, 25, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    28157312184208187, 48893554159070379, 33829737527350226, 28894277782314735, 28157312184208187, 28894277782314735,
    32839136225587614, 33015293179335759, 43954892411080161, 48900003672239076, 31284417038794438, 52920399548370955,
    35913463574139040, 30939281561434072, 52920400205175301, 29977755717092648, 29977755717092648, 35058503114444748,
    30859111206120832, 35913463574139040, 35058503114444748, 48899990618707963, 30939281561434072, 30859111206120832,
    31284417038794438, 47396464424837767, 29137762260660153, 27522102962716638, 52184512440903689, 30857925501275303,
    50396463993105202, 31860228287234134, 30702332972626595, 29137762260660153, 27522102962716638, 31831384147335099,
    37010908373317385, 40010908903502084, 34831364933134162, 38921241767255472, 39682412094628966, 38921241767255472,
    47180338472439226, 47180099812379492, 33547692973774089, 34308863307459596, 33547692973774089, 12463779785335462,
    12463779785335462, 22128253977578882, 28522103310772461, 27522102962716638, 21128283245028767, 25710780348016212,
    31917255252347632, 35298930773972696, 31917255252347632, 25710780348016212, 26895924402380042, 32075448625512095,
    35075449155696795, 29895905188178154, 25630609999252044, 31837084899082653
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
noncomputable def negativeCeiling : ℝ := 12776638229 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 44177920996224884403848871936, coefficient := (-44177920996224884403848871936) }, { argument := 294371786044911078729203056640, coefficient := (-294371786044911078729203056640) }, { argument := 70408561587733409518634139648, coefficient := (-70408561587733409518634139648) }, { argument := 2300933385220046062700462080, coefficient := (-2300933385220046062700462080) }, { argument := 44177920996224884403848871936, coefficient := (-44177920996224884403848871936) }, { argument := 2300933385220046062700462080, coefficient := (-2300933385220046062700462080) }, { argument := 70868748264777418731174232064, coefficient := (-70868748264777418731174232064) }, { argument := 40036240902828801490988040192, coefficient := (-40036240902828801490988040192) }, { argument := 4799332735189004917382578176, coefficient := (-4799332735189004917382578176) }, { argument := 295690709694176855669478522880, coefficient := (-295690709694176855669478522880) }, { argument := 24123351911425617107028541440, coefficient := (-24123351911425617107028541440) }, { argument := 9596821739827522143034865090560, coefficient := (-9596821739827522143034865090560) }, { argument := 596924644106127504159025397760, coefficient := (-596924644106127504159025397760) }, { argument := 18990723845164847509788426240, coefficient := (-18990723845164847509788426240) }, { argument := 9596826108897073855599235563520, coefficient := (-9596826108897073855599235563520) }, { argument := 19503986651790924469512437760, coefficient := (-19503986651790924469512437760) }, { argument := 19503986651790924469512437760, coefficient := (-19503986651790924469512437760) }, { argument := 330027984660567485102539407360, coefficient := (-330027984660567485102539407360) }, { argument := 17964198231912693590340403200, coefficient := (-17964198231912693590340403200) }, { argument := 596924644106127504159025397760, coefficient := (-596924644106127504159025397760) }, { argument := 330027984660567485102539407360, coefficient := (-330027984660567485102539407360) }, { argument := 295688034291541197976124784640, coefficient := (-295688034291541197976124784640) }, { argument := 18990723845164847509788426240, coefficient := (-18990723845164847509788426240) }, { argument := 17964198231912693590340403200, coefficient := (-17964198231912693590340403200) }, { argument := 24123351911425617107028541440, coefficient := (-24123351911425617107028541440) }, { argument := 834290416414182462104946081792, coefficient := (-834290416414182462104946081792) }, { argument := 43583305032191092269986611200, coefficient := (-43583305032191092269986611200) }, { argument := 1777740073681478763644190720, coefficient := (-1777740073681478763644190720) }, { argument := 2881199570386201853175860822016, coefficient := (-2881199570386201853175860822016) }, { argument := 35898880197567926001331077120, coefficient := (-35898880197567926001331077120) }, { argument := 834290166749300292519922237440, coefficient := (-834290166749300292519922237440) }, { argument := 35956226651557651122738954240, coefficient := (-35956226651557651122738954240) }, { argument := 32228707142225518231226941440, coefficient := (-32228707142225518231226941440) }, { argument := 43583305032191092269986611200, coefficient := (-43583305032191092269986611200) }, { argument := 1777740073681478763644190720, coefficient := (-1777740073681478763644190720) }, { argument := 70488968274984504784670687232, coefficient := (-70488968274984504784670687232) }, { argument := 2554543542216550534072126930944, coefficient := (-2554543542216550534072126930944) }, { argument := 2554544481001332404270986690560, coefficient := (-2554544481001332404270986690560) }, { argument := 70488029490202634585810927616, coefficient := (-70488029490202634585810927616) }, { argument := 2400606455803609035197940498432, coefficient := (-2400606455803609035197940498432) }, { argument := 8137407551180641383714245312512, coefficient := (-8137407551180641383714245312512) }, { argument := 2400606455803609035197940498432, coefficient := (-2400606455803609035197940498432) }, { argument := 89777368881185457798524174336, coefficient := (-89777368881185457798524174336) }, { argument := 89762518549359727063244734464, coefficient := (-89762518549359727063244734464) }, { argument := 57905738079342740339026821120, coefficient := (-57905738079342740339026821120) }, { argument := 196284813433027187064092753920, coefficient := (-196284813433027187064092753920) }, { argument := 57905738079342740339026821120, coefficient := (-57905738079342740339026821120) }, { argument := 54633775640024321663321505792, coefficient := (-54633775640024321663321505792) }, { argument := 54633775640024321663321505792, coefficient := (-54633775640024321663321505792) }, { argument := 21141117018289734571524096, coefficient := (-21141117018289734571524096) }, { argument := 1777740502568278477391265792, coefficient := (-1777740502568278477391265792) }, { argument := 1777740073681478763644190720, coefficient := (-1777740073681478763644190720) }, { argument := 21141545905089448318599168, coefficient := (-21141545905089448318599168) }, { argument := 126632689902524256852377600, coefficient := (-126632689902524256852377600) }, { argument := 18702985605086592244488601600, coefficient := (-18702985605086592244488601600) }, { argument := 194938091103876420210786304000, coefficient := (-194938091103876420210786304000) }, { argument := 18702985605086592244488601600, coefficient := (-18702985605086592244488601600) }, { argument := 126632689902524256852377600, coefficient := (-126632689902524256852377600) }, { argument := 2303561054738055711917342720, coefficient := (-2303561054738055711917342720) }, { argument := 83481815105116030525232906240, coefficient := (-83481815105116030525232906240) }, { argument := 83481845784357268113430937600, coefficient := (-83481845784357268113430937600) }, { argument := 2303530375496818123719311360, coefficient := (-2303530375496818123719311360) }, { argument := 119787679637522945671168000, coefficient := (-119787679637522945671168000) }, { argument := 17692013410217046717759488000, coefficient := (-17692013410217046717759488000) }] }

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

end TermShard5


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
